(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan): the inner walk from the join 0x13b28 to
   0x13c34, L02W_inv.L02_back_stmt. The UBSan twin of
   lib/Prog/Seg/L02W_back.v.
   - 0x13b28-0x13b2c: s0 = f + 1 (`addiw`), `bgeu s0,s10` to the last turn;
   - walk_drop, a drop-in turn (f + 1 < nfiles): m_file(m, t, label) 0x13b3c (m from the frame cell 0x50),
     reac_segconf_parse_file(c, t, label) 0x13b4c (c from 0x48), the trap 0x13b54 (`ld 0x38(sp)` = m & 3 = 0, not
     taken), s4 &= (a0 == m->n) ? -1 : 0, to 0x13c2c;
   - walk_last, the last turn: m_file(m, t, NULL) 0x13b7c, the trap 0x13b84, the inline m_cross 0x13b88-0x13c08
     (walk_loop: an induction on the entries left; the traps 0x13b9c (i = 33: i < m->n <= 32) and 0x13ba0
     (~m < 256 i: m + 9236 <= 2^47) not taken; the state after i entries is fold_left m_cross_seg (seq 0 i) of
     m_file's model; m_refuse(m, 0) at 0x13bcc / 0x13bec and the `sw zero` field stores, re-encoded by L02W_mx),
     then reac_segconf_parse(c, t) 0x13c14, s4 &= (a0 == m->n), s10 = nfiles (walk_cross);
   - walk_K, 0x13c2c-0x13c30: s1 -= s6, a0 = s7: L02_post at 0x13c34.
   Segment lemma of LLVMFuzzerTestOneInput's walk: L02 from 0x13b28, UBSan. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c printf_facts_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memcpy_c snprintf_m_c memset_c m_refuse_c
  reac_segconf_parse_file_c reac_segconf_parse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M L02W_mx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import L02D L02W_inv.
Import ListNotations.
Open Scope Z_scope.

(** ** The model side (as lib/Prog/Seg/L02W_back.v) *)
Lemma l02_step_drop : forall s lb rc mc ret,
  l02_step s lb false (rc, mc, ret) =
  (fst (r_parse_file rc s (label_of lb)), m_file mc s (label_of lb),
   ret && (snd (r_parse_file rc s (label_of lb)) =? Z.of_nat (length (mc_seg (m_file mc s (label_of lb)))))).
Proof. intros. unfold l02_step. destruct (r_parse_file rc s (label_of lb)). reflexivity. Qed.

Lemma l02_step_last : forall s lb rc mc ret,
  l02_step s lb true (rc, mc, ret) =
  (fst (r_parse rc s), m_cross (m_file mc s None),
   ret && (snd (r_parse rc s) =? Z.of_nat (length (mc_seg (m_cross (m_file mc s None)))))).
Proof. intros. unfold l02_step. destruct (r_parse rc s). reflexivity. Qed.

Lemma r_parse_file_n : forall rc s l, snd (r_parse_file rc s l) = Z.of_nat (length (rc_seg (fst (r_parse_file rc s l)))).
Proof. intros. unfold r_parse_file. destruct (r_lines _ _ _) as [[c2 x] y]. reflexivity. Qed.

Lemma r_cross_seg_len : forall c i, length (rc_seg (r_cross_seg c i)) = length (rc_seg c).
Proof.
  intros c i. unfold r_cross_seg. cbv zeta.
  destruct (rs_model_set _ && negb _); [|destruct (_ && negb _)].
  - unfold r_upd, r_set_segs. cbn [rc_seg]. rewrite mx_upd_nth_length. apply (f_equal (@length rseg)).
    apply (proj1 (refuse_proj _ _ _ _)).
  - unfold r_upd, r_set_segs. cbn [rc_seg]. rewrite mx_upd_nth_length. apply (f_equal (@length rseg)).
    apply (proj1 (refuse_proj _ _ _ _)).
  - reflexivity.
Qed.

Lemma cross_check_len : forall c, length (rc_seg (cross_check c)) = length (rc_seg c).
Proof.
  intros c. unfold cross_check. generalize (seq 0 (length (rc_seg c))) as l. intros l. revert c.
  induction l as [|i l IH]; intros c; [reflexivity|]. cbn [fold_left]. rewrite IH. apply r_cross_seg_len.
Qed.

Lemma r_parse_n : forall rc s, snd (r_parse rc s) = Z.of_nat (length (rc_seg (fst (r_parse rc s)))).
Proof.
  intros rc s. unfold r_parse. destruct (r_parse_file rc s (Some S_base)) as [c1 n] eqn:E. cbn [fst snd].
  rewrite cross_check_len. pose proof (r_parse_file_n rc s (Some S_base)) as H. rewrite E in H. exact H.
Qed.

Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity|]. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma swrap32_small : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 v = v.
Proof. intros v Hv. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma bv_sub_lits : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma b2z_rng : forall b, 0 <= b2z b <= 1.
Proof. intros []; cbn; lia. Qed.

Lemma lts_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.

Lemma eqb_lits : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma lxor_pos : forall r k, 0 <= r -> 0 <= k -> r <> k -> 0 < Z.lxor r k.
Proof.
  intros r k Hr Hk E. assert (N : 0 <= Z.lxor r k) by (apply Z.lxor_nonneg; split; intros; lia).
  assert (Z.lxor r k <> 0) by (intros H0; apply Z.lxor_eq in H0; lia). lia.
Qed.

(** The returned flag of a drop-in turn: a0 = (n == m->n) ? -1 : 0, then s4 = a0 & s4. *)
Lemma flag_drop : forall r k b, 0 <= r -> 0 <= k ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.b2z (0 <? Z.lxor r k) + -1)))) (b2z b) = b2z (b && (r =? k)).
Proof.
  intros r k b Hr Hk. destruct (Z.eqb_spec r k) as [E|E].
  - subst k. rewrite Z.lxor_nilpotent. destruct b; reflexivity.
  - replace (0 <? Z.lxor r k) with true by (symmetry; apply Z.ltb_lt; apply lxor_pos; assumption).
    destruct b; reflexivity.
Qed.

(** The last turn's: a0 = (n == m->n), then s4 = a0 & s4. *)
Lemma flag_last : forall r k b, 0 <= r -> 0 <= k ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z (Z.lxor r k <? 1)))) (b2z b) = b2z (b && (r =? k)).
Proof.
  intros r k b Hr Hk. destruct (Z.eqb_spec r k) as [E|E].
  - subst k. rewrite Z.lxor_nilpotent. destruct b; reflexivity.
  - replace (Z.lxor r k <? 1) with false by (symmetry; apply Z.ltb_ge; pose proof (lxor_pos r k Hr Hk E); lia).
    destruct b; reflexivity.
Qed.

(** The same two flags in the form the step tactics leave (each operand reduced mod 2^64). *)
Lemma flag_drop_z : forall r k b, 0 <= r -> 0 <= k ->
  Z.land (bv_swrap 32 (Z.b2z (0 <? Z.lxor r k) + -1) mod 18446744073709551616) (b2z b mod 18446744073709551616) =
  b2z (b && (r =? k)).
Proof.
  intros r k b Hr Hk. destruct (Z.eqb_spec r k) as [E|E].
  - subst k. rewrite Z.lxor_nilpotent. destruct b; reflexivity.
  - replace (0 <? Z.lxor r k) with true by (symmetry; apply Z.ltb_lt; apply lxor_pos; assumption).
    destruct b; reflexivity.
Qed.

Lemma flag_last_z : forall r k b, 0 <= r -> 0 <= k ->
  Z.land (Z.b2z (Z.lxor r k <? 1)) (b2z b mod 18446744073709551616) = b2z (b && (r =? k)).
Proof.
  intros r k b Hr Hk. destruct (Z.eqb_spec r k) as [E|E].
  - subst k. rewrite Z.lxor_nilpotent. destruct b; reflexivity.
  - replace (Z.lxor r k <? 1) with false by (symmetry; apply Z.ltb_ge; pose proof (lxor_pos r k Hr Hk E); lia).
    destruct b; reflexivity.
Qed.

(** m_cross's `addi a0,a0,-4; seqz a0,a0` on a role other than 4 (0 <= role < 2^31). *)
Lemma seqz_ne4 : forall r, 0 <= r < 2 ^ 31 -> r <> 4 -> ((r + -4) mod 18446744073709551616 <? 1) = false.
Proof.
  intros r Hr E. apply Z.ltb_ge.
  destruct (Z_lt_le_dec r 4) as [L|L].
  - replace (r + -4) with ((r - 4 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(** ~m as an unsigned word (s2). *)
Lemma not_lit : forall mm, 0 <= mm < 2 ^ 64 -> bv_unsigned (bv_not (Z_to_bv 64 mm)) = 2 ^ 64 - 1 - mm.
Proof.
  intros mm H. rewrite bv_not_unsigned, unsigned_lit by lia. unfold bv_wrap, Z.lnot.
  change (bv_modulus 64) with (2 ^ 64).
  replace (Z.pred (- mm)) with ((2 ^ 64 - 1 - mm) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(** ** The back half *)
Section Back.
Variables (S c mm t nt src x1 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
  (gp tp s2 s3 : word) (m0 : word -> option byte).
Hypothesis HK : K_L02.
Hypothesis HST : l02_static S c mm t nt src s.
Hypothesis HMD : L02_model s lb rc mc.
Hypothesis Hf : 0 <= f < nf.
Hypothesis Hnf : nf <= 4.
Hypothesis Hs2 : bv_unsigned s2 = 2 ^ 64 - 1 - mm.

Local Abbreviation Post := (L02_post S c mm t nt x1 x6 f nf lb s rc mc ret (Z_to_bv 64 (S - L02_FRAME)) gp tp
  s2 s3 (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 (mm + MC_N)) m0).
Local Abbreviation STP := (l02_step s lb (f + 1 =? nf) (rc, mc, ret)).

(** The bounds a step's side conditions need, without the disjunctions. *)
Lemma bk_bounds : 2 ^ 40 + 65536 <= S <= 2 ^ 47 /\ 0 < c /\ c + 16616 <= S - 65536 /\ 0 < mm /\
  mm + 9236 <= S - 65536 /\ 0 < t /\ t + nt <= S - 65536 /\ nt = Z.of_nat (length s) + 1 /\ 0 <= src.
Proof. pose proof HST as H. st_dst H. unfold SEG_C_SIZE, SEG_M_SIZE in *. lia. Qed.

Lemma bk_m4 : mm mod 4 = 0.
Proof. pose proof HST as H. st_dst H. clear - Hm16. Z.div_mod_to_equations. lia. Qed.

(** The facts every point after 0x13b28 carries. *)
Definition bst (m : word -> option byte) : Prop :=
  munch (L02_W S c mm t nt) m0 m /\ wmono rsegs m0 m /\ l02_env S c mm nf m /\ txt_at t s m.

Lemma bst_tr : forall m m' W, bst m -> munch W m m' -> sub_fp W (A_back S c mm) -> wmono rsegs m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (S - 65472) (S - 240) -> bst m'.
Proof.
  intros m m' W (MU0 & WM0 & ENV & TXT) MU SF WM MI TM ST.
  pose proof (st_num _ _ _ _ _ _ _ HST) as HN. pose proof (sub_fp_trans _ _ _ SF (A_back_all S c mm t nt)) as SFa.
  refine (conj (munch_acc S c mm t nt m0 m m' W MU0 MU SFa) (conj (wmono_trans _ _ _ _ WM0 WM) (conj _ _))).
  - exact (env_tr S c mm nf t nt m m' W HN ENV MU SFa WM MI TM ST).
  - pose proof bk_bounds as (_ & _ & _ & _ & _ & _ & _ & Hnt & _).
    exact (txt_tr S c mm t nt s m m' W HN Hnt TXT MU SF).
Qed.

(** A 4-byte store of zero into m->seg[i] (i < 32). *)
Lemma bst_store : forall m i off, bst m -> (i < 32)%nat -> 0 <= off -> off + 4 <= 256 ->
  bst (write_to_mem m (wa (mm + 256 * Z.of_nat i + off)) (le4 (Z_to_bv 64 0))) /\
  store_ok rsegs m (wa (mm + 256 * Z.of_nat i + off)) 4 = true.
Proof.
  intros m i off B Hi H1 H2. pose proof bk_bounds as BB.
  pose proof B as (_ & _ & ENV & _). env_dst ENV.
  assert (SO : store_ok rsegs m (wa (mm + 256 * Z.of_nat i + off)) 4 = true).
  { replace (mm + 256 * Z.of_nat i + off) with (mm + (256 * Z.of_nat i + off)) by lia.
    apply (wr_at_store_ok rsegs m mm SEG_M_SIZE); [exact EWM | lia | unfold SEG_M_SIZE; lia]. }
  split; [|exact SO].
  assert (L4 : length (le4 (Z_to_bv 64 0)) = 4%nat) by apply length_le4.
  pose proof (munch_store m (mm + 256 * Z.of_nat i + off) (le4 (Z_to_bv 64 0)) ltac:(lia) ltac:(rewrite L4; lia))
    as MU.
  rewrite L4 in MU. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in MU.
  eapply bst_tr; [exact B | exact MU | |
    exact (wmono_write rsegs m m (wa (mm + 256 * Z.of_nat i + off)) (le4 (Z_to_bv 64 0)) (wmono_refl rsegs m)) | | | ].
  - eapply sub_fp_trans; [apply (W_seg4 S mm i off Hi H1 H2) | apply A_m_back].
  - refine (mem_inv_store rsegs m (wa (mm + 256 * Z.of_nat i + off)) (le4 (Z_to_bv 64 0)) EMI _).
    rewrite L4. exact SO.
  - eapply task_mem_out; [exact ETM | exact MU|]. intros x Hx. rewrite TASK_SIZE_val.
    destruct (Z_lt_le_dec x (mm + 256 * Z.of_nat i + off + 4)) as [L|L]; [left; lia|].
    right. cbn [outside]. split; [lia | exact I].
  - refine (stk_write rsegs m _ _ (mm + 256 * Z.of_nat i + off) (le4 (Z_to_bv 64 0)) EST _ _); [lia | rewrite L4; lia].
Qed.

(** ** 0x13c2c - 0x13c30 *)
Lemma walk_K : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4w s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  frm0 fc -> munch (L02_W S c mm t nt) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  rconf_at rsegs m c (seg_rc STP) -> mconf_at rsegs m mm (seg_mc STP) ->
  s4w = Z_to_bv 64 (b2z (seg_ret STP)) ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6
             a7 s2 s3 s4w (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) s8 s9 (Z_to_bv 64 nf)
             (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c2c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4w s8 s9 t3 t4 t5 t6 F fc m FRM MU WM MI TM RC MC HA.
  do 2 step.
  apply evt_done. unfold L02_post.
  do 23 eexists. exists F, fc, m. split; [reflexivity|].
  split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact TM|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [first [reflexivity | apply bv_sub_lits]|]. split; [reflexivity|].
  split; [exact HA|]. split; [exact RC | exact MC].
Qed.

(** A load of one of main's frame cells. *)
Lemma rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v B.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 B ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal.
Qed.

Lemma lab_rng : forall lp lab m, lab_ok S lp lab m -> 0 <= lp < 2 ^ 47.
Proof.
  intros lp [l|] m H; [|cbn in H; lia]. destruct H as (P & _ & _ & R). pose proof bk_bounds. lia.
Qed.

(** Branch tactics: ntk for a branch the facts refute (not taken), tkn for one they force. *)
Ltac ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia
      | clear K ]
  | _ => idtac end.
Ltac tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ clear K
      | exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia ]
  | _ => idtac end.

(** A condition with no variable left: compute it. *)
Ltac if_closed := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      lazymatch v with
      | true => replace cnd with true by (vm_compute; reflexivity)
      | false => replace cnd with false by (vm_compute; reflexivity)
      end; cbv iota
  end.

(** ** A drop-in turn: 0x13b28 - 0x13b6c *)
Lemma walk_drop : f + 1 < nf ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lp : Z),
  frm0 fc -> bst m -> rconf_at rsegs m c rc -> mconf_at rsegs m mm mc -> lab_ok S lp (label_of lb) m ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) s8 (Z_to_bv 64 lp)
             (Z_to_bv 64 nf) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs)).
Proof.
  intros Hlast ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc m lp FRM B RC MC LAB.
  pose proof HK as (_ & _ & _ & HMF & _ & HPF & _).
  pose proof bk_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Hnt & Bsrc).
  pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  pose proof HMD as (HsF & HsL & Hlb & R1 & R2 & R3 & M1 & M2 & M3).
  pose proof (lab_rng lp _ m LAB) as LP.
  pose proof B as (_ & _ & ENV & TXT).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F50 & _).
  pose proof (rd8 m _ _ F50) as R50.
  (* 0x13b28 addiw s0,s0,1 *)
  zstep. rewrite swrap32_small by lia.
  (* bgeu s0,s10: f + 1 < nf, not taken *)
  zstep. ntk.
  (* 0x13b30 ld a0,0x50(sp); mv a1,s7; mv a2,s9; jal m_file *)
  do 4 zstep.
  eapply evt_cut.
  { eapply HMF with (lo := S - 65472) (mc := mc) (s := s) (lab := label_of lb).
    rewrite !unsigned_lit by lia.
    exact (mfile_pre_of S c mm nf t nt src s m fc mc lp (label_of lb) HST ENV TXT MC M1 ltac:(lia) M3 LAB FRM). }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 &
    m1 & -> & FRM1 & _ & MU1 & WM1 & MI1 & TM1 & ST1 & MC1).
  rewrite ret_pc_even by (try lia; reflexivity).
  repeat (rewrite unsigned_lit in MU1 by lia). repeat (rewrite unsigned_lit in ST1 by lia).
  repeat (rewrite unsigned_lit in MC1 by lia).
  pose proof (mconf_len _ _ _ MC1) as (L1 & L2).
  pose proof (W_mfile S mm (length (mc_kept mc)) (m_file mc s (label_of lb)) L1 L2) as SFm.
  pose proof (sub_fp_trans _ _ _ SFm (A_m_back S c mm)) as SFb.
  pose proof (bst_tr m m1 _ B MU1 SFb WM1 MI1 TM1 ST1) as B1.
  pose proof (rc_tr m m1 _ c rc RC MU1 (fun x Hx => SFm x (out_c_m S c mm t nt x HN Hx))) as RC1.
  pose proof (lab_tr S c mm t nt lp (label_of lb) m m1 _ HN LAB MU1 SFb) as LAB1.
  clear MU1 SFm SFb WM1 MI1 TM1 ST1 B RC MC LAB ENV TXT R50 F50.
  pose proof B1 as (_ & _ & ENV1 & TXT1).
  pose proof ENV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F48 & _).
  pose proof (rd8 m1 _ _ F48) as R48.
  (* 0x13b40 ld a0,0x48(sp); mv a1,s7; mv a2,s9; jal reac_segconf_parse_file *)
  do 4 zstep.
  eapply evt_cut.
  { eapply HPF with (lo := S - 65472) (rc := rc) (s := s) (lab := label_of lb).
    rewrite !unsigned_lit by lia. split.
    - apply (reader_pre_of S c mm nf t nt src s m1 fc1 rc _ HST ENV1 TXT1 RC1 R1 R2 R3 FRM1).
      unfold reac_segconf_parse_file_c.PARSE_FILE_STACK, reac_segconf_parse_file_c.PARSE_FILE_FRAME, REFUSE_STACK,
        PRINTF_K. lia.
    - exact (pfile_lab_of S c mm t nt src s m1 lp (label_of lb) HST LAB1). }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
    F2 & fc2 & m2 & -> & FRM2 & _ & MU2 & WM2 & MI2 & TM2 & ST2 & RC2).
  rewrite ret_pc_even by (try lia; reflexivity).
  repeat (rewrite unsigned_lit in MU2 by lia). repeat (rewrite unsigned_lit in ST2 by lia).
  repeat (rewrite unsigned_lit in RC2 by lia).
  pose proof (mc_tr m1 m2 _ mm _ MC1 MU2 (fun x Hx => W_pfile S c x (out_m_c S c mm t nt x HN Hx))) as MC2.
  pose proof (bst_tr m1 m2 _ B1 MU2 (sub_fp_trans _ _ _ (W_pfile S c) (A_c_back S c mm)) WM2 MI2 TM2 ST2) as B2.
  pose proof (rconf_len _ _ _ RC2) as LR. pose proof (mconf_len _ _ _ MC2) as (LM & _).
  pose proof (mx_read_n rsegs m2 mm _ MC2) as RN.
  pose proof (r_parse_file_n rc s (label_of lb)) as En.
  pose proof B2 as (_ & _ & ENV2 & _).
  pose proof ENV2 as (_ & _ & _ & _ & _ & _ & _ & _ & F38 & _).
  rewrite bk_m4 in F38. pose proof (rd8 m2 _ _ F38) as R38.
  (* 0x13b50 ld a1,0x38(sp); bnez a1: m & 3 = 0, not taken *)
  zstep. zstep. first [if_closed | ntk].
  (* 0x13b58 lw a1,0(s11) *)
  zstep. rewrite sx32_small by lia.
  (* xor a0,a0,a1; snez a0,a0; addiw a0,a0,-1; and s4,a0,s4; j 0x13c2c *)
  do 5 zstep.
  pose proof B2 as (MU02 & WM02 & _).
  assert (EL : (f + 1 =? nf) = false) by (apply Z.eqb_neq; lia).
  eapply walk_K; [exact FRM2 | exact MU02 | exact WM02 | exact MI2 | exact TM2 | | | ];
    rewrite EL, l02_step_drop; cbn [seg_rc seg_mc seg_ret fst snd].
  - exact RC2.
  - exact MC2.
  - f_equal. first [apply flag_drop_z | pose proof (b2z_rng ret); rewrite (unsigned_lit (b2z ret)) by lia; apply flag_drop]; lia.
Qed.

(** ** The last turn: m_cross's loop 0x13b9c - 0x13c08, then the reader's parse 0x13c0c - 0x13c28 *)
Lemma walk_cross : f + 1 = nf ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
  frm0 fc -> bst m -> rconf_at rsegs m c rc -> mconf_at rsegs m mm (m_cross (m_file mc s None)) ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6
             a7 s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) s8 s9 s10
             (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c0c) fc None m (seg_rom rsegs)).
Proof.
  intros Hlast ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc m FRM B RC MC.
  pose proof HK as (_ & _ & _ & _ & _ & _ & HPA).
  pose proof bk_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Hnt & Bsrc).
  pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  pose proof HMD as (HsF & HsL & Hlb & R1 & R2 & R3 & M1 & M2 & M3).
  pose proof B as (_ & _ & ENV & TXT).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F48 & _).
  pose proof (rd8 m _ _ F48) as R48.
  (* 0x13c0c ld a0,0x48(sp); mv a1,s7; jal reac_segconf_parse *)
  do 3 zstep.
  eapply evt_cut.
  { eapply HPA with (lo := S - 65472) (rc := rc) (s := s).
    repeat (rewrite unsigned_lit by lia).
    apply (reader_pre_of S c mm nf t nt src s m fc rc _ HST ENV TXT RC R1 R2 R3 FRM).
    unfold reac_segconf_parse_c.PARSE_STACK, reac_segconf_parse_file_c.PARSE_FILE_STACK,
      reac_segconf_parse_file_c.PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K. lia. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
    F2 & fc2 & m2 & -> & FRM2 & _ & MU2 & WM2 & MI2 & TM2 & ST2 & RC2).
  rewrite ret_pc_even by (try lia; reflexivity).
  repeat (rewrite unsigned_lit in MU2 by lia). repeat (rewrite unsigned_lit in ST2 by lia).
  repeat (rewrite unsigned_lit in RC2 by lia).
  pose proof (mc_tr m m2 _ mm _ MC MU2 (fun x Hx => W_parse S c x (out_m_c S c mm t nt x HN Hx))) as MC2.
  pose proof (bst_tr m m2 _ B MU2 (sub_fp_trans _ _ _ (W_parse S c) (A_c_back S c mm)) WM2 MI2 TM2 ST2) as B2.
  pose proof (rconf_len _ _ _ RC2) as LR. pose proof (mconf_len _ _ _ MC2) as (LM & _).
  pose proof (mx_read_n rsegs m2 mm _ MC2) as RN.
  pose proof (r_parse_n rc s) as En.
  pose proof B2 as (_ & _ & ENV2 & _).
  pose proof ENV2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F40 & _).
  pose proof (rd8 m2 _ _ F40) as R40.
  (* 0x13c18 lw a1,0(s11); xor a0,a0,a1; seqz a0,a0; and s4,a0,s4; ld s10,0x40(sp) *)
  zstep. rewrite sx32_small by lia.
  do 4 zstep.
  pose proof B2 as (MU02 & WM02 & _).
  assert (EL : (f + 1 =? nf) = true) by (apply Z.eqb_eq; lia).
  eapply walk_K; [exact FRM2 | exact MU02 | exact WM02 | exact MI2 | exact TM2 | | | ];
    rewrite EL, l02_step_last; cbn [seg_rc seg_mc seg_ret fst snd].
  - exact RC2.
  - exact MC2.
  - f_equal. first [apply flag_last_z | pose proof (b2z_rng ret); rewrite (unsigned_lit (b2z ret)) by lia; apply flag_last]; lia.
Qed.

(** m_cross's refusals: at most one per entry before, at most one per line in m_file. *)
Lemma cross_refused : forall i, (i < 32)%nat ->
  mc_refused (fold_left m_cross_seg (seq 0 i) (m_file mc s None)) + 1 < 2 ^ 32.
Proof.
  intros i Hi. pose proof (mx_refused (m_file mc s None) i) as H1.
  pose proof HMD as (HsF & HsL & _ & _ & _ & _ & _ & M2 & _).
  pose proof (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.m_file_c.m_file_refused mc s None (Forall_nul s HsF)) as H2.
  pose proof (nat_le_65535 _ HsL). lia.
Qed.

(** A store into m->seg[i] keeps c's block. *)
Lemma rc_store : forall m i off, rconf_at rsegs m c rc -> (i < 32)%nat -> 0 <= off -> off + 4 <= 256 ->
  rconf_at rsegs (write_to_mem m (wa (mm + 256 * Z.of_nat i + off)) (le4 (Z_to_bv 64 0))) c rc.
Proof.
  intros m i off RC Hi H1 H2. pose proof bk_bounds as BB. pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  assert (L4 : length (le4 (Z_to_bv 64 0)) = 4%nat) by apply length_le4.
  pose proof (munch_store m (mm + 256 * Z.of_nat i + off) (le4 (Z_to_bv 64 0)) ltac:(lia) ltac:(rewrite L4; lia))
    as MU.
  rewrite L4 in MU.
  apply (rc_tr _ _ _ c rc RC MU). intros x Hx. apply (W_seg4 S mm i off Hi H1 H2). exact (out_c_m S c mm t nt x HN Hx).
Qed.

Lemma walk_loop : f + 1 = nf -> forall k i (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8w s9w s10w t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (i + k = length (mc_seg (m_file mc s None)))%nat -> (0 < k)%nat ->
  s8w = Z_to_bv 64 (256 * Z.of_nat i) -> s9w = Z_to_bv 64 (Z.of_nat i) ->
  s10w = Z_to_bv 64 (mm + 16 + 256 * Z.of_nat i) ->
  frm0 fc -> bst m -> rconf_at rsegs m c rc ->
  mconf_at rsegs m mm (fold_left m_cross_seg (seq 0 i) (m_file mc s None)) ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6
             a7 s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) s8w s9w s10w
             (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b9c) fc None m (seg_rom rsegs)).
Proof.
  intros Hlast k. induction k as [|k IH];
    intros i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8w s9w s10w t3 t4 t5 t6 F fc m Hik Hk E8 E9 E10 FRM B RC MC;
    [lia|].
  subst s8w s9w s10w.
  pose proof HK as (_ & _ & _ & _ & HMR & _ & _).
  pose proof bk_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Hnt & Bsrc).
  pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  remember (fold_left m_cross_seg (seq 0 i) (m_file mc s None)) as cur eqn:Ecur.
  assert (Elen : length (mc_seg cur) = length (mc_seg (m_file mc s None))) by (subst cur; apply mx_len).
  assert (Hi : (i < length (mc_seg cur))%nat) by lia.
  pose proof (mconf_len _ _ _ MC) as (L32 & LK).
  assert (Hi32 : (i < 32)%nat) by lia.
  assert (HR : mc_refused cur + 1 < 2 ^ 32) by (subst cur; apply cross_refused; lia).
  (* The tail 0x13bf8: m->n again, i + 1, s10 + 256, s8 + 256, `blt` back or out. *)
  assert (TAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    frm0 fc' -> bst m' -> rconf_at rsegs m' c rc -> mconf_at rsegs m' mm (m_cross_seg cur i) ->
    evt rsegs Post
      (MS (mkR ra' (Z_to_bv 64 (S - 240)) gp tp t0' t1' t2' (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0' a1' a2'
               a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t)
               (Z_to_bv 64 (256 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (mm + 16 + 256 * Z.of_nat i))
               (Z_to_bv 64 (mm + MC_N)) t3' t4' t5' t6')
          F' (Z_to_bv 64 0x13bf8) fc' None m' (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' B' RC' MC'.
    pose proof (mx_read_n rsegs m' mm _ MC') as RN.
    rewrite mx_seg_len, Elen in RN.
    zstep. rewrite sx32_small by lia.
    do 4 zstep.
    rewrite lts_small by lia.
    destruct k as [|k].
    - ntk.
      eapply walk_cross; [exact Hlast | exact FRM' | exact B' | exact RC' |].
      rewrite mx_all. replace (length (mc_seg (m_file mc s None))) with (Datatypes.S i) by lia.
      rewrite mx_step, <- Ecur. exact MC'.
    - tkn.
      eapply (IH (Datatypes.S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact FRM' | exact B'
        | exact RC' |].
      rewrite mx_step, <- Ecur. exact MC'. }
  pose proof B as (_ & _ & ENV & TXT).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F50 & _).
  pose proof (rd8 m _ _ F50) as R50.
  (* PA, 0x13bc4: m_refuse(m, 0), m->seg[i].model_set = 0, to the tail. *)
  assert (PA : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    m_cross_seg cur i = m_upd (m_refuse cur 0 false) i ms_drop_model ->
    evt rsegs Post
      (MS (mkR ra' (Z_to_bv 64 (S - 240)) gp tp t0' t1' t2' (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0' a1' a2'
               a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t)
               (Z_to_bv 64 (256 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (mm + 16 + 256 * Z.of_nat i))
               (Z_to_bv 64 (mm + MC_N)) t3' t4' t5' t6')
          F (Z_to_bv 64 0x13bc4) fc None m (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' EQ.
    do 3 zstep.
    eapply evt_cut.
    { eapply HMR with (lo := S - 65472) (mc := cur) (knock := false).
      repeat (rewrite unsigned_lit by lia).
      exact (mrefuse_pre_of S c mm nf t nt src s m fc cur HST ENV MC HR FRM). }
    intros ms' (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
      t6'' & F1 & fc1 & m1 & -> & FRM1 & _ & MU1 & WM1 & MI1 & TM1 & ST1 & MC1).
    rewrite ret_pc_even by (try lia; reflexivity).
    repeat (rewrite unsigned_lit in MU1 by lia). repeat (rewrite unsigned_lit in ST1 by lia).
    repeat (rewrite unsigned_lit in MC1 by lia).
    pose proof (W_mrefuse S mm cur LK) as SFm.
    pose proof (bst_tr m m1 _ B MU1 (sub_fp_trans _ _ _ SFm (A_m_back S c mm)) WM1 MI1 TM1 ST1) as B1.
    pose proof (rc_tr m m1 _ c rc RC MU1 (fun x Hx => SFm x (out_c_m S c mm t nt x HN Hx))) as RC1.
    destruct (bst_store m1 i 0x20 B1 Hi32 ltac:(lia) ltac:(lia)) as (B2 & SO).
    (* 0x13bd0 sw zero,0x10(s10) *)
    zstep.
    (* 0x13bd4 j 0x13bf8 *)
    zstep.
    eapply TAIL; [exact FRM1 | exact B2 | exact (rc_store m1 i 0x20 RC1 Hi32 ltac:(lia) ltac:(lia)) |].
    rewrite EQ. apply mx_store_drop_model; [exact MC1 | rewrite mx_refuse_seg; exact Hi]. }
  (* PB, 0x13be4: m_refuse(m, 0), m->seg[i].role = 0 and role_set = 0, on to the tail. *)
  assert (PB : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    m_cross_seg cur i = m_upd (m_refuse cur 0 false) i ms_drop_role ->
    evt rsegs Post
      (MS (mkR ra' (Z_to_bv 64 (S - 240)) gp tp t0' t1' t2' (Z_to_bv 64 (f + 1)) (Z_to_bv 64 x1) a0' a1' a2'
               a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t)
               (Z_to_bv 64 (256 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (mm + 16 + 256 * Z.of_nat i))
               (Z_to_bv 64 (mm + MC_N)) t3' t4' t5' t6')
          F (Z_to_bv 64 0x13be4) fc None m (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' EQ.
    do 3 zstep.
    eapply evt_cut.
    { eapply HMR with (lo := S - 65472) (mc := cur) (knock := false).
      repeat (rewrite unsigned_lit by lia).
      exact (mrefuse_pre_of S c mm nf t nt src s m fc cur HST ENV MC HR FRM). }
    intros ms' (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
      t6'' & F1 & fc1 & m1 & -> & FRM1 & _ & MU1 & WM1 & MI1 & TM1 & ST1 & MC1).
    rewrite ret_pc_even by (try lia; reflexivity).
    repeat (rewrite unsigned_lit in MU1 by lia). repeat (rewrite unsigned_lit in ST1 by lia).
    repeat (rewrite unsigned_lit in MC1 by lia).
    pose proof (W_mrefuse S mm cur LK) as SFm.
    pose proof (bst_tr m m1 _ B MU1 (sub_fp_trans _ _ _ SFm (A_m_back S c mm)) WM1 MI1 TM1 ST1) as B1.
    pose proof (rc_tr m m1 _ c rc RC MU1 (fun x Hx => SFm x (out_c_m S c mm t nt x HN Hx))) as RC1.
    destruct (bst_store m1 i 0x10 B1 Hi32 ltac:(lia) ltac:(lia)) as (B2 & SO).
    (* 0x13bf0 sw zero,0(s10) *)
    zstep.
    destruct (bst_store _ i 0x14 B2 Hi32 ltac:(lia) ltac:(lia)) as (B3 & SO2).
    (* 0x13bf4 sw zero,4(s10) *)
    zstep.
    pose proof (rc_store m1 i 0x10 RC1 Hi32 ltac:(lia) ltac:(lia)) as RC2.
    eapply TAIL; [exact FRM1 | exact B3 | exact (rc_store _ i 0x14 RC2 Hi32 ltac:(lia) ltac:(lia)) |].
    rewrite EQ. apply mx_store_drop_role; [exact MC1 | rewrite mx_refuse_seg; exact Hi]. }
  (* The traps: 0x13b9c beq s9,s5 (i = 33) and 0x13ba0 bltu s2,s8 (~m < 256 i), not taken. *)
  zstep. rewrite eqb_lits by lia. first [if_closed | ntk].
  zstep. unfold bv_ltu. rewrite Hs2, unsigned_lit by lia. ntk.
  (* The entry: role_set, role, model_set of m->seg[i]. *)
  pose proof (mx_read_role_set rsegs m mm cur i MC Hi) as RRS.
  pose proof (mx_read_model_set rsegs m mm cur i MC Hi) as RMS.
  pose proof (mx_read_role rsegs m mm cur i MC Hi) as (ROk & RRO).
  assert (Ecs : m_cross_seg cur i =
    if ms_model_set (nth i (mc_seg cur) mseg_d) && negb (ms_role_set (nth i (mc_seg cur) mseg_d) &&
         (ms_role (nth i (mc_seg cur) mseg_d) =? 4))
    then m_upd (m_refuse cur 0 false) i ms_drop_model
    else if (ms_role_set (nth i (mc_seg cur) mseg_d) && (ms_role (nth i (mc_seg cur) mseg_d) =? 4)) &&
            negb (ms_model_set (nth i (mc_seg cur) mseg_d))
    then m_upd (m_refuse cur 0 false) i ms_drop_role else cur) by reflexivity.
  remember (nth i (mc_seg cur) mseg_d) as g eqn:Eg.
  destruct (ms_role_set g) eqn:ERS; try rewrite ERS in RRS; try rewrite ERS in Ecs; cbn [b2z] in RRS.
  - (* role_set = 1: 0x13ba4 lw, beqz not taken, 0x13bac lw role *)
    zstep. rewrite sx32_small by lia. zstep. first [if_closed | ntk].
    zstep. rewrite sx32_small by lia.
    destruct (Z.eqb_spec (ms_role g) 4) as [E4|E4].
    + rewrite E4. try rewrite E4 in Ecs; try rewrite Z.eqb_refl in Ecs.
      (* addi a0,a0,-4; seqz a0,a0: a0 = 1 *)
      zstep. zstep.
      destruct (ms_model_set g) eqn:EMS; try rewrite EMS in RMS; try rewrite EMS in Ecs;
        cbn [b2z andb negb] in RMS, Ecs.
      * (* model_set: beqz a1 not taken, bnez a0 taken, seqz, and, beqz taken: nothing *)
        zstep. rewrite sx32_small by lia. zstep. first [if_closed | ntk].
        zstep. first [if_closed | tkn].
        do 3 zstep. first [if_closed | tkn].
        eapply TAIL; [exact FRM | exact B | exact RC | rewrite Ecs; exact MC].
      * (* no model: beqz a1 taken, seqz, and, beqz not taken: drop the role *)
        zstep. rewrite sx32_small by lia. zstep. first [if_closed | tkn].
        do 3 zstep. first [if_closed | ntk].
        eapply PB. exact Ecs.
    + try rewrite (proj2 (Z.eqb_neq _ _) E4) in Ecs.
      (* addi a0,a0,-4; seqz a0,a0: a0 = 0 *)
      zstep. zstep. rewrite (seqz_ne4 (ms_role g) ROk E4).
      destruct (ms_model_set g) eqn:EMS; try rewrite EMS in RMS; try rewrite EMS in Ecs;
        cbn [b2z andb negb] in RMS, Ecs.
      * (* model_set, no box: beqz a1 not taken, bnez a0 not taken: drop the model *)
        zstep. rewrite sx32_small by lia. zstep. first [if_closed | ntk].
        zstep. first [if_closed | ntk].
        eapply PA. exact Ecs.
      * (* neither: beqz a1 taken, seqz, and, beqz taken *)
        zstep. rewrite sx32_small by lia. zstep. first [if_closed | tkn].
        do 3 zstep. first [if_closed | tkn].
        eapply TAIL; [exact FRM | exact B | exact RC | rewrite Ecs; exact MC].
  - (* role_set = 0: beqz taken, a0 = 0 *)
    zstep. rewrite sx32_small by lia. zstep. first [if_closed | tkn].
    destruct (ms_model_set g) eqn:EMS; try rewrite EMS in RMS; try rewrite EMS in Ecs;
      cbn [b2z andb negb] in RMS, Ecs.
    + (* model_set: beqz a1 not taken, bnez a0 not taken: drop the model *)
      zstep. rewrite sx32_small by lia. zstep. first [if_closed | ntk].
      zstep. first [if_closed | ntk].
      eapply PA. exact Ecs.
    + (* neither: beqz a1 taken, seqz, and, beqz taken *)
      zstep. rewrite sx32_small by lia. zstep. first [if_closed | tkn].
      do 3 zstep. first [if_closed | tkn].
      eapply TAIL; [exact FRM | exact B | exact RC | rewrite Ecs; exact MC].
Qed.

Lemma walk_last : f + 1 = nf ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lp : Z),
  frm0 fc -> bst m -> rconf_at rsegs m c rc -> mconf_at rsegs m mm mc ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (S - 240)) gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 x1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3
             (Z_to_bv 64 (b2z ret)) (Z_to_bv 64 33) (Z_to_bv 64 x6) (Z_to_bv 64 t) s8 (Z_to_bv 64 lp)
             (Z_to_bv 64 nf) (Z_to_bv 64 (mm + MC_N)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b28) fc None m (seg_rom rsegs)).
Proof.
  intros Hlast ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc m lp FRM B RC MC.
  pose proof HK as (_ & _ & _ & HMF & _ & _ & _).
  pose proof bk_bounds as (BS & Bc0 & Bcb & Bm0 & Bmb & Bt0 & Btb & Hnt & Bsrc).
  pose proof (st_num _ _ _ _ _ _ _ HST) as HN.
  pose proof HMD as (HsF & HsL & Hlb & R1 & R2 & R3 & M1 & M2 & M3).
  pose proof B as (_ & _ & ENV & TXT).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F50 & _).
  pose proof (rd8 m _ _ F50) as R50.
  (* 0x13b28 addiw s0,s0,1 *)
  zstep. rewrite swrap32_small by lia.
  (* bgeu s0,s10: f + 1 = nf, taken *)
  zstep. tkn.
  (* 0x13b70 ld a0,0x50(sp); mv a1,s7; mv a2,zero; jal m_file *)
  do 4 zstep.
  eapply evt_cut.
  { eapply HMF with (lo := S - 65472) (mc := mc) (s := s) (lab := None).
    repeat (rewrite unsigned_lit by lia).
    exact (mfile_pre_of S c mm nf t nt src s m fc mc 0 None HST ENV TXT MC M1 ltac:(lia) M3 eq_refl FRM). }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 &
    m1 & -> & FRM1 & _ & MU1 & WM1 & MI1 & TM1 & ST1 & MC1).
  rewrite ret_pc_even by (try lia; reflexivity).
  repeat (rewrite unsigned_lit in MU1 by lia). repeat (rewrite unsigned_lit in ST1 by lia).
  repeat (rewrite unsigned_lit in MC1 by lia).
  pose proof (mconf_len _ _ _ MC1) as (L1 & L2).
  pose proof (W_mfile S mm (length (mc_kept mc)) (m_file mc s None) L1 L2) as SFm.
  pose proof (bst_tr m m1 _ B MU1 (sub_fp_trans _ _ _ SFm (A_m_back S c mm)) WM1 MI1 TM1 ST1) as B1.
  pose proof (rc_tr m m1 _ c rc RC MU1 (fun x Hx => SFm x (out_c_m S c mm t nt x HN Hx))) as RC1.
  pose proof (mx_read_n rsegs m1 mm _ MC1) as RN.
  pose proof B1 as (_ & _ & ENV1 & _).
  pose proof ENV1 as (_ & _ & _ & _ & _ & _ & F28 & _ & F38 & _).
  rewrite bk_m4 in F38. pose proof (rd8 m1 _ _ F38) as R38.
  pose proof (rd8 m1 _ _ F28) as R28.
  (* 0x13b80 ld a0,0x38(sp); bnez a0: m & 3 = 0, not taken *)
  zstep. zstep. first [if_closed | ntk].
  (* 0x13b88 lw a0,0(s11); blez a0 *)
  zstep. rewrite sx32_small by lia.
  zstep.
  destruct (Nat.eq_dec (length (mc_seg (m_file mc s None))) 0) as [N0|N0].
  - (* no entry: to 0x13c0c *)
    tkn.
    eapply walk_cross; [exact Hlast | exact FRM1 | exact B1 | exact RC1 |].
    rewrite mx_all, N0. exact MC1.
  - ntk.
    (* 0x13b90 mv s8,zero; mv s9,zero; ld s10,0x28(sp) *)
    do 3 zstep.
    eapply (walk_loop Hlast (length (mc_seg (m_file mc s None))) 0);
      [lia | lia | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
      | first [reflexivity | f_equal; lia] | exact FRM1 | exact B1 | exact RC1 | exact MC1].
Qed.

End Back.

Theorem l02_back : K_L02 -> L02_back_stmt.
Proof.
  intros HK S c mm t nt src x1 x6 f nf lb s rc mc ret sp gp tp s2 s3 s5 s6 s11 m0 HST HMD Esp Es11 Es2 Es5 Hf Hnf
    Es6.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc m lp FRM MU WM ENV TXT RC MC LAB.
  assert (Hs2 : bv_unsigned s2 = 2 ^ 64 - 1 - mm).
  { subst s2. pose proof HST as H. st_dst H. apply not_lit. unfold SEG_M_SIZE in *. lia. }
  subst sp s11 s5 s6.
  destruct (Z.eq_dec (f + 1) nf) as [E|E].
  - eapply walk_last; first [eassumption | exact (conj MU (conj WM (conj ENV TXT))) | lia].
  - eapply walk_drop; first [eassumption | exact (conj MU (conj WM (conj ENV TXT))) | lia].
Qed.
