(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): the facts of the walk from 0x13984 to the
   join 0x139f0 (Prog/Seg/L02W_front.v) that step no instruction.
   - the branch conditions: `beqz` of a nonzero / zero word, `bltz` of lb << 56 (bit 7 of the label byte);
   - txt0 / txt_store: the text block at 0x13984 (L02_mem) and after memcpy(t, src, n) (0x1399c) and its NUL
     (`sb zero, 0(s9)`, 0x139a8): the writes inside [t, t + nt) and the bytes zb s ++ [0] at t;
   - l02_mid: the memory at 0x139ac: the writes inside L02_W, l02_env, txt_at, the two blocks' contents and the
     label calls' resources (longl's 128 bytes, the label buffer [S - 144, S - 104), the frame cell 0x28 = the
     label format's address);
   - l02_join: the memory facts L02_J takes at 0x139f0, from l02_mid in each label case: lb = 0 (no call),
     bit 7 set (memset(longl, 'L', 120), 0x139e4), 0 < lb < 128 (snprintf(sp + 0x40, 40, fmt, lb), 0x139c8);
   - memcpy_ok / snp_ok: the callee contracts at their call sites, premises discharged.
   Segment lemma of LLVMFuzzerTestOneInput's walk: L02's front memory facts. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env printf_facts_c
  printf_model_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require memcpy_c snprintf_m_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M L02D L02W_inv L02W_lab.
Import ListNotations.
Open Scope Z_scope.

(** ** Branch conditions *)
Lemma weq0_false : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma weq0_true : forall z, z = 0 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = true.
Proof. intros z ->. reflexivity. Qed.

(** `slli a0, s8, 0x38; bltz a0`: bit 7 of the byte lb. *)
Lemma bltz_lb : forall lb, 0 <= lb < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 lb)) 56)) (Z_to_bv 64 0) = (128 <=? lb).
Proof.
  intros lb H. rewrite bv_lts_zero_r. rewrite (unsigned_lit lb) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. apply eq_true_iff_eq. rewrite !Z.leb_le. lia.
Qed.

(** ** Cells and byte runs *)
Lemma rw1_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] ->
  bytes_at rsegs m A bs /\ length bs = n /\ wr_at rsegs m A (Z.of_nat n).
Proof.
  intros m A n bs ((Hwf & Hb) & Hw). cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf, Hb, Hw.
  rewrite app_nil_r in Hb. rewrite Nat.add_0_r in Hw. destruct Hwf as [L _].
  split; [exact Hb|]. split; [exact L | exact Hw].
Qed.

Lemma bytes_at_firstn : forall m a bs l, bytes_at rsegs m a bs -> (l <= length bs)%nat ->
  bytes_at rsegs m a (firstn l bs).
Proof.
  intros m a bs l H Hl. pose proof (bytes_at_sub m a bs 0 l H ltac:(lia)) as H'.
  cbn [Z.of_nat skipn] in H'. rewrite Z.add_0_r in H'. exact H'.
Qed.

Lemma rw1_prefix : forall m A n bs j, rw_cells rsegs m A [CB n bs] -> (j <= n)%nat ->
  rw_cells rsegs m A [CB j (firstn j bs)].
Proof.
  intros m A n bs j H Hj. destruct (rw1_bytes m A n bs H) as (B & L & (W0 & W1 & W)).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, Nat.min_l by lia; reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_firstn; [exact B | lia].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
Qed.

(** ** The static facts, piecewise *)
Lemma st_S : forall S c mm t nt src s, l02_static S c mm t nt src s ->
  S mod 16 = 0 /\ 2 ^ 40 <= S - 65536 /\ S <= 2 ^ 47.
Proof. intros S c mm t nt src s HST. st_dst HST. split; [exact HS16|]. split; assumption. Qed.

Lemma st_txt : forall S c mm t nt src s, l02_static S c mm t nt src s ->
  0 < t /\ t + nt <= S - 65536 /\ nt = Z.of_nat (length s) + 1 /\ 0 <= src /\
  apart src (Z.of_nat (length s)) t (t + nt) /\ (length s <= 65535)%nat.
Proof.
  intros S c mm t nt src s HST. st_dst HST.
  split; [exact Ht0|]. split; [exact Htb|]. split; [exact Hnt|]. split; [exact Hsrc|]. split; assumption.
Qed.

(** The text block, the mconf block and the reader block: below the stack window and outside the image. *)
Lemma blocks_bound : forall S c mm t nt x, l02_num S c mm t nt ->
  (t <= x < t + nt + (- (t + nt)) mod 8) \/ (c <= x < c + SEG_C_SIZE) \/ (mm <= x < mm + SEG_M_SIZE) ->
  x < S - 65536 /\ (x < 0x10000 \/ 0x54000 <= x).
Proof.
  intros S c mm t nt x HN Hx. num_dst HN.
  destruct Hx as [Hx|[Hx|Hx]].
  - destruct (rup8 (t + nt)) as (R & q & Eq). clear - ES Ntimg Ntb Hx R Eq. lia.
  - clear - Ncimg Ncb Hx. lia.
  - clear - Nmimg Nmb Hx. lia.
Qed.

(** ** The memory at 0x13984 *)
Lemma mslack4 : forall mm, mm mod 16 = 0 -> (- (mm + SEG_M_SIZE)) mod 8 = 4.
Proof.
  intros mm H. destruct (mod16_ex _ H) as (k & ->). unfold SEG_M_SIZE.
  replace (- (16 * k + 9236)) with (4 + (- 2 * k - 1155) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma env0 : forall S c mm t nt src s rc mc m, L02_mem S c mm t nt src s rc mc m -> l02_env S c mm m.
Proof.
  intros S c mm t nt src s rc mc m HM.
  destruct HM as (MI & TM & SSP & CI & WI & _ & _ & _ & ST & _ & F20 & _ & F30 & _ & _ & _ & _ & _ & Hm16 &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WC & _ & WM & (sl & BL & SLn) & _).
  destruct (stk_split rsegs m (S - 65536) (S - 208) S ST ltac:(lia)) as [ST1 _].
  destruct (stk_split rsegs m (S - 65536) (S - 65472) (S - 208) ST1 ltac:(lia)) as [_ ST2].
  rewrite (mslack4 mm Hm16) in SLn.
  assert (L4 : (4 <= length sl)%nat) by lia.
  unfold l02_env.
  refine (conj MI (conj TM (conj SSP (conj CI (conj WI (conj ST2 (conj F20 (conj F30 (conj WC (conj WM _)))))))))).
  exists (firstn 4 sl). split; [apply bytes_at_firstn; [exact BL | exact L4]|].
  rewrite length_firstn, Nat.min_l by exact L4. reflexivity.
Qed.

(** What the text walk takes from L02_mem (n = length s). *)
Lemma txt0 : forall S c mm t nt src s rc mc m lb n,
  L02_mem S c mm t nt src s rc mc m -> L02_model s lb rc mc -> n = Z.of_nat (length s) ->
  0 < t /\ t + nt <= 2 ^ 47 /\ nt = n + 1 /\ 0 <= n <= 65535 /\ 0 <= src /\ src + n <= 2 ^ 64 /\
  (src + n <= t \/ t + nt <= src) /\ mem_inv rsegs m /\ bytes_at rsegs m src (zb s) /\
  (exists junk, rw_cells rsegs m t [CB (length s) junk]) /\ wr_at rsegs m t nt.
Proof.
  intros S c mm t nt src s rc mc m lb n HM HMOD En.
  pose proof (l02_static_of S c mm t nt src s rc mc m lb HM HMOD) as HST.
  destruct (st_S S c mm t nt src s HST) as (_ & HSlo & HShi).
  destruct (st_txt S c mm t nt src s HST) as (Ht0 & Htb & Hnt & Hsrc & Ast & HsL).
  apply nat_le_65535 in HsL.
  destruct HM as (MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (jt & RT) & _ & BS & _).
  destruct (rw1_bytes m t (Z.to_nat nt) jt RT) as (_ & _ & WT).
  rewrite Z2Nat.id in WT by lia.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite zb_length in BB.
  unfold apart in Ast. subst n.
  split; [exact Ht0|]. split; [lia|]. split; [exact Hnt|]. split; [lia|]. split; [exact Hsrc|].
  split; [lia|]. split; [lia|]. split; [exact MI|]. split; [exact BS|].
  split; [|exact WT].
  exists (firstn (length s) jt). apply (rw1_prefix m t (Z.to_nat nt) jt (length s) RT). lia.
Qed.

(** The NUL `sb zero, 0(s9)` at t + n after the copy. *)
Lemma txt_store : forall m0 m t nt n s,
  n = Z.of_nat (length s) -> nt = n + 1 -> 0 <= t -> t + nt <= 2 ^ 64 ->
  munch [(t, t + n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m t (zb s) ->
  store_ok rsegs m (wa (t + n)) 1 = true ->
  munch [(t, t + nt)] m0 (write_to_mem m (Z_to_bv 64 (t + n)) (le1 (Z_to_bv 64 0))) /\
  wmono rsegs m0 (write_to_mem m (Z_to_bv 64 (t + n)) (le1 (Z_to_bv 64 0))) /\
  mem_inv rsegs (write_to_mem m (Z_to_bv 64 (t + n)) (le1 (Z_to_bv 64 0))) /\
  bytes_at rsegs (write_to_mem m (Z_to_bv 64 (t + n)) (le1 (Z_to_bv 64 0))) t (zb s ++ [ZERO]).
Proof.
  intros m0 m t nt n s En Hnt Ht Htn MU WM MI BT HS.
  change (Z_to_bv 64 (t + n)) with (wa (t + n)).
  assert (L1 : le1 (Z_to_bv 64 0) = [ZERO]) by reflexivity.
  rewrite L1.
  refine (conj _ (conj _ (conj _ _))).
  - apply munch_write; [ | lia | cbn [length]; lia | cbn [inside length]; left; lia ].
    eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as [Hx _].
    split; [lia | exact I].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact BT | lia | cbn [length]; lia | rewrite zb_length; cbn [length]; lia].
    + rewrite zb_length. rewrite <- En. apply bytes_at_write_same; [lia | cbn [length]; lia].
Qed.

(** ** The memory at 0x139ac *)
(** The label calls' resources: longl's 120 writable bytes and the NUL and 7 bytes after them, main's label buffer
    [S - 144, S - 104) writable, the frame cell 0x28 (the label format's address). *)
Definition lab_res (S : Z) (m : word -> option byte) : Prop :=
  (exists junk, rw_cells rsegs m 0x32ac0 [CB 120 junk]) /\
  (exists sl, bytes_at rsegs m (0x32ac0 + 120) (ZERO :: sl) /\ length sl = 7%nat) /\
  (exists junk, rw_cells rsegs m (S - 144) [CB 40 junk]) /\
  bytes_at rsegs m (S - 208 + 0x28) (le8 (Z_to_bv 64 0x1093b)).

Definition l02_mid (S c mm t nt : Z) (s : list Z) (rc : rconf) (mc : mconf) (m0 m : word -> option byte) : Prop :=
  munch (L02_W S c mm t nt) m0 m /\ wmono rsegs m0 m /\ l02_env S c mm m /\ txt_at t s m /\
  rconf_at rsegs m c rc /\ mconf_at rsegs m mm mc /\ lab_res S m.

Lemma l02_mid_of : forall S c mm t nt src s rc mc m0 m1 lb,
  L02_mem S c mm t nt src s rc mc m0 -> L02_model s lb rc mc ->
  munch [(t, t + nt)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> bytes_at rsegs m1 t (zb s ++ [ZERO]) ->
  l02_mid S c mm t nt s rc mc m0 m1.
Proof.
  intros S c mm t nt src s rc mc m0 m1 lb HM HMOD MU WMo MI1 BT.
  pose proof (l02_static_of S c mm t nt src s rc mc m0 lb HM HMOD) as HST.
  pose proof (st_num S c mm t nt src s HST) as HN.
  pose proof (env0 S c mm t nt src s rc mc m0 HM) as ENV.
  destruct HM as (_ & TM & _ & _ & _ & _ & HSlo & HShi & ST & _ & _ & F28 & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & Htb & Hnt & Atm & Atc & _ & Atl & _ & _ & RC & _ & MC & _ & _ & _ & (tsl & TSL & TSLn) & _ & _ &
    (jl & RL) & (sl & BL & SLn)).
  unfold SA, SEG_PLAIN in Atl, RL, BL. cbn [sa_longl] in Atl, RL, BL. unfold L02_FRAME, L02_FMT in F28.
  assert (OUTB : forall x, x < t \/ t + nt <= x -> outside [(t, t + nt)] x).
  { intros x Hx. cbn [outside]. split; [lia | exact I]. }
  unfold l02_mid. refine (conj _ (conj WMo (conj _ (conj _ (conj _ (conj _ _)))))).
  - eapply munch_weaken; [|exact MU]. unfold L02_W. intros x Hx. cbn [outside] in *. tauto.
  - eapply env_tr; [exact HN | exact ENV | exact MU | | exact WMo | exact MI1 | |].
    + unfold A_all. intros x Hx. cbn [outside] in *. tauto.
    + eapply task_mem_out; [exact TM | exact MU |]. intros x Hx. rewrite TASK_SIZE_val.
      destruct (Z.lt_ge_cases x (t + nt)) as [H1|H1]; [left; lia | right; apply OUTB; lia].
    + destruct ENV as (_ & _ & _ & _ & _ & ST2 & _).
      eapply stk_transport_disjoint; [exact ST2 | exact MU | exact WMo |]. cbn [disjoint_from].
      split; [lia | exact I].
  - set (k := (- (t + nt)) mod 8) in TSLn.
    assert (Hk : 0 <= k < 8) by (apply Z.mod_pos_bound; lia).
    assert (B2 : bytes_at rsegs m0 (t + nt) (firstn (Z.to_nat k) tsl)) by (apply bytes_at_firstn; [exact TSL | lia]).
    assert (B3 : bytes_at rsegs m1 (t + nt) (firstn (Z.to_nat k) tsl)).
    { eapply bytes_at_out; [exact B2 | exact MU |]. intros x Hx. apply OUTB. lia. }
    exists (firstn (Z.to_nat k) tsl). split.
    + replace (zb s ++ ZERO :: firstn (Z.to_nat k) tsl) with ((zb s ++ [ZERO]) ++ firstn (Z.to_nat k) tsl)
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact BT|]. rewrite length_app, zb_length. cbn [length].
      replace (t + Z.of_nat (length s + 1)) with (t + nt) by lia. exact B3.
    + rewrite length_firstn, Nat.min_l by lia. rewrite Z2Nat.id by lia. unfold k.
      replace (t + nt) with (t + Z.of_nat (length s) + 1) by lia. reflexivity.
  - eapply rc_tr; [exact RC | exact MU |]. intros x Hx. apply OUTB. unfold apart in Atc. lia.
  - eapply mc_tr; [exact MC | exact MU |]. intros x Hx. apply OUTB. unfold apart in Atm. lia.
  - unfold lab_res. refine (conj _ (conj _ (conj _ _))).
    + exists jl. eapply rw_cells_transport; [exact RL | exact MU | exact WMo |]. cbn [disjoint_from cells_size csize].
      unfold apart in Atl. split; [lia | exact I].
    + exists sl. split; [|exact SLn]. eapply bytes_at_out; [exact BL | exact MU |]. cbn [length]. rewrite SLn.
      intros x Hx. apply OUTB. unfold apart in Atl. lia.
    + destruct (stk_rw m0 (S - 65536) S (S - 144) 40 ST ltac:(lia) ltac:(lia)) as (jd & RD).
      exists jd. eapply rw_cells_transport; [exact RD | exact MU | exact WMo |]. cbn [disjoint_from cells_size csize].
      split; [lia | exact I].
    + eapply bytes_at_out; [exact F28 | exact MU |]. rewrite length_le8. intros x Hx. apply OUTB. lia.
Qed.

(** ** The memory at 0x139f0 *)
Definition l02_join (S c mm t nt : Z) (s : list Z) (rc : rconf) (mc : mconf) (lb lp : Z)
    (m0 m : word -> option byte) : Prop :=
  munch (L02_W S c mm t nt) m0 m /\ wmono rsegs m0 m /\ l02_env S c mm m /\ txt_at t s m /\
  rconf_at rsegs m c rc /\ mconf_at rsegs m mm mc /\ lab_ok S lp (label_of lb) m.

Lemma txt_out : forall t s m m' W, txt_at t s m -> munch W m m' ->
  (forall x, t <= x < t + Z.of_nat (length s) + 1 + (- (t + Z.of_nat (length s) + 1)) mod 8 -> outside W x) ->
  txt_at t s m'.
Proof.
  intros t s m m' W (sl & B & L) MU H. exists sl. split; [|exact L].
  eapply bytes_at_out; [exact B | exact MU |]. rewrite length_app, zb_length. cbn [length].
  intros x Hx. apply H. rewrite <- L. lia.
Qed.

(** A label call's write set W, inside A_all and missing the three blocks, keeps all but the label. *)
Lemma mid_tr : forall S c mm t nt src s rc mc m0 m1 m2 W,
  l02_static S c mm t nt src s -> l02_mid S c mm t nt s rc mc m0 m1 ->
  munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 ->
  stk rsegs m2 (S - 65472) (S - 208) -> sub_fp W (A_all S c mm t nt) ->
  (forall x, (t <= x < t + nt + (- (t + nt)) mod 8) \/ (c <= x < c + SEG_C_SIZE) \/ (mm <= x < mm + SEG_M_SIZE) ->
     outside W x) ->
  munch (L02_W S c mm t nt) m0 m2 /\ wmono rsegs m0 m2 /\ l02_env S c mm m2 /\ txt_at t s m2 /\
  rconf_at rsegs m2 c rc /\ mconf_at rsegs m2 mm mc.
Proof.
  intros S c mm t nt src s rc mc m0 m1 m2 W HST (MU0 & WM0 & ENV & TXT & RC & MC & _) MU WMo MI TM ST SF OUT.
  pose proof (st_num S c mm t nt src s HST) as HN.
  destruct (st_txt S c mm t nt src s HST) as (_ & _ & Hnt & _).
  refine (conj (munch_acc S c mm t nt m0 m1 m2 W MU0 MU SF) (conj (wmono_trans rsegs m0 m1 m2 WM0 WMo)
          (conj (env_tr S c mm t nt m1 m2 W HN ENV MU SF WMo MI TM ST) (conj _ (conj _ _))))).
  - eapply txt_out; [exact TXT | exact MU |]. intros x Hx. apply OUT. left.
    replace (t + nt) with (t + Z.of_nat (length s) + 1) by lia. exact Hx.
  - eapply rc_tr; [exact RC | exact MU |]. intros x Hx. apply OUT. right; left; exact Hx.
  - eapply mc_tr; [exact MC | exact MU |]. intros x Hx. apply OUT. right; right; exact Hx.
Qed.

(** lb = 0: no call, the label is NULL. *)
Lemma join_zero : forall S c mm t nt s rc mc m0 m1,
  l02_mid S c mm t nt s rc mc m0 m1 -> l02_join S c mm t nt s rc mc 0 0 m0 m1.
Proof.
  intros S c mm t nt s rc mc m0 m1 (MU & WM & ENV & TXT & RC & MC & _).
  unfold l02_join. rewrite label_of_zero. refine (conj MU (conj WM (conj ENV (conj TXT (conj RC (conj MC _)))))).
  exact (@eq_refl Z 0).
Qed.

(** Bit 7 of lb set: memset(longl, 'L', 120); the label is longl's 120 bytes, the NUL GI keeps and 7 slack bytes. *)
Lemma join_hi : forall S c mm t nt src s rc mc m0 m1 m2 lb,
  l02_static S c mm t nt src s -> l02_mid S c mm t nt s rc mc m0 m1 -> 128 <= lb < 256 ->
  munch [(0x32ac0, 0x32ac0 + 120)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 0x32ac0 [CB 120 (repeat (Z_to_bv 8 76) 120)] ->
  l02_join S c mm t nt s rc mc lb 0x32ac0 m0 m2.
Proof.
  intros S c mm t nt src s rc mc m0 m1 m2 lb HST MID Hlb MU WMo MI RW.
  pose proof (st_num S c mm t nt src s HST) as HN.
  destruct (st_S S c mm t nt src s HST) as (_ & HSlo & HShi).
  pose proof MID as (_ & _ & ENV & _ & _ & _ & (_ & (sl & BL & SLn) & _)).
  pose proof ENV as (_ & TM & _ & _ & _ & ST & _).
  assert (OUTL : forall x, x < 0x32ac0 \/ 0x32ac0 + 120 <= x -> outside [(0x32ac0, 0x32ac0 + 120)] x).
  { intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (TM2 : MemNorm.task_mem rsegs m2).
  { eapply task_mem_out; [exact TM | exact MU |]. intros x Hx. rewrite TASK_SIZE_val.
    destruct (Z.lt_ge_cases x (0x32ac0 + 120)); [left; lia | right; apply OUTL; lia]. }
  assert (ST2 : stk rsegs m2 (S - 65472) (S - 208)).
  { eapply stk_transport_disjoint; [exact ST | exact MU | exact WMo |]. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (SF : sub_fp [(0x32ac0, 0x32ac0 + 120)] (A_all S c mm t nt)).
  { unfold A_all. intros x Hx. cbn [outside] in *. tauto. }
  assert (OUT : forall x, (t <= x < t + nt + (- (t + nt)) mod 8) \/ (c <= x < c + SEG_C_SIZE) \/
                          (mm <= x < mm + SEG_M_SIZE) -> outside [(0x32ac0, 0x32ac0 + 120)] x).
  { intros x Hx. apply OUTL. destruct (blocks_bound S c mm t nt x HN Hx) as [_ H]. lia. }
  destruct (mid_tr S c mm t nt src s rc mc m0 m1 m2 _ HST MID MU WMo MI TM2 ST2 SF OUT)
    as (J1 & J2 & J3 & J4 & J5 & J6).
  unfold l02_join. refine (conj J1 (conj J2 (conj J3 (conj J4 (conj J5 (conj J6 _)))))).
  rewrite (label_of_hi lb Hlb). cbn [lab_ok].
  destruct longl_ok as [LL LF].
  split; [lia|]. split; [|split; [exact LF|]].
  - exists sl. split.
    + unfold zb, longl. rewrite map_repeat.
      apply bytes_at_app. split.
      * destruct (rw1_bytes m2 0x32ac0 120 _ RW) as (B & _ & _). exact B.
      * rewrite repeat_length. eapply bytes_at_out; [exact BL | exact MU |]. cbn [length]. rewrite SLn.
        intros x Hx. apply OUTL. lia.
    + rewrite SLn, LL. reflexivity.
  - left. rewrite LL. lia.
Qed.

(** 0 < lb < 128: snprintf(sp + 0x40, 40, "reac-pw.conf.d/%u-x.conf", lb); the label is the whole text in the label
    buffer, its slack the buffer's own bytes after the NUL (outside snprintf's write set). *)
Lemma join_mid : forall S c mm t nt src s rc mc m0 m1 m2 lb,
  l02_static S c mm t nt src s -> l02_mid S c mm t nt s rc mc m0 m1 -> 0 < lb < 128 ->
  munch [(S - 65472, S - 208); (S - 144, S - 144 + Z.of_nat (length (lab_txt lb)) + 1)] m1 m2 ->
  wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemNorm.task_mem rsegs m2 -> stk rsegs m2 (S - 65472) (S - 208) ->
  bytes_at rsegs m2 (S - 144) (pf_bytes (lab_txt lb ++ [0])) ->
  l02_join S c mm t nt s rc mc lb (S - 144) m0 m2.
Proof.
  intros S c mm t nt src s rc mc m0 m1 m2 lb HST MID Hlb MU WMo MI TM ST BD.
  unfold l02_join. rewrite (label_of_mid lb Hlb).
  destruct (lab_txt_ok lb Hlb) as [LL LF].
  pose proof (st_num S c mm t nt src s HST) as HN.
  destruct (st_S S c mm t nt src s HST) as (_ & HSlo & HShi).
  pose proof MID as (_ & _ & _ & _ & _ & _ & (_ & _ & (jd & RD) & _)).
  assert (BD' : bytes_at rsegs m2 (S - 144) (zb (lab_txt lb) ++ [ZERO])).
  { unfold pf_bytes in BD. rewrite map_app in BD. exact BD. }
  clear BD.
  revert MU BD' LL LF. generalize (lab_txt lb). intros o.
  remember (Z.of_nat (length o)) as k eqn:Ek. intros MU BD' LL LF.
  assert (Hk : 0 <= k <= 25) by lia.
  assert (OUTW : forall x, x < S - 65472 \/ (S - 208 <= x < S - 144) \/ S - 144 + k + 1 <= x ->
                           outside [(S - 65472, S - 208); (S - 144, S - 144 + k + 1)] x).
  { intros x Hx. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  assert (SF : sub_fp [(S - 65472, S - 208); (S - 144, S - 144 + k + 1)] (A_all S c mm t nt)).
  { unfold A_all. intros x Hx. cbn [outside] in *. destruct Hx as (H1 & H2 & _).
    split; [exact H1|]. split; [|exact I]. clear - H2 Hk. lia. }
  assert (OUT : forall x, (t <= x < t + nt + (- (t + nt)) mod 8) \/ (c <= x < c + SEG_C_SIZE) \/
                          (mm <= x < mm + SEG_M_SIZE) -> outside [(S - 65472, S - 208); (S - 144, S - 144 + k + 1)] x).
  { intros x Hx. apply OUTW. destruct (blocks_bound S c mm t nt x HN Hx) as [H _]. lia. }
  destruct (mid_tr S c mm t nt src s rc mc m0 m1 m2 _ HST MID MU WMo MI TM ST SF OUT)
    as (J1 & J2 & J3 & J4 & J5 & J6).
  refine (conj J1 (conj J2 (conj J3 (conj J4 (conj J5 (conj J6 _)))))).
  cbn [lab_ok]. rewrite <- Ek.
  remember ((- (S - 144 + k + 1)) mod 8) as q eqn:Eq.
  assert (Hq : 0 <= q < 8) by (rewrite Eq; apply Z.mod_pos_bound; lia).
  destruct (rw1_bytes m1 (S - 144) 40 jd RD) as (BJ & LJ & _).
  assert (BS1 : bytes_at rsegs m1 (S - 144 + Z.of_nat (Z.to_nat (k + 1)))
                  (firstn (Z.to_nat q) (skipn (Z.to_nat (k + 1)) jd))).
  { apply bytes_at_sub; [exact BJ | lia]. }
  rewrite Z2Nat.id in BS1 by lia.
  assert (BS2 : bytes_at rsegs m2 (S - 144 + (k + 1)) (firstn (Z.to_nat q) (skipn (Z.to_nat (k + 1)) jd))).
  { eapply bytes_at_out; [exact BS1 | exact MU |]. rewrite length_firstn, length_skipn. intros x Hx.
    apply OUTW. right; right. lia. }
  split; [lia|]. split; [|split; [exact LF|]].
  - exists (firstn (Z.to_nat q) (skipn (Z.to_nat (k + 1)) jd)). split.
    + replace (zb o ++ ZERO :: firstn (Z.to_nat q) (skipn (Z.to_nat (k + 1)) jd))
        with ((zb o ++ [ZERO]) ++ firstn (Z.to_nat q) (skipn (Z.to_nat (k + 1)) jd))
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact BD'|]. rewrite length_app, zb_length. cbn [length].
      replace (S - 144 + Z.of_nat (length o + 1)) with (S - 144 + (k + 1)) by lia. exact BS2.
    + rewrite length_firstn, length_skipn, LJ. rewrite Nat.min_l by lia. rewrite Z2Nat.id by lia. reflexivity.
  - right. lia.
Qed.

(** ** The callees at their call sites *)
(** memcpy(t, src, n) at 0x1399c, its post with the words read back. *)
Definition cpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t n : Z) (s : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(t, t + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ bytes_at rsegs m' t (zb s).

Lemma memcpy_ok : memcpy_c.memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t src n : Z) (s : list Z) (junk : list byte),
  n = Z.of_nat (length s) -> 0 <= t < 2 ^ 64 -> 0 <= src < 2 ^ 64 -> n < 2 ^ 64 ->
  bytes_at rsegs m src (zb s) -> rw_cells rsegs m t [CB (length s) junk] ->
  (src + n <= t \/ t + n <= src) -> mem_inv rsegs m ->
  evt rsegs (cpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t n s m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1e52c) fc None m (seg_rom rsegs)).
Proof.
  intros HMC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t src n s
    junk En Ht Hs Hn BS RW AP MI.
  assert (Hn0 : 0 <= n) by lia.
  eapply evt_mono.
  - apply (HMC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4
      s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (zb s) junk).
    + rewrite unsigned_lit by lia. exact BS.
    + rewrite unsigned_lit by lia. rewrite zb_length, En, Nat2Z.id. reflexivity.
    + rewrite !unsigned_lit by lia. rewrite En, Nat2Z.id. exact RW.
    + rewrite !unsigned_lit by lia. exact AP.
    + exact MI.
  - intros ms' PO. unfold memcpy_c.memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
      MU & WM & MI' & RW' & _).
    rewrite !unsigned_lit in MU, RW' by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj E (conj MU (conj WM (conj MI' _)))).
    exact (proj1 (rw1_bytes m' t _ _ RW')).
Qed.

(** The label format's bytes, .rodata at 0x1093b. *)
Lemma fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1093b (pf_bytes (F_label ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | |].
  - unfold pf_bytes. rewrite length_map, length_app. change (length F_label) with 24%nat. cbn [length]. lia.
  - apply (ro_bytes_b_sound rsegs). vm_compute. reflexivity.
Qed.

Lemma fmt_hi : 0x1093b + Z.of_nat (length F_label) + 1 <= snprintf_c.RO_END.
Proof. unfold snprintf_c.RO_END. change (length F_label) with 24%nat. cbn. lia. Qed.

Lemma lab_firstn : forall lb, 0 < lb < 128 -> firstn (Z.to_nat (40 - 1)) (lab_txt lb) = lab_txt lb.
Proof.
  intros lb H. destruct (lab_txt_ok lb H) as [L _]. apply firstn_all2. change (Z.to_nat (40 - 1)) with 39%nat. lia.
Qed.

(** snprintf(S - 144, 40, fmt, lb) at 0x139c8 with sp = S - 208 and lo := S - 65472. *)
Lemma snp_ok : snprintf_m_c.snprintf_m_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S c mm lb : Z) (jd : list byte),
  2 ^ 40 <= S - 65536 -> S <= 2 ^ 47 -> 0 < lb < 128 -> l02_env S c mm m -> frm0 fc ->
  rw_cells rsegs m (S - 144) [CB 40 jd] ->
  evt rsegs (printf_post ra (Z_to_bv 64 (S - 208)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (S - 65472)
               (S - 144) (Z.of_nat (length (lab_txt lb))) (lab_txt lb) m)
    (MS (mkR ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S - 144)) (Z_to_bv 64 40)
           (Z_to_bv 64 0x1093b) (Z_to_bv 64 lb) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19078) fc None m (seg_rom rsegs)).
Proof.
  intros HSN ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S c mm lb jd
    HSlo HShi Hlb ENV FRM RD.
  pose proof ENV as (MI & TM & (G1 & g & G2) & _ & _ & ST & _).
  pose proof (HSN ra (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S - 144)) (Z_to_bv 64 40)
    (Z_to_bv 64 0x1093b) (Z_to_bv 64 lb) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (S - 65472) g F_label [Printf_model.PA_u lb] (Z.of_nat (length (lab_txt lb))) (lab_txt lb) jd []) as H.
  cbv zeta in H.
  rewrite !unsigned_lit in H by lia.
  rewrite (lab_firstn lb Hlb) in H.
  apply H; clear H.
  all: first
    [ exact (fmt_at m MI) | exact fmt_hi | exact (proj1 lab_fmt_good) | exact (proj2 lab_fmt_good)
    | exact (lab_pm lb Hlb) | exact RD | exact ST | exact FRM | exact MI | exact TM | exact G1 | exact G2
    | apply noimg_hi; lia
    | cbn [pm_args_ok pm_arg_ok app]; split; [split; [lia | rewrite unsigned_lit by lia; apply Z.mod_small; lia]
                                              | exact I]
    | change (u64s []) with (@nil byte); apply bytes_at_nil; lia
    | unfold snprintf_c.RO_LO, snprintf_c.SNPRINTF_K, snprintf_c.IMG_END; cbn [length Z.of_nat]; lia ].
Qed.
