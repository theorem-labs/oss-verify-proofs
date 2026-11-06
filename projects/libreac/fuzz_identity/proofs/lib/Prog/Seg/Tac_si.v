From Stdlib Require Import ZArith List Bool Lia Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import strlen_c check_str_c strcmp_c
reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
Import ListNotations.
Open Scope Z_scope.

Definition nzb (l : list byte) : bool := forallb (fun b => negb (bz b =? 0)) l.

Lemma nzb_app : forall l1 l2, nzb (l1 ++ l2) = nzb l1 && nzb l2.
Proof. intros. unfold nzb. apply forallb_app. Qed.

Lemma nzb_notin : forall l, nzb l = true -> ~ In z8 l.
Proof.
  intros l H Hin. unfold nzb in H. rewrite forallb_forall in H. specialize (H _ Hin).
  vm_compute in H. discriminate H.
Qed.

Lemma nzb_nth : forall l i, nzb l = true -> (i < length l)%nat -> bz (nthb l i) <> 0.
Proof.
  intros l i H Hi E. unfold nzb in H. rewrite forallb_forall in H.
  specialize (H (nthb l i) (nth_In l (zb 0) Hi)). rewrite E in H. discriminate H.
Qed.

Lemma nzb_first_zero : forall l, nzb (firstn (first_zero l) l) = true.
Proof.
  induction l as [|b r IH]; cbn [first_zero]; [reflexivity|].
  destruct (bz b =? 0) eqn:E; [reflexivity|].
  unfold nzb in *. cbn [firstn forallb]. rewrite E, IH. reflexivity.
Qed.

Lemma nzb_stem_img : forall f, nzb (stem_img f) = true.
Proof.
  intro f. unfold stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|].
  destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.

Lemma nzb_stem : forall inp, nzb (n_stem inp) = true.
Proof.
  intro inp. unfold n_stem. destruct (n_use_said inp); [apply nzb_first_zero | apply nzb_stem_img].
Qed.

Lemma nzb_dec_all : forall x, 0 <= x <= 40 -> nzb (DEC x 1) = true /\ nzb (DEC x 2) = true.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => nzb (DEC x 1) && nzb (DEC x 2)) (Z.to_nat 41) 0
    ltac:(vm_compute; reflexivity) x ltac:(lia)) as H.
  apply andb_true_iff in H. exact H.
Qed.

Lemma n_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intro inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.

Lemma n_r0 : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.

Lemma fits_unfold : forall inp, n_fits inp = true ->
  n_ln inp < t_cap_name inp /\ n_lt inp < t_cap_tok inp /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_fits in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1, H2, H3. auto.
Qed.

Lemma nzb_EXP_NM : forall inp, n_wok inp = true -> nzb (n_EXP_NM inp) = true.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  destruct (nzb_dec_all _ Hi) as [_ Ni]. destruct (nzb_dec_all _ Ho) as [_ No].
  unfold n_EXP_NM. destruct (n_ends_w4 inp); [apply nzb_stem|].
  rewrite !nzb_app, nzb_stem. unfold n_W4. rewrite nzb_app, Ni, No. reflexivity.
Qed.

Lemma nzb_EXP_DP : forall inp, n_wok inp = true -> nzb (n_EXP_DP inp) = true.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  destruct (nzb_dec_all _ Hi) as [Ni _]. destruct (nzb_dec_all _ Ho) as [No _].
  unfold n_EXP_DP. rewrite !nzb_app, (nzb_EXP_NM inp H), Ni, No. vm_compute. reflexivity.
Qed.

Lemma lower_bz : forall b, bz (lower b) = if (65 <=? bz b) && (bz b <=? 90) then bz b + 32 else bz b.
Proof.
  intro b. unfold lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
  unfold zb, bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. unfold bz in *. lia.
Qed.

Lemma nzb_tok : forall l d, nzb l = true -> nzb (tok_go d l) = true.
Proof.
  induction l as [|b r IH]; intros d H; [reflexivity|].
  unfold nzb in H. cbn [forallb] in H. apply andb_true_iff in H as [Hb Hr].
  cbn [tok_go]. destruct (negb d && (bz b =? 45)); [apply IH; exact Hr|].
  unfold nzb. cbn [forallb]. apply andb_true_iff. split; [|apply IH; exact Hr].
  rewrite lower_bz. apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. apply negb_true_iff. apply Z.eqb_neq.
  pose proof (bz_range b). destruct ((65 <=? bz b) && (bz b <=? 90)); lia.
Qed.

Lemma has_dash_cons : forall b r, has_dash (b :: r) = (bz b =? 45) || has_dash r.
Proof. reflexivity. Qed.

Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.

Lemma tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|].
  rewrite has_dash_cons. destruct d.
  - cbn [tok_go negb andb length]. rewrite IH. cbn [negb andb]. lia.
  - destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb length]; rewrite E; cbn [andb orb].
    + rewrite IH. cbn [negb andb]. lia.
    + cbn [length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
      pose proof (has_dash_len r D). lia.
Qed.

Lemma tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite tok_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.

Lemma tok_app : forall l1 l2 d, tok_go d (l1 ++ l2) = tok_go d l1 ++ tok_go (d || has_dash l1) l2.
Proof.
  induction l1 as [|b r IH]; intros l2 d.
  - cbn. rewrite orb_false_r. reflexivity.
  - cbn [app tok_go]. rewrite has_dash_cons. destruct d; cbn [negb andb orb].
    + rewrite IH. reflexivity.
    + destruct (bz b =? 45) eqn:E; cbn [orb]; rewrite IH; reflexivity.
Qed.

Lemma firstn_snoc : forall (l : list byte) q, (q < length l)%nat ->
  firstn (S q) l = firstn q l ++ [nthb l q].
Proof.
  induction l as [|b r IH]; intros q H; [cbn in H; lia|].
  destruct q as [|q]; [reflexivity|]. cbn [firstn]. unfold nthb. cbn [nth]. cbn in H.
  rewrite (IH q ltac:(lia)). reflexivity.
Qed.

Lemma skipn_nth : forall (l : list byte) q, (q < length l)%nat -> skipn q l = nthb l q :: skipn (S q) l.
Proof.
  induction l as [|b r IH]; intros q H; [cbn in H; lia|].
  destruct q as [|q]; [reflexivity|]. cbn [skipn]. unfold nthb. cbn [nth]. cbn in H.
  rewrite (IH q ltac:(lia)). reflexivity.
Qed.

Lemma has_dash_app : forall l1 l2, has_dash (l1 ++ l2) = has_dash l1 || has_dash l2.
Proof. intros. unfold has_dash. apply existsb_app. Qed.

Lemma dropped_S : forall l q, (q < length l)%nat ->
  dropped l (S q) = if (bz (nthb l q) =? 45) || has_dash (firstn q l) then 1 else 0.
Proof.
  intros l q H. unfold dropped. rewrite (firstn_snoc l q H), has_dash_app. cbn [has_dash existsb].
  rewrite orb_false_r, orb_comm. reflexivity.
Qed.

Lemma dropped_range : forall l q, 0 <= dropped l q <= 1.
Proof. intros. unfold dropped. destruct (has_dash _); lia. Qed.

Lemma dropped_le : forall l q, dropped l q <= Z.of_nat q.
Proof.
  intros l q. unfold dropped. destruct (has_dash (firstn q l)) eqn:D; [|lia].
  pose proof (has_dash_len _ D). rewrite length_firstn in H. lia.
Qed.

Lemma tok_at : forall l q, (q < length l)%nat ->
  ~ (bz (nthb l q) = 45 /\ dropped l q = 0) ->
  (Z.to_nat (Z.of_nat q - dropped l q) < length (TOK l))%nat /\
  nthb (TOK l) (Z.to_nat (Z.of_nat q - dropped l q)) = lower (nthb l q).
Proof.
  intros l q Hq Hn.
  assert (ET : TOK l = tok_go false (firstn q l) ++ tok_go (has_dash (firstn q l)) (nthb l q :: skipn (S q) l)).
  { unfold TOK. rewrite <- (firstn_skipn q l) at 1. rewrite tok_app. cbn [orb].
    rewrite (skipn_nth l q Hq). reflexivity. }
  assert (Hl : length (tok_go false (firstn q l)) = Z.to_nat (Z.of_nat q - dropped l q)).
  { rewrite tok_len, length_firstn. unfold dropped. cbn [negb andb].
    destruct (has_dash (firstn q l)) eqn:D; [|lia]. pose proof (has_dash_len _ D) as D1.
    rewrite length_firstn in D1. lia. }
  rewrite ET. cbn [tok_go]. destruct (negb (has_dash (firstn q l)) && (bz (nthb l q) =? 45)) eqn:E.
  - exfalso. apply Hn. apply andb_true_iff in E as [E1 E2]. apply negb_true_iff in E1. apply Z.eqb_eq in E2.
    unfold dropped. rewrite E1. auto.
  - rewrite length_app. cbn [length]. split; [lia|]. unfold nthb.
    rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. reflexivity.
Qed.

Lemma tok_dash_drop : forall l q, (q < length l)%nat -> bz (nthb l q) = 45 -> dropped l q = 0 ->
  dropped l (S q) = 1.
Proof. intros l q Hq E D. rewrite (dropped_S l q Hq), E. reflexivity. Qed.

Lemma tok_other_keep : forall l q, (q < length l)%nat -> ~ (bz (nthb l q) = 45 /\ dropped l q = 0) ->
  dropped l (S q) = dropped l q.
Proof.
  intros l q Hq Hn. rewrite (dropped_S l q Hq). unfold dropped in *.
  destruct (has_dash (firstn q l)); [rewrite orb_true_r; reflexivity|].
  rewrite orb_false_r. destruct (Z.eqb_spec (bz (nthb l q)) 45); [exfalso; apply Hn; auto | reflexivity].
Qed.

Lemma tok_len_full : forall l, Z.of_nat (length (TOK l)) = Z.of_nat (length l) - dropped l (length l).
Proof.
  intro l. unfold TOK, dropped. rewrite tok_len, firstn_all. cbn [negb andb].
  destruct (has_dash l) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.

Definition lw (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

Lemma lower_lw : forall b, bz (lower b) = lw (bz b).
Proof. intro b. rewrite lower_bz. reflexivity. Qed.

Lemma lower_or_bv : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 c))
    (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (c + -65)) 26) ≪ 5)))) = Z_to_bv 64 (lw c).
Proof.
  intros c Hc. f_equal.
  pose proof (z_all_spec (fun c => Z.lor (bv_unsigned (Z_to_bv 64 c))
    (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (c + -65)) 26) ≪ 5))) =? lw c)
    (Z.to_nat 256) 0 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma neg_eqb_same : forall x : word, negb (bv_eqb x x) = false.
Proof. intro x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma lw_range : forall c, 0 <= c < 256 -> 0 <= lw c < 256.
Proof. intros c H. unfold lw. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|lia]. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E2. lia. Qed.

Definition SKEEP (regs R : bvmap 5 word) : Prop :=
  YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\ YK11.getr R 4 = YK11.getr regs 4 /\
  YK11.getr R 8 = YK11.getr regs 8 /\ YK11.getr R 9 = YK11.getr regs 9 /\
  YK11.getr R 18 = YK11.getr regs 18 /\ YK11.getr R 19 = YK11.getr regs 19 /\
  YK11.getr R 20 = YK11.getr regs 20 /\ YK11.getr R 21 = YK11.getr regs 21 /\
  YK11.getr R 22 = YK11.getr regs 22 /\ YK11.getr R 23 = YK11.getr regs 23 /\
  YK11.getr R 24 = YK11.getr regs 24 /\ YK11.getr R 25 = YK11.getr regs 25 /\
  YK11.getr R 26 = YK11.getr regs 26 /\ YK11.getr R 27 = YK11.getr regs 27.

Lemma SKEEP_trans : forall r1 r2 r3, SKEEP r1 r2 -> (forall r, YK11.getr r3 r = YK11.getr r2 r) -> SKEEP r1 r3.
Proof.
  intros r1 r2 r3 H E. unfold SKEEP in *. rewrite !E. exact H.
Qed.

Ltac solve_keep :=
  unfold SKEEP; repeat split;
  first [ reflexivity
        | match goal with H : YK11.getr ?r ?k = _ |- YK11.getr _ ?k = YK11.getr ?r ?k => exact (eq_sym H) end ].

Definition KQ (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (W : list ivl)
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (R : bvmap 5 word) (pc' : word)
    (mem' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 pc /\ SKEEP regs R /\ munch W mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
  P R mem'.

Ltac greg := unfold YK11.getr;
  lazymatch goal with |- (if ?b then _ else _) = _ => let v := eval vm_compute in b in change b with v; cbv iota end;
  simp_regs.

Lemma ret_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> MState.ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H1 H2. apply ret_pc_even; assumption. Qed.

Lemma munch_nil_any : forall m m' lo hi, munch [] m m' -> munch [(lo, hi)] m m'.
Proof. intros m m' lo hi H x _. apply H. exact I. Qed.

Lemma sextw_small : forall x, 0 <= x < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 0)) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. rewrite Z.add_0_r. f_equal.
  unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma caps_range : forall inp,
  0 <= t_cap_name inp < 40 /\ 0 <= t_cap_tok inp < 40 /\ 0 <= t_cap_disp inp < 64.
Proof.
  intro inp. unfold t_cap_name, t_cap_tok, t_cap_disp.
  pose proof (Z.mod_pos_bound (tb inp 5) 40). pose proof (Z.mod_pos_bound (tb inp 6) 40).
  pose proof (Z.mod_pos_bound (tb inp 7) 64). lia.
Qed.

Lemma cstr_byte : forall m a s i, cstr m a s -> (i <= length s)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nthb (s ++ [z8]) i].
Proof.
  intros m a s i H Hi. unfold cstr in H.
  rewrite (bytes_at_read rsegs m a _ (Z.of_nat i) 1 H) by (rewrite ?length_app; cbn [length]; lia).
  rewrite Nat2Z.id, (skipn_nth (s ++ [z8]) i) by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Lemma nthb_snoc_lt : forall s i, (i < length s)%nat -> nthb (s ++ [z8]) i = nthb s i.
Proof. intros s i H. unfold nthb. apply app_nth1. exact H. Qed.

Lemma nthb_snoc_eq : forall s, nthb (s ++ [z8]) (length s) = z8.
Proof. intros s. unfold nthb. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma zxb_bz : forall b : byte, zxb b = Z_to_bv 64 (bz b).
Proof. reflexivity. Qed.

Lemma bv_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Section Fx.
Context {fx : YK11.FPState}.

Lemma strlen_call : strlen_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (str slack : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ z8 :: slack) -> ~ In z8 str ->
  (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5'
                          a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m str slack Q Hro HB NZ WP K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply SL with (str := str) (slack := slack);
      [apply bytes_at_normalize; assumption | exact NZ | exact WP | apply mem_inv_normalize]. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs [] m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma stk_normalize : forall m lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> ro_addr rsegs (wa a) = false) -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hro. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hw [b Hb]].
  assert (E : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize; rewrite (Hro a Ha); reflexivity).
  split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma check_str_call : check_str_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (r o c lo : Z) (str slack : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m ->
  -2^31 <= r < 2^31 -> a0 = Z_to_bv 64 r -> 0 <= o < 2^64 -> a1 = Z_to_bv 64 o ->
  0 <= c < 2^64 -> a2 = Z_to_bv 64 c ->
  (0 <= r -> check_str_ok m sp r o c str slack) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_STR_FRAME <= bv_unsigned sp ->
  (forall a, lo <= a < bv_unsigned sp -> ro_addr rsegs (wa a) = false) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(bv_unsigned sp - CHECK_STR_FRAME, bv_unsigned sp)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 CHECK_STR) fc None m (seg_rom rsegs)).
Proof.
  intros CS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r o c lo str slack Q Hro Hr E0 Ho E1 Hc E2 OK ST HL HRO K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply CS with (str := str) (slack := slack) (lo := lo);
      [exact Hr | exact E0 | exact Ho | exact E1 | exact Hc | exact E2 | | | exact HL |
      apply mem_inv_normalize].
    - intros H0. destruct (OK H0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      split; [exact Q1|]. split; [exact Q2|]. split; [apply bytes_at_normalize; assumption|].
      split; [exact Q4|]. split; [exact Q5 | exact Q6].
    - apply stk_normalize; assumption. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs _ m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma strcmp_call : strcmp_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sx sy : list byte) (Q : machine_state -> Prop),
  bytes_at rsegs m (bv_unsigned a0) (sx ++ [z8]) -> ~ In z8 sx ->
  bytes_at rsegs m (bv_unsigned a1) (sy ++ [z8]) -> ~ In z8 sy ->
  (forall r x11 x12 x13 : word, (r = Z_to_bv 64 0 <-> sx = sy) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (MState.ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 STRCMP) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sx sy Q H1 H2 H3 H4 K.
  eapply evt_cut; [eapply SC; eassumption|].
  intros s (r & x11 & x12 & x13 & -> & HR). apply K. exact HR.
Qed.

Lemma cat_call : reac_box_catalogue_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (c : Z) (Q : machine_state -> Prop),
  a0 = Z_to_bv 64 c -> c <> 0 -> c mod 8 = 0 -> wr_at rsegs m c 8 ->
  (forall (a1' : word) (m' : word -> option byte),
     bytes_at rsegs m' c (le8 (Z_to_bv 64 11)) -> munch [(c, c + 8)] m m' -> wmono rsegs m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BOX_CATALOGUE) a1' a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (MState.ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 REAC_BOX_CATALOGUE) fc None m (seg_rom rsegs)).
Proof.
  intros CC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m c Q E0 Hc0 Hc8 HW K.
  eapply evt_cut; [eapply CC; [exact E0 | right; split; assumption]|].
  intros s (a1' & m' & -> & HP). destruct (Z.eqb_spec c 0) as [Ec|Ec]; [contradiction|].
  destruct HP as (HB & MU & WM & _). apply K; assumption.
Qed.

End Fx.

Fixpoint rd_list (mem : word -> option byte) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => (match mem (Z_to_bv 64 a) with Some b => b | None => z8 end) :: rd_list mem (a + 1) k'
  end.

Lemma rd_list_len : forall mem k a, length (rd_list mem a k) = k.
Proof. intros mem k. induction k as [|k IH]; intros a; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rd_list_nth : forall mem k a j, (j < k)%nat ->
  nth_error (rd_list mem a k) j =
  Some (match mem (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => z8 end).
Proof.
  intros mem k. induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j]; cbn [rd_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. reflexivity.
Qed.

Section Frm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Abbreviation ACL := (@YM05.alloc_ceiling rc).

Lemma FF_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma img_low_B : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite FF_segs. vm_compute. reflexivity.
  - pose proof YM05.alloc_ceiling_value. lia.
Qed.

Lemma find_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < ACL.
Proof. intros x seg H. destruct img_low_B as [_ IL]. rewrite FF_segs in IL. exact (IL x seg H). Qed.

Lemma ro_addr_high : forall a, ACL <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. pose proof YM05.alloc_ceiling_value. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (find_seg_low a seg E). lia.
Qed.

Lemma present_high : forall (m : word -> option byte) a, ACL <= a < 2 ^ 64 ->
  wview rsegs m (wa a) <> None -> exists b, m (wa a) = Some b.
Proof.
  intros m a Ha H. pose proof YM05.alloc_ceiling_value. unfold wview in H.
  destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  rewrite wa_unsigned in H by lia. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|contradiction].
  pose proof (find_seg_low a seg E). lia.
Qed.

Lemma blk_range : forall L A mem md a k, aa_MR (APIf rc) L A mem md -> In (a, k) (blocks L A) ->
  4096 <= a /\ a + k <= ACL.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-.
  exact (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ q k' HM Hq).
Qed.

Lemma blk_present : forall L A mem md a k i, aa_MR (APIf rc) L A mem md -> In (a, k) (blocks L A) ->
  0 <= i < k -> present mem (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
  cbn in Eq. injection Eq as <- <-.
  exact (proj1 (mr_blocks _ _ (aa_laws (APIf rc)) _ _ _ _ q k' i HM Hq Hi)).
Qed.

Lemma slack_ok : forall L A mem md p n s, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  cstr mem p s -> Z.of_nat (length s) + 1 <= n ->
  exists slack, bytes_at rsegs mem p (s ++ z8 :: slack) /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= ACL.
Proof.
  intros L A mem md p n s HM Hin HC Hn.
  pose proof (blk_range _ _ _ _ _ _ HM Hin) as [B1 B2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  assert (HSL : block_slack_present B (APIf rc)).
  { destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & HFA).
    destruct (HFA rc fx) as (_ & _ & _ & _ & _ & H & _). exact H. }
  set (x := p + Z.of_nat (length s) + 1).
  set (e := 8 * ((p + n + 7) / 8)).
  assert (He1 : p + n <= e) by (unfold e; Z.div_mod_to_equations; lia).
  assert (He2 : e <= ACL) by (unfold e; Z.div_mod_to_equations; lia).
  assert (PR : forall a, x <= a < e -> present mem a).
  { intros a Ha. destruct (Z_lt_le_dec a (p + n)) as [Hlt|Hge].
    - replace a with (p + (a - p)) by lia. apply (blk_present L A mem md p n); [exact HM | exact Hin | lia].
    - exact (HSL L A mem md p n a HM Hin ltac:(unfold e in Ha; lia)). }
  exists (rd_list mem x (Z.to_nat (e - x))). rewrite rd_list_len.
  destruct HC as (C1 & C2 & C3). rewrite length_app in C2. cbn [length] in C2.
  split; [| split; [fold x; Z.div_mod_to_equations; lia | fold x; lia]].
  split; [lia|]. split; [rewrite length_app; cbn [length]; rewrite rd_list_len; lia|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite rd_list_len in Hi.
  replace (s ++ z8 :: rd_list mem x (Z.to_nat (e - x))) with ((s ++ [z8]) ++ rd_list mem x (Z.to_nat (e - x)))
    by (rewrite <- app_assoc; reflexivity).
  destruct (Nat.lt_ge_cases i (length s + 1)) as [Hl|Hl].
  - rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia). apply C3. rewrite length_app. cbn. lia.
  - rewrite nth_error_app2 by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length].
    rewrite rd_list_nth by lia.
    destruct (PR (p + Z.of_nat i) ltac:(unfold x; lia)) as [b Hb].
    replace (x + Z.of_nat (i - (length s + 1))) with (p + Z.of_nat i) by (unfold x; lia).
    unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma nmb_in : forall g nm tk dp L A, Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  In (nm, bsz (t_cap_name (g_in g))) (blocks L A) /\ In (tk, bsz (t_cap_tok (g_in g))) (blocks L A) /\
  In (dp, bsz (t_cap_disp (g_in g))) (blocks L A).
Proof.
  intros g nm tk dp L A HP.
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; unfold NMB; cbn; tauto]).
Qed.

Lemma FR_md : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros g km hb L A regs mem md H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  exact (kb_md B (APIf rc) L A mem md HM).
Qed.

Lemma FR_parts : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  g_S g mod 16 = 0 /\ ACL + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\
  YK11.getr regs 2 = Z_to_bv 64 (fsp g) /\ aa_MR (APIf rc) L A mem md /\ ro_agree rsegs mem /\
  stk rsegs mem (g_S g - SLOT_K) (g_S g) /\
  (forall a, g_S g - SLOT_K <= a < g_S g -> writable_at rsegs mem a).
Proof.
  intros g km hb L A regs mem md H.
  destruct H as ((_ & _ & _ & G4 & G5 & G6 & _) & H2 & _ & _ & _ & HSTK & HMI & _ & HM & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & HSW).
  unfold MI in HMI. rewrite FF_segs in HMI, HSW. auto 10.
Qed.

Lemma FR_regs : forall g km hb L A regs mem md regs',
  FR B APIf ra empty g km hb L A regs mem md ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof.
  intros g km hb L A regs mem md regs' H E2 E3 E4. unfold FR in *.
  destruct H as (H1 & H2 & H3 & H4 & H). rewrite E2, E3, E4. auto.
Qed.

Lemma FR_after : forall g km hb L A regs mem md regs' mem' lo hi,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  g_S g - SLOT_K <= lo -> hi <= g_S g - 104 ->
  munch [(lo, hi)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' lo hi HFR HP Hlo Hhi MU WM RO E2 E3 E4.
  pose proof img_low_B as [IL1 _].
  destruct FF as (Hsegs & _ & _ & _ & _ & _ & Herr & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Heo & _ & Hhead &
    Hlock & Hthr & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (Herr rc) as Herr'. unfold errno_addr in Herr'. rewrite Htp, Heo in Herr'.
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  unfold FR in *.
  destruct HFR as (HGV & H2 & H3 & H4 & HSV & HSTK & HMI & HRL & HMR & HWF & HBD & HID & HMD & HFRM & HIMG &
    HBLK & HERR & HSINK & HRES & HSW).
  pose proof HGV as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  unfold SLOT_K, SLOT_STACK in *.
  rewrite Hsegs in *.
  assert (OUT : forall x, x < lo -> outside [(lo, hi)] x) by (intros x Hx; cbn; split; [lia | exact I]).
  assert (MB : forall a, 0 <= a < ACL -> mbyte rsegs mem' a = mbyte rsegs mem a)
    by (intros a Ha; apply (KindBGlue.mbyte_munch rsegs [(lo, hi)]); [exact MU | lia | apply OUT; lia]).
  assert (WB : forall a, 0 <= a < ACL -> (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (intros a Ha; apply (KindBGlue.writable_munch rsegs [(lo, hi)]); [exact MU | lia | apply OUT; lia]).
  split; [exact HGV|]. split; [rewrite E2; exact H2|]. split; [rewrite E3; exact H3|].
  split; [rewrite E4; exact H4|].
  split.
  { apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ HSV MU). cbn. split; [right; lia | exact I]. }
  split.
  { apply (stk_transport rsegs [(lo, hi)] mem mem' _ _ HSTK MU WM). intros x Hx.
    destruct (Z_lt_le_dec x lo) as [H|H]; [left; apply OUT; exact H|].
    destruct (Z_lt_le_dec x hi) as [H'|H']; [|left; cbn; split; [lia | exact I]].
    right. apply present_high; [lia|]. apply WM. destruct HSTK as (_ & _ & HS). apply (HS x). lia. }
  split; [unfold MI; rewrite Hsegs; exact RO|].
  split.
  { unfold relro, G_img_c in *. rewrite Hsegs in *. intros a Ha. rewrite MB; [apply HRL; exact Ha|].
    destruct Ha as (lo' & len & Hin & Hr). unfold frame_RELRO in Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split.
  { apply (kb_MR_A B (APIf rc) L A mem mem' md [(lo, hi)] HMR MU). intros x Hx _. apply OUT. lia. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HID|]. split; [exact HMD|].
  split.
  { intros a Ha Hs He. destruct (HFRM a Ha Hs He) as [Q1 Q2].
    assert (Ho : outside [(lo, hi)] a) by (cbn; split; [lia | exact I]).
    split.
    - rewrite (KindBGlue.mbyte_munch rsegs [(lo, hi)] mem mem' a MU ltac:(lia) Ho). exact Q1.
    - rewrite Q2. exact (KindBGlue.writable_munch rsegs [(lo, hi)] mem mem' a MU ltac:(lia) Ho). }
  split.
  { intros a Hi Hs Hc He. destruct (HIMG a Hi Hs Hc He) as [Q1 Q2]. pose proof (IL1 a Hi).
    split; [rewrite MB by lia; exact Q1 | rewrite Q2; apply WB; lia]. }
  split.
  { intros a k i Hin Hi. rewrite <- (HBLK a k i Hin Hi).
    assert (Hin' : In (a, k) (blocks L A))
      by (eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; right; exact Hin]).
    pose proof (blk_range L A mem md a k HMR Hin'). apply MB. lia. }
  split.
  { intros a Ha. unfold errno_addr in Ha. rewrite Htp, Heo in Ha. apply WB; [lia|]. apply HERR.
    unfold errno_addr. rewrite Htp, Heo. exact Ha. }
  split.
  { unfold sink_none, closed_stdio_env, val_mem, word_mem in *. rewrite Hsegs, Hhead, Hlock, Hthr in *.
    destruct HSINK as ((S1 & S2) & S3 & S4).
    split; [split|split; [|exact S4]]; intros k Hk; rewrite MB by lia; auto. }
  split; [exact HRES|].
  intros a Ha. unfold writable_at in *. apply WM. apply HSW. exact Ha.
Qed.

Lemma IRb_after : forall g nm tk dp L A regs mem md regs' mem' lo hi km,
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  IRb g nm tk dp regs mem ->
  g_S g - SLOT_K <= lo -> (hi <= fsp g + 48 \/ (fsp g + 176 <= lo /\ hi <= fsp g + 184)) ->
  munch [(lo, hi)] mem mem' -> SKEEP regs regs' ->
  IRb g nm tk dp regs' mem'.
Proof.
  intros g nm tk dp L A regs mem md regs' mem' lo hi km HFR HP HI Hlo Hhi MU HSK.
  destruct (FR_parts _ _ _ _ _ _ _ _ HFR) as (P1 & P2 & P3 & _ & HMR & _).
  destruct (nmb_in _ _ _ _ _ _ HP) as (N1 & N2 & N3).
  pose proof (blk_range _ _ _ _ _ _ HMR N1) as [R1 R1'].
  pose proof (blk_range _ _ _ _ _ _ HMR N2) as [R2 R2'].
  pose proof (blk_range _ _ _ _ _ _ HMR N3) as [R3 R3'].
  unfold SLOT_K, SLOT_STACK in *.
  unfold IRb, OUTS, IDb, cstr, SKEEP, spk, fsp, SLOT_FRAME in *.
  destruct HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  destruct HSK as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof (rec_id_length (g_in g) (NRn g)) as LI. unfold ID_SIZE in LI.
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  split.
  { apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ HID MU). cbn. split; [|exact I]. rewrite LI.
    destruct Hhi as [Hh|[Hh1 Hh2]]; [right; lia | left; lia]. }
  rewrite K9, K18, K19, K20, K21, K22, K23, K24, K25, K27.
  do 10 (split; [assumption|]).
  split.
  { intros R0. destruct (HO R0) as (C1 & C2 & C3). destruct (n_r0 _ R0) as [Wk Ft].
    destruct (fits_unfold _ Ft) as (F1 & F2 & F3). pose proof (tk_len (g_in g)) as TL.
    unfold n_ln, n_ld, bsz in *.
    split; [|split].
    - apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ C1 MU). cbn. rewrite length_app. cbn.
      split; [left; lia | exact I].
    - apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ C2 MU). cbn. rewrite length_app. cbn.
      split; [left; lia | exact I].
    - apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ C3 MU). cbn. rewrite length_app. cbn.
      split; [left; lia | exact I]. }
  intros R0. destruct (HE R0) as [C1 C2]. destruct (n_r0 _ R0) as [Wk Ft].
  pose proof (n_ln_le _ Wk). pose proof (n_ld_le _ Wk). unfold n_ln, n_ld in *.
  split.
  - apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ C1 MU). cbn. rewrite length_app. cbn.
    split; [|exact I]. destruct Hhi as [Hh|[Hh1 Hh2]]; right; lia.
  - apply (bytes_at_transport rsegs [(lo, hi)] mem mem' _ _ C2 MU). cbn. rewrite length_app. cbn.
    split; [|exact I]. destruct Hhi as [Hh|[Hh1 Hh2]]; [right; lia | left; lia].
Qed.

Lemma close_IR : forall (X : ghost -> config -> Prop) g nm tk dp L A regs mem md km pc regs' mem' lo hi
    (P' : bvmap 5 word -> (word -> option byte) -> Prop),
  (forall c, CUTST B APIf ra empty g pc km (NMB g nm tk dp) P' c -> X g c) ->
  FR B APIf ra empty g km (NMB g nm tk dp) L A regs mem md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ blocks (g_L g) (g_A g)) ->
  IRb g nm tk dp regs mem ->
  g_S g - SLOT_K <= lo -> (hi <= fsp g + 48 \/ (fsp g + 176 <= lo /\ hi <= fsp g + 184)) ->
  munch [(lo, hi)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> SKEEP regs regs' ->
  (IRb g nm tk dp regs' mem' -> P' regs' mem') ->
  X g (mkCfg (YK11.mkst regs' (Z_to_bv 64 pc) mem' (YK11.seg_rom (ms_segs B))) md).
Proof.
  intros X g nm tk dp L A regs mem md km pc regs' mem' lo hi P' HX HFR HP HI Hlo Hhi MU WM RO HSK HP'.
  apply HX. exists L, A, regs', mem', md. split; [reflexivity|].
  destruct HSK as (K2 & K3 & K4 & HSK').
  split.
  { eapply FR_after; [exact HFR | exact HP | exact Hlo | | exact MU | exact WM | exact RO | exact K2 | exact K3 |
      exact K4]. unfold fsp, SLOT_FRAME in Hhi. lia. }
  split; [exact HP|]. apply HP'. eapply IRb_after; [exact HFR | exact HP | exact HI | exact Hlo | exact Hhi |
    exact MU | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact HSK']]]].
Qed.

Lemma run_close : forall g km hb L A regs mem md pc0
    (Kp : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Exec.evt rsegs (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (PropExec.seg_rom rsegs) /\
      Kp R pc' mem')
    (MS (rmk regs) fp_regs (Z_to_bv 64 pc0) fp_csr None mem (PropExec.seg_rom rsegs)) ->
  (forall R pc' mem' regs', Kp R pc' mem' -> (forall r, YK11.getr regs' r = YK11.getr R r) ->
     Rz (ms_segs B) (mkCfg (YK11.mkst regs' pc' mem' (YK11.seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc0) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md pc0 Kp P HFR HE HK.
  destruct (FR_md _ _ _ _ _ _ _ _ HFR) as [Hh Hl].
  eapply (kb_run_rz B regs _ mem md Kp P Hh Hl); [| exact HK].
  rewrite FF_segs. exact HE.
Qed.

End Frm.
