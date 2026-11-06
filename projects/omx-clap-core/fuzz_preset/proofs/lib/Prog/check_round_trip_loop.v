From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame strcmp_c same_c check_round_trip_c.
Import ListNotations.
Open Scope Z_scope.

(* The member compares of check_round_trip (fuzz_preset.c:742-765, round_trip_rewrite inlined) in the #102 plain twin
   (fuzz_preset.plain c8f4d6b8e567b0b1...): 0x1411c .. 0x14238, the same instructions as the old 0x13ddc .. 0x13ef8
   moved by 0x340, with s3 / s4 / s5 renamed: doc->n saved before pj_string is s3 (was s5), doc->n reloaded is s4 (was
   s3), the index `at` is s5 (was s4); 0x1411c tests s4 = (parse_noting's rc <> 0) where 0x13ddc tested a0. *)

Ltac crt_if b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry]
  end.

Ltac crt_side := unfold_cond; rewrite ?unsigned_lit by lia; solve_cond_rec.

Lemma crt_modat_img : forall m, mem_inv rsegs m -> bytes_at rsegs m MOD_AT_A (map (Z_to_bv 8) (MOD_AT ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold MOD_AT_A; lia | cbn; unfold MOD_AT_A; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma crt_stamp_img : forall m, mem_inv rsegs m -> bytes_at rsegs m STAMP_A (map (Z_to_bv 8) (STAMP ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold STAMP_A; lia | cbn; unfold STAMP_A; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma crt_modat_ok : Forall (fun c => 0 < c < 256) MOD_AT.
Proof. unfold MOD_AT. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma crt_stamp_ok : Forall (fun c => 0 < c < 256) STAMP.
Proof. unfold STAMP. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma crt_map_nz : forall s, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s).
Proof.
  intros s Hf Hin. apply in_map_iff in Hin. destruct Hin as (c & Ec & Hc).
  rewrite Forall_forall in Hf. specialize (Hf c Hc).
  apply (f_equal (@bv_unsigned 8)) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
  change (bv_modulus 8) with 256 in Ec. rewrite (Z.mod_small c) in Ec by lia. rewrite Z.mod_0_l in Ec by lia. lia.
Qed.

Lemma crt_img_at : forall m a s, bytes_at rsegs m a (map (Z_to_bv 8) (s ++ [0])) ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 a)) (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]).
Proof.
  intros m a s H. pose proof (bytes_at_bound rsegs m a _ H) as R.
  rewrite length_map, length_app in R. cbn [length] in R. rewrite unsigned_lit by lia.
  rewrite map_app in H. exact H.
Qed.

Lemma crt_seqz : forall a b, 0 <= a -> 0 <= b -> Z.b2z (Z.lxor a b <? 1) = (if a =? b then 1 else 0).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [E|E].
  - subst b. rewrite Z.lxor_nilpotent. reflexivity.
  - assert (N : Z.lxor a b <> 0) by (intros H; apply E; apply Z.lxor_eq_0_iff; exact H).
    assert (P : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma crt_flag : forall a b (c : bool), 0 <= a -> 0 <= b -> (a =? b) = c ->
  Z_to_bv 64 (Z.b2z (Z.lxor a b <? 1)) = Z_to_bv 64 (if c then 1 else 0).
Proof. intros a b c Ha Hb E. subst c. rewrite crt_seqz by lia. reflexivity. Qed.

Ltac crt_flag_tac :=
  apply crt_flag; [lia | lia | apply eq_true_iff_eq; rewrite Z.eqb_eq, Nat.eqb_eq; split; intros; lia].

Lemma crt_neq0 : forall a b : Z, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b ->
  bv_eqb (Z_to_bv 64 (a - b)) (Z_to_bv 64 0) = false.
Proof.
  intros a b Ha Hb E. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq.
  Z.div_mod_to_equations. lia.
Qed.

Lemma crt_mem : forall m L p ms D kd yd i nm u,
  pj_node rsegs m L p (JObj ms) D -> pj_u64 rsegs m (p + 24) kd -> pj_u64 rsegs m (p + 32) yd ->
  nth_error ms i = Some (nm, u) ->
  exists x k D1, pj_u64 rsegs m (yd + 8 * Z.of_nat i) x /\ pj_cstr rsegs m L x k nm /\
    pj_node rsegs m L (kd + 56 * Z.of_nat i) u D1 /\
    (forall z, pj_foot (kd + 56 * Z.of_nat i) D1 z -> pj_foot p D z) /\
    0 <= yd + 8 * Z.of_nat i /\ yd + 8 * Z.of_nat i + 8 <= 2 ^ 64 /\
    0 <= kd + 56 * Z.of_nat i /\ kd + 56 * Z.of_nat i + 56 <= 2 ^ 64.
Proof.
  intros m L p ms0 D0 kd yd i nm u H K Y E.
  assert (E' : nth_error (slots (JObj ms0)) i = Some (Some nm, u))
    by (cbn [slots]; rewrite nth_error_map, E; reflexivity).
  destruct (pj_slot rsegs m L p (JObj ms0) D0 i (Some nm) u H E')
    as (num & str & kids & keys & n & cap & D1 & Hh & _ & _ & HN & HF & (_ & x & k & X & C)).
  destruct Hh as (_ & _ & _ & _ & K' & Y' & _ & _).
  pose proof (pj_u64_uniq rsegs m _ _ _ K' K) as EK. pose proof (pj_u64_uniq rsegs m _ _ _ Y' Y) as EY.
  subst kids keys.
  assert (R : 0 <= kd + 56 * Z.of_nat i /\ kd + 56 * Z.of_nat i + 56 <= 2 ^ 64).
  { destruct u; cbn [pj_node] in HN;
      destruct HN as (_ & _ & _ & _ & _ & _ & _ & _ & ((_ & (I0 & I1 & _)) & _) & _); lia. }
  pose proof X as (_ & (X0 & X1 & _)). rewrite length_le8 in X1.
  exists x, k, D1. split; [exact X|]. split; [exact C|]. split; [exact HN|]. split; [exact HF|]. lia.
Qed.

Definition crt_post (sp gp tp s1 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
    : machine_state -> Prop :=
  fun ms0 => exists (t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9'
                     t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms0 = MS (mkR (Z_to_bv 64 0x1423c) sp gp tp t0' t1' t2' s0' s1 s1 a1' a2' a3' a4' a5' a6' a7'
                  s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x157f8) fc None m' (seg_rom rsegs) /\
    munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Section Cmp.
Hypothesis HSTR : strcmp_contract.
Hypothesis HSAME : same_contract.
Variables (sp gp tp s1 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo doc : Z)
  (Lb : Z -> Z -> Prop) (ms ms' : list (list Z * jv)) (D Db : list (Z * Z)) (ix : nat) (kd yd kb yb : Z).
Hypothesis PD : pj_node rsegs m Lb doc (JObj ms) D.
Hypothesis PB : pj_node rsegs m Lb (bv_unsigned sp + 112) (JObj ms') Db.
Hypothesis REL : crt_set_rel ms ms' ix.
Hypothesis MI : mem_inv rsegs m.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : lo + same_k (JObj ms) <= bv_unsigned sp.
Hypothesis OD : forall z, pj_foot doc D z -> outside [(lo, bv_unsigned sp)] z.
Hypothesis OB : forall z, pj_foot (bv_unsigned sp + 112) Db z -> outside [(lo, bv_unsigned sp)] z.
Hypothesis KD : pj_u64 rsegs m (doc + 24) kd.
Hypothesis YD : pj_u64 rsegs m (doc + 32) yd.
Hypothesis ND : pj_u64 rsegs m (doc + 40) (Z.of_nat (length ms)).
Hypothesis KB : pj_u64 rsegs m (bv_unsigned sp + 112 + 24) kb.
Hypothesis YB : pj_u64 rsegs m (bv_unsigned sp + 112 + 32) yb.
Hypothesis NB : pj_u64 rsegs m (bv_unsigned sp + 112 + 40) (Z.of_nat (length ms')).

Lemma now_d : forall m1, munch [(lo, bv_unsigned sp)] m m1 -> pj_node rsegs m1 Lb doc (JObj ms) D.
Proof.
  intros m1 MU.
  exact (pj_node_munch rsegs _ m Lb m1 Lb doc (JObj ms) D PD (pj_node_blocks rsegs (JObj ms) m Lb doc D PD) MU OD).
Qed.

Lemma now_b : forall m1, munch [(lo, bv_unsigned sp)] m m1 -> pj_node rsegs m1 Lb (bv_unsigned sp + 112) (JObj ms') Db.
Proof.
  intros m1 MU.
  exact (pj_node_munch rsegs _ m Lb m1 Lb _ (JObj ms') Db PB
           (pj_node_blocks rsegs (JObj ms') m Lb _ Db PB) MU OB).
Qed.

Lemma u64d : forall m1 off v, munch [(lo, bv_unsigned sp)] m m1 -> 0 <= off <= 48 ->
  pj_u64 rsegs m (doc + off) v -> pj_u64 rsegs m1 (doc + off) v.
Proof.
  intros m1 off v MU Ho H. apply (pj_u64_eq rsegs m m1 _ v H).
  intros x Hx. apply MU. apply OD. left. lia.
Qed.

Lemma u64b : forall m1 off v, munch [(lo, bv_unsigned sp)] m m1 -> 0 <= off <= 48 ->
  pj_u64 rsegs m (bv_unsigned sp + 112 + off) v -> pj_u64 rsegs m1 (bv_unsigned sp + 112 + off) v.
Proof.
  intros m1 off v MU Ho H. apply (pj_u64_eq rsegs m m1 _ v H).
  intros x Hx. apply MU. apply OB. left. lia.
Qed.

Lemma crt_tail : forall m1 ra1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  s2 = Z_to_bv 64 yb -> s5 = Z_to_bv 64 (Z.of_nat ix) ->
  munch [(lo, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra1 t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 E2 E4 MU WM MI1 ST1.
  subst s2 s5.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  destruct REL as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (proj1 ND) as Rnd. pose proof (proj1 KB) as Rkb. pose proof (proj1 YB) as Ryb.
  pose proof (now_b m1 MU) as QB.
  pose proof (u64b m1 24 kb MU ltac:(lia) KB) as KB1. pose proof (u64b m1 32 yb MU ltac:(lia) YB) as YB1.
  destruct (crt_mem _ _ _ _ _ _ _ _ _ _ QB KB1 YB1 R6) as (x & k & D1 & X & C & HN & _ & RX0 & RX1 & RK0 & RK1).
  cbn [pj_node] in HN.
  destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & _ & _ & _ & _ & ks & Cs & _).
  destruct Hh as (_ & T & _ & SR & _ & _ & _ & _). cbn [tag] in T.
  pose proof (rd8 _ _ _ _ X) as RX. pose proof (rd8 _ _ _ _ KB1) as RKB. pose proof (rd8 _ _ _ _ SR) as RS.
  pose proof (rd4 _ _ _ _ T) as RT.
  pose proof (proj1 X) as Rx. pose proof (proj1 SR) as Rs.
  zstep.
  replace (Z.shiftl (Z.of_nat ix) 3) with (8 * Z.of_nat ix) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep.
  destruct (cstr_bytes _ _ _ _ _ _ C) as (BY & NZ).
  do 3 zstep.
  eapply evt_cut.
  { eapply HSTR with (sx := map (Z_to_bv 8) MOD_AT) (sy := map (Z_to_bv 8) MOD_AT).
    - rewrite unsigned_lit by lia. exact BY.
    - exact NZ.
    - exact (crt_img_at _ _ _ (crt_modat_img m1 MI1)).
    - exact NZ. }
  intros ms2 (r & x11 & x12 & x13 & E & RE). subst ms2.
  replace (ret_pc (Z_to_bv 64 0x14200)) with (Z_to_bv 64 0x14200) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Er : r = Z_to_bv 64 0) by (apply RE; reflexivity). subst r.
  zstep. crt_if false; [|reflexivity].
  zstep. zstep.
  replace (Z.shiftl (Z.of_nat ix) 6) with (64 * Z.of_nat ix) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  do 3 zstep.
  rewrite ?sx32_small by lia.
  zstep. zstep. crt_if false; [|crt_side].
  zstep.
  destruct (cstr_bytes _ _ _ _ _ _ Cs) as (BYs & NZs).
  do 3 zstep.
  eapply evt_cut.
  { eapply HSTR with (sx := map (Z_to_bv 8) STAMP) (sy := map (Z_to_bv 8) STAMP).
    - rewrite unsigned_lit by lia. exact BYs.
    - exact NZs.
    - exact (crt_img_at _ _ _ (crt_stamp_img m1 MI1)).
    - exact NZs. }
  intros ms2 (r2 & y11 & y12 & y13 & E2 & RE2). subst ms2.
  replace (ret_pc (Z_to_bv 64 0x14230)) with (Z_to_bv 64 0x14230) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Er2 : r2 = Z_to_bv 64 0) by (apply RE2; reflexivity). subst r2.
  zstep. crt_if false; [|reflexivity].
  zstep. zstep.
  apply evt_done. unfold crt_post. do 24 eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MI1 ST1))).
Qed.

Definition cmp_loop (k i : nat) : Prop :=
  forall m1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  (i + k = length ms)%nat ->
  s0 = Z_to_bv 64 doc -> s2 = Z_to_bv 64 yb -> s4 = Z_to_bv 64 (Z.of_nat k) -> s5 = Z_to_bv 64 (Z.of_nat ix) ->
  s3 = Z_to_bv 64 (56 * Z.of_nat i) -> s6 = Z_to_bv 64 (yd + 8 * Z.of_nat i) -> s7 = Z_to_bv 64 kb ->
  s8 = Z_to_bv 64 (yb + 8 * Z.of_nat i) -> s9 = Z_to_bv 64 (Z.of_nat ix - Z.of_nat i) ->
  munch [(lo, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141a8) fc None m1 (seg_rom rsegs)).

Lemma cmp_next : forall k i, (i + S k = length ms)%nat -> (k = 0%nat \/ cmp_loop k (S i)) ->
  forall m1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  s0 = Z_to_bv 64 doc -> s2 = Z_to_bv 64 yb -> s4 = Z_to_bv 64 (Z.of_nat (S k)) -> s5 = Z_to_bv 64 (Z.of_nat ix) ->
  s3 = Z_to_bv 64 (56 * Z.of_nat i) -> s6 = Z_to_bv 64 (yd + 8 * Z.of_nat i) -> s7 = Z_to_bv 64 kb ->
  s8 = Z_to_bv 64 (yb + 8 * Z.of_nat i) -> s9 = Z_to_bv 64 (Z.of_nat ix - Z.of_nat i) ->
  munch [(lo, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141d0) fc None m1 (seg_rom rsegs)).
Proof.
  intros k i HI HK m1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6
    E0 E2 E3 E4 E5 E6 E7 E8 E9 MU WM MI1 ST1.
  subst s0 s2 s3 s4 s5 s6 s7 s8 s9.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (proj1 ND) as Rnd.
  do 6 zstep.
  destruct k as [|k].
  - crt_if false; [|reflexivity].
    eapply crt_tail; first [reflexivity | eassumption].
  - crt_if true; [|crt_side].
    destruct HK as [HK|HL]; [lia|].
    unfold cmp_loop in HL.
    eapply HL; first [eassumption | lia | word_eq_tac].
Qed.

Lemma cmp_iter : forall k i, (k = 0%nat \/ cmp_loop k (S i)) -> cmp_loop (S k) i.
Proof.
  intros k i HK. unfold cmp_loop.
  intros m1 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6
    HI E0 E2 E3 E4 E5 E6 E7 E8 E9 MU WM MI1 ST1.
  subst s0 s2 s3 s4 s5 s6 s7 s8 s9.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof REL as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (proj1 ND) as Rnd. pose proof (proj1 KB) as Rkb. pose proof (proj1 YB) as Ryb.
  pose proof (proj1 KD) as Rkd. pose proof (proj1 YD) as Ryd.
  destruct (nth_error ms i) as [[nm u]|] eqn:Hi; [|apply nth_error_None in Hi; lia].
  destruct (R5 i nm u Hi) as (u' & Hi' & Eu).
  pose proof (now_d m1 MU) as QD. pose proof (now_b m1 MU) as QB.
  pose proof (u64d m1 24 kd MU ltac:(lia) KD) as KD1. pose proof (u64d m1 32 yd MU ltac:(lia) YD) as YD1.
  pose proof (u64b m1 24 kb MU ltac:(lia) KB) as KB1. pose proof (u64b m1 32 yb MU ltac:(lia) YB) as YB1.
  destruct (crt_mem _ _ _ _ _ _ _ _ _ _ QD KD1 YD1 Hi)
    as (xd & kd' & D1 & XD & CD & ND1 & FD & RXD0 & RXD1 & RKD0 & RKD1).
  destruct (crt_mem _ _ _ _ _ _ _ _ _ _ QB KB1 YB1 Hi')
    as (xb & kb' & D2 & XB & CB & NB1 & FB & RXB0 & RXB1 & RKB0 & RKB1).
  pose proof (rd8 _ _ _ _ XD) as RXD. pose proof (rd8 _ _ _ _ XB) as RXB. pose proof (rd8 _ _ _ _ KD1) as RKD.
  pose proof (proj1 XD) as Rxd. pose proof (proj1 XB) as Rxb.
  do 3 zstep.
  destruct (cstr_bytes _ _ _ _ _ _ CB) as (BYb & NZb). destruct (cstr_bytes _ _ _ _ _ _ CD) as (BYd & NZd).
  eapply evt_cut.
  { eapply HSTR with (sx := map (Z_to_bv 8) nm) (sy := map (Z_to_bv 8) nm).
    - rewrite unsigned_lit by lia. exact BYb.
    - exact NZb.
    - rewrite unsigned_lit by lia. exact BYd.
    - exact NZd. }
  intros ms2 (r & x11 & x12 & x13 & E & RE). subst ms2.
  replace (ret_pc (Z_to_bv 64 0x141b4)) with (Z_to_bv 64 0x141b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Er : r = Z_to_bv 64 0) by (apply RE; reflexivity). subst r.
  zstep. crt_if false; [|reflexivity].
  zstep.
  destruct (Nat.eq_dec i ix) as [EI|EI].
  - crt_if true; [|subst i; rewrite Z.sub_diag; reflexivity].
    eapply (cmp_next k i); first [exact HK | eassumption | lia | word_eq_tac].
  - crt_if false; [|apply crt_neq0; lia].
    do 4 zstep.
    rewrite (Eu EI) in NB1.
    assert (DU : (depth u < depth (JObj ms))%nat) by exact (depth_member ms nm u (nth_error_In _ _ Hi)).
    assert (KU : lo + same_k u <= bv_unsigned sp) by (pose proof LO as LO'; unfold same_k, SAME_FS in LO' |- *; lia).
    eapply evt_cut.
    { eapply HSAME with (pa := kb + 56 * Z.of_nat i) (pb := kd + 56 * Z.of_nat i) (ta := u) (tb := u)
        (Da := D2) (Db := D1) (L := Lb) (lo := lo).
      - word_eq_tac.
      - word_eq_tac.
      - exact NB1.
      - exact ND1.
      - exact MI1.
      - exact ST1.
      - exact KU.
      - intros z Hz. pose proof (OB z (FB z Hz)) as Oz. cbn [outside] in Oz |- *. lia.
      - intros z Hz. pose proof (OD z (FD z Hz)) as Oz. cbn [outside] in Oz |- *. lia. }
    intros ms2 (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                E & MU2 & WM2 & MI2 & ST2 & RES & _ & _).
    subst ms2.
    replace (ret_pc (Z_to_bv 64 0x141cc)) with (Z_to_bv 64 0x141cc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct RES as [(_ & Er)|(NE & _)]; [subst r | exfalso; apply NE; reflexivity].
    assert (MUF : munch [(lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. lia. }
    pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMF.
    zstep. crt_if false; [|reflexivity].
    eapply (cmp_next k i); first [exact HK | eassumption | lia | word_eq_tac].
Qed.

Lemma cmp_all : forall k i, (0 < k)%nat -> cmp_loop k i.
Proof.
  induction k as [|k IHk]; intros i Hk; [lia|].
  apply cmp_iter. destruct k as [|k]; [left; reflexivity | right; apply IHk; lia].
Qed.

Lemma cmp_from : forall ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  s0 = Z_to_bv 64 doc -> s4 = Z_to_bv 64 (Z.of_nat (length ms)) -> s5 = Z_to_bv 64 (Z.of_nat ix) ->
  a0 = Z_to_bv 64 (if Nat.eqb ix (length ms) then 1 else 0) ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14180) fc None m (seg_rom rsegs)).
Proof.
  intros ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 E0 E3 E4 EA.
  subst s0 s4 s5 a0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof REL as (R1 & R2 & R3 & R4 & R5 & R6).
  assert (EN : Z.of_nat (length ms') = Z.of_nat (length ms) + (if Nat.eqb ix (length ms) then 1 else 0))
    by (rewrite R4; destruct (Nat.eqb ix (length ms)); lia).
  pose proof (rd8 _ _ _ _ NB) as RNB. rewrite EN in RNB.
  pose proof (rd8 _ _ _ _ YB) as RYB. pose proof (rd8 _ _ _ _ KB) as RKB. pose proof (rd8 _ _ _ _ YD) as RYD.
  pose proof (proj1 YB) as Ryb. pose proof (proj1 KB) as Rkb. pose proof (proj1 YD) as Ryd.
  pose proof (proj1 ND) as Rnd.
  do 3 zstep.
  crt_if false; [|unfold bv_eqb; rewrite Z.eqb_refl; reflexivity].
  do 2 zstep.
  destruct (Nat.eq_dec (length ms) 0) as [N0|N0].
  - crt_if true; [|rewrite N0; reflexivity].
    eapply crt_tail; first [reflexivity | apply munch_refl | apply wmono_refl | eassumption].
  - crt_if false; [|rewrite bv_eqb_lit by lia; apply Z.eqb_neq; lia].
    do 5 zstep.
    pose proof (cmp_all (length ms) 0 ltac:(lia)) as LP. unfold cmp_loop in LP.
    eapply LP; first [reflexivity | apply munch_refl | apply wmono_refl | eassumption | lia | word_eq_tac].
Qed.

Definition at_loop (k i : nat) : Prop :=
  forall ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  (i + k = length ms)%nat -> (i <= ix)%nat ->
  s0 = Z_to_bv 64 doc -> s2 = Z_to_bv 64 MOD_AT_A -> s4 = Z_to_bv 64 (Z.of_nat (length ms)) ->
  s3 = Z_to_bv 64 (Z.of_nat (length ms)) -> s6 = Z_to_bv 64 (yd + 8 * Z.of_nat i) ->
  s7 = Z_to_bv 64 (Z.of_nat i + 1) ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14144) fc None m (seg_rom rsegs)).

Lemma at_iter : forall k i, (k = 0%nat \/ at_loop k (S i)) -> at_loop (S k) i.
Proof.
  intros k i HK. unfold at_loop.
  intros ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 HI HX E0 E2 E3 E5 E6 E7.
  subst s0 s2 s3 s4 s6 s7.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof REL as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (proj1 ND) as Rnd. pose proof (proj1 YD) as Ryd.
  destruct (nth_error ms i) as [[nm u]|] eqn:Hi; [|apply nth_error_None in Hi; lia].
  destruct (crt_mem _ _ _ _ _ _ _ _ _ _ PD KD YD Hi) as (xd & kd' & D1 & XD & CD & _ & _ & RXD0 & RXD1 & _ & _).
  pose proof (rd8 _ _ _ _ XD) as RXD. pose proof (proj1 XD) as Rxd.
  do 3 zstep.
  destruct (cstr_bytes _ _ _ _ _ _ CD) as (BYd & NZd).
  eapply evt_cut.
  { eapply HSTR with (sx := map (Z_to_bv 8) nm) (sy := map (Z_to_bv 8) MOD_AT).
    - rewrite unsigned_lit by lia. exact BYd.
    - exact NZd.
    - exact (crt_img_at _ _ _ (crt_modat_img m MI)).
    - exact (crt_map_nz _ crt_modat_ok). }
  intros ms2 (r & x11 & x12 & x13 & E & RE). subst ms2.
  replace (ret_pc (Z_to_bv 64 0x14150)) with (Z_to_bv 64 0x14150) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (Nat.eq_dec i ix) as [EI|EI].
  - subst i.
    assert (Hlt : (ix < length ms)%nat) by lia.
    destruct (R3 Hlt) as (u0 & Hu0). rewrite Hi in Hu0. injection Hu0 as Enm _. subst nm.
    assert (Er : r = Z_to_bv 64 0) by (apply RE; reflexivity). subst r.
    zstep. crt_if true; [|reflexivity].
    do 4 zstep.
    destruct k as [|k].
    + crt_if true; [|crt_side].
      eapply cmp_from; first [word_eq_tac | crt_flag_tac].
    + crt_if false; [|crt_side].
      do 3 zstep. crt_if false; [|crt_side].
      zstep.
      eapply cmp_from; first [word_eq_tac | crt_flag_tac].
  - assert (Hlt : (i < ix)%nat) by lia.
    assert (NM : nm <> MOD_AT) by exact (R2 i nm u Hlt Hi).
    assert (Er : r <> Z_to_bv 64 0).
    { intros E0. apply NM. apply (map8_inj _ _ (cstr_forall _ _ _ _ _ _ CD) crt_modat_ok). apply RE. exact E0. }
    zstep.
    crt_if false; [|destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER; [apply bv_eqb_true in ER; contradiction | reflexivity]].
    do 5 zstep.
    destruct k as [|k].
    + crt_if true; [|crt_side].
      eapply cmp_from; first [word_eq_tac | crt_flag_tac].
    + crt_if false; [|crt_side].
      do 3 zstep. crt_if true; [|crt_side].
      destruct HK as [HK|HL]; [lia|].
      unfold at_loop in HL.
      eapply HL; first [lia | word_eq_tac].
Qed.

Lemma at_all : forall k i, (0 < k)%nat -> at_loop k i.
Proof.
  induction k as [|k IHk]; intros i Hk; [lia|].
  apply at_iter. destruct k as [|k]; [left; reflexivity | right; apply IHk; lia].
Qed.

Lemma cmp_main : forall ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6,
  s0 = Z_to_bv 64 doc -> s3 = Z_to_bv 64 (Z.of_nat (length ms)) -> s4 = Z_to_bv 64 0 ->
  evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x1411c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 E0 E3 E4.
  subst s0 s3 s4.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof REL as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (rd8 _ _ _ _ ND) as RND. pose proof (rd8 _ _ _ _ YD) as RYD.
  pose proof (proj1 ND) as Rnd. pose proof (proj1 YD) as Ryd.
  zstep. crt_if false; [|reflexivity].
  do 4 zstep.
  destruct (Nat.eq_dec (length ms) 0) as [N0|N0].
  - crt_if true; [|rewrite N0; reflexivity].
    zstep.
    eapply cmp_from; first [word_eq_tac | crt_flag_tac].
  - crt_if false; [|rewrite bv_eqb_lit by lia; apply Z.eqb_neq; lia].
    zstep. crt_if false; [|unfold bv_eqb; rewrite Z.eqb_refl; reflexivity].
    do 4 zstep.
    pose proof (at_all (length ms) 0 ltac:(lia)) as LP. unfold at_loop in LP.
    eapply LP; first [lia | word_eq_tac].
Qed.

End Cmp.

Lemma crt_cmp : strcmp_contract -> same_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo doc : Z) (Lb : Z -> Z -> Prop)
         (ms ms' : list (list Z * jv)) (D Db : list (Z * Z)) (ix : nat),
    s0 = Z_to_bv 64 doc -> s3 = Z_to_bv 64 (Z.of_nat (length ms)) -> s4 = Z_to_bv 64 0 ->
    pj_node rsegs m Lb doc (JObj ms) D ->
    pj_node rsegs m Lb (bv_unsigned sp + 112) (JObj ms') Db ->
    crt_set_rel ms ms' ix ->
    bytes_at rsegs m MOD_AT_A (map (Z_to_bv 8) (MOD_AT ++ [0])) ->
    bytes_at rsegs m STAMP_A (map (Z_to_bv 8) (STAMP ++ [0])) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + same_k (JObj ms) <= bv_unsigned sp ->
    (forall z, pj_foot doc D z -> outside [(lo, bv_unsigned sp)] z) ->
    (forall z, pj_foot (bv_unsigned sp + 112) Db z -> outside [(lo, bv_unsigned sp)] z) ->
    evt rsegs
      (fun ms0 => exists (t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9'
                         t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms0 = MS (mkR (Z_to_bv 64 0x1423c) sp gp tp t0' t1' t2' s0' s1 s1 a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x157f8) fc None m' (seg_rom rsegs) /\
         munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x1411c) fc None m (seg_rom rsegs)).
Proof.
  intros HS HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo doc Lb ms ms' D Db ix E0 E3 E4 PD PB REL _ _ MI ST LO OD OB.
  destruct (pj_view _ _ _ _ _ _ PD) as (numd & strd & kidsd & keysd & nd & capd & HD & NDn & _).
  destruct (pj_view _ _ _ _ _ _ PB) as (numb & strb & kidsb & keysb & nb & capb & HB & NBn & _).
  cbn [slots] in NDn, NBn. rewrite length_map in NDn, NBn. subst nd nb.
  destruct HD as (_ & _ & _ & _ & KD & YD & ND & _).
  destruct HB as (_ & _ & _ & _ & KB & YB & NB & _).
  change (evt rsegs (crt_post sp gp tp s1 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0x1411c) fc None m (seg_rom rsegs))).
  eapply cmp_main with (Lb := Lb) (ms' := ms') (D := D) (Db := Db) (ix := ix) (kd := kidsd) (yd := keysd)
    (kb := kidsb) (yb := keysb); eassumption.
Qed.
