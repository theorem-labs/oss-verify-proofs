From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import memcpy_c read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.
Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac rn_fin :=
  apply evt_done; do 11 eexists; split; [reflexivity|];
  repeat (split; [eassumption|]);
  repeat split; ulit; f_equal; lia.


Definition m48 (u : Z) : Z :=
  Z.land (bv_unsigned (Z_to_bv 64 (u + bv_swrap 32
    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (u * 171))) 13))) 4)) -
     bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (u * 171))) 13))) 6))))))
    255.

Lemma m48_val : forall u, 0 <= u < 256 -> m48 u = u mod 48.
Proof.
  intros u Hu.
  assert (H : forallb (fun v => m48 v =? v mod 48) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace u with (Z.of_nat (Z.to_nat u)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. exact R. Qed.

Lemma zxb_unsigned : forall x : byte, bv_unsigned (zxb x) = bv_unsigned x.
Proof. intros x. unfold zxb. pose proof (byte_range x). apply unsigned_lit. lia. Qed.

Lemma rn_k_nil : forall pl : list byte, length pl = 0%nat -> rn_k pl = 0.
Proof. intros [|x rest] H; [reflexivity|cbn in H; lia]. Qed.

Lemma rn_k_cons : forall (pl : list byte) x, nth_error pl 0 = Some x ->
  rn_k pl = Z.min (bv_unsigned x mod 48) (Z.of_nat (length pl) - 1).
Proof.
  intros [|y rest] x H; [discriminate|]. cbn in H. inversion H; subst. cbn [rn_k length]. f_equal. lia.
Qed.

Lemma rn_k_range : forall pl : list byte, 0 <= rn_k pl <= 47 /\ rn_k pl <= Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1.
Proof.
  intros [|x rest]; cbn [rn_k length]; [lia|].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)). lia.
Qed.

Lemma first_byte : forall m p (pl : list byte) x, bytes_at rsegs m p pl -> nth_error pl 0 = Some x ->
  ov_read_bytes rsegs m (wa (p + 0)) 1 = Some [x].
Proof.
  intros m p pl x HB Hx. destruct pl as [|y rest]; [discriminate|]. cbn in Hx. inversion Hx; subst.
  rewrite (bytes_at_read rsegs m p (x :: rest) 0 1 HB ltac:(lia)) by (cbn; lia). reflexivity.
Qed.

Lemma land7 : forall c, 0 <= c -> c mod 8 = 0 -> Z.land c 7 = 0.
Proof. intros c Hc H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof. intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (a <? b); reflexivity. Qed.

Lemma sltiu_lit : forall a i, 0 <= a < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 a) i = Z_to_bv 64 (if a <? i then 1 else 0).
Proof.
  intros a i Ha Hi. unfold v_sltiu. rewrite unsigned_lit by lia. rewrite (bv_wrap_small 64 i) by (unfold bv_modulus; lia).
  destruct (a <? i); reflexivity.
Qed.

Ltac ltb_dec :=
  repeat match goal with |- context [?a <? ?b] =>
    first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ] end;
  cbn [negb]; cbv iota.

Ltac chk2 := rewrite sltu_lit by lia; rewrite sltiu_lit by lia; ltb_dec.

Ltac rn_mid :=
  step; step; rewrite ltu_lit by lia; ltb_dec;
  step; step; chk2;
  step; step; if_false;
  do 5 step; rn_fin.

Lemma rn_head : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (lo c p : Z) (pl : list byte),
  a0 = Z_to_bv 64 c -> c mod 8 = 0 ->
  rw_cells rsegs m c [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
  bytes_at rsegs m p pl ->
  0 <= p < 2 ^ 64 ->
  (pl <> [] -> 1 <= p /\ p + Z.of_nat (length pl) <= lo) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= c ->
  evt rsegs
    (fun ms' => exists (s0' s1' a0' a1' a2' a3' a4' a5' cp cn : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13800) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0' s1' a0' a1' a2' a3' a4'
                     a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MALLOC) fc None m' ro /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16)] m m' /\
       wmono rsegs m m' /\
       rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
       rw_cells rsegs m' c [C8 cp; C8 cn] /\
       stk rsegs m' lo (bv_unsigned sp + -32) /\
       s0' = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1) /\
       s1' = Z_to_bv 64 (rn_k pl) /\ a0' = Z_to_bv 64 (rn_k pl + 1) /\
       cp = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl) /\
       cn = Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 READ_NAME) fc None m ro).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ro
    lo c p pl -> CA CU PB HP PL ST LO SPC.
  unfold READ_NAME, MALLOC.
  pose proof (bytes_at_bound rsegs m p _ PB) as PBB.
  pose proof (rw_cells_bound rsegs m c _ CU) as CUB. cbn [cells_size csize Nat.add] in CUB.
  pose proof (rn_k_range pl) as KR.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (NR : Z.of_nat (length pl) < 2 ^ 64)
    by (destruct pl as [|y r]; [cbn; lia | specialize (PL ltac:(discriminate)); lia]).
  destruct (Z.eqb_spec (Z.of_nat (length pl)) 0) as [N0|N1].
  - rewrite (rn_k_nil pl) by lia. rewrite N0 in CU |- *.
    carve_frame 32%nat ST.
    do 6 step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    do 3 step. if_true.
    step. step. if_true.
    step.
    destruct (Z.eq_dec p 0) as [P0|P0].
    + rn_mid.
    + rn_mid.
  - destruct (nth_error pl 0) as [x|] eqn:NX;
      [|destruct pl; [cbn in N1; lia|discriminate]].
    assert (PL' : 1 <= p /\ p + Z.of_nat (length pl) <= lo) by (apply PL; intros E; subst pl; cbn in N1; lia).
    clear PL.
    rewrite (rn_k_cons pl x NX) in *.
    pose proof (byte_range x) as XR.
    pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)) as XM.
    carve_frame 32%nat ST.
    do 6 step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    do 3 step.
    rewrite eqb_lit by lia.
    if_false.
    do 5 step.
    rewrite ltu_lit by lia. ltb_dec.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (first_byte mm p pl x PB NX) as RD end.
    do 9 step.
    lazymatch goal with |- context [Z.land ?T 255] => change (Z.land T 255) with (m48 (bv_unsigned (zxb x))) end.
    rewrite zxb_unsigned, m48_val by exact XR.
    do 2 step.
    destruct (Z.ltb_spec (bv_unsigned x mod 48) (Z.of_nat (length pl) + -1)) as [LT|GE].
    + assert (BC : bv_ltu (Z_to_bv 64 (bv_unsigned x mod 48)) (Z_to_bv 64 (Z.of_nat (length pl) + -1)) = true)
        by (rewrite ltu_lit by lia; apply Z.ltb_lt; exact LT).
      rewrite BC; cbv iota.
      rn_mid.
    + assert (BC : bv_ltu (Z_to_bv 64 (bv_unsigned x mod 48)) (Z_to_bv 64 (Z.of_nat (length pl) + -1)) = false)
        by (rewrite ltu_lit by lia; apply Z.ltb_ge; exact GE).
      rewrite BC; cbv iota.
      step.
      rn_mid.
Qed.

Lemma rel_MS : forall segs s R F pc fc rv m0 ro, ms_rel segs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro.
Proof.
  intros segs s R F pc fc rv m0 ro H. destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). cbn in *. subst. reflexivity.
Qed.

Lemma rn_tail : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s k src : Z) (name j1 j2 : list byte) (rao s0o s1o s2o : word),
  a0 = Z_to_bv 64 s -> s0 = Z_to_bv 64 src -> s1 = Z_to_bv 64 k ->
  0 < s -> 0 <= k -> s + k + 1 <= bv_unsigned sp -> src < 2 ^ 64 ->
  (src + k <= s \/ s + k <= src) ->
  bytes_at rsegs m src name -> Z.of_nat (length name) = k ->
  rw_cells rsegs m s [CB (Z.to_nat k) j1] -> rw_cells rsegs m (s + k) [CB 1 j2] ->
  rw_cells rsegs m (bv_unsigned sp) [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  ro_agree rsegs m ->
  (forall i, 0 <= i < k + 1 -> ro_addr rsegs (wa (s + i)) = false) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pc' : word) (m' : word -> option byte),
       ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 s) a1' a2' a3' a4' a5'
                     a6' a7' s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F pc' fc None m' (seg_rom rsegs) /\
       pc' = ret_pc rao /\
       munch [(s, s + k + 1)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' s (name ++ [Z_to_bv 8 0]) /\
       rw_cells rsegs m' (bv_unsigned sp) [C8 s2o; C8 s1o; C8 s0o; C8 rao])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13800) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    s k src name j1 j2 rao s0o s1o s2o -> -> -> SP K0 SB SRCR DJ NB NL C1 C2 FR RA RO.
  pose proof (bytes_at_bound rsegs m src name NB) as NBB.
  pose proof (rw_cells_bound rsegs m (bv_unsigned sp) _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (mem_rel_normalize rsegs m RA) as MR0.
  step.
  rewrite eqb_lit by lia. if_false.
  do 4 step.
  eapply evt_cut.
  { apply (evt_normalize rsegs); [exact OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.FrameAPI.wx_apart_rsegs | exact RA |].
    eapply MEMCPY.
    - rewrite unsigned_lit by lia. apply bytes_at_normalize; [exact RA | exact NB].
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. destruct C1 as [[Hwf Hb] Hw].
      split; [split; [exact Hwf | apply bytes_at_normalize; [exact RA | exact Hb]] |].
      apply (wr_at_norm rsegs m (normalize rsegs m)); [exact MR0 | exact Hw |].
      intros i Hi. cbn [cells_size csize] in Hi. apply RO. lia.
    - rewrite !unsigned_lit by lia. lia.
    - apply mem_inv_normalize. }
  intros ms' (s0 & PO & REL & RS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & -> & MU & WM & MI' & DST & SRC).
  rewrite (rel_MS _ _ _ _ _ _ _ _ _ REL).
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 REL))))))) as MR1. unfold MS in MR1. cbn [ms_mem] in MR1.
  set (m' := ms_mem ms') in *. clearbody m'.
  rewrite !unsigned_lit in MU, DST by lia.
  pose proof (munch_rel rsegs _ m (normalize rsegs m) m' m0' MR0 MR1 RS MU) as MU'.
  pose proof (wmono_rel rsegs m (normalize rsegs m) m' m0' MR0 MR1 RS WM) as WM'.
  pose proof (ro_agree_same rsegs m m' RA RS) as RA'.
  assert (DST' : rw_cells rsegs m' s [CB (Z.to_nat k) name]).
  { destruct DST as [[Hwf Hb] Hw]. split; [split; [exact Hwf | apply (bytes_at_rel rsegs m' m0' s _ MR1); exact Hb] |].
    exact (wr_at_rel rsegs m' m0' s _ MR1 Hw). }
  clear MU WM DST SRC MI' REL RS MR1 MR0.
  replace (ret_pc (Z_to_bv 64 0x13814)) with (Z_to_bv 64 0x13814) by (apply bv_eq; vm_compute; reflexivity).
  pose proof (rw_cells_transport rsegs [(s, s + k)] m m' (bv_unsigned sp) _ FR MU' WM'
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR'.
  pose proof (rw_cells_transport rsegs [(s, s + k)] m m' (s + k) _ C2 MU' WM'
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as C2'.
  pose proof (munch_weaken [(s, s + k)] [(s, s + k + 1)] m m'
    ltac:(intros x Hx; cbn [outside] in *; lia) MU') as MU1.
  clear FR C2 C1 NB MU'.
  rename FR' into FR, C2' into C2, DST' into DST, WM' into WM.
  pose proof (rw_cells_store_ok rsegs m' (s + k) [CB 1 j2] 0 (CB 1 j2) 1 C2 eq_refl eq_refl) as HS.
  replace (s + k + Z.of_nat 0) with (s + k) in HS by lia.
  step.
  rewrite (unsigned_lit s) by lia. rewrite zb_lxor_ones by lia.
  step. rewrite ltu_lit by lia. ltb_dec.
  step. step.
  change (Z_to_bv 64 (s + k)) with (wa (s + k)).
  lazymatch goal with |- context [write_to_mem m' (wa (s + k)) ?bs] =>
    replace bs with [Z_to_bv 8 0] by (vm_compute; reflexivity) end.
  assert (RS2 : ro_same rsegs m' (write_to_mem m' (wa (s + k)) [Z_to_bv 8 0])).
  { intros x Hx. apply (write_ro_same rsegs); [split; [apply RO; lia | exact I] | exact Hx]. }
  pose proof (ro_agree_same rsegs _ _ RA' RS2) as RA2.
  pose proof (rw_cells_frame rsegs m' s _ (s + k) [Z_to_bv 8 0] DST ltac:(lia) ltac:(cbn [length]; lia)
    ltac:(cbn [cells_size csize length Nat.add]; lia)) as DST2.
  pose proof (rw_cells_frame rsegs m' (bv_unsigned sp) _ (s + k) [Z_to_bv 8 0] FR ltac:(lia) ltac:(cbn [length]; lia)
    ltac:(cbn [cells_size csize length Nat.add]; lia)) as FR2.
  pose proof (bytes_at_write_same rsegs m' (s + k) [Z_to_bv 8 0] ltac:(lia) ltac:(cbn [length]; lia)) as B0.
  pose proof (munch_write [(s, s + k + 1)] m m' (s + k) [Z_to_bv 8 0] MU1 ltac:(lia) ltac:(cbn [length]; lia)
    ltac:(cbn [inside length]; lia)) as MU2.
  pose proof (wmono_write rsegs m m' (wa (s + k)) [Z_to_bv 8 0] WM) as WM2.
  set (m2 := write_to_mem m' (wa (s + k)) [Z_to_bv 8 0]) in *.
  clearbody m2.
  clear RA' RS2 DST FR C2 HS MU1 WM.
  do 7 step.
  apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact RA2|].
  split; [|exact FR2].
  apply bytes_at_app. split.
  - destruct DST2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
  - rewrite NL. exact B0.
Qed.

Ltac outs := cbn [outside]; repeat split; try exact I; lia.

Lemma land_m2_mod2 : forall z, Z.land z (-2) mod 2 = 0.
Proof.
  intros z. change (Z.land z (-2) mod 2) with (Z.land z (-2) mod 2 ^ 1).
  rewrite <- (Z.land_ones _ 1) by lia. rewrite <- Z.land_assoc.
  change (Z.land (-2) (Z.ones 1)) with 0. apply Z.land_0_r.
Qed.

Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, YK14.v_jalr, YK11.jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  assert (E : bv_unsigned k mod 2 = 0).
  { rewrite <- H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    pose proof (land_m2_mod2 (bv_unsigned k)). Z.div_mod_to_equations. lia. }
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [lia | exact E].
Qed.

Lemma munch_byte : forall segs W m m' a, munch W m m' -> outside W a -> 0 <= a < 2 ^ 64 ->
  mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a HM HO HA.
  assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (apply HM; rewrite unsigned_lit by lia; exact HO).
  unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Ltac mb MU := eapply proj1; eapply (munch_byte _ _ _ _ _ MU); [outs | lia].

Lemma bytes_at_pt : forall segs m m' A bs, bytes_at segs m A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (A + i) = mbyte segs m (A + i)) -> bytes_at segs m' A bs.
Proof.
  intros segs m m' A bs (H1 & H2 & H3) HE. split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- H3 by exact Hi. exact (HE (Z.of_nat i) ltac:(lia)).
Qed.

Lemma rw_cells_pt : forall segs m m' A cs, rw_cells segs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte segs m' (A + i) = mbyte segs m (A + i) /\ (writable_at segs m (A + i) -> writable_at segs m' (A + i))) ->
  rw_cells segs m' A cs.
Proof.
  intros segs m m' A cs [[Hwf Hb] (W1 & W2 & W3)] HE. split; [split; [exact Hwf|]|].
  - apply (bytes_at_pt segs m m' A _ Hb). intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf.
    exact (proj1 (HE i Hi)).
  - split; [lia|]. split; [lia|]. intros i Hi. exact (proj2 (HE i Hi) (W3 i Hi)).
Qed.

Lemma bytes_at_sub : forall segs m a (bs : list byte) j len, bytes_at segs m a bs -> 0 <= j -> 0 <= len ->
  j + len <= Z.of_nat (length bs) -> bytes_at segs m (a + j) (bsub bs j len).
Proof.
  intros segs m a bs j len HB Hj Hl Hjl.
  rewrite <- (firstn_skipn (Z.to_nat j) bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn in HB. replace (Z.of_nat (Nat.min (Z.to_nat j) (length bs))) with j in HB by lia.
  unfold bsub. rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat j) bs)) in HB.
  apply bytes_at_app in HB. exact (proj1 HB).
Qed.

Lemma find_segment_in : forall segs a n sg, find_segment segs a n = Some sg ->
  In sg segs /\ Z.of_N (seg_base sg) <= a /\ a + n <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction segs as [|s0 rest IH]; intros a n sg H; cbn in H; [discriminate|].
  match type of H with context [if ?t then _ else _] => destruct t eqn:E end.
  - inversion H; subst. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity|lia].
  - destruct (IH a n sg H) as (H1 & H2 & H3). split; [right; exact H1|lia].
Qed.

Lemma rsegs_res : forallb (fun sg => let r := segment_reservation sg in
  (bv_unsigned (fst r) <=? Z.of_N (seg_base sg)) &&
  (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? bv_unsigned (fst r) + bv_unsigned (snd r))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_top : forallb (fun r => bv_unsigned (fst r) + bv_unsigned (snd r) <=? 140735332483072)
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_res : forall a sg, find_segment rsegs a 1 = Some sg ->
  In (segment_reservation sg) (segments_reserved rsegs) /\
  bv_unsigned (fst (segment_reservation sg)) <= a < bv_unsigned (fst (segment_reservation sg)) + bv_unsigned (snd (segment_reservation sg)).
Proof.
  intros a sg E. destruct (find_segment_in _ _ _ _ E) as (Hin & H1 & H2).
  split; [unfold segments_reserved; apply in_map; exact Hin|].
  pose proof rsegs_res as R. rewrite forallb_forall in R. specialize (R sg Hin). cbv zeta in R.
  apply andb_prop in R. destruct R as [R1 R2]. apply Z.leb_le in R1, R2. lia.
Qed.

Lemma res_low : forall r, In r (segments_reserved rsegs) -> bv_unsigned (fst r) + bv_unsigned (snd r) <= 140735332483072.
Proof. intros r Hr. pose proof rsegs_top as T. rewrite forallb_forall in T. apply Z.leb_le. exact (T r Hr). Qed.

Lemma rsegs_ne : rsegs <> [].
Proof. vm_compute. discriminate. Qed.

Lemma no_seg : forall B a, ms_segs B = rsegs -> (140735332483072 <= a \/ ~ in_img B a) -> find_segment rsegs a 1 = None.
Proof.
  intros B a SEGS H. destruct (find_segment rsegs a 1) as [sg|] eqn:E; [|reflexivity].
  destruct (seg_res a sg E) as [Hin Hb]. pose proof (res_low _ Hin) as T.
  destruct H as [H|H]; [lia|]. exfalso. apply H. unfold in_img. rewrite SEGS. split; [exact rsegs_ne|].
  exists (segment_reservation sg). split; [exact Hin|exact Hb].
Qed.

Lemma img_low : forall B a, ms_segs B = rsegs -> in_img B a -> 0 <= a < 140735332483072.
Proof.
  intros B a SEGS (_ & r & Hr & H1 & H2). rewrite SEGS in Hr. pose proof (res_low r Hr).
  pose proof (bv_unsigned_in_range 64 (fst r)). lia.
Qed.

Lemma mrd_present : forall m (x : word), find_segment rsegs (bv_unsigned x) 1 = None ->
  mrd rsegs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x HF HM. unfold mrd, PropExec.seg_rom, memory_read in HM. change (Z.of_N 1) with 1 in HM.
  rewrite HF in HM. destruct (m x) as [b|]; [exists b; reflexivity|contradiction].
Qed.

Lemma wview_present : forall m (x : word), find_segment rsegs (bv_unsigned x) 1 = None ->
  wview rsegs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x HF HW. unfold wview in HW. rewrite HF in HW. destruct (m x) as [b|]; [exists b; reflexivity|contradiction].
Qed.

Lemma high_none : forall a, 140735332483072 <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a H. destruct (find_segment rsegs a 1) as [sg|] eqn:E; [|reflexivity].
  destruct (seg_res a sg E) as [Hin Hb]. pose proof (res_low _ Hin). lia.
Qed.

Lemma stk_high : forall m lo hi, 140735332483072 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha. specialize (H a Ha).
  split; [exact H|].
  destruct (wview_present m (wa a) ltac:(rewrite wa_unsigned by lia; apply high_none; lia) H) as [b Hb].
  exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma stk_present : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> present m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [b Hb].
  unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma blocks_in : forall L A a n, In (a, n) (blocks L A) -> exists q, ptr_addr L q = a /\ In (q, n) (user_blocks A).
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H. destruct H as ([q n'] & E & Hin).
  cbn in E. inversion E; subst. exists q. split; [reflexivity|exact Hin].
Qed.

Lemma pw_mid : forall (b1 b2 : list (Z * Z)) x y, pairwise ranges_disjoint (b1 ++ x :: b2) -> In y (b1 ++ b2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  induction b1 as [|z b1 IH]; intros b2 x y HP Hy; cbn in HP, Hy.
  - destruct HP as [H _]. exact (H y Hy).
  - destruct HP as [H HP]. destruct Hy as [<-|Hy].
    + assert (Hx : In x (b1 ++ x :: b2)) by (apply in_or_app; right; left; reflexivity).
      pose proof (H x Hx) as D. unfold ranges_disjoint in D. lia.
    + exact (IH b2 x y HP Hy).
Qed.

Lemma ro_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 140735332483072.
Proof.
  intros x H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:E; [|discriminate].
  destruct (seg_res _ _ E) as [Hin Hb]. pose proof (res_low _ Hin). lia.
Qed.

Lemma present_of_bytes : forall B m a bs, ms_segs B = rsegs -> bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ in_img B (a + i)) ->
  forall i, 0 <= i < Z.of_nat (length bs) -> present m (a + i).
Proof.
  intros B m a bs SEGS (H1 & H2 & H3) HI i Hi.
  pose proof (H3 (Z.to_nat i) ltac:(lia)) as Hj. rewrite Z2Nat.id in Hj by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  destruct (mrd_present m (wa (a + i))) as [b' Hb'].
  - rewrite wa_unsigned by lia. apply (no_seg B (a + i) SEGS). right. apply HI. exact Hi.
  - rewrite Hj. discriminate.
  - exists b'. exact Hb'.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable.YK11.
Local Open Scope Z_scope.

Lemma canon_mkst : forall regs pc mem ro,
  canonical_register_state (mkst regs pc mem ro) = MS (mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma eqv_mkst : forall can ms R pc m ro, can = mkst R pc m ro -> ms_eqv can ms ->
  ms = mkst (ms_regs ms) pc m ro /\ forall r, getr (ms_regs ms) r = getr R r.
Proof.
  intros can ms R pc m ro -> H. destruct ms as [R' F' pc' sv' rv' fc' m' ro'].
  destruct H as (HR & HF & HP & HS & HV & HC & HM & HO). cbn in *. subst. split; [reflexivity|].
  intros r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply HR. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma head_canon : forall regs mem ro lo c p (pl : list byte),
  getr regs 10 = Z_to_bv 64 c -> c mod 8 = 0 ->
  rw_cells rsegs mem c [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
  bytes_at rsegs mem p pl -> 0 <= p < 2 ^ 64 ->
  (pl <> [] -> 1 <= p /\ p + Z.of_nat (length pl) <= lo) ->
  stk rsegs mem lo (bv_unsigned (getr regs 2)) -> lo + 32 <= bv_unsigned (getr regs 2) ->
  bv_unsigned (getr regs 2) <= c ->
  evt rsegs
    (fun ms' => exists m', ms' = mkst (ms_regs ms') (Z_to_bv 64 MALLOC) m' ro /\
       getr (ms_regs ms') 1 = Z_to_bv 64 0x13800 /\
       getr (ms_regs ms') 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32) /\
       getr (ms_regs ms') 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1) /\
       getr (ms_regs ms') 9 = Z_to_bv 64 (rn_k pl) /\
       getr (ms_regs ms') 10 = Z_to_bv 64 (rn_k pl + 1) /\
       (forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr (ms_regs ms') (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       munch [(bv_unsigned (getr regs 2) + -32, bv_unsigned (getr regs 2)); (c, c + 16)] mem m' /\
       wmono rsegs mem m' /\
       rw_cells rsegs m' (bv_unsigned (getr regs 2) + -32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
       rw_cells rsegs m' c [C8 (Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl));
                            C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))] /\
       stk rsegs m' lo (bv_unsigned (getr regs 2) + -32))
    (canonical_register_state (mkst regs (Z_to_bv 64 READ_NAME) mem ro)).
Proof.
  intros regs mem ro lo c p pl A0 CA CU PB HP PL ST LO SPC.
  rewrite canon_mkst. unfold mkR_of.
  eapply evt_mono.
  { apply rn_head with (F := fp_regs) (fc := fp_csr) (m := mem) (ro := ro) (lo := lo) (c := c) (p := p) (pl := pl);
      [exact A0 | exact CA | exact CU | exact PB | exact HP | exact PL | exact ST | exact LO | exact SPC]. }
  intros ms' (s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & cp & cn & m' & -> & MU & WM & FR & CU' & ST' & E0 & E1 & E2 & E3 & E4).
  subst s0' s1' a0' cp cn.
  exists m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr.
    assert (Hr' : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                  r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact FR|]. split; [exact CU'|]. exact ST'.
Qed.

Lemma tail_canon : memcpy_contract -> forall regs mem (s k src sp2 : Z) (name j1 j2 : list byte) (rao s0o s1o s2o : word),
  getr regs 10 = Z_to_bv 64 s -> getr regs 8 = Z_to_bv 64 src -> getr regs 9 = Z_to_bv 64 k ->
  getr regs 2 = Z_to_bv 64 sp2 -> 0 <= sp2 < 2 ^ 64 ->
  0 < s -> 0 <= k -> s + k + 1 <= sp2 -> src < 2 ^ 64 ->
  (src + k <= s \/ s + k <= src) ->
  bytes_at rsegs mem src name -> Z.of_nat (length name) = k ->
  rw_cells rsegs mem s [CB (Z.to_nat k) j1] -> rw_cells rsegs mem (s + k) [CB 1 j2] ->
  rw_cells rsegs mem sp2 [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  ro_agree rsegs mem ->
  (forall i, 0 <= i < k + 1 -> ro_addr rsegs (wa (s + i)) = false) ->
  evt rsegs
    (fun ms' => exists m', ms' = mkst (ms_regs ms') (ret_pc rao) m' (PropExec.seg_rom rsegs) /\
       getr (ms_regs ms') 2 = Z_to_bv 64 (sp2 + 32) /\
       getr (ms_regs ms') 8 = s0o /\ getr (ms_regs ms') 9 = s1o /\ getr (ms_regs ms') 10 = Z_to_bv 64 s /\
       getr (ms_regs ms') 18 = s2o /\
       (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr (ms_regs ms') (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       munch [(s, s + k + 1)] mem m' /\ wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' s (name ++ [Z_to_bv 8 0]) /\
       rw_cells rsegs m' sp2 [C8 s2o; C8 s1o; C8 s0o; C8 rao])
    (canonical_register_state (mkst regs (Z_to_bv 64 0x13800) mem (PropExec.seg_rom rsegs))).
Proof.
  intros MEMCPY regs mem s k src sp2 name j1 j2 rao s0o s1o s2o A0 S0 S1 SP R2 SPOS K0 SB SRCR DJ NB NL C1 C2 FR RA RO.
  rewrite canon_mkst. unfold mkR_of.
  replace (LinuxProcessSemantics.Riscv.Sem.reg_get regs 2) with (Z_to_bv 64 sp2) by (symmetry; exact SP).
  eapply evt_mono.
  { apply (rn_tail MEMCPY) with (F := fp_regs) (fc := fp_csr) (m := mem) (s := s) (k := k) (src := src) (name := name)
      (j1 := j1) (j2 := j2) (rao := rao) (s0o := s0o) (s1o := s1o) (s2o := s2o);
      [exact A0 | exact S0 | exact S1 | exact SPOS | exact K0 | rewrite unsigned_lit by lia; exact SB | exact SRCR |
       exact DJ | exact NB | exact NL | exact C1 | exact C2 | rewrite unsigned_lit by lia; exact FR | exact RA | exact RO]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & pc' & m' & -> & EPC &
              MU & WM & MI' & NM & FR').
  subst pc'. rewrite unsigned_lit in FR' by lia.
  exists m'. split; [reflexivity|].
  split; [rewrite unsigned_lit by lia; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr.
    assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                  r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact NM|]. exact FR'.
Qed.

Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem read_name_holds : malloc_contract B API -> memcpy_contract -> read_name_contract B API.
Proof.
  intros MALLOCH MEMCPY. unfold read_name_contract.
  intros L A regs mem md c p pl b SEGS MPC ERRL CP INIT A0 CAL SPC CUR CWR PR PAY PBLK RAG ROK ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_value as ACV.
  pose proof (rn_k_range pl) as KR.
  unfold call_pre_k in CP.
  destruct CP as (HMR & HWF & HBD & HRA & HAL & HCE & H63 & HWS & HTP & HWE & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (HH & HLZ & HMT).
  unfold spZ in *. unfold ALLOC_STACK in *.
  unfold malloc_contract in MALLOCH. rewrite SEGS in MALLOCH.
  rewrite SEGS in CUR, CWR, PAY, RAG, HWS, HWE. rewrite SEGS.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. unfold bv_modulus in RSP.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  assert (PLB : pl <> [] -> exists a len, In (a, len) (blocks L A) /\ a <= p /\ p + Z.of_nat (length pl) <= a + len /\
                  4096 <= a /\ a + len <= YM05.alloc_ceiling).
  { intros NE. destruct (PBLK NE) as (a & len & Hin & H1 & H2). destruct (blocks_in _ _ _ _ Hin) as (q & Eq & Hq).
    pose proof (mr_blocks_range _ _ LAWS _ _ _ _ _ _ HMR Hq) as R. subst a.
    exists (ptr_addr L q), len. repeat split; first [exact Hin | lia]. }
  eapply evt_SR_canon; [ | exact HH | exact HLZ | ].
  { apply (head_canon regs mem _ (bv_unsigned (getr regs 2) - (32 + 8192)) c p pl).
    - exact A0.
    - exact CAL.
    - split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact CUR] | exact CWR].
    - exact PAY.
    - exact PR.
    - intros NE. destruct (PLB NE) as (a & len & _ & H1 & H2 & H3 & H4). split; lia.
    - apply stk_high; [lia | lia | intros a Ha; apply HWS; lia].
    - lia.
    - exact SPC. }
  intros ms1 (can1 & HQ1 & EQ1).
  destruct HQ1 as (m1 & E1 & G1 & G2 & G8 & G9 & G10 & GR & MU1 & WM1 & FR1 & CU1 & ST1).
  destruct (eqv_mkst _ _ _ _ _ _ E1 EQ1) as [EM1 GE1].
  rewrite EM1. set (R1 := ms_regs ms1) in *. clearbody R1.
  assert (Q1 : getr R1 1 = Z_to_bv 64 0x13800) by (rewrite GE1; exact G1).
  assert (Q2 : getr R1 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32)) by (rewrite GE1; exact G2).
  assert (Q8 : getr R1 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1)) by (rewrite GE1; exact G8).
  assert (Q9 : getr R1 9 = Z_to_bv 64 (rn_k pl)) by (rewrite GE1; exact G9).
  assert (Q10 : getr R1 10 = Z_to_bv 64 (rn_k pl + 1)) by (rewrite GE1; exact G10).
  assert (QR : forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (intros r Hr; rewrite GE1; exact (GR r Hr)).
  clear GE1 G1 G2 G8 G9 G10 GR E1 EQ1 EM1 can1 ms1.
  assert (MR1 : aa_MR API L A m1 md).
  { apply (mr_frame _ _ LAWS L A mem m1 md md HMR).
    - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) as Hl.
      mb MU1.
    - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) as Hl.
      exists x. rewrite <- Hx. apply MU1. rewrite unsigned_lit by lia. outs.
    - intros q n0 i Hq Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as ([x Hx] & H1 & H2 & _).
      exists x. rewrite <- Hx. apply MU1. rewrite unsigned_lit by lia. outs.
    - reflexivity.
    - exact HH.
    - exact HLZ.
    - exact HMT. }
  assert (RA1 : ro_agree rsegs m1).
  { intros x Hx. pose proof (ro_low x Hx) as Hl. pose proof (bv_unsigned_in_range 64 x) as Rx.
    unfold mrd. rewrite (MU1 x ltac:(outs)). exact (RAG x Hx). }
  eapply SR_bind.
  { replace (Z_to_bv 64 MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MPC; reflexivity).
    apply (MALLOCH L A R1 m1 md (rn_k pl + 1) b).
    - unfold call_pre, spZ. rewrite Q2, unsigned_lit by lia. rewrite SEGS. unfold ALLOC_STACK.
      split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite Q1; apply ret_ok_even; rewrite unsigned_lit by lia; reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply WM1; apply HWS; lia|].
      split; [rewrite <- HTP; exact (QR 4 ltac:(lia))|].
      split; [intros a Ha; apply WM1; apply HWE; exact Ha|].
      intros E. rewrite INIT in E. discriminate.
    - exact RA1.
    - exact Q10.
    - exact ROK.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L' & A' & regs2 & mem2 & md2 & s & -> & CPOST & A0s & SNZ & S16 & FRESH & BLKS & KEPT & RA2 & GK &
                   UBK & INIT' & REGL & ROK').
  rewrite Q1, SEGS. rewrite SEGS in RA2.
  unfold call_post_k in CPOST.
  destruct CPOST as (MR2 & WF2 & BD2 & LL2 & PA2 & RP2 & VM2 & FRM2 & BK2 & SCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ MR2) as (HH2 & HLZ2 & HMT2).
  destruct FRESH as (F1 & F2 & F3).
  destruct BLKS as (b1 & b2 & BL' & BL).
  assert (NBin : In (s, rn_k pl + 1) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  destruct (blocks_in _ _ _ _ NBin) as (qn & Eqn & Hqn).
  assert (NBP : forall i, 0 <= i < rn_k pl + 1 -> present mem2 (s + i) /\ ~ owned B L' A' (s + i)).
  { intros i Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR2 Hqn Hi) as (H1 & _ & _ & H4).
    rewrite Eqn in H1, H4. split; assumption. }
  assert (DISJ : forall a len, In (a, len) (blocks L A) -> s + (rn_k pl + 1) <= a \/ a + len <= s).
  { intros a len Hin. rewrite BL in Hin. pose proof (mr_blocks_disjoint _ _ LAWS _ _ _ _ MR2) as PW.
    rewrite BL' in PW. exact (pw_mid b1 b2 (s, rn_k pl + 1) (a, len) PW Hin). }
  assert (P8 : getr regs2 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1)).
  { rewrite <- Q8. exact (RP2 8 ltac:(unfold callee_saved; lia)). }
  assert (P9 : getr regs2 9 = Z_to_bv 64 (rn_k pl)).
  { rewrite <- Q9. exact (RP2 9 ltac:(unfold callee_saved; lia)). }
  assert (P2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32)).
  { rewrite <- Q2. exact (RP2 2 ltac:(unfold callee_saved; lia)). }
  assert (NAME : bytes_at rsegs mem2 (p + Z.min (Z.of_nat (length pl)) 1) (bsub pl 1 (rn_k pl))).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - apply length_zero_iff_nil in E0. subst pl. cbn. apply bytes_at_nil. lia.
    - assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
      destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4).
      assert (PAY1 : bytes_at rsegs m1 p pl).
      { apply (bytes_at_pt rsegs mem m1 p pl PAY). intros i Hi.
        mb MU1. }
      assert (PAY2 : bytes_at rsegs mem2 p pl).
      { apply (bytes_at_pt rsegs m1 mem2 p pl PAY1). intros i Hi. rewrite <- SEGS.
        replace (p + i) with (a + (p - a + i)) by lia. apply (KEPT a len (p - a + i) Hin (fun H => H)). lia. }
      replace (p + Z.min (Z.of_nat (length pl)) 1) with (p + 1) by lia.
      apply bytes_at_sub; [exact PAY2 | lia | lia | lia]. }
  assert (NL : Z.of_nat (length (bsub pl 1 (rn_k pl))) = rn_k pl).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - apply length_zero_iff_nil in E0. subst pl. reflexivity.
    - rewrite bsub_length by lia. lia. }
  assert (DJ : p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl <= s \/ s + rn_k pl <= p + Z.min (Z.of_nat (length pl)) 1).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - rewrite (rn_k_nil pl E0). lia.
    - assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
      destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4). pose proof (DISJ a len Hin). lia. }
  assert (STB : stk rsegs mem2 s (s + (rn_k pl + 1))).
  { apply stk_present; [lia | lia |]. intros a Ha. replace a with (s + (a - s)) by lia.
    exact (proj1 (NBP (a - s) ltac:(lia))). }
  destruct (stk_carve rsegs mem2 s (s + (rn_k pl + 1)) 1 STB ltac:(lia)) as [STB1 [j2 C2]].
  replace (s + (rn_k pl + 1) - Z.of_nat 1) with (s + rn_k pl) in STB1, C2 by lia.
  destruct (stk_carve rsegs mem2 s (s + rn_k pl) (Z.to_nat (rn_k pl)) STB1 ltac:(lia)) as [_ [j1 C1]].
  replace (s + rn_k pl - Z.of_nat (Z.to_nat (rn_k pl))) with s in C1 by lia.
  assert (FRMx : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> bv_unsigned (getr regs 2) + -32 <= a ->
                  mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs mem2 a)).
  { intros a Ha Hb.
    assert (N1 : ~ owned B L A a) by (intros Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR1 Ho); lia).
    assert (N2 : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho); lia).
    assert (N3 : ~ scratch_k B ALLOC_STACK R1 a)
      by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
    destruct (FRM2 a (or_introl Ha) N1 N2 N3 (fun H => H)) as [E1 E2].
    rewrite SEGS in E1, E2. split; [exact E1 | apply E2]. }
  assert (FR2 : rw_cells rsegs mem2 (bv_unsigned (getr regs 2) + -32)
                  [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_pt rsegs m1 mem2 _ _ FR1). intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    apply FRMx; lia. }
  assert (CU2 : rw_cells rsegs mem2 c [C8 (Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl));
                  C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))]).
  { pose proof (rw_cells_bound rsegs m1 c _ CU1) as CB. cbn [cells_size csize Nat.add] in CB.
    apply (rw_cells_pt rsegs m1 mem2 _ _ CU1). intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    apply FRMx; lia. }
  assert (ROB : forall i, 0 <= i < rn_k pl + 1 -> ro_addr rsegs (wa (s + i)) = false).
  { intros i Hi. unfold ro_addr. rewrite wa_unsigned by lia.
    rewrite (no_seg B (s + i) SEGS (or_intror (F3 i Hi))). reflexivity. }
  assert (SRCR : p + Z.min (Z.of_nat (length pl)) 1 < 2 ^ 64).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0]; [lia|].
    assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
    destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4). lia. }
  change (YK11.seg_rom rsegs) with (PropExec.seg_rom rsegs).
  eapply evt_SR_canon; [ | exact HH2 | exact HLZ2 | ].
  { apply (tail_canon MEMCPY regs2 mem2 s (rn_k pl) (p + Z.min (Z.of_nat (length pl)) 1)
             (bv_unsigned (getr regs 2) + -32) (bsub pl 1 (rn_k pl)) j1 j2 (getr regs 1) (getr regs 8) (getr regs 9)
             (getr regs 18)); try assumption; lia. }
  intros ms3 (can3 & HQ3 & EQ3).
  destruct HQ3 as (m3 & E3 & T2 & T8 & T9 & T10 & T18 & TR & MU3 & WM3 & RA3 & NM3 & FR3).
  destruct (eqv_mkst _ _ _ _ _ _ E3 EQ3) as [EM3 GE3].
  rewrite EM3. set (R3 := ms_regs ms3) in *. clearbody R3.
  apply SR_ret.
  exists L', A', R3, m3, md2, s.
  split. { rewrite (ret_pc_ok _ HRA). reflexivity. }
  split. { exact RA3. }
  split.
  { unfold guard_kept. intros i Hi.
    assert (GO : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    assert (GO' : owned B L' A' (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR GO) as GL.
    assert (NI : ~ (s <= ms_got_guard B + i < s + rn_k pl + 1)).
    { intros Hr. destruct (NBP (ms_got_guard B + i - s) ltac:(lia)) as [_ Hn].
      replace (s + (ms_got_guard B + i - s)) with (ms_got_guard B + i) in Hn by lia. exact (Hn GO'). }
    rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (ms_got_guard B + i) MU3 ltac:(outs) ltac:(lia))).
    rewrite (GK i Hi).
    mb MU1. }
  split.
  { unfold call_post_k.
    split.
    { apply (mr_frame _ _ LAWS L' A' mem2 m3 md2 md2 MR2).
      - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho) as Hl.
        assert (NI : ~ (s <= a < s + rn_k pl + 1)).
        { intros Hr. destruct (NBP (a - s) ltac:(lia)) as [_ Hn]. replace (s + (a - s)) with a in Hn by lia.
          exact (Hn Ho). }
        mb MU3.
      - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho) as Hl.
        assert (NI : ~ (s <= a < s + rn_k pl + 1)).
        { intros Hr. destruct (NBP (a - s) ltac:(lia)) as [_ Hn]. replace (s + (a - s)) with a in Hn by lia.
          exact (Hn Ho). }
        exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
      - intros q n0 i Hq Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR2 Hq Hi) as ([x Hx] & H1 & H2 & _).
        destruct (Z.ltb_spec (ptr_addr L' q + i) s) as [Lt|Ge].
        + exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
        + destruct (Z.ltb_spec (ptr_addr L' q + i) (s + rn_k pl + 1)) as [Lt2|Ge2].
          * replace (ptr_addr L' q + i) with (s + (ptr_addr L' q + i - s)) by lia.
            apply (present_of_bytes B m3 s _ SEGS NM3).
            { intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply F3. lia. }
            rewrite length_app. cbn [length]. lia.
          * exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
      - reflexivity.
      - exact HH2.
      - exact HLZ2.
      - exact HMT2. }
    split; [exact WF2|]. split; [exact BD2|]. split; [exact LL2|]. split; [exact PA2|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc as [->|[->|[->|[->|Hc]]]].
      - rewrite GE3. etransitivity; [exact T2|].
        replace (bv_unsigned (getr regs 2) + -32 + 32) with (bv_unsigned (getr regs 2)) by lia.
        exact (Z_to_bv_bv_unsigned (getr regs 2)).
      - rewrite GE3. exact T8.
      - rewrite GE3. exact T9.
      - rewrite GE3. exact T18.
      - assert (Hr3 : r = 3 \/ r = 4 \/ 19 <= r <= 27) by lia.
        rewrite GE3, (TR r Hr3), (RP2 r ltac:(unfold callee_saved; lia)). apply QR. lia. }
    split; [exact VM2|].
    split.
    { intros a Ha Ho Ho' Hs He. unfold scratch_k, spZ in Hs. unfold rn_writes in He.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (img_low B a SEGS Ha); lia]).
      assert (AL : YM05.alloc_ceiling <= a \/ a < 140735332483072)
        by (destruct Ha as [Ha|Ha]; [left; lia | right; pose proof (img_low B a SEGS Ha); lia]).
      destruct (munch_byte (ms_segs B) _ _ _ a MU3 ltac:(outs) AR) as [E3a E3b].
      assert (N3 : ~ scratch_k B ALLOC_STACK R1 a)
        by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
      destruct (FRM2 a Ha Ho Ho' N3 (fun H => H)) as [E2a E2b].
      destruct (munch_byte (ms_segs B) _ _ _ a MU1 ltac:(outs) AR) as [E1a E1b].
      split; [rewrite E3a, E2a, E1a; reflexivity | tauto]. }
    split.
    { intros q n0 i Hq Hq' Hi.
      assert (Hb : In (ptr_addr L q, n0) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hq)).
      destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as (_ & B1 & B2 & _).
      pose proof (DISJ _ _ Hb) as D.
      rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (ptr_addr L q + i) MU3 ltac:(outs) ltac:(lia))).
      rewrite (BK2 q n0 i Hq Hq' Hi).
      mb MU1. }
    { intros a Hs. unfold scratch_k, spZ in Hs.
      assert (Hcase : (bv_unsigned (getr regs 2) - 32 <= a < bv_unsigned (getr regs 2)) \/ scratch_k B ALLOC_STACK R1 a)
        by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
      rewrite SEGS. apply WM3.
      destruct Hcase as [Hf|Hk].
      - apply (proj2 (FRMx a ltac:(lia) ltac:(lia))). apply WM1. apply HWS. lia.
      - pose proof (SCR2 a Hk) as W. rewrite SEGS in W. exact W. } }
  split. { rewrite GE3. exact T10. }
  split. { lia. }
  split. { split; [lia | split; [lia | exact F3]]. }
  split. { exists b1, b2. split; assumption. }
  split. { exact NM3. }
  split.
  { destruct CU2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    pose proof (bytes_at_bound rsegs mem2 c _ HB) as CB.
    apply (bytes_at_pt rsegs mem2 m3 c _ HB). intros i Hi.
    mb MU3. }
  split.
  { unfold blocks_kept. intros a len i Hin _ Hi.
    destruct (blocks_in _ _ _ _ Hin) as (q & Eq & Hq).
    destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as (_ & B1 & B2 & _). rewrite Eq in B1, B2.
    pose proof (DISJ _ _ Hin) as D.
    rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (a + i) MU3 ltac:(outs) ltac:(lia))).
    rewrite (KEPT a len i Hin (fun H => H) Hi).
    mb MU1. }
  split; [exact INIT' | exact ROK'].
Qed.

End P.
