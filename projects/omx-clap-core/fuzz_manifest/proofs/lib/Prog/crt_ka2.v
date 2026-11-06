From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem printf_facts_c snprintf_c plain_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_text crt_ka0 crt_snp crt_whole.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition head_regs (s0 s3 s8 s9 s10 s11 : word) (u : list byte) (k : nat) : Prop :=
  s3 = Z_to_bv 64 (bv_unsigned s0 + Z.of_nat k) /\ s8 = Z_to_bv 64 (Z.of_nat k) /\
  s9 = Z_to_bv 64 (Z.of_nat (length u) - Z.of_nat k) /\ s10 = Z_to_bv 64 1 /\ s11 = Z_to_bv 64 62 /\
  (1 <= k < length u)%nat /\ (length u <= 255)%nat /\ 0 < bv_unsigned s0 /\ bv_unsigned s0 + 256 < 2 ^ 64.

Lemma zb_skipn : forall (u : list byte) k, zbytes (skipn k u) = skipn k (zbytes u).
Proof. intros u. unfold zbytes. induction u as [|b u IH]; intros [|k]; cbn; auto. Qed.

Lemma firstn1_skipn : forall (l : list byte) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma byte_at_nth : forall (u : list byte) i, (i < length u)%nat ->
  bv_unsigned (nth i u (Z_to_bv 8 0)) = byte_at (zbytes u) i.
Proof.
  intros u i H. unfold byte_at, zbytes.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact H).
  symmetry. apply map_nth.
Qed.

Lemma head_read : forall m (s3 : word) U u us k, cstr_at m U u us -> (1 <= k < length u)%nat ->
  bv_unsigned s3 = U + Z.of_nat k ->
  ov_read_bytes rsegs m (wa (bv_unsigned s3 + -1)) 1 = Some [nth (k - 1) u (Z_to_bv 8 0)].
Proof.
  intros m s3 U u us k (BU & _ & _) Hk E.
  replace (bv_unsigned s3 + -1) with (U + Z.of_nat (k - 1)) by lia.
  rewrite (bytes_at_read rsegs m U _ (Z.of_nat (k - 1)) 1 BU) by (rewrite ?length_app; cbn [length]; lia).
  rewrite Nat2Z.id. rewrite (firstn1_skipn _ _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma bvne_neg : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b ->
  negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = true.
Proof. intros a b Ha Hb H. rewrite (bveq_ne a b Ha Hb H). reflexivity. Qed.

Lemma bveq_neg : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b ->
  negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = false.
Proof. intros a b Ha Hb H. rewrite (bveq_eq a b Ha Hb H). reflexivity. Qed.

Lemma swrap_k : forall k : nat, (k < 255)%nat -> bv_swrap 32 (Z.of_nat k + 1) = Z.of_nat (S k).
Proof. intros k H. rewrite bv_swrap_small; [lia | change (bv_half_modulus 32) with 2147483648; lia]. Qed.

Lemma cstr_transport : forall W m m' U u us, cstr_at m U u us -> munch W m m' ->
  disjoint_from W U (Z.of_nat (length (u ++ Z_to_bv 8 0 :: us))) -> cstr_at m' U u us.
Proof.
  intros W m m' U u us (B & N & A) MU D. split; [|split; assumption].
  eapply bytes_at_transport; [exact B | exact MU | exact D].
Qed.

Lemma crt_head_plain : plain_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (u us : list byte) (k : nat),
  head_regs s0 s3 s8 s9 s10 s11 u k -> cstr_at m (bv_unsigned s0) u us ->
  byte_at (zbytes u) (k - 1) <> 62 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned s0 + Z.of_nat (length u) + 1 + Z.of_nat (length us) <= lo ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13404) sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (if plain_name (skipn k (zbytes u)) then 1 else 0)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13404) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs)).
Proof.
  intros PL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo u us k
    HR0 CU BN ST LO MI UL.
  pose proof HR0 as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (U3 : bv_unsigned s3 = bv_unsigned s0 + Z.of_nat k) by (rewrite E3; apply unsigned_lit; lia).
  pose proof (head_read m s3 _ u us k CU Hk U3) as HR.
  pose proof (byte_at_nth u (k - 1) ltac:(lia)) as BV.
  assert (R8 : 0 <= bv_unsigned (nth (k - 1) u (Z_to_bv 8 0)) < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 8 (nth (k - 1) u (Z_to_bv 8 0))) as R; unfold bv_modulus in R; cbn in R; lia).
  clear E3 E8 E9 E10.
  subst s11.
  zstep. zstep.
  if_false_by (bveq_ne _ 62 R8 ltac:(lia) ltac:(rewrite BV; exact BN)).
  zstep. zstep.
  eapply evt_cut.
  { eapply PL with (bs := skipn k u) (slack := us) (lo := lo).
    - rewrite U3. apply cstr_sfx; [exact CU | lia].
    - exact MI.
    - exact ST.
    - unfold PLAIN_K. lia.
    - unfold off_stack, PLAIN_K. left. rewrite U3, length_skipn. lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
    E & MU1 & WM1 & MI1 & ST1 & Ra0).
  subst ms' a0'.
  replace (ret_pc (Z_to_bv 64 0x13404)) with (Z_to_bv 64 0x13404) by (apply bv_eq; vm_compute; reflexivity).
  rewrite zb_skipn. unfold PLAIN_K in MU1.
  apply evt_done. do 14 eexists. exists m1. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1 | exact ST1].
Qed.

Lemma crt_gt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (u us j : list byte) (k : nat)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  head_regs s0 s3 s8 s9 s10 s11 u k -> cstr_at m (bv_unsigned s0) u us ->
  byte_at (zbytes u) (k - 1) = 62 ->
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = exit_state xra (bv_unsigned sp) gp tp t0 t1 t2 xs0 xs1 s2 a1 a2 a3 a4 a5 a6 a7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m u us j k
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra (E3 & E8 & E9 & E10 & -> & Hk & Hu & H0 & H256) CU BG FR HI.
  assert (U3 : bv_unsigned s3 = bv_unsigned s0 + Z.of_nat k) by (rewrite E3; apply unsigned_lit; lia).
  pose proof (head_read m s3 _ u us k CU Hk U3) as HR.
  pose proof (byte_at_nth u (k - 1) ltac:(lia)) as BV. rewrite BG in BV.
  clear E3.
  assert (R8 : 0 <= bv_unsigned (nth (k - 1) u (Z_to_bv 8 0)) < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 8 (nth (k - 1) u (Z_to_bv 8 0))) as R; unfold bv_modulus in R; cbn in R; lia).
  zstep. zstep.
  if_true_by (bveq_eq _ 62 R8 ltac:(lia) BV).
  eapply crt_exit; [exact FR | exact HI].
Qed.

Lemma crt_np_next : plain_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (u us : list byte) (k : nat),
  head_regs s0 s3 s8 s9 s10 s11 u k -> cstr_at m (bv_unsigned s0) u us ->
  byte_at (zbytes u) (k - 1) <> 62 -> plain_name (skipn k (zbytes u)) = false -> (k + 1 < length u)%nat ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned s0 + Z.of_nat (length u) + 1 + Z.of_nat (length us) <= lo ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13404) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat (S k))) s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat (S k)))
                    (Z_to_bv 64 (Z.of_nat (length u) - Z.of_nat (S k))) s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x133f4) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs)).
Proof.
  intros PL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo u us k
    HR0 CU BN PN HK ST LO MI UL.
  eapply evt_cut; [eapply crt_head_plain; eauto|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
  rewrite PN. cbv iota.
  destruct HR0 as (-> & -> & -> & -> & -> & Hk & Hu & H0 & H256).
  zstep. if_lit.
  do 4 zstep.
  if_true_by (bvne_neg (Z.of_nat (length u) - Z.of_nat k + -1) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  replace (bv_unsigned s0 + Z.of_nat k + 1) with (bv_unsigned s0 + Z.of_nat (S k)) by lia.
  rewrite (swrap_k k) by lia.
  replace (Z.of_nat (length u) - Z.of_nat k + -1) with (Z.of_nat (length u) - Z.of_nat (S k)) by lia.
  apply evt_done. do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1 | exact MI1].
Qed.

Lemma crt_np_last : plain_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (u us j : list byte) (k : nat)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  head_regs s0 s3 s8 s9 s10 s11 u k -> cstr_at m (bv_unsigned s0) u us ->
  byte_at (zbytes u) (k - 1) <> 62 -> plain_name (skipn k (zbytes u)) = false -> (k + 1 = length u)%nat ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned s0 + Z.of_nat (length u) + 1 + Z.of_nat (length us) <= lo ->
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = exit_state xra (bv_unsigned sp) gp tp t0' t1' t2' xs0 xs1 s2 a1' a2' a3' a4' a5' a6' a7'
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6' F fc m' /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs)).
Proof.
  intros PL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo u us j k
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra HR0 CU BN PN HK ST LO MI UL FR HI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  eapply evt_cut; [eapply crt_head_plain; eauto|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
  rewrite PN. cbv iota.
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra)).
  { eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [right; lia | exact I]. }
  destruct HR0 as (-> & -> & -> & -> & -> & Hk & Hu & H0 & H256).
  zstep. if_lit.
  do 4 zstep.
  if_false_by (bveq_neg (Z.of_nat (length u) - Z.of_nat k + -1) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  eapply evt_mono; [eapply crt_exit; [exact FR1 | exact HI] |].
  intros ms' ->. do 14 eexists. exists m1. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1 | exact MI1].
Qed.

Lemma crt_t1 : plain_contract -> snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte) (k : nat),
  head_regs s0 s3 s8 s9 s10 s11 u k -> s1 = Z_to_bv 64 (3 * Z.of_nat (length u) + 64) -> s2 = Z_to_bv 64 res ->
  s4 = Z_to_bv 64 0x1035d ->
  byte_at (zbytes u) (k - 1) <> 62 -> plain_name (skipn k (zbytes u)) = true ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x13430) sp gp tp t0' t1' t2' s0 s1 s2 s0 a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13c1c) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_t1 (zbytes u) k)) (skipn (length (txt_t1 (zbytes u) k) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs)).
Proof.
  intros PL SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk k HR0 -> -> -> BN PN FRM
    (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt) (CU & U0 & UL & UD).
  pose proof HR0 as (E3 & E8 & _ & _ & _ & Hk & Hu & H0 & H256).
  assert (U3 : bv_unsigned s3 = bv_unsigned s0 + Z.of_nat k) by (rewrite E3; apply unsigned_lit; lia).
  assert (U8 : bv_unsigned s8 = Z.of_nat k) by (rewrite E8; apply unsigned_lit; lia).
  clear E3 E8.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  eapply evt_cut; [eapply crt_head_plain; eauto; lia|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
  rewrite PN. cbv iota.
  assert (CU1 : cstr_at m1 (bv_unsigned s0) u us).
  { eapply cstr_transport; [exact CU | exact MU1 |]. cbn [disjoint_from]. rewrite length_app. cbn [length].
    split; [left; lia | exact I]. }
  assert (BLK1 : rw_cells rsegs m1 res [CB (Z.to_nat (3 * Z.of_nat (length u) + 64)) junk]).
  { eapply rw_cells_transport; [exact BLK | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize].
    split; [left; lia | exact I]. }
  assert (GG1 : bytes_at rsegs m1 GOT_GUARD (le8 (Z_to_bv 64 GUARD))).
  { eapply bytes_at_transport; [exact GG | exact MU1 |]. cbn [disjoint_from]. rewrite length_le8.
    unfold GOT_GUARD. split; [left; lia | exact I]. }
  assert (GC1 : bytes_at rsegs m1 GUARD (le8 canary)).
  { eapply bytes_at_transport; [exact GC | exact MU1 |]. cbn [disjoint_from]. rewrite length_le8.
    unfold GUARD. split; [left; lia | exact I]. }
  assert (FS1 : bytes_at rsegs m1 FMT_T1 (pf_bytes (fmt_t1 ++ [0]))).
  { eapply bytes_at_transport; [exact (proj1 (proj2 (proj2 (proj2 CS)))) | exact MU1 |].
    assert (LF : Z.of_nat (length (pf_bytes (fmt_t1 ++ [0]))) < 1000) by (vm_compute; reflexivity).
    cbn [disjoint_from]. unfold FMT_T1. split; [left; lia | exact I]. }
  assert (TM1 : MemNorm.task_mem rsegs m1).
  { intros a b0 Ha.
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp - 16)) as [L1|L1];
      [|destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp)) as [L2|L2]].
    - rewrite (MU1 a ltac:(cbn [outside]; split; [lia | exact I])) in Ha. exact (TM a b0 Ha).
    - right. lia.
    - rewrite (MU1 a ltac:(cbn [outside]; split; [lia | exact I])) in Ha. exact (TM a b0 Ha). }
  zstep. if_lit.
  do 7 zstep.
  assert (LT : (length (txt_t1 (zbytes u) k) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite len_t1, length_zb by (rewrite length_zb; lia); lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_t1 (zbytes u) k))
    by (apply nz_t1; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_t1) (ps := ps_t1)
        (args := [AInt (Z.of_nat k); APtr (zbytes u); APtr (skipn k (zbytes u))])
        (T := txt_t1 (zbytes u) k) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66397)) with FMT_T1. exact FS1.
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_t1.
    - split; [|split; [|split; [|exact I]]].
      + cbn [pf_arg_ok]. split; [lia | rewrite U8; reflexivity].
      + apply aptr_ok with (sl := us); [exact CU1 | lia | left; lia |].
        rewrite URes, USz. exact UD.
      + rewrite <- zb_skipn. apply aptr_ok with (sl := us).
        * rewrite U3. apply cstr_sfx; [exact CU1 | lia].
        * lia.
        * left. rewrite U3, length_skipn. lia.
        * rewrite URes, USz, U3, length_skipn. lia.
    - exact (text_t1 (zbytes u) k ltac:(rewrite length_zb; lia)).
    - rewrite URes, USz. exact BLK1.
    - rewrite USz. lia.
    - rewrite len_t1, length_zb by (rewrite length_zb; lia). lia.
    - rewrite URes. lia.
    - rewrite URes, USz. left. lia.
    - rewrite URes, USz. exact RI.
    - exact ST1.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - exact S63.
    - exact FRM.
    - exact MI1.
    - exact TM1.
    - exact GG1.
    - exact GC1. }
  intros ms' PO.
  destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & Ft & fc' & m2 &
    E & MU2 & WM2 & MI2 & TMp & FRM2 & _ & _ & BT).
  subst ms'.
  rewrite USz, URes in MU2, BT. rewrite (firstn_all2 _ LT) in MU2, BT.
  replace (ret_pc (Z_to_bv 64 0x13424)) with (Z_to_bv 64 0x13424) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m2 res (pf_bytes (txt_t1 (zbytes u) k)) (skipn (length (txt_t1 (zbytes u) k) + 1) junk)).
  { apply (text_cstr m1 m2 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK1 BT MU2);
      [| exact NZ | rewrite len_t1, length_zb by (rewrite length_zb; lia); lia].
    cbn [disjoint_from]. rewrite len_t1, length_zb by (rewrite length_zb; lia). lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m2. split; [reflexivity|].
  split; [exact FRM2|]. split.
  { apply (munch_trans _ m m1 m2).
    - eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. lia.
    - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in *.
      rewrite len_t1, length_zb by (rewrite length_zb; lia). lia. }
  split; [exact (wmono_trans rsegs m m1 m2 WM1 WM2)|]. split; [exact MI2 | exact TC].
Qed.
