From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec strlen_c bcmp_c check_as_written_body.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Open Scope Z_scope.

Lemma cw_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cw_rel_shape : forall s R F pc fc m0 ro, ms_rel rsegs s (MS R F pc fc None m0 ro) ->
  s = MS R F pc fc None (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma cw_ro_agree_hi : forall m m' lo hi, ro_agree rsegs m -> munch [(lo, hi)] m m' -> 0x55000 <= lo ->
  ro_agree rsegs m'.
Proof.
  intros m m' lo hi RA MU Hlo a Ha. unfold mrd. rewrite (MU a); [exact (RA a Ha)|].
  cbn [outside]. split; [|exact I]. intros [H1 H2]. unfold ro_addr in Ha.
  rewrite (HsKindB.find_segment_above rsegs 0x55000 (bv_unsigned a) 1 HsKindB.rsegs_top) in Ha by lia.
  discriminate.
Qed.

Lemma cw_bytes_eq : forall m m' a bs, (forall x, m' x = m x) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs E (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold mrd. rewrite E. exact (H i Hi).
Qed.

Lemma cw_wr_eq : forall m m' a n, (forall x, m' x = m x) -> wr_at rsegs m a n -> wr_at rsegs m' a n.
Proof.
  intros m m' a n E (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold wview. rewrite E. exact (H i Hi).
Qed.

Lemma cw_rw_eq : forall m m' a cs, (forall x, m' x = m x) -> rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs E [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (cw_bytes_eq m m' a _ E Hb)] | exact (cw_wr_eq m m' a _ E Hw)].
Qed.

Lemma cw_munch_eq : forall W m m0 m1, munch W m m0 -> (forall x, m1 x = m0 x) -> munch W m m1.
Proof. intros W m m0 m1 H E x Hx. rewrite E. exact (H x Hx). Qed.

Lemma cw_wmono_eq : forall m m0 m1, wmono rsegs m m0 -> (forall x, m1 x = m0 x) -> wmono rsegs m m1.
Proof. intros m m0 m1 H E x Hx. unfold wview. rewrite E. exact (H x Hx). Qed.

Lemma cw_ro_agree_eq : forall m m', (forall x, m' x = m x) -> ro_agree rsegs m -> ro_agree rsegs m'.
Proof. intros m m' E RA a Ha. unfold mrd. rewrite E. exact (RA a Ha). Qed.

Lemma strlen_ev : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (Q : machine_state -> Prop),
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  ro_agree rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     (forall x, m' x = m x) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    str slack Q BA NZ SLK RA K.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_cut.
  { apply (evt_normalize rsegs); [exact cw_wx | exact RA |].
    apply SL; [exact (bytes_at_normalize rsegs m _ _ RA BA) | exact NZ | exact SLK | apply mem_inv_normalize]. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m0 & E & MU & _) &
    REL & ROS).
  subst s0'.
  destruct (cw_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  rewrite Es. apply K.
  apply (mem_unchanged_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS).
  intros x. apply MU. exact I.
Qed.

Lemma bcmp_ev : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z) (Q : machine_state -> Prop),
  bytes_at rsegs m (bv_unsigned a0) ls -> bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  ro_agree rsegs m ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     (forall x, m' x = m x) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ls rs v Q BL BR MC RA K.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_cut.
  { apply (evt_normalize rsegs); [exact cw_wx | exact RA |].
    apply BC; [exact (bytes_at_normalize rsegs m _ _ RA BL) | exact (bytes_at_normalize rsegs m _ _ RA BR) |
      exact MC | apply mem_inv_normalize]. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m0 & E & MU & _) &
    REL & ROS).
  subst s0'.
  destruct (cw_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  rewrite Es. apply K.
  apply (mem_unchanged_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS).
  intros x. apply MU. exact I.
Qed.

Lemma run1 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb slack : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x55000 <= lo ->
  bytes_at rsegs m (bv_unsigned a0) (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (bv_unsigned a0 + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
  bv_unsigned a0 + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) <= lo ->
  Z.of_nat (length tb) < 2 ^ 62 ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' junk,
      ms' = MS (mkR (Z_to_bv 64 0x13628) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' a2 a1
                    (Z_to_bv 64 (Z.of_nat (length tb) / 4 * 3 + 3)) a1' a2' a3' a4' a5' a6' a7'
                    s2 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x16594) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135ec) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo tb slack ST LO HL TX NZ SLK DJ NB RA.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ TX) as TB. rewrite length_app in TB. cbn [length] in TB.
  carve_frame 48%nat ST.
  do 10 zstep.
  apply (strlen_ev SL (Z_to_bv 64 0x13614) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a2 a1 a0 a1 a2 a3 a4
    a5 a6 a7 s2 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 tb slack); [exact TX | exact NZ | exact SLK | |].
  { apply (cw_ro_agree_hi m m0 _ _ RA MU). lia. }
  intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m1 EQ.
  replace (ret_pc (Z_to_bv 64 0x13614)) with (Z_to_bv 64 0x13614) by (apply bv_eq; vm_compute; reflexivity).
  do 5 zstep.
  replace (Z.shiftl (Z.shiftr (Z.of_nat (length tb)) 2) 1 + Z.shiftr (Z.of_nat (length tb)) 2 + 3)
    with (Z.of_nat (length tb) / 4 * 3 + 3)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 2) with 4; change (2 ^ 1) with 2; lia).
  apply evt_done. do 14 eexists. exists m1. eexists. split; [reflexivity|].
  split; [exact (cw_rw_eq m0 m1 _ _ EQ FR)|].
  split; [exact (cw_munch_eq _ m m0 m1 MU EQ)|].
  exact (cw_wmono_eq m m0 m1 WM EQ).
Qed.

Lemma run2 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (w : Z) (tb slack : list byte),
  0 < w < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned s3) (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
  (- (bv_unsigned s3 + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
  Z.of_nat (length tb) < 2 ^ 62 ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13644) sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (Z.max (Z.of_nat (length tb)) 1)) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 w) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x16594) fc None m' (seg_rom rsegs) /\
      (forall x, m' x = m x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13628) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w tb slack Hw TX NZ SLK NB RA.
  zstep.
  assert (B0 : bv_eqb (Z_to_bv 64 w) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite B0; cbv iota.
  do 3 zstep.
  apply (strlen_ev SL (Z_to_bv 64 0x13638) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) s3
    s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tb slack); [exact TX | exact NZ | exact SLK | exact RA |].
  intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m1 EQ.
  replace (ret_pc (Z_to_bv 64 0x13638)) with (Z_to_bv 64 0x13638) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  replace (Z.of_nat (length tb) + Z.b2z (Z.of_nat (length tb) <? 1)) with (Z.max (Z.of_nat (length tb)) 1)
    by (destruct (Z.ltb_spec (Z.of_nat (length tb)) 1); cbn [Z.b2z]; lia).
  apply evt_done. do 14 eexists. exists m1. split; [reflexivity | exact EQ].
Qed.

Lemma run3 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t want six n : Z) (tb junkw junks : list byte),
  Z.of_nat (length tb) = n -> n < 2 ^ 31 -> 0 < six < 2 ^ 64 ->
  ~ In (Z_to_bv 8 0) tb ->
  bytes_at rsegs m t (tb ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m want [CB (Z.to_nat (n / 4 * 3 + 3)) junkw] ->
  rw_cells rsegs m six [CB (Z.to_nat (Z.max n 1)) junks] ->
  (six + Z.max n 1 <= want \/ want + (n / 4 * 3 + 3) <= six) ->
  (six + Z.max n 1 <= t \/ t + n + 1 <= six) ->
  (want + (n / 4 * 3 + 3) <= t \/ t + n + 1 <= want) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x13824) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 six) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 want) r s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x16454) fc None m' (seg_rom rsegs) /\
      munch [(six, six + Z.max n 1); (want, want + (n / 4 * 3 + 3))] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' t (tb ++ [Z_to_bv 8 0]) /\
      match b64_dec (map (fun b : byte => bv_unsigned b) tb) with
      | Some bs => r = Z_to_bv 64 (Z.of_nat (length bs)) /\ bytes_at rsegs m' want (map (Z_to_bv 8) bs)
      | None => r = Z_to_bv 64 (2 ^ 64 - 1)
      end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 six) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 want) (Z_to_bv 64 t)
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13644) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t want six n
    tb junkw junks HN HN31 Hsix NZ TX WN SX D1 D2 D3.
  zstep.
  assert (B0 : bv_eqb (Z_to_bv 64 six) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite B0; cbv iota.
  assert (NZ' : Forall (fun b : byte => bv_unsigned b <> 0) tb).
  { apply Forall_forall. intros b Hb E. apply NZ. replace b with (Z_to_bv 8 0) in Hb; [exact Hb|].
    apply bv_eq. rewrite E. reflexivity. }
  eapply evt_cut.
  { exact (asw_body ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      t want six n tb junkw junks m HN HN31 NZ' TX WN SX D1 D2 D3). }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & r & m' & -> & MU & WM & TX' & RS).
  zstep.
  apply evt_done. do 15 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact TX' | exact RS].
Qed.

Lemma memcmp_self : forall l, memcmp_model l l (length l) = Some 0.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite Z.eqb_refl. exact IH. Qed.

Lemma run4 : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l bd w : Z) (junk : list byte)
    (xra xs0 xs1 xs2 xs3 : word),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  0 <= l < 2 ^ 64 -> 0 <= bd < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  ((bd = 0 /\ r = Z_to_bv 64 (2 ^ 64 - 1)) \/
   (exists bs, bd <> 0 /\ l = Z.of_nat (length bs) /\ l < 2 ^ 64 - 1 /\ r = Z_to_bv 64 l /\
      bytes_at rsegs m bd (map (Z_to_bv 8) bs) /\ bytes_at rsegs m w (map (Z_to_bv 8) bs))) ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' xs0 xs1 (Z_to_bv 64 w)
                    a1' a2' a3' a4' a5' a6' a7' xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x16454) fc None m' (seg_rom rsegs) /\
      (forall x, m' x = m x))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 bd) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) r
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13824) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l bd w junk
    xra xs0 xs1 xs2 xs3 FR Hl Hbd Hw CASE RA.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  destruct CASE as [(-> & ->) | (bs & Hbd0 & El & Hl1 & -> & BD & BW)].
  - do 3 zstep.
    if_false.
    zstep.
    if_true.
    do 8 zstep.
    apply evt_done. do 14 eexists. exists m. split; [reflexivity | intros x; reflexivity].
  - do 3 zstep.
    rewrite (proj2 (Z.ltb_ge bd 1)) by lia. rewrite (proj2 (Z.ltb_lt l 18446744073709551615)) by lia.
    cbn [Z.b2z]. if_false.
    zstep.
    assert (B1 : bv_eqb (Z_to_bv 64 bd) (Z_to_bv 64 0) = false)
      by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    rewrite B1; cbv iota.
    zstep.
    rewrite bv_eqb_refl. change (negb true) with false. cbv iota.
    zstep.
    destruct (Z.eq_dec l 0) as [L0|L0].
    + assert (B2 : bv_eqb (Z_to_bv 64 l) (Z_to_bv 64 0) = true) by (rewrite L0; reflexivity).
      rewrite B2; cbv iota.
      do 8 zstep.
      apply evt_done. do 14 eexists. exists m. split; [reflexivity | intros x; reflexivity].
    + assert (B2 : bv_eqb (Z_to_bv 64 l) (Z_to_bv 64 0) = false)
        by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
      rewrite B2; cbv iota.
      do 4 zstep.
      apply (bcmp_ev BC (Z_to_bv 64 0x1384c) sp gp tp t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 bd) (Z_to_bv 64 bd)
        (Z_to_bv 64 w) (Z_to_bv 64 l) a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 l) s4 s5 s6 s7 s8 s9 s10 s11
        t3 t4 t5 t6 F fc m (map (Z_to_bv 8) bs) (map (Z_to_bv 8) bs) 0).
      * rewrite unsigned_lit by lia. exact BD.
      * rewrite unsigned_lit by lia. exact BW.
      * rewrite unsigned_lit by lia. rewrite El, Nat2Z.id, <- (length_map (Z_to_bv 8) bs). apply memcmp_self.
      * exact RA.
      * intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m1 EQ.
        replace (ret_pc (Z_to_bv 64 0x1384c)) with (Z_to_bv 64 0x1384c) by (apply bv_eq; vm_compute; reflexivity).
        zstep.
        if_false.
        pose proof (cw_rw_eq m m1 _ _ EQ FR) as FR1. clear FR.
        do 8 zstep.
        apply evt_done. do 14 eexists. exists m1. split; [reflexivity | exact EQ].
Qed.
