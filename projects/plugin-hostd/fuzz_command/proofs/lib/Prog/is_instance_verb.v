From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem VerbsFacts strcspn_c strncmp_c is_instance_verb_c.
Import ListNotations.
Open Scope Z_scope.

Definition IV_LOOP : Z := 0x17dfc.
Definition IV_TAIL : Z := 0x17e24.
Definition IV_JOIN : Z := 0x17e3c.

Ltac fix_ret :=
  lazymatch goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
  end.

Definition ivs (m0 : word -> option byte) (lo : Z) (sp0 v : word) (tb : list byte) (can : word) : Prop :=
  cstr0_at m0 (bv_unsigned v) tb /\ Z.of_nat (length tb) + 1 < 2^62 /\
  off_lo lo sp0 (bv_unsigned v) (Z.of_nat (length tb + 1)) /\
  bytes_at rsegs m0 DS_STR (map (Z_to_bv 8) [32; 0]) /\ off_lo lo sp0 DS_STR 2 /\
  ssp_at m0 can /\ off_lo lo sp0 SSP_GOT 8 /\ off_lo lo sp0 SSP_GUARD 8 /\
  lo + 160 <= bv_unsigned sp0.

Definition fmts (m0 : word -> option byte) (lo : Z) (sp0 : word) (ps : list Z) (fl : list (list byte)) : Prop :=
  Forall2 (fun p f => exists fs, cstr_at m0 p f fs /\ off_lo lo sp0 p (Z.of_nat (length f + 1 + length fs))) ps fl.

Definition tab_at (m0 : word -> option byte) (lo : Z) (sp0 : word) (A : Z) (ps : list Z) : Prop :=
  bytes_at rsegs m0 A (concat (map (fun p => le8 (Z_to_bv 64 p)) ps)) /\ off_lo lo sp0 A (8 * Z.of_nat (length ps)).

Definition loop_post (sp1 gp tp v kw s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
    (m : word -> option byte) (r : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp1 gp tp t0' t1' t2' v kw (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 IV_JOIN) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp1 - 96, bv_unsigned sp1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp1).

Lemma bytes_win : forall m0 m lo (sp0 : word) a bs,
  bytes_at rsegs m0 a bs -> off_lo lo sp0 a (Z.of_nat (length bs)) -> lo + 160 <= bv_unsigned sp0 ->
  munch [(bv_unsigned sp0 - 160, bv_unsigned sp0)] m0 m -> bytes_at rsegs m a bs.
Proof.
  intros m0 m lo sp0 a bs H O L M. eapply bytes_at_transport; [exact H | exact M |].
  unfold off_lo in O. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma length_concat_le8 : forall ps,
  length (concat (map (fun p : Z => le8 (Z_to_bv 64 p)) ps)) = (8 * length ps)%nat.
Proof.
  induction ps as [|p ps IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, length_le8, IH.
  cbn [length]. lia.
Qed.

Lemma read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

Lemma munch_sub : forall (m m' : word -> option byte) lo hi lo' hi',
  lo' <= lo -> hi <= hi' -> munch [(lo, hi)] m m' -> munch [(lo', hi')] m m'.
Proof.
  intros m m' lo hi lo' hi' L H M. eapply munch_weaken; [|exact M].
  intros x [Hx _]. split; [lia | exact I].
Qed.

Lemma nz_notin : forall l, Forall (fun b : byte => bv_unsigned b <> 0) l -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite Forall_forall in H. apply (H _ Hin). reflexivity. Qed.

Lemma sp_notin : ~ In (Z_to_bv 8 0) [Z_to_bv 8 32].
Proof. intros [H|H]; [|exact H]. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

Lemma sep_notin : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) [32; 9]).
Proof.
  cbn [map]. intros [H|[H|H]]; [| |exact H]; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

Lemma eqb_nat : forall x y : nat, Z.of_nat x < 2^64 -> Z.of_nat y < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.of_nat x)) (Z_to_bv 64 (Z.of_nat y)) = Nat.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia.
  destruct (Nat.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl | apply Z.eqb_neq; lia].
Qed.

Lemma eqb_small : forall w, -256 < w < 256 -> bv_eqb (Z_to_bv 64 w) (Z_to_bv 64 0) = (w =? 0).
Proof.
  intros w Hw. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.eqb_spec w 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. intros C. apply E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_nat0 : forall x : nat, Z.of_nat x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.of_nat x)) (Z_to_bv 64 0) = Nat.eqb x 0.
Proof. intros x Hx. exact (eqb_nat x 0 Hx ltac:(lia)). Qed.

Lemma munch_nil : forall W (m m' : word -> option byte), munch [] m m' -> munch W m m'.
Proof. intros W m m' H. eapply munch_weaken; [|exact H]. intros x _. exact I. Qed.

Lemma iv_loop : strcspn_contract -> strncmp_contract ->
  forall ps fl m0 lo (sp0 v : word) tb can A
    (ra sp1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ivs m0 lo sp0 v tb can -> fmts m0 lo sp0 ps fl -> tab_at m0 lo sp0 A ps -> ps <> [] ->
  bv_unsigned sp1 = bv_unsigned sp0 - 64 ->
  munch [(bv_unsigned sp0 - 160, bv_unsigned sp0)] m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp1) ->
  evt rsegs (loop_post sp1 gp tp v (Z_to_bv 64 (Z.of_nat (length (tfirst tb)))) (Z_to_bv 64 DS_STR)
               s6 s7 s8 s9 s10 s11 F fc lo m (if existsb (verb_is_m tb) fl then 1 else 0))
    (MS (mkR ra sp1 gp tp t0 t1 t2 v (Z_to_bv 64 (Z.of_nat (length (tfirst tb)))) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 DS_STR) s3 (Z_to_bv 64 (Z.of_nat (length ps))) (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IV_LOOP) fc None m (seg_rom rsegs)).
Proof.
  intros CSPN NCMP ps. induction ps as [|p ps IH];
    intros fl m0 lo sp0 v tb can A ra sp1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m HS HF HTA HNE SP1 MU HMI ST; [congruence|].
  destruct fl as [|f fl]; [inversion HF|].
  assert (HPF : exists fs, cstr_at m0 p f fs /\ off_lo lo sp0 p (Z.of_nat (length f + 1 + length fs)))
    by (inversion HF; assumption).
  assert (HFR : fmts m0 lo sp0 ps fl) by (inversion HF; assumption).
  clear HF.
  destruct HPF as (fs & (HFb & HFz & HFp) & OF).
  pose proof HS as (HV & HTL & OV & HDS & ODS & HSSP & OG & OGd & LO).
  destruct HSSP as [HG HGd]. destruct HV as [HVb HVz].
  destruct HTA as [HTb OTb].
  cbn [map concat] in HTb. apply bytes_at_app in HTb. destruct HTb as [HT0 HTr]. rewrite length_le8 in HTr.
  assert (HTR : tab_at m0 lo sp0 (A + 8) ps).
  { split; [exact HTr|]. unfold off_lo in *. cbn [length] in OTb. lia. }
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound rsegs _ _ _ HFb) as BF. rewrite length_app in BF. cbn [length] in BF.
  pose proof (bytes_at_bound rsegs _ _ _ HT0) as BT. rewrite length_le8 in BT.
  assert (MT : bytes_at rsegs m A (le8 (Z_to_bv 64 p))).
  { eapply bytes_win; [exact HT0 | | exact LO | exact MU]. unfold off_lo in *. rewrite length_le8. cbn [length] in OTb. lia. }
  pose proof (read_all _ _ _ MT) as RD. rewrite length_le8 in RD.
  assert (MF : bytes_at rsegs m p (f ++ Z_to_bv 8 0 :: fs)).
  { eapply bytes_win; [exact HFb | | exact LO | exact MU]. unfold off_lo in *. rewrite length_app. cbn [length]. lia. }
  assert (MDS : bytes_at rsegs m DS_STR (map (Z_to_bv 8) [32; 0])).
  { eapply bytes_win; [exact HDS | exact ODS | exact LO | exact MU]. }
  assert (MG : bytes_at rsegs m SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD))).
  { eapply bytes_win; [exact HG | | exact LO | exact MU]. rewrite length_le8. exact OG. }
  assert (MGd : bytes_at rsegs m SSP_GUARD (le8 can)).
  { eapply bytes_win; [exact HGd | | exact LO | exact MU]. rewrite length_le8. exact OGd. }
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  unfold off_lo in OV, ODS, OG, OGd, OF.
  assert (LT : (length (tfirst tb) <= length tb)%nat) by apply upto_length.
  assert (LF : (length (vfirst f) <= length f)%nat) by apply upto_length.
  assert (TAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m3,
    verb_is_m tb f = false ->
    munch [(bv_unsigned sp0 - 160, bv_unsigned sp0)] m0 m3 ->
    munch [(bv_unsigned sp1 - 96, bv_unsigned sp1)] m m3 -> wmono rsegs m m3 -> mem_inv rsegs m3 ->
    stk rsegs m3 lo (bv_unsigned sp1) ->
    evt rsegs (loop_post sp1 gp tp v (Z_to_bv 64 (Z.of_nat (length (tfirst tb)))) (Z_to_bv 64 DS_STR)
                 s6 s7 s8 s9 s10 s11 F fc lo m (if existsb (verb_is_m tb) (f :: fl) then 1 else 0))
      (MS (mkR ra' sp1 gp tp t0' t1' t2' v (Z_to_bv 64 (Z.of_nat (length (tfirst tb)))) a0' a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 DS_STR) (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (length (p :: ps)))) (Z_to_bv 64 A)
               s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 IV_TAIL) fc None m3 (seg_rom rsegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 VF M03 MU3 WM3 MI3 ST3.
    cbn [existsb]. rewrite VF. cbn [orb]. unfold IV_TAIL.
    do 3 zstep.
    replace (Z.of_nat (length (p :: ps)) + -1) with (Z.of_nat (length ps)) by (cbn [length]; lia).
    assert (LPS : Z.of_nat (length ps) < 2^64).
    { pose proof (bytes_at_bound rsegs _ _ _ HTr) as B. rewrite length_concat_le8 in B. lia. }
    rewrite eqb_nat0 by exact LPS.
    destruct ps as [|p' ps']; cbn [length Nat.eqb negb].
    - destruct fl as [|f' fl']; [|inversion HFR]. cbn [existsb].
      do 2 zstep.
      apply evt_done. unfold loop_post. do 19 eexists.
      split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3| exact ST3].
    - eapply evt_mono.
      + eapply IH; [exact HS | exact HFR | exact HTR | discriminate | exact SP1 | exact M03 | exact MI3 | exact ST3].
      + intros ms' PO. unfold loop_post in PO |- *.
        destruct PO as (ra'' & t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s3'' & s4'' &
                        s5'' & t3'' & t4'' & t5'' & t6'' & m4 & E4 & MU4 & WM4 & MI4 & ST4).
        do 19 eexists. split; [exact E4|].
        split; [exact (munch_trans _ _ _ _ MU3 MU4)|]. split; [exact (wmono_trans rsegs _ _ _ WM3 WM4)|].
        split; [exact MI4| exact ST4]. }
  unfold IV_LOOP.
  do 4 zstep.
  eapply evt_cut.
  { eapply CSPN with (str := f) (slack := fs) (set := [Z_to_bv 8 32]) (lo := lo) (can := can).
    - rewrite UP. exact MF.
    - apply nz_notin. exact HFz.
    - intros _. rewrite UP. exact HFp.
    - exact MDS.
    - exact sp_notin.
    - exact MG.
    - exact MGd.
    - exact ST.
    - lia.
    - rewrite UP. lia.
    - cbn [length]. rewrite unsigned_lit by (unfold DS_STR; lia). lia.
    - unfold CSPN_SSP_GOT. unfold SSP_GOT in OG. lia.
    - unfold CSPN_SSP_GUARD. unfold SSP_GUARD in OGd. lia.
    - exact HMI. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & ST2).
  subst ms'. rewrite cspn_vfirst.
  fix_ret.
  assert (M02 : munch [(bv_unsigned sp0 - 160, bv_unsigned sp0)] m0 m2).
  { eapply munch_trans; [exact MU|]. eapply munch_sub; [| | exact MU2]; lia. }
  zstep.
  rewrite eqb_nat by lia.
  destruct (Nat.eqb_spec (length (tfirst tb)) (length (vfirst f))) as [EQ|NE]; cbn [negb].
  - do 4 zstep.
    destruct (strncmp_verb tb f fs HVz HFz EQ) as (w & HW & RW & QW).
    assert (MV2 : bytes_at rsegs m2 (bv_unsigned v) (tb ++ [Z_to_bv 8 0])).
    { eapply bytes_win; [exact HVb | | exact LO | exact M02]. unfold off_lo. rewrite length_app. cbn [length]. lia. }
    assert (MF2 : bytes_at rsegs m2 p (f ++ Z_to_bv 8 0 :: fs)).
    { eapply bytes_win; [exact HFb | | exact LO | exact M02]. unfold off_lo. rewrite length_app. cbn [length]. lia. }
    eapply evt_cut.
    { eapply NCMP with (ls := tb ++ [Z_to_bv 8 0]) (rs := f ++ Z_to_bv 8 0 :: fs) (v := w).
      - exact MV2.
      - rewrite UP. exact MF2.
      - rewrite unsigned_lit by lia. rewrite EQ. exact HW.
      - exact MI2. }
    intros ms' PO. unfold strncmp_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
                    E3 & MU3 & WM3 & MI3 & _ & _).
    subst ms'.
    fix_ret.
    assert (M23 : munch [(bv_unsigned sp1 - 96, bv_unsigned sp1)] m m3).
    { eapply munch_trans; [exact MU2| apply munch_nil; exact MU3]. }
    assert (M03 : munch [(bv_unsigned sp0 - 160, bv_unsigned sp0)] m0 m3).
    { eapply munch_trans; [exact M02| apply munch_nil; exact MU3]. }
    assert (WM23 : wmono rsegs m m3) by exact (wmono_trans rsegs _ _ _ WM2 WM3).
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp1)).
    { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 | exact I]. }
    zstep.
    rewrite eqb_small by exact RW.
    destruct (w =? 0) eqn:W0.
    + zstep.
      cbn [existsb]. rewrite <- QW. cbn [orb].
      apply evt_done. unfold loop_post. do 19 eexists.
      split; [reflexivity|]. split; [exact M23|]. split; [exact WM23|]. split; [exact MI3| exact ST3].
    + eapply TAIL; [rewrite <- QW; reflexivity | exact M03 | exact M23 | exact WM23 | exact MI3 | exact ST3].
  - eapply TAIL; [apply verb_is_m_len_ne; exact NE | exact M02 | exact MU2 | exact WM2 | exact MI2 | exact ST2].
Qed.

Theorem is_instance_verb_holds : strcspn_contract -> strncmp_contract -> is_instance_verb_contract.
Proof.
  intros CSPN NCMP. unfold is_instance_verb_contract, IS_INSTANCE_VERB, IS_INSTANCE_VERB_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo can tb
    HT HTL HTAB HF HDS HDT HSSP OG OGd HMI ST LO OT OTAB ODS ODT.
  assert (HS : ivs m lo sp a0 tb can)
    by exact (conj HT (conj HTL (conj OT (conj HDS (conj ODS (conj HSSP (conj OG (conj OGd LO)))))))).
  assert (HTA : tab_at m lo sp IV_TABLE iv_ptrs) by (split; [exact HTAB | exact OTAB]).
  assert (HDT0 : bytes_at rsegs m DT_STR (map (Z_to_bv 8) [32; 9; 0]) /\ off_lo lo sp DT_STR 3)
    by (split; assumption).
  clear HTAB HDS HDT HTL OT OTAB ODS ODT OG OGd HSSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (proj1 ST) as LO0.
  carve_frame 64%nat ST.
  do 8 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  do 5 zstep.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; lia).
  assert (MUw : munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m1).
  { eapply munch_sub; [| | exact MU]; lia. }
  pose proof HS as ((HTb & HTz) & HTL & OV & HDS & ODS & (HG & HGd) & OG & OGd & _).
  destruct HDT0 as [HDT ODT].
  assert (MV1 : bytes_at rsegs m1 (bv_unsigned a0) (tb ++ [Z_to_bv 8 0])).
  { eapply bytes_win; [exact HTb | | exact LO | exact MUw]. unfold off_lo in *. rewrite length_app. cbn [length]. lia. }
  assert (MDT : bytes_at rsegs m1 DT_STR (map (Z_to_bv 8) [32; 9; 0])).
  { eapply bytes_win; [exact HDT | exact ODT | exact LO | exact MUw]. }
  assert (MG : bytes_at rsegs m1 SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD))).
  { eapply bytes_win; [exact HG | | exact LO | exact MUw]. rewrite length_le8. exact OG. }
  assert (MGd : bytes_at rsegs m1 SSP_GUARD (le8 can)).
  { eapply bytes_win; [exact HGd | | exact LO | exact MUw]. rewrite length_le8. exact OGd. }
  unfold off_lo in OV, ODT, OG, OGd.
  eapply evt_cut.
  { eapply CSPN with (str := tb) (slack := []) (set := map (Z_to_bv 8) [32; 9]) (lo := lo) (can := can).
    - exact MV1.
    - apply nz_notin. exact HTz.
    - intros H. cbn [length map] in H. lia.
    - exact MDT.
    - exact sep_notin.
    - exact MG.
    - exact MGd.
    - rewrite SPU. exact ST.
    - rewrite SPU. lia.
    - rewrite SPU. cbn [length]. lia.
    - rewrite SPU. cbn [length map]. rewrite unsigned_lit by lia. unfold DT_STR in ODT. lia.
    - rewrite SPU. unfold CSPN_SSP_GOT. unfold SSP_GOT in OG. lia.
    - rewrite SPU. unfold CSPN_SSP_GUARD. unfold SSP_GUARD in OGd. lia.
    - exact HMI. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & ST2).
  subst ms'. rewrite cspn_tfirst.
  fix_ret.
  rewrite SPU in MU2, ST2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) [CB 8
         (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
       C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn; lia]. }
  clear FR.
  assert (M02 : munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MUw|]. eapply munch_sub; [| | exact MU2]; lia. }
  do 6 zstep.
  eapply evt_cut.
  { eapply (iv_loop CSPN NCMP iv_ptrs instance_verb_formats m lo sp a0 tb can IV_TABLE).
    - exact HS.
    - exact HF.
    - exact HTA.
    - discriminate.
    - rewrite SPU. lia.
    - exact M02.
    - exact MI2.
    - rewrite SPU. exact ST2. }
  intros ms' PO. unfold loop_post in PO.
  destruct PO as (ra' & t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s3' & s4' & s5' &
                  t3'' & t4'' & t5'' & t6'' & m3 & E3 & MU3 & WM3 & MI3 & ST3).
  subst ms'. unfold IV_JOIN.
  rewrite SPU in MU3, ST3.
  assert (FR : rw_cells rsegs m3 (bv_unsigned sp + -64) [CB 8
         (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
       C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 | cbn; lia]. }
  clear FR2.
  assert (MUF : munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m3).
  { eapply munch_trans; [exact M02|]. eapply munch_sub; [| | exact MU3]; lia. }
  pose proof (wmono_trans rsegs _ _ _ (wmono_trans rsegs _ _ _ WM WM2) WM3) as WMF.
  clear MU MUw M02 MU2 MU3 WM WM2 WM3.
  do 8 zstep.
  release_frame FR ST3 (bv_unsigned sp).
  zstep.
  finish.
  reflexivity.
Qed.
