(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AFake_iface AFakeK_iface AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition fk_held (P : Prop) : Prop := P.
Lemma fk_held_intro : forall P : Prop, P -> fk_held P. Proof. intros P H. exact H. Qed.
Ltac fk_hold H := apply fk_held_intro in H.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fk_outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof.
  induction l1 as [|[a b] l1 IH]; intros l2 x; cbn [outside app]; [tauto|]. rewrite IH. tauto.
Qed.

(* [comment removed for export] *)
Lemma fk_ablk_lits : forall A B, ablk A B -> (6443008 <= A /\ B <= 2147446784) \/ (17594333495296 <= A /\ B <= ATOP).
Proof. intros A B H. unfold ablk, AIMG_HI, KLS, KHIGH in *. pose proof atop_range. lia. Qed.

(* [comment removed for export] *)
Lemma fk_unp_shadow_zero : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
  m (wa (shad p)) = Some (Z_to_bv 8 0).
Proof.
  intros m X n p (H0 & H1 & H) Hp Hg. rewrite shad_div.
  destruct (H (p / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
    as (b & Hb & Hok).
  rewrite Hb. f_equal. apply (gran_ok_full _ _ Hok). Z.div_mod_to_equations. lia.
Qed.

Lemma fk_byte_of_c1 : forall (m : amem) s b, rw_cells bsegs m s [C1 b] -> 0x625000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.

Lemma fk_mem_eq_single : forall (mp m' : amem) A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> forall x, m' x = write_to_mem mp (wa A) [b] x.
Proof.
  intros mp m' A b HA HB MU Hb x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_bytes_at1 : forall (m : amem) s b, m (wa s) = Some b -> 0x625000 <= s -> s + 1 <= 2^64 -> bytes_at bsegs m s [b].
Proof.
  intros m s b H Hs Hs'. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [| lia]. cbn [nth_error]. rewrite Z.add_0_r.
  rewrite (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fk_sh0_at : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X ->
  bytes_at bsegs m (shad p) [Z_to_bv 8 0].
Proof.
  intros m X n p U Hp Hg HX. pose proof (fk_unp_shadow_zero m X n p U Hp Hg) as H.
  apply fk_bytes_at1; [exact H | rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia |].
  destruct U as (_ & U1 & _). rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Lemma fk_ahull_pres : forall RNG (m m' : amem) X k, wmono bsegs m m' -> ahull RNG m X k -> ahull RNG m' X k.
Proof.
  intros RNG m m' X k WM (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R). exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W | exact WM] | exact R].
Qed.

Section FK.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fk_unp_pres : forall L RNG st LB LB' SP (m m' : amem) X k,
    AHEAP AI L RNG st LB' m' -> (forall b, In b LB -> In b LB') -> aheap_pres CI LB SP m m' ->
    ainblk LB X k -> 0 <= k -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
  Proof.
    intros L RNG st LB LB' SP m m' X k AH HI HP (b & Hb & H1 & H2) Hk U.
    destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
    - (* [comment removed for export] *)
      destruct (AI_block AI _ _ _ _ _ _ _ _ AH (HI _ Hb)) as (N & (BR & B2 & B3 & B4) & RA & RS & SHB & _).
      assert (A8 : A mod 8 = 0) by (clear - B4; Z.div_mod_to_equations; lia).
      pose proof (ablk_lin _ _ BR) as (X1 & X2 & X3 & X4).
      assert (UA : unpoisoned m' A (A + n)) by (apply ablock_unpoisoned; [exact SHB| exact A8| lia| lia| lia]).
      eapply unpoisoned_sub; [exact UA| lia| lia].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec k 0) as [->|Kp].
      { destruct U as (U0 & U1 & _). split; [lia|]. split; [lia|]. intros G HG. lia. }
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (HI _ Hb)) as (Q1 & Q2 & Q3). cbn [ab_addr ab_size] in Q1, Q2, Q3.
      pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX, AIMG_HI in *.
      eapply unpoisoned_agree; [exact U|]. intros s Hs. rewrite !shad_div in Hs.
      set (a' := Z.max X (8 * (s - ASHOFF))).
      assert (Ra : X <= a' < X + k).
      { subst a'. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
      assert (Ea : shad a' = s).
      { subst a'. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
      rewrite <- Ea. eapply (aheap_pres_shadow CI LB SP m m' a' HP).
      + right; right. exists c, A, n. split; [exact Hb | lia].
      + rewrite shad_div. unfold ASHOFF in *. lia.
  Qed.

  Lemma fk_acr_inblk : forall LB T X k, ainblk LB X k -> aclient_range CI LB T X k.
  Proof. intros LB T X k (b & Hb & H1 & H2). right; left. exists b. split; [exact Hb | lia]. Qed.

  Lemma fk_bytes_pres : forall LB SP (m m' : amem) X bs,
    aheap_pres CI LB SP m m' -> ainblk LB X (Z.of_nat (length bs)) -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
  Proof. intros LB SP m m' X bs HP IB B. eapply aheap_pres_bytes_at; [exact HP | exact B | apply fk_acr_inblk; exact IB]. Qed.

  Lemma fk_cells_pres : forall LB SP (m m' : amem) X cs,
    aheap_pres CI LB SP m m' -> ainblk LB X (Z.of_nat (cells_size cs)) -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
  Proof. intros LB SP m m' X cs HP IB C. eapply aheap_pres_rw_cells; [exact HP | exact C | apply fk_acr_inblk; exact IB]. Qed.

  (* [comment removed for export] *)
  Lemma fk_ffr_of_pres : forall LB SP (m m' : amem) W, aheap_pres CI LB SP m m' -> ffr_pres W LB m m'.
  Proof.
    intros LB SP m m' W HP a Ha [((c & A & n & Hb & Hr) & _)|(a' & (c & A & n & Hb & Hr) & ->)]; apply (HP _ Ha).
    - right; right; left. exists (FKB c A n). split; [exact Hb | cbn; lia].
    - right; right; right. exists a'. split; [| reflexivity]. right; right. exists c, A, n. split; [exact Hb | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fk_frame_notin : forall L RNG st LB m b, AHEAP AI L RNG st (b :: LB) m -> ~ In b LB.
  Proof. intros L RNG st LB m b AH. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND as [|x l NI N3]. exact NI. Qed.

  Lemma fk_frame_apart : forall L RNG st LB m c F N, AHEAP AI L RNG st (FKB c F N :: LB) m ->
    forall b, In b LB -> F + N <= ab_addr b \/ ab_addr b + ab_size b <= F.
  Proof.
    intros L RNG st LB m c F N AH b Hb. pose proof (fk_frame_notin _ _ _ _ _ _ AH) as NI.
    assert (NE : FKB c F N <> b) by (intros E; apply NI; rewrite E; exact Hb).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fk_inblk_apart : forall L RNG st LB m c F N X k, AHEAP AI L RNG st (FKB c F N :: LB) m -> ainblk LB X k -> 0 <= k ->
    X + k <= F \/ F + N <= X.
  Proof.
    intros L RNG st LB m c F N X k AH (b & Hb & H1 & H2) Hk. pose proof (fk_frame_apart _ _ _ _ _ _ _ _ AH b Hb). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fk_inblk_ablk : forall LB X k, ablkLB LB -> ainblk LB X k -> 0 <= k -> exists A N, ablk A N /\ A <= X /\ X + k <= N.
  Proof.
    intros LB X k H (b & Hb & H1 & H2) Hk. exists (ab_addr b), (ab_addr b + ab_size b). split; [exact (H b Hb) | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fk_ffr_stack : forall L RNG st LB (m m' : amem) W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => ATOP <= fst iv) W -> ffr_pres [] LB m m'.
  Proof.
    intros L RNG st LB m m' W AH MU WM HW. unfold ffr_pres. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
    intros a [((cls & FA & fn & Hin & Ha) & _)|(a' & (cls & FA & fn & Hin & Ha') & ->)];
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hin) as (B1 & B2 & B3); cbn [ab_addr ab_size] in B1, B2, B3; unfold AIMG_HI in B1.
    - clear MU. induction HW as [|[x y] W Hx HW IH]; cbn [outside]; [exact I|]. cbn [fst] in Hx. split; [clear - Hx Ha B3; lia | exact IH].
    - clear MU. induction HW as [|[x y] W Hx HW IH]; cbn [outside]; [exact I|]. cbn [fst] in Hx. split; [| exact IH].
      rewrite shad_div. unfold ASHOFF. clear - Hx Ha' B1 B3 ATR. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fk_relro_C8 : forall L RNG st LB (m : amem) A v,
    AHEAP AI L RNG st LB m -> ARELRO_LO <= A -> A + 8 <= ARELRO_HI ->
    rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
    rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
  Proof.
    intros L RNG st LB m A v AH HLO HHI HB. pose proof (AI_relro AI L RNG st LB m AH) as R.
    eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | exact HB | unfold ARELRO_LO in *; lia | rewrite length_le8; unfold ARELRO_HI in *; lia ]
      | cbn; split; exact I | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fk_acr_stack : forall LB lo A n, ATOP + 4096 <= lo -> lo <= A -> A + n <= 2^47 -> aclient_range CI LB (ATOP + 4096) A n.
  Proof. intros LB lo A n H1 H2 H3. left; left. lia. Qed.

  Lemma fk_acr_frame : forall LB c F N A n, In (FKB c F N) LB -> F <= A -> A + n <= F + N -> aclient_range CI LB (ATOP + 4096) A n.
  Proof. intros LB c F N A n Hb H1 H2. right; left. exists (FKB c F N). split; [exact Hb | cbn; lia]. Qed.

  (* [comment removed for export] *)
  Lemma fk_acr_fshadow : forall LB c F N A n, In (FKB c F N) LB -> F <= A -> A + 8 * n <= F + N -> A mod 8 = 0 -> 0 <= A ->
    aclient_range CI LB (ATOP + 4096) (shad A) n.
  Proof.
    intros LB c F N A n Hb H1 H2 A8 A0. right; right.
    replace (8 * (shad A - ASHOFF)) with A by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    right; right. exists c, F, N. split; [exact Hb | lia].
  Qed.

  Lemma fk_aheap_eq : forall L RNG st LB (m m' : amem), AHEAP AI L RNG st LB m -> (forall x, m' x = m x) -> AHEAP AI L RNG st LB m'.
  Proof.
    intros L RNG st LB m m' AH E. eapply (AI_frame AI) with (W := []); [exact AH| | | constructor].
    - intros x _. apply E.
    - intros x Hx. unfold wview in *. rewrite E. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma fk_release : forall (fflag : alayout -> Z -> Z -> Z) L RNG st LB (mA mB : amem) c F N,
    fake_release_law AI fflag -> AHEAP AI L RNG st (FKB c F N :: LB) mA ->
    0 <= fflag L c F -> fflag L c F + 1 <= 2^64 -> 0x625000 <= fflag L c F ->
    munch [(fflag L c F, fflag L c F + 1)] mA mB -> rw_cells bsegs mB (fflag L c F) [C1 (Z_to_bv 8 0)] ->
    AHEAP AI L RNG st LB mB.
  Proof.
    intros fflag L RNG st LB mA mB c F N FRL AH G0 G1 G2 MU FLC.
    eapply fk_aheap_eq; [exact (FRL _ _ _ _ _ _ _ _ AH) |].
    apply (fk_mem_eq_single mA mB (fflag L c F) (Z_to_bv 8 0)); [exact G0 | exact G1 | exact MU |].
    apply fk_byte_of_c1; [exact FLC | exact G2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fk_ffr_fin : forall L RNG st LB (m0 m m5 : amem) c F N SHF SHN (Wr Wa : list (Z * Z)),
    AHEAP AI L RNG st (FKB c F N :: LB) m -> ablkLB LB -> ablk F (F + N) -> F mod 8 = 0 -> SHF = shad F -> 8 * SHN <= N -> 0 <= SHN ->
    (* [comment removed for export] *)
    Forall (fun iv => fst iv <= snd iv /\
                      ((ATOP <= fst iv /\ snd iv <= 2^47)
                       \/ ((forall b, In b LB -> snd iv <= ab_addr b \/ ab_addr b + ab_size b <= fst iv)
                           /\ exists A B, ablk A B /\ A <= fst iv /\ snd iv <= B))) Wa ->
    Forall (fun iv => (exists A B, ablk A B /\ A <= fst iv /\ snd iv <= B) /\ fst iv <= snd iv) Wr ->
    ffr_pres [] LB m0 m ->
    munch (Wr ++ Wa ++ [(SHF, SHF + SHN)]) m m5 -> wmono bsegs m m5 ->
    ffr_pres Wr LB m0 m5.
  Proof.
    intros L RNG st LB m0 m m5 c F N SHF SHN Wr Wa AH LBH FBK F8 ESHF SN SN0 HWa HWr FFR MU WM.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof (fk_ablk_lits _ _ FBK) as FBL.
    pose proof (fk_frame_apart _ _ _ _ _ _ _ _ AH) as FAP.
    unfold ffr_pres in *.
    eapply magree_trans; [eapply magree_mono; [exact FFR |]; intros a [(H1 & _)|H2]; [left; split; [exact H1| cbn; exact I] | right; exact H2]|].
    eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
    intros a [((cls & FA & fn & Hin & Ha) & OUT)|(a' & (cls & FA & fn & Hin & Ha') & ->)].
    - (* [comment removed for export] *)
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
      pose proof (FAP _ Hin) as A1. pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A1, A3. pose proof (fk_ablk_lits _ _ A3) as A4.
      rewrite fk_outside_app. split; [exact OUT|]. rewrite fk_outside_app. split.
      + clear MU FFR HWr OUT. induction HWa as [|[x y] Wa [Hle Hxy] HWa IH]; cbn [outside]; [exact I|]. split; [| exact IH].
        cbn [fst snd] in Hxy, Hle. destruct Hxy as [Hx|[Hx _]]; [clear - Hx Ha B3 Hle; lia|]. specialize (Hx _ Hin). cbn [ab_addr ab_size] in Hx. clear - Hx Ha Hle. lia.
      + cbn [outside]. split; [| exact I]. rewrite ESHF, shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha A4 SN SN0 FBL ATR B3. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
      pose proof (FAP _ Hin) as A1. pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A1, A3. pose proof (fk_ablk_lits _ _ A3) as A4.
      assert (APP : forall x y A B, ablk A B -> A <= x -> y <= B -> x <= y -> outside [(x, y)] (shad a')).
      { intros x y A B AB Hx Hy Hxy. cbn [outside]. split; [| exact I]. pose proof (fk_ablk_lits _ _ AB) as ABL. pose proof (ablk_disj_band _ _ AB) as ABD.
        rewrite shad_div. unfold ASHOFF, AIMG_HI, KLS in *. clear - Ha' A4 ABL ABD Hx Hy Hxy ATR B3. Z.div_mod_to_equations. lia. }
      assert (STKA : forall x y, ATOP <= x -> y <= 2^47 -> x <= y -> outside [(x, y)] (shad a')).
      { intros x y Hx Hy Hxy. cbn [outside]. split; [| exact I]. rewrite shad_div. unfold ASHOFF, AIMG_HI in *. clear - Ha' A4 Hx Hy Hxy ATR B3. Z.div_mod_to_equations. lia. }
      rewrite fk_outside_app. split.
      { clear MU FFR HWa. induction HWr as [|[x y] Wr [(A & B & AB & HA & HB) Hle] HWr IH]; [exact I|]. cbn [fst snd] in HA, HB, Hle.
        change ((x, y) :: Wr) with ([(x, y)] ++ Wr). rewrite fk_outside_app. split; [exact (APP x y A B AB HA HB Hle) | exact IH]. }
      rewrite fk_outside_app. split.
      { clear MU FFR HWr. induction HWa as [|[x y] Wa [Hle [[H1 H2]|[_ (A & B & AB & HA & HB)]]] HWa IH]; [exact I| |]; cbn [fst snd] in Hle;
          change ((x, y) :: Wa) with ([(x, y)] ++ Wa); rewrite fk_outside_app; (split; [| exact IH]).
        - cbn [fst snd] in H1, H2. exact (STKA x y H1 H2 Hle).
        - cbn [fst snd] in HA, HB. exact (APP x y A B AB HA HB Hle). }
      cbn [outside]. split; [| exact I]. rewrite ESHF, !shad_div. unfold ASHOFF, AIMG_HI in *.
      clear - Ha' A1 A4 F8 SN SN0 FBL ATR B3. Z.div_mod_to_equations. lia.
  Qed.
End FK.
End CANSEC1.
