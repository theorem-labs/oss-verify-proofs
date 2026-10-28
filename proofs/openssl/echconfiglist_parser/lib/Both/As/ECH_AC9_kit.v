(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk AsConst AsIface AsIfaceX AsCXXHeap AsCall ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outside_app : forall (A B : list (Z * Z)) x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[l h] A IH]; intros B x; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma sub_fp_app_r : forall A B : list (Z * Z), sub_fp B (A ++ B).
Proof. intros A B x Hx. apply outside_app in Hx. tauto. Qed.
Lemma sub_fp_app_l : forall A B : list (Z * Z), sub_fp A (A ++ B).
Proof. intros A B x Hx. apply outside_app in Hx. tauto. Qed.
Lemma sub_fp_app_mid : forall A B C : list (Z * Z), sub_fp B C -> sub_fp (A ++ B) (A ++ C).
Proof. intros A B C S x Hx. apply outside_app in Hx. apply outside_app. destruct Hx as [H1 H2]. split; [exact H1| apply S, H2]. Qed.
Lemma sub_fp_trans : forall A B C : list (Z * Z), sub_fp A B -> sub_fp B C -> sub_fp A C.
Proof. intros A B C S1 S2 x Hx. apply S1, S2, Hx. Qed.
Lemma sub_fp_refl : forall A : list (Z * Z), sub_fp A A.
Proof. intros A x Hx. exact Hx. Qed.
(* [comment removed for export] *)
Lemma munch_join : forall (A B C : list (Z * Z)) m0 m1 m2,
  munch A m0 m1 -> munch B m1 m2 -> sub_fp A C -> sub_fp B C -> munch C m0 m2.
Proof. intros A B C m0 m1 m2 M1 M2 S1 S2. eapply munch_trans; [eapply munch_weaken; [exact S1| exact M1]| eapply munch_weaken; [exact S2| exact M2]]. Qed.
Lemma outside_Forall : forall (P : Z * Z -> Prop) W x,
  Forall P W -> (forall iv, P iv -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  intros P W x FA HP. induction W as [|[l h] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FA)].
  exact (HP _ (Forall_inv FA)).
Qed.
Lemma disjoint_from_Forall : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall iv, P iv -> a + n <= fst iv \/ snd iv <= a) -> disjoint_from W a n.
Proof.
  intros P W a n FA HP. induction W as [|[l h] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FA)].
  exact (HP _ (Forall_inv FA)).
Qed.
Lemma disjoint_from_app : forall (A B : list (Z * Z)) a n, disjoint_from (A ++ B) a n <-> disjoint_from A a n /\ disjoint_from B a n.
Proof. induction A as [|[l h] A IH]; intros B a n; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma disjoint_from_callee : forall (l h : Z) (XS W : list (Z * Z)) A n,
  (A + n <= l \/ h <= A) -> disjoint_from XS A n -> disjoint_from W A n -> disjoint_from ((l, h) :: XS ++ W) A n.
Proof. intros l h XS W A n H1 H2 H3. cbn. split; [exact H1|]. apply disjoint_from_app. split; assumption. Qed.

(* [comment removed for export] *)
Definition covered (lohi : Z * Z) (W : list (Z * Z)) (w : Z * Z) : Prop :=
  (fst lohi <= fst w /\ snd w <= snd lohi) \/ Exists (fun v => fst v <= fst w /\ snd w <= snd v) W.
Lemma outside_inside_pt : forall (W : list (Z * Z)) x w,
  Exists (fun v => fst v <= fst w /\ snd w <= snd v) W -> outside W x -> ~ (fst w <= x < snd w).
Proof.
  intros W x w EX OUT. induction W as [|[l h] W IH]; [inversion EX|]. cbn in OUT. destruct OUT as [O1 O2].
  inversion EX; subst; [cbn in *; lia| exact (IH ltac:(assumption) O2)].
Qed.
Lemma sub_fp_covered : forall lohi (XS W Wc : list (Z * Z)),
  Forall (covered lohi W) Wc -> sub_fp Wc (lohi :: XS ++ W).
Proof.
  intros [lo hi] XS W Wc FA x Hx. cbn in Hx. destruct Hx as [H0 Hx]. apply outside_app in Hx. destruct Hx as [_ HW].
  induction Wc as [|[l h] Wc IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FA)].
  pose proof (Forall_inv FA) as C. unfold covered in C. cbn in C. destruct C as [C|C]; [lia|].
  exact (outside_inside_pt W x (l, h) C HW).
Qed.
(* [comment removed for export] *)
Lemma sub_fp_callee : forall lo hi hi' (XSc XS W Wc : list (Z * Z)),
  hi' <= hi -> Forall (covered (lo, hi) W) Wc -> sub_fp ((lo, hi') :: XSc ++ Wc) ((lo, hi) :: (XSc ++ XS) ++ W).
Proof.
  intros lo hi hi' XSc XS W Wc LE FA x Hx. cbn in Hx |- *. destruct Hx as [H0 Hx]. split; [lia|].
  rewrite <- app_assoc in Hx. apply outside_app in Hx. destruct Hx as [H1 Hx]. apply outside_app. split; [exact H1|].
  apply (sub_fp_covered (lo, hi) XS W Wc FA). cbn. split; [exact H0| exact Hx].
Qed.
(* [comment removed for export] *)
Lemma sub_fp_grow : forall lohi (XSc XS W : list (Z * Z)), sub_fp (lohi :: XS ++ W) (lohi :: (XSc ++ XS) ++ W).
Proof.
  intros [lo hi] XSc XS W x Hx. cbn in Hx |- *. destruct Hx as [H0 Hx]. split; [exact H0|].
  rewrite <- app_assoc in Hx. apply outside_app in Hx. tauto.
Qed.

Lemma Forall_app_scratch : forall {A} (P : A -> Prop) (XSc XS : list A), Forall P XSc -> Forall P XS -> Forall P (XSc ++ XS).
Proof. intros A P XSc XS F1 F2. apply Forall_app. split; assumption. Qed.

Lemma land_ones64k : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mset (M : membio) (pos fl nr : Z) : membio :=
  mkMB (mb_buf M) (mb_len M) pos fl (mb_numf M) nr (mb_next M) (mb_prev M) (mb_bb M) (mb_bm M) (mb_rp M)
       (mb_id M) (mb_bbid M) (mb_bmid M) (mb_rpid M).
Lemma mb_after_read_mset : forall M pos fl nr n,
  mb_after_read (mset M pos fl nr) n = mset M (pos + n) (Z.land fl (Z.lnot BIO_FLAGS_RETRY_MASK)) (nr + n).
Proof. intros. reflexivity. Qed.
Lemma mset_self : forall M, mset M (mb_pos M) (mb_flags M) (mb_nread M) = M.
Proof. intros M. destruct M. reflexivity. Qed.
Lemma rw_cells_CB_bytes_at : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs /\ length bs = n.
Proof.
  intros segs m A n bs [[WF B] W]. cbn in WF. destruct WF as [L _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. split; assumption.
Qed.

(* [comment removed for export] *)
Section HC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Definition appwin (iv : Z * Z) : Prop := snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv.

  Lemma outside_sh_of_scratch : forall LF O n m XS x,
    as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> Forall (fs_scratch H LF) XS ->
    O <= x < O + n -> outside XS (sh x).
  Proof.
    intros LF O n m XS x R OB HO Hn HT FX Hx.
    eapply outside_Forall; [exact FX|]. intros iv Hiv.
    assert (OB1 : fsobj H LF x 1) by (eapply fsobj_sub; [exact OB| lia| lia]).
    pose proof (fsobj_scratch_sh H HH _ _ _ _ _ R OB1 ltac:(lia) ltac:(lia) ltac:(lia) Hiv) as D.
    change (nsh 1) with 1 in D. lia.
  Qed.

  Lemma outside_sh_of_appwin : forall W x, 0 <= x -> x < AAPP_HI -> Forall appwin W -> outside W (sh x).
  Proof.
    intros W x H0 H1 FW. eapply outside_Forall; [exact FW|]. intros [l h] Hiv. unfold appwin in Hiv. cbn in Hiv |- *.
    assert (SX : ASHADOW_BASE <= sh x < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)) as K. unfold nsh in K. change ((1 + 7) / 8) with 1 in K. lia. }
    lia.
  Qed.

  Lemma accessible_across3 : forall LF O n m m' lo hi XS W',
    accessible m O n -> as_RFS H LF m -> fsobj H LF O n -> 0 <= n ->
    munch ((lo, hi) :: XS ++ W') m m' -> aceil <= lo -> Forall (fs_scratch H LF) XS -> Forall appwin W' ->
    accessible m' O n.
  Proof.
    intros LF O n m m' lo hi XS W' ACC R OB Hn MU CE FX FW. pose proof ACC as (A0 & A1 & _).
    eapply accessible_transport; [exact ACC| exact MU|]. intros x Hx. cbn. split.
    - pose proof aceil_range as CR. pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)) as K. unfold nsh in K. change ((1 + 7) / 8) with 1 in K.
      unfold AHI_LO in *. lia.
    - apply outside_app. split; [eapply outside_sh_of_scratch; eauto; lia| apply outside_sh_of_appwin; [lia| lia| exact FW]].
  Qed.

  Lemma disjoint_sh_of_scratch : forall LF O n m XS,
    as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> Forall (fs_scratch H LF) XS ->
    disjoint_from XS (sh O) (nsh n).
  Proof.
    intros LF O n m XS R OB HO Hn HT FX. eapply disjoint_from_Forall; [exact FX|]. intros iv Hiv.
    exact (fsobj_scratch_sh H HH _ _ _ _ _ R OB HO Hn HT Hiv).
  Qed.
  Lemma disjoint_of_scratch : forall LF O n m XS,
    as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n -> Forall (fs_scratch H LF) XS ->
    disjoint_from XS O n.
  Proof.
    intros LF O n m XS R OB HO Hn HT AP FX. eapply disjoint_from_Forall; [exact FX|]. intros iv Hiv.
    exact (fsobj_scratch H HH _ _ _ _ _ R OB HO Hn HT AP Hiv).
  Qed.
  (* [comment removed for export] *)
  Lemma disjoint_of_scratch_inapp : forall LF O n m XS,
    as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> in_app_mem O (O + n) -> Forall (fs_scratch H LF) XS ->
    disjoint_from XS O n.
  Proof.
    intros LF O n m XS R OB HO Hn HT IA FX. eapply disjoint_from_Forall; [exact FX|]. intros iv [->|(k & ff & fp & FF & E)].
    - cbn. destruct OB as [OB|(f & IN & D1 & D2)]; [unfold AFS_FLAGS, AFS_SIZE in *; lia|].
      pose proof (proj2 (ah_RFS_range H HH _ _ R) f IN) as (K' & Q1 & Q2 & Q3 & Q4). unfold AFS_FLAGS, AFS_HDR in *. lia.
    - pose proof (fsobj_windows H HH _ _ _ _ _ _ _ R OB FF HO Hn HT) as (D1 & D2 & D3 & D4).
      destruct E as [-> |[-> | ->]]; cbn; [lia| lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & _).
      pose proof (fsz_pos k ltac:(lia)).
      unfold AIMG_TOP, AFS_HDR in R1.
      assert (S1 : ASHADOW_BASE <= sh ff) by (unfold sh; Z.div_mod_to_equations; lia).
      assert (S2 : sh ff + fshn k <= AHI_LO).
      { rewrite fshn_nsh by lia. apply sh_nsh_high; [lia| lia|]. pose proof aceil_range. unfold AAPP_HI in *. lia. }
      unfold in_app_mem in IA. lia.
  Qed.
  Lemma disjoint_sh_of_appwin : forall W O n, 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> Forall appwin W -> disjoint_from W (sh O) (nsh n).
  Proof.
    intros W O n HO Hn HT FW. eapply disjoint_from_Forall; [exact FW|]. intros [l h] Hiv. unfold appwin in Hiv. cbn in Hiv |- *.
    assert (S1 : ASHADOW_BASE <= sh O) by (unfold sh; Z.div_mod_to_equations; lia).
    pose proof (sh_nsh_high O n HO Hn HT) as S2. lia.
  Qed.

  Lemma addressable_across3 : forall LF O n m m' lo hi XS W',
    addressable m O n -> as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> O + n <= AAPP_HI ->
    munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> aceil <= lo -> Forall (fs_scratch H LF) XS -> Forall appwin W' ->
    addressable m' O n.
  Proof.
    intros LF O n m m' lo hi XS W' AD R OB HO HT MU WM CE FX FW. pose proof AD as [Hn _].
    eapply addressable_transport; [exact AD| exact MU| exact WM|]. cbn. split.
    - pose proof aceil_range as CR. pose proof (sh_nsh_high O n HO Hn HT) as K. unfold AHI_LO in *. lia.
    - apply disjoint_from_app. split; [eapply disjoint_sh_of_scratch; eauto| apply disjoint_sh_of_appwin; auto].
  Qed.

  Lemma shvis_across3 : forall LF O n m m' lo hi XS W',
    shvis m O (O + n) -> as_RFS H LF m -> fsobj H LF O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI ->
    munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> aceil <= lo -> Forall (fs_scratch H LF) XS -> Forall appwin W' ->
    shvis m' O (O + n).
  Proof.
    intros LF O n m m' lo hi XS W' SV R OB HO Hn HT MU WM CE FX FW.
    pose proof (hull_lo_le O HO) as (A1 & A2 & A3). pose proof (hull_hi_ge (O + n) ltac:(lia)) as (B1 & B2 & B3).
    assert (HH2 : hull_hi (O + n) <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo O)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi (O + n)) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    eapply shvis_transport; [exact SV| exact MU| exact WM|]. cbn. split.
    - pose proof aceil_range as CR. unfold AHI_LO in *. lia.
    - apply disjoint_from_app. split.
      + eapply disjoint_from_Forall; [exact FX|]. intros iv Hiv.
        pose proof (fsobj_scratch_hull H HH _ _ _ _ _ R OB HO Hn HT Hiv). lia.
      + eapply disjoint_from_Forall; [exact FW|]. intros [l h] Hiv. unfold appwin in Hiv. cbn in Hiv |- *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_across3 : forall LF O cs m m' lo hi XS W',
    rw_cells asegs m O cs -> as_RFS H LF m -> fsobj H LF O (Z.of_nat (cells_size cs)) -> 0 <= O -> O + Z.of_nat (cells_size cs) <= AAPP_HI ->
    aapp O (Z.of_nat (cells_size cs)) -> O + Z.of_nat (cells_size cs) <= lo ->
    munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> Forall (fs_scratch H LF) XS -> disjoint_from W' O (Z.of_nat (cells_size cs)) ->
    rw_cells asegs m' O cs.
  Proof.
    intros LF O cs m m' lo hi XS W' RC R OB HO HT AP OL MU WM FX DW.
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn. split; [lia|].
    apply disjoint_from_app. split; [eapply disjoint_of_scratch; eauto; lia| exact DW].
  Qed.

  (* [comment removed for export] *)
  Definition b64rd_shpat : list cell :=
    [C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 4); C1 (b8 243); C1 (b8 243); C1 (b8 243)].

  (* [comment removed for export] *)
  Lemma acc4_of_shpat : forall m ff, rw_cells asegs m (sh ff) b64rd_shpat -> 0 <= ff -> ff mod 8 = 0 -> ff + 40 <= AAPP_HI ->
    accessible m (ff + 32) 4.
  Proof.
    intros m ff RC HF HM HT.
    pose proof (C1_chunk_nth m (sh ff) b64rd_shpat 4 (b8 4) RC eq_refl ltac:(repeat constructor)) as C4c.
    replace (sh ff + Z.of_nat 4) with (sh (ff + 32)) in C4c by (unfold sh; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|]. intros x Hx. exists 4. split; [lia|]. split.
    - replace (sh x) with (sh (ff + 32)) by (unfold sh; Z.div_mod_to_equations; lia).
      exact (rw_cells_C1_mrd _ _ _ _ _ C4c).
    - right. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma shpat_across3 : forall LF ff fp m m' lo hi XS W',
    rw_cells asegs m (sh ff) b64rd_shpat -> as_RFS H LF m -> In (0, ff, fp) LF ->
    munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> aceil <= lo -> Forall (fs_scratch H LF) XS -> Forall appwin W' ->
    rw_cells asegs m' (sh ff) b64rd_shpat.
  Proof.
    intros LF ff fp m m' lo hi XS W' RC R IN MU WM CE FX FW.
    pose proof (proj2 (ah_RFS_range H HH _ _ R) _ IN) as AR. cbn in AR.
    pose proof (RFS_fsb H HH _ _ R) as FB.
    assert (OB : fsobj H LF ff 64) by (eapply fsobj_inframe; [exact IN| cbn; lia| cbn; change (fsz 0) with 64; lia]).
    destruct AR as (Q1 & Q2 & Q3 & Q4 & Q5). destruct FB as (F1 & F2 & F3 & F4).
    assert (HF : 0 <= ff /\ ff + 64 <= AAPP_HI).
    { acb. unfold AIMG_TOP, AAPP_HI, AFS_HDR, AFS_SIZE in *. change (fsz 0) with 64 in *. pose proof aceil_range. lia. }
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. change (Z.of_nat (cells_size b64rd_shpat)) with (nsh 64). cbn -[nsh]. split.
    - pose proof aceil_range as CR. pose proof (sh_nsh_high ff 64 ltac:(lia) ltac:(lia) ltac:(lia)) as K. unfold AHI_LO in *. lia.
    - apply disjoint_from_app. split; [eapply disjoint_sh_of_scratch; eauto; lia| apply disjoint_sh_of_appwin; auto; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma abiogetflags_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (-1) -> rw_cells asegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      addressable m a BIO_SIZE -> BIO_ranges H a -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (bioacc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (bio_flags B)) a B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_test_flags) fc None m (seg_rom asegs)).
  Proof.
    intros until B; intros A0 A1 BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    unfold BIO_ranges, BIOACC_STACK, FR_BIO_set_data, BIO_SIZE in *; acb.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB; unfold bio_cells in BB; cbn [cells_size csize Nat.add] in BB.
    unfold bio_ok in BOK; unfold bio_cells, wz in BC.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof BR as (APOS & AAL & _ & _ & _ & _ & AP1). pose proof (aapp_not_shadowland _ _ AP1) as NS1.
    pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _). unfold AAPP_HI in AH1.
    assert (ACC' : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SH| lia| lia| unfold AAPP_HI; lia]).
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128)])
      by (constructor; [cbn; unfold AHI_LO in *; lia| constructor; [cbn; exact NS1| constructor]]).
    destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_test_flags, O_BIO_FLAGS.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 128) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end; clear ACC'.
    step. ub_dead. step. ubal_by AAL. step. if_lit.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 48).
    (* [comment removed for export] *)
    st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia.
    rewrite (land_ones64k (bio_flags B)) by lia.
    do 4 step.
    release_frame FR ST (bv_unsigned sp). unfold bioacc_post. finish.
    all: try (lazymatch goal with |- ACONST _ => eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| assumption| lia] end).
    all: match goal with |- ?G => idtac "GETF-LEFT:" G end.
  Qed.
  (* [comment removed for export] *)
  Definition bioget_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : word) (a : Z) (B : biorep) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' a (bio_cells B).
  Lemma abiogetflags_rd_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (-1) -> rw_cells asegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      addressable m a BIO_SIZE -> BIO_ranges H a -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (bioget_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (bio_flags B)) a B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_test_flags) fc None m (seg_rom asegs)).
  Proof.
    intros until B; intros A0 A1 BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    unfold BIO_ranges, BIOACC_STACK, FR_BIO_set_data, BIO_SIZE in *; acb.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB; unfold bio_cells in BB; cbn [cells_size csize Nat.add] in BB.
    unfold bio_ok in BOK; unfold bio_cells, wz in BC.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    pose proof BR as (APOS & AAL & _ & _ & _ & _ & AP1). pose proof (aapp_not_shadowland _ _ AP1) as NS1.
    pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _). unfold AAPP_HI in AH1.
    assert (ACC' : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SH| lia| lia| unfold AAPP_HI; lia]).
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (constructor; [cbn; unfold AHI_LO in *; lia| constructor]).
    destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_test_flags, O_BIO_FLAGS.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 128) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end; clear ACC'.
    step. ub_dead. step. ubal_by AAL. step. if_lit.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 48).
    (* [comment removed for export] *)
    st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia.
    rewrite (land_ones64k (bio_flags B)) by lia.
    do 4 step.
    release_frame FR ST (bv_unsigned sp). unfold bioget_post. finish.
    all: try (lazymatch goal with |- ACONST _ => eapply ECH_AKit.ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL] end).
    all: match goal with |- ?G => idtac "GETF2-LEFT:" G end.
  Qed.
End HC.

