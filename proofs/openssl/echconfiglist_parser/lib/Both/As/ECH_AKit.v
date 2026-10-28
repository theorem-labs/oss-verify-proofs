(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aword_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma abyte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma abyte_eq_of_unsigned : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.
(* [comment removed for export] *)
Lemma signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec (z mod 2^64) (2^63)) as [L|L].
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) in L by lia. rewrite Z.mod_small in L by lia. lia.
  - destruct (Z.neg_nonneg_cases z) as [N|N]; [| rewrite Z.mod_small in * by lia; lia].
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma lxor_top : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof. intros n Hn. change 9223372036854775808 with (2^63). apply zb_lxor_pow2_small; lia. Qed.
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> disjoint_from W A' n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n A' n' H H1 H2 H3; [exact I|]. destruct H as [Ha Hb]. split; [lia| eauto]. Qed.
(* [comment removed for export] *)
Lemma arw_cells_recut : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section X.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma xpres_of_munch_gen : forall LB SP X W m m',
    munch W m m' -> wmono asegs m m' ->
    (forall a, 0 <= a < 2^64 -> xclient H LB SP X a -> outside W a) ->
    xpres H LB SP X m m'.
  Proof.
    intros LB SP X W m m' MU WM HO a Ha Hc. split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HO; assumption.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma xpres_X_mono : forall LB SP X X' m m',
    xpres H LB SP X m m' -> (forall a, rin_ivs X a -> rin_ivs X' a) -> xpres H LB SP X' m m'.
  Proof. intros LB SP X X' m m' XP HX a Ha [Hc Hx]. apply XP; [exact Ha|]. split; [exact Hc|]. intros K. apply Hx, HX, K. Qed.
  Lemma xpres_nil_X : forall LB SP X m m', xpres H LB SP [] m m' -> xpres H LB SP X m m'.
  Proof. intros LB SP X m m' XP. eapply xpres_X_mono; [exact XP|]. intros a K. destruct K. Qed.

  (* [comment removed for export] *)
  Lemma xpres_rw_cells' : forall LB SP X m m' A cs,
    xpres H LB SP X m m' -> rw_cells asegs m A cs -> aclient_range H LB SP A (Z.of_nat (cells_size cs)) ->
    Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) X ->
    rw_cells asegs m' A cs.
  Proof. intros LB SP X m m' A cs XP HC HR HX. eapply xpres_rw_cells; [exact XP| exact HC| split; [exact HR| exact HX]]. Qed.
  Lemma xpres_bytes_at' : forall LB SP X m m' A bs,
    xpres H LB SP X m m' -> bytes_at asegs m A bs -> aclient_range H LB SP A (Z.of_nat (length bs)) ->
    Forall (fun iv : Z * Z => A + Z.of_nat (length bs) <= fst iv \/ snd iv <= A) X ->
    bytes_at asegs m' A bs.
  Proof. intros LB SP X m m' A bs XP HC HR HX. eapply xpres_bytes_at; [exact XP| exact HC| split; [exact HR| exact HX]]. Qed.

  (* [comment removed for export] *)
  Lemma afresh_outside : forall s' LB m' p A n SP a,
    as_RHEAP H s' ((p, A, n) :: LB) m' -> aceil <= SP -> aclient_addr H LB SP a -> A <= a < A + n -> False.
  Proof.
    intros s' LB m' p A n SP a RH CE HC Ha. acb.
    pose proof (ah_blocks H HH _ _ _ _ RH (or_introl eq_refl)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    assert (QC : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; lia). pose proof (sh_below_aceil aceil QC) as SHC.
    assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_app (as_FSB H + AFS_SIZE) QB) as SB.
    assert (SH0 : forall x, 0 <= x -> ASHADOW_BASE <= sh x) by (intros x Hx; unfold sh; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
    unfold aapp, aapp_lo, aapp_hi in B7. unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
    unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *. rewrite ASHADOW_BASE_val in SH0.
    destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]].
    - lia.
    - lia.
    - pose proof (ah_nodup H HH _ _ _ RH) as ND. cbn [map blk_id fst snd] in ND. inversion ND as [|x l NI ND']; subst.
      assert (NE : blk_id (p, A, n) <> blk_id b).
      { cbn [blk_id fst snd]. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
      pose proof (ah_disj H HH _ _ _ _ _ RH (or_introl eq_refl) (or_intror Hb) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH (or_intror Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). pose proof (SH0 (blk_addr b) ltac:(lia)).
      unfold AHI_LO in S4. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - lia.
    - pose proof (SH0 (as_FSB H) ltac:(unfold AIMG_TOP in F1; lia)). unfold AHI_LO in SB. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - assert (QA : 0 <= aceil) by lia. pose proof (SH0 aceil QA). destruct B7 as [[P1 P2]|[P1 P2]]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_fresh : forall s' LB m0 m m' p A n SP X W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> aceil <= SP ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + n)
                              \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m m'.
  Proof.
    intros s' LB m0 m m' p A n SP X W RH CE MU WM FW.
    assert (RH' : as_RHEAP H s' LB m0 -> True) by auto.
    apply (xpres_trans H LB SP X m m m'); [apply xpres_refl|].
    (* [comment removed for export] *)
    eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC HX].
    clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as K1. cbn in K1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K1 as [[K1 K2]|[[K1 K2]|K1]].
    - intros K. acb. pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
      assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) QB) as SB.
      unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
      destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]]; unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *.
      + lia.
      + lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH (or_intror Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH (or_intror Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
        pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). unfold AHI_LO in S4. lia.
      + lia.
      + lia.
      + lia.
    - intros K. exact (afresh_outside s' LB m0 p A n SP a RH CE HC ltac:(lia)).
    - intros R. apply HX. apply K1. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_cons_block : forall LB SP X m m' p D n,
    xpres H LB SP X m m' -> (forall q, D <= q < D + n -> rin_ivs X q) -> (forall q, sh D <= q < sh D + nsh n -> rin_ivs X q) ->
    xpres H ((p, D, n) :: LB) SP X m m'.
  Proof.
    intros LB SP X m m' p D n XP HB HS q Hq [HC HX]. apply XP; [exact Hq|]. split; [| exact HX].
    unfold aclient_addr, in_block, in_block_sh in HC |- *.
    destruct HC as [K|[K|[(b & [<-|Hb] & R)|[(b & [<-|Hb] & R)|K]]]].
    - left; exact K.
    - right; left; exact K.
    - exfalso. apply HX. apply HB. cbn [blk_addr blk_size fst snd] in R. exact R.
    - right; right; left. exists b. split; [exact Hb| exact R].
    - exfalso. apply HX. apply HS. cbn [blk_addr blk_size fst snd] in R. exact R.
    - right; right; right; left. exists b. split; [exact Hb| exact R].
    - right; right; right; right. exact K.
  Qed.
End X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section C.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma MEMFLAG_across : forall W m m1 v,
    munch W m m1 -> wmono asegs m m1 -> disjoint_from W A_mem_inited 1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros W m m1 v MU WM DJ (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply rw_cells_transport; [exact MF| exact MU| exact WM| exact DJ].
  Qed.
  Lemma IMPL_across : forall W m m1,
    munch W m m1 -> wmono asegs m m1 ->
    disjoint_from W A_malloc_impl 72 -> IMPL_mem m -> IMPL_mem m1.
  Proof.
    intros W m m1 MU WM DJ (I1 & I2 & I3). unfold IMPL_mem. unfold A_malloc_impl, A_realloc_impl, A_free_impl in *.
    repeat split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_sub; [exact DJ| cbn; lia| cbn; lia| cbn; lia]]).
  Qed.
  Lemma GOT_across : forall W m m1,
    munch W m m1 -> wmono asegs m m1 -> disjoint_from W A_got_CRYPTO_malloc 32 -> GOT_mem m -> GOT_mem m1.
  Proof. intros W m m1 MU WM DJ GM. eapply rw_cells_transport; [exact GM| exact MU| exact WM| exact DJ]. Qed.

  (* [comment removed for export] *)
  Lemma MEMFLAG_apres : forall LB SP m m1 v, apres H LB SP m m1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros LB SP m m1 v HPRES (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply (apres_rw_cells H); [exact HPRES| exact MF|]. right; left. unfold A_mem_inited, aimg_client. cbn. lia.
  Qed.
  Lemma IMPL_apres : forall LB SP m m1, apres H LB SP m m1 -> IMPL_mem m -> IMPL_mem m1.
  Proof.
    intros LB SP m m1 HPRES (I1 & I2 & I3). unfold IMPL_mem.
    repeat split; (eapply (apres_rw_cells H); [exact HPRES| eassumption|]); right; left; unfold A_malloc_impl, A_realloc_impl, A_free_impl, aimg_client; cbn; lia.
  Qed.
  Lemma GOT_apres : forall LB SP m m1, apres H LB SP m m1 -> GOT_mem m -> GOT_mem m1.
  Proof.
    intros LB SP m m1 HPRES GM. eapply (apres_rw_cells H); [exact HPRES| exact GM|]. right; left. unfold A_got_CRYPTO_malloc, aimg_client. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma IMPL_xpres : forall LB SP m m1, xpres H LB SP memflag_foot m m1 -> IMPL_mem m -> IMPL_mem m1.
  Proof.
    intros LB SP m m1 XP (I1 & I2 & I3). unfold IMPL_mem.
    repeat split; (eapply xpres_rw_cells'; [exact XP| eassumption| right; left; unfold A_malloc_impl, A_realloc_impl, A_free_impl, aimg_client; cbn; lia
                                        | unfold memflag_foot, A_malloc_impl, A_realloc_impl, A_free_impl, A_mem_inited; constructor; [cbn; lia| constructor]]).
  Qed.
  Lemma GOT_xpres : forall LB SP m m1, xpres H LB SP memflag_foot m m1 -> GOT_mem m -> GOT_mem m1.
  Proof.
    intros LB SP m m1 XP GM. eapply xpres_rw_cells'; [exact XP| exact GM| |].
    - right; left. unfold A_got_CRYPTO_malloc, aimg_client. cbn. lia.
    - unfold memflag_foot, A_got_CRYPTO_malloc, A_mem_inited. constructor; [cbn; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma errno_across : forall W m m1 errv,
    rw_cells asegs m (ATP + -164) [C4 errv] -> munch W m m1 -> wmono asegs m m1 -> disjoint_from W (ATP + -164) 4 ->
    rw_cells asegs m1 (ATP + -164) [C4 errv].
  Proof. intros W m m1 errv ERR MU WM DJ. eapply rw_cells_transport; [exact ERR| exact MU| exact WM| exact DJ]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
  Lemma achain_below : forall m m1 cur CH W (bnd : Z),
    as_chain H m cur CH -> (forall fp' ra', In (fp', ra') CH -> bnd <= fp') ->
    munch W m m1 -> Forall (fun iv : Z * Z => snd iv <= bnd - 16 \/ (forall fp' ra', In (fp', ra') CH -> snd iv <= fp' - 16 \/ fp' <= fst iv)) W ->
    as_chain H m1 cur CH.
  Proof.
    intros m m1 cur CH W bnd CHN CHS MU FW. acb.
    eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha.
    destruct (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (R1 & _ & _). specialize (CHS _ _ Hin).
    rewrite <- (Z_to_bv_bv_unsigned 64 (wa a)) || idtac.
    unfold wa. apply MU. rewrite unsigned_lit by lia.
    clear MU. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K as [K|K]; [lia|]. destruct (K _ _ Hin); lia.
  Qed.
End C.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section O.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma ashobj_mono : forall LB LB' SP A n, ashobj H LB SP A n -> (forall b, In b LB -> In b LB') -> ashobj H LB' SP A n.
  Proof.
    intros LB LB' SP A n [(b & IN & R)|K] HL; [| right; exact K]. left. exists b. split; [apply HL; exact IN| exact R].
  Qed.

  Lemma ashobj_sub : forall LB SP A n A' n', ashobj H LB SP A n -> A <= A' -> A' + n' <= A + n -> ashobj H LB SP A' n'.
  Proof.
    intros LB SP A n A' n' [(b & IN & R)|[K|K]] L1 L2.
    - left. exists b. split; [exact IN| lia].
    - right; left. lia.
    - right; right. lia.
  Qed.

  Lemma ashobj_lowerSP : forall LB SP SP' A n, ashobj H LB SP A n -> SP' <= SP -> ashobj H LB SP' A n.
  Proof. intros LB SP SP' A n [K|[K|K]] L; [left; exact K| right; left; exact K| right; right; lia]. Qed.

  (* [comment removed for export] *)
  Lemma xpres_nil_apres : forall LB SP m m', xpres H LB SP [] m m' -> apres H LB SP m m'.
  Proof. intros LB SP m m' XP a Ha Hc. apply XP; [exact Ha|]. split; [exact Hc|]. intros K; exact K. Qed.

  Lemma ashobj_client_range : forall LB SP A n, ashobj H LB SP A n -> aclient_range H LB SP A n.
  Proof.
    intros LB SP A n [(b & IN & R)|[K|K]].
    - right; right; left. exists b. split; [exact IN| lia].
    - right; right; right; right; left. exact K.
    - left. exact K.
  Qed.

  Lemma ashobj_xclient_range : forall LB SP X A n, ashobj H LB SP A n ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X -> xclient_range H LB SP X A n.
  Proof. intros LB SP X A n OB HX. split; [apply ashobj_client_range; exact OB| exact HX]. Qed.

  (* [comment removed for export] *)
  Lemma ashobj_bounds : forall s LB m SP A n, as_RHEAP H s LB m -> aceil <= SP -> ashobj H LB SP A n -> 0 <= n ->
    AIMG_TOP <= A /\ (A + n <= ALOWSH_LO \/ AHI_LO <= A).
  Proof.
    intros s LB m SP A n HP HSP [(b & IN & R1 & R2)|[K|K]] Hn.
    - pose proof (ah_blocks H HH _ _ _ _ HP IN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (aapp_not_shadowland _ _ (aapp_sub _ _ A n D7 R1 R2)). lia.
    - pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
      pose proof (aapp_not_shadowland _ _ (aapp_sub _ _ A n F4 ltac:(lia) ltac:(lia))). lia.
    - acb. unfold AIMG_TOP, AHI_LO in *. lia.
  Qed.

  Lemma ashobj_write_ok : forall LB SP A n, aceil <= SP -> ashobj H LB SP A n -> aclient_write_ok H LB (A, A + n).
  Proof.
    intros LB SP A n HSP [(b & IN & R)|[K|K]].
    - right; right; left. exists b. split; [exact IN| cbn; lia].
    - right; right; right; right; left. cbn. lia.
    - left. cbn. lia.
  Qed.

  Lemma ashobj_aconst_ok : forall s LB m SP A n lo hi, as_RHEAP H s LB m -> aceil <= SP -> ashobj H LB SP A n ->
    A <= lo -> hi <= A + n -> aconst_ok (lo, hi).
  Proof.
    intros s LB m SP A n lo hi HP HSP [(b & IN & R1 & R2)|[K|K]] L1 L2.
    - pose proof (ah_blocks H HH _ _ _ _ HP IN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). eapply aconst_ok_aapp; [exact D7| lia| lia].
    - pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). eapply aconst_ok_aapp; [exact F4| lia| lia].
    - apply aconst_ok_hi. acb. unfold AHI_LO in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ashobj_off_frame : forall s LB m SP A n lo, as_RHEAP H s LB m -> ashobj H LB SP A n -> aceil <= lo ->
    A + n <= lo \/ SP <= A.
  Proof.
    intros s LB m SP A n lo HP [(b & IN & R1 & R2)|[K|K]] HL.
    - pose proof (ah_blocks H HH _ _ _ _ HP IN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). left. lia.
    - pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). left. lia.
    - right. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma afresh_apart : forall s' LB m' p A n SP a k,
    as_RHEAP H s' ((p, A, n) :: LB) m' -> aceil <= SP -> aclient_range H LB SP a k -> 0 < k -> 0 < n -> A + n <= a \/ a + k <= A.
  Proof.
    intros s' LB m' p A n SP a k HP CE CR Hk Hn.
    destruct (Z.le_gt_cases (A + n) a) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases (a + k) A) as [L2|L2]; [right; exact L2|]. exfalso.
    destruct (Z.lt_ge_cases a A) as [L3|L3].
    - apply (afresh_outside H HH s' LB m' p A n SP A HP CE); [| lia].
      eapply aclient_range_addr; [exact CR| lia].
    - apply (afresh_outside H HH s' LB m' p A n SP a HP CE); [| lia]. eapply aclient_range_addr; [exact CR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ashobj_sh_client : forall s LB m SP A n x, as_RHEAP H s LB m -> aceil <= SP -> ashobj H LB SP A n ->
    0 <= A -> A + n <= AAPP_HI -> A <= x < A + n -> aclient_addr H LB SP (sh x).
  Proof.
    intros s LB m SP A n x HP HSP [(b & IN & R1 & R2)|[K|K]] HA Htop Hx.
    - destruct b as [[p AD] nD]. cbn [blk_addr blk_size fst snd] in R1, R2.
      pose proof (ah_blocks H HH _ _ _ _ HP IN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in *.
      right; right; right; left. exists (p, AD, nD). split; [exact IN|]. cbn [blk_addr blk_size fst snd].
      assert (D8 : AD mod 8 = 0) by (clear - D2; Z.div_mod_to_equations; lia).
      pose proof (sh_rel_lt AD x nD D8 ltac:(lia)). rewrite (sh_rel AD x D8) by lia. unfold nsh. lia.
    - pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
      right; right; right; right; right; left.
      assert (F8 : as_FSB H mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
      pose proof (sh_rel_lt (as_FSB H) x AFS_SIZE F8 ltac:(lia)). rewrite (sh_rel (as_FSB H) x F8) by lia.
      rewrite (sh_rel (as_FSB H) (as_FSB H + AFS_SIZE) F8) by lia. unfold AFS_SIZE in *.
      replace ((as_FSB H + 11571200 - as_FSB H) / 8) with 1446400 by (symmetry; Z.div_mod_to_equations; lia). lia.
    - right; right; right; right; right; right.
      split; [apply sh_mono; lia|]. pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. 
      change ((1 + 7) / 8) with 1 in H0. lia.
  Qed.

  Lemma ashobj_sh_client_sub : forall s LB LB2 m SP A n x, as_RHEAP H s LB m -> (forall b, In b LB2 -> In b LB) -> aceil <= SP -> ashobj H LB2 SP A n ->
    0 <= A -> A + n <= AAPP_HI -> A <= x < A + n -> aclient_addr H LB2 SP (sh x).
  Proof.
    intros s LB LB2 m SP A n x HP SUB HSP [(b & IN & R1 & R2)|[K|K]] HA Htop Hx.
    - destruct b as [[p AD] nD]. cbn [blk_addr blk_size fst snd] in R1, R2.
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ IN)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in *.
      right; right; right; left. exists (p, AD, nD). split; [exact IN|]. cbn [blk_addr blk_size fst snd].
      assert (D8 : AD mod 8 = 0) by (clear - D2; Z.div_mod_to_equations; lia).
      pose proof (sh_rel_lt AD x nD D8 ltac:(lia)). rewrite (sh_rel AD x D8) by lia. unfold nsh. lia.
    - pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
      right; right; right; right; right; left.
      assert (F8 : as_FSB H mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
      pose proof (sh_rel_lt (as_FSB H) x AFS_SIZE F8 ltac:(lia)). rewrite (sh_rel (as_FSB H) x F8) by lia.
      rewrite (sh_rel (as_FSB H) (as_FSB H + AFS_SIZE) F8) by lia. unfold AFS_SIZE in *.
      replace ((as_FSB H + 11571200 - as_FSB H) / 8) with 1446400 by (symmetry; Z.div_mod_to_equations; lia). lia.
    - right; right; right; right; right; right.
      split; [apply sh_mono; lia|]. pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. 
      change ((1 + 7) / 8) with 1 in H0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ashobj_accessible_xpres_sub : forall s LB LB2 m m' SP X A n,
    as_RHEAP H s LB m -> (forall b, In b LB2 -> In b LB) -> aceil <= SP -> ashobj H LB2 SP A n -> accessible m A n -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) X ->
    accessible m' A n.
  Proof.
    intros s LB LB2 m m' SP X A n HP SUB HSP OB (Q0 & Q1 & QA) XP HX.
    split; [exact Q0|]. split; [exact Q1|]. intros x Hx. destruct (QA x Hx) as (v & V1 & RD & OK).
    exists v. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
    assert (SX : ASHADOW_BASE <= sh x < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. change ((1 + 7) / 8) with 1 in H0. lia. }
    destruct (XP (sh x)) as [E _].
    { unfold AHI_LO in SX. rewrite ASHADOW_BASE_val in SX. lia. }
    { split; [eapply ashobj_sh_client_sub; eauto|].
      clear - HX SX. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K].
      - pose proof (Forall_inv HX) as K1. cbn in K1. unfold ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val in SX. lia.
      - exact (IH (Forall_inv_tail HX) K). }
    rewrite E. exact RD.
  Qed.
  Lemma ashobj_accessible_xpres : forall s LB m m' SP X A n,
    as_RHEAP H s LB m -> aceil <= SP -> ashobj H LB SP A n -> accessible m A n -> xpres H LB SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) X ->
    accessible m' A n.
  Proof. intros s LB m m' SP X A n HP HSP OB ACC XP HX. eapply ashobj_accessible_xpres_sub with (LB2 := LB); eauto. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ashobj_addressable_xpres : forall s LB LB2 m m' SP X A n,
    as_RHEAP H s LB m -> (forall b, In b LB2 -> In b LB) -> aceil <= SP -> ashobj H LB2 SP A n -> A + n <= AAPP_HI ->
    addressable m A n -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) X ->
    addressable m' A n.
  Proof.
    intros s LB LB2 m m' SP X A n HP SUB HSP OB Htop (Hn & A0 & A8 & (B0 & B1 & BA) & (W0 & W1 & WA)) XP HX.
    assert (PT : forall i, 0 <= i < nsh n -> exists x, A <= x < A + n /\ sh x = sh A + i).
    { intros i Hi. exists (A + 8 * i). unfold nsh in Hi. split; [Z.div_mod_to_equations; lia|]. unfold sh. Z.div_mod_to_equations; lia. }
    assert (CL : forall i, 0 <= i < nsh n -> m' (wa (sh A + i)) = m (wa (sh A + i)) /\ (wview asegs m (wa (sh A + i)) <> None -> wview asegs m' (wa (sh A + i)) <> None)).
    { intros i Hi. destruct (PT i Hi) as (x & Hx & SX). rewrite <- SX.
      assert (SXR : ASHADOW_BASE <= sh x < AHI_LO).
      { split; [unfold sh; Z.div_mod_to_equations; lia|].
        pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. change ((1 + 7) / 8) with 1 in H0. lia. }
      apply XP. { unfold AHI_LO in SXR. rewrite ASHADOW_BASE_val in SXR. lia. }
      split; [eapply ashobj_sh_client_sub; eauto; lia|].
      clear - HX SXR. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K].
      - pose proof (Forall_inv HX) as K1. cbn in K1. unfold ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val in SXR. lia.
      - exact (IH (Forall_inv_tail HX) K). }
    pose proof (shadow_of_length n Hn) as SL.
    split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
    - split; [exact B0|]. split; [exact B1|].
      intros i Hi. rewrite <- (BA i Hi). unfold mrd. destruct (CL (Z.of_nat i) ltac:(lia)) as [E _]. rewrite E. reflexivity.
    - split; [exact W0|]. split; [exact W1|].
      intros i Hi. destruct (CL i ltac:(lia)) as [_ Wp]. apply Wp. apply WA. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma accessible_across : forall W m m' A n,
    accessible m A n -> munch W m m' -> Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> accessible m' A n.
  Proof.
    intros W m m' A n ACC MU HW. eapply accessible_transport; [exact ACC| exact MU|].
    intros x Hx. destruct ACC as (Q0 & Q1 & _).
    assert (SX : ASHADOW_BASE <= sh x < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high x 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. change ((1 + 7) / 8) with 1 in H0. lia. }
    rewrite ASHADOW_BASE_val in SX. unfold AHI_LO in SX.
    clear - HW SX. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.

  (* [comment removed for export] *)
  Lemma RFS_via_xpres : forall LF LB SP X m m',
    as_RFS H LF m -> xpres H LB SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO) X ->
    as_RFS H LF m'.
  Proof.
    intros LF LB SP X m m' R XP HX. pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4).
    eapply (ah_RFS_ext H HH); [exact R|].
    intros a Ha Hr. apply XP; [exact Ha|]. split.
    - unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
      + right; right; right; right; left. exact Hr.
      + right; left. unfold aimg_client. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      + right; right; right; right; right; left. exact Hr.
    - assert (LO : ATLS_PRIV_LO <= a).
      { pose proof (sh_mono AIMG_TOP (as_FSB H) F1). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP, AIMG_TOP in *. lia. }
      clear - HX LO. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K].
      + pose proof (Forall_inv HX) as K1. cbn in K1. lia.
      + exact (IH (Forall_inv_tail HX) K).
  Qed.
End O.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stale (P : Prop) : Prop := P.
Ltac carry MU WM :=
  lazymatch type of MU with
  | munch ?W ?m0 ?m1 =>
      repeat match goal with
      | H : rw_cells ?segs m0 ?A ?cs |- _ =>
          first [ apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MU WM) in H; [| cbn; lia]
                | change (stale (rw_cells segs m0 A cs)) in H ]
      | H : bytes_at ?segs m0 ?A ?bs |- _ =>
          first [ apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MU) in H; [| cbn; lia]
                | change (stale (bytes_at segs m0 A bs)) in H ]
      | H : stk ?segs m0 ?lo ?hi |- _ =>
          first [ apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MU WM) in H; [| cbn; lia]
                | change (stale (stk segs m0 lo hi)) in H ]
      end
  end.
Ltac extend_munch MU WM MU' WM' :=
  lazymatch type of MU with munch ?W ?m ?m0 =>
  lazymatch type of MU' with munch ?W' m0 ?m1 =>
    let T := fresh "MUx" in
    assert (T : munch W m m1)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU'];
          let xa := fresh "xa" in let Hxa := fresh "Hxa" in
          intros xa Hxa; unfold outside in Hxa |- *; cbn in Hxa |- *;
          first [ solve [clear - Hxa; tauto] | lia ]);
    clear MU; rename T into MU;
    let T2 := fresh "WMx" in
    pose proof (wmono_trans _ _ _ _ WM WM') as T2; clear WM; rename T2 into WM;
    clear MU' WM'
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_flatten : forall segs m A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros segs m A cs HC. pose proof (rw_cells_merge segs m A [] cs [] ) as T. cbn [app] in T. rewrite app_nil_r in T. exact (T HC).
Qed.
Lemma u64arr_CB : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A [CB (8 * length ws)%nat (u64s ws)].
Proof.
  intros segs m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.
Lemma u64arr_nil : forall segs m A, 0 <= A <= 2^64 -> u64arr segs m A [].
Proof.
  intros segs m A HA. split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
Lemma u64arr_of_CB : forall segs m A ws, rw_cells segs m A [CB (8 * length ws)%nat (u64s ws)] -> u64arr segs m A ws.
Proof.
  intros segs m A ws [[WF B] W]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn [cells_size csize Nat.add] in W.
  split; [exact B|]. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws + 0)) by lia. exact W.
Qed.
(* [comment removed for export] *)
Lemma SKobj_hdr_CB : forall LB m a K, SKobj LB m a K -> exists bs, rw_cells asegs m a [CB (Z.to_nat SK_SIZE) bs].
Proof.
  intros LB m a K ((pad & PL & HDR) & _). exists (cells_bytes (sk_hdr_cells K pad)).
  pose proof (rw_cells_flatten _ _ _ _ HDR) as T. unfold sk_hdr_cells in T at 1. cbn [cells_size csize Nat.add] in T. exact T.
Qed.
Lemma SKobj_data_CB : forall LB m a K, SKobj LB m a K -> sk_cap K <> 0 ->
  exists bs, rw_cells asegs m (sk_data K) [CB (Z.to_nat (8 * sk_cap K)) bs].
Proof.
  intros LB m a K (_ & _ & _ & NC & _ & _ & _ & DAT) CAP. destruct DAT as [[C0 _]|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [lia|].
  unfold sk_num, zlength in *.
  pose proof (u64arr_CB _ _ _ _ AR) as A1. rewrite length_map in A1.
  assert (J : rw_cells asegs m (sk_data K) ([CB (8 * length (sk_elems K))%nat (u64s (map wz (sk_elems K)))] ++ [CB (Z.to_nat (8 * (sk_cap K - Z.of_nat (length (sk_elems K))))) junk])).
  { apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact A1|]. cbn [cells_size csize Nat.add].
    replace (sk_data K + Z.of_nat (8 * length (sk_elems K) + 0)) with (sk_data K + 8 * Z.of_nat (length (sk_elems K))) by lia. exact JK. }
  pose proof (rw_cells_flatten _ _ _ _ J) as T. cbn [cells_size csize Nat.add cells_bytes cbytes app] in T.
  eexists. replace (Z.to_nat (8 * sk_cap K)) with (8 * length (sk_elems K) + (Z.to_nat (8 * (sk_cap K - Z.of_nat (length (sk_elems K)))) + 0))%nat by lia. exact T.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_id_inj : forall (LB : list block) b1 b2, List.NoDup (map blk_id LB) -> In b1 LB -> In b2 LB -> blk_id b1 = blk_id b2 -> b1 = b2.
Proof.
  induction LB as [|c LB IH]; intros b1 b2 ND H1 H2 E; [destruct H1|].
  cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply NI. apply in_map_iff. exists b2. split; [symmetry; exact E| exact H2].
  - exfalso. apply NI. apply in_map_iff. exists b1. split; [exact E| exact H1].
Qed.
Section R.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma alb_remove_exact : forall p A n LB,
    List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    lb_bytes (as_lb_remove H p LB) = lb_bytes LB - n
    /\ (S (length (as_lb_remove H p LB)) = length LB)%nat
    /\ (forall b, In b (as_lb_remove H p LB) <-> (In b LB /\ blk_id b <> p)).
  Proof.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    intros p A n LB. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct Hin as [->|Hin].
    - cbn in NI. rewrite L1 by exact NI. rewrite lb_bytes_cons. cbn [blk_size snd length].
      split; [lia|]. split; [reflexivity|].
      intros b. split.
      + intros Hb. split; [right; exact Hb|]. intros E. apply NI. apply in_map_iff. exists b. split; [exact E| exact Hb].
      + intros [[<-|Hb] NE]; [cbn in NE; congruence| exact Hb].
    - assert (NE : blk_id c <> p).
      { intros E. apply NI. apply in_map_iff. exists (p, A, n). split; [symmetry; exact E| exact Hin]. }
      rewrite L2 by exact NE. rewrite !lb_bytes_cons. cbn [length].
      destruct (IH ND' Hin) as (B1 & B2 & B3). split; [lia|]. split; [lia|].
      intros b. split.
      + intros [<-|Hb]; [split; [left; reflexivity| exact NE]|]. destruct (proj1 (B3 b) Hb) as [K1 K2]. split; [right; exact K1| exact K2].
      + intros [[<-|Hb] NEb]; [left; reflexivity| right]. apply (proj2 (B3 b)). split; [exact Hb| exact NEb].
  Qed.

  Lemma alb_remove_perm : forall s LB m p A n,
    as_RHEAP H s LB m -> In (p, A, n) LB -> Permutation ((p, A, n) :: as_lb_remove H p LB) LB.
  Proof.
    intros s LB m p A n HP Hin. pose proof (ah_nodup H HH _ _ _ HP) as ND. clear HP.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    revert ND Hin. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|].
    cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct Hin as [->|Hin].
    - cbn in NI. rewrite L1 by exact NI. apply Permutation_refl.
    - assert (NE : blk_id c <> p).
      { intros E. apply NI. apply in_map_iff. exists (p, A, n). split; [symmetry; exact E| exact Hin]. }
      rewrite L2 by exact NE. eapply Permutation_trans; [apply perm_swap| apply perm_skip]. apply IH; assumption.
  Qed.

  Lemma afresh_id_ne : forall s p' A' n' LBr m q,
    as_RHEAP H s ((p', A', n') :: LBr) m -> In q (map blk_id LBr) -> p' <> q.
  Proof.
    intros s p' A' n' LBr m q HP Hq E. subst q. pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst. contradiction.
  Qed.

  Lemma alb_remove_fresh : forall s p A n LB m,
    as_RHEAP H s ((p, A, n) :: LB) m -> as_lb_remove H p ((p, A, n) :: LB) = LB.
  Proof.
    intros s p A n LB m HP. pose proof (ah_lb_remove H HH) as (L1 & _ & _). apply L1.
    pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst. assumption.
  Qed.
End R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ST.
  Context {HCEIL : HeapCeil}.

  Lemma magree_of_munch : forall (R : Z -> Prop) W m m',
    munch W m m' -> wmono asegs m m' -> (forall a, R a -> outside W a) -> magree R m m'.
  Proof.
    intros R W m m' MU WM HR a Ha Hr. split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. apply HR. exact Hr.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma LIBX_below : forall a, rin_ivs LIBX a -> a < AIMG_TOP.
  Proof. intros a HX. revert HX. unfold LIBX, LIBX0, LIBXW, AIMG_TOP. cbn. lia. Qed.

  Lemma outside_of_Forall_lo : forall W a bnd, Forall (fun iv : Z * Z => bnd <= fst iv) W -> a < bnd -> outside W a.
  Proof.
    intros W a bnd FW Ha. induction W as [|[lo hi] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [lia| exact (IH (Forall_inv_tail FW))].
  Qed.

  Lemma statics_magree : forall W m m', munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> magree (lib_addr []) m m'.
  Proof.
    intros W m m' MU WM FW. eapply magree_of_munch; [exact MU| exact WM|].
    intros a [HX|[(b & Hb & _)|(b & Hb & _)]]; [| destruct Hb| destruct Hb].
    eapply outside_of_Forall_lo; [exact FW| apply LIBX_below; exact HX].
  Qed.

  Lemma CTX_statics_across : forall W m m' x, CTX_statics m x -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> CTX_statics m' x.
  Proof. intros W m m' x CS MU WM FW. eapply (CTX_statics_frame []); [exact CS| eapply statics_magree; eassumption]. Qed.

  Lemma ERR_statics_across : forall W m m' c, ERR_statics m c -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> ERR_statics m' c.
  Proof. intros W m m' c ES MU WM FW. eapply (ERR_statics_frame []); [exact ES| eapply statics_magree; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma chain_blocks_in : forall LB m c b, ERR_chain LB m c -> In b (chain_blocks c) -> In b LB.
  Proof.
    intros LB m c b (I2 & _ & _ & I3 & _ & _ & I4 & _ & _ & I5 & _ & I6 & _ & _) Hb.
    destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
  Qed.
  Lemma lib_addr_mono : forall L1 L2 a, (forall b, In b L1 -> In b L2) -> lib_addr L1 a -> lib_addr L2 a.
  Proof.
    intros L1 L2 a SUB [HX|[(b & Hb & R)|(b & Hb & R)]]; [left; exact HX| right; left| right; right]; exists b; split; auto.
  Qed.

  Lemma arelro_across : forall W m m', arelro_lib m -> munch W m m' -> Forall (fun iv : Z * Z => 0x5ea000 <= fst iv) W -> arelro_lib m'.
  Proof.
    intros W m m' RL MU FW i Hi. rewrite <- (RL i Hi). unfold wa. apply MU. rewrite unsigned_lit by lia.
    eapply outside_of_Forall_lo; [exact FW| lia].
  Qed.

  Lemma ACONST_stack_frame : forall m m' lo hi, ACONST m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> ACONST m'.
  Proof.
    intros m m' lo hi AC MU WM CE. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
  Qed.
End ST.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FF.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma acc8_of_C1 : forall m A, rw_cells asegs m (sh A) [C1 (b8 0)] -> 0 <= A -> A mod 8 = 0 -> A + 8 <= AAPP_HI -> accessible m A 8.
  Proof.
    intros m A RC HA HM HT.
    assert (AD : addressable m A 8).
    { split; [lia|]. change (shadow_of 8) with [b8 0]. apply (SHAD_of_rw_cells m A 1); [exact HA| exact HM|].
      pose proof (rw_cells_merge asegs m (sh A) [] [C1 (b8 0)] []) as M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      apply M. exact RC. }
    eapply addressable_accessible; [exact AD| lia| lia| exact HT].
  Qed.

  (* [comment removed for export] *)
  Lemma C1_chunk_nth : forall m A cs k b, rw_cells asegs m A cs -> nth_error cs k = Some (C1 b) ->
    Forall (fun c => csize c = 1%nat) cs -> rw_cells asegs m (A + Z.of_nat k) [C1 b].
  Proof.
    intros m A cs k b RC NK FA. revert A cs RC NK FA. induction k as [|k IH]; intros A cs RC NK FA.
    - destruct cs as [|c cs]; [discriminate|]. cbn in NK. injection NK as ->.
      change (C1 b :: cs) with ([C1 b] ++ cs) in RC. apply (proj1 (rw_cells_app _ _ _ _ _)) in RC. destruct RC as [RC _].
      rewrite Z.add_0_r. exact RC.
    - destruct cs as [|c cs]; [discriminate|]. cbn in NK. pose proof (Forall_inv FA) as S1. cbn in S1.
      change (c :: cs) with ([c] ++ cs) in RC. apply (proj1 (rw_cells_app _ _ _ _ _)) in RC. destruct RC as [_ RC].
      cbn [cells_size Nat.add] in RC. rewrite S1 in RC.
      replace (A + Z.of_nat (S k)) with (A + Z.of_nat 1 + Z.of_nat k) by lia.
      apply (IH _ _ RC NK (Forall_inv_tail FA)).
  Qed.

  (* [comment removed for export] *)
  Lemma relro_cell : forall m A cs, arelro_lib m -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 ->
    cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> rw_cells asegs m A cs.
  Proof.
    intros m A cs RL HA HB WF RB. pose proof (cells_bytes_length cs WF) as L.
    apply (arw_cells_recut m A [CB (length (cells_bytes cs)) (cells_bytes cs)] cs); [| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
    apply none_on_rw_cells; [| exact RB| lia| rewrite L; lia].
    intros a Ha. apply RL. rewrite L in Ha. lia.
  Qed.

  Variable H : asr.
  Lemma fresh_frame_mono : forall LF f k ff fp, fresh_frame H (f :: LF) k ff fp -> fresh_frame H LF k ff fp.
  Proof. intros LF f k ff fp (A & B & C). split; [exact A| split; [exact B|]]. intros g Hg. apply C. right. exact Hg. Qed.
  Lemma fs_scratch_mono : forall LF f iv, fs_scratch H (f :: LF) iv -> fs_scratch H LF iv.
  Proof.
    intros LF f iv [E|(k & ff & fp & FF & E)]; [left; exact E| right]. exists k, ff, fp. split; [| exact E].
    eapply fresh_frame_mono. exact FF.
  Qed.
  Lemma fs_scratch_mono_Forall : forall LF f XS, Forall (fs_scratch H (f :: LF)) XS -> Forall (fs_scratch H LF) XS.
  Proof. intros LF f XS FA. eapply Forall_impl; [| exact FA]. intros iv. apply fs_scratch_mono. Qed.

  (* [comment removed for export] *)
  Hypothesis HH : asan_rt_hyps H.
  Lemma fs_scratch_write_ok : forall LF LB iv, fs_scratch H LF iv -> aclient_write_ok H LB iv.
  Proof.
    intros LF LB iv [->|(k & ff & fp & FF & E)]; unfold aclient_write_ok; cbn [fst snd].
    - right; right; right; right; left. unfold AFS_FLAGS, AFS_SIZE. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FZ. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [->|[->| ->]]; cbn [fst snd].
      + do 4 right. left. split; lia.
      + do 4 right. left. split; lia.
      + do 5 right. left. split.
        * apply sh_mono. lia.
        * unfold fshn. unfold fsz in P6. unfold sh. Z.div_mod_to_equations. nia.
  Qed.
  (* [comment removed for export] *)
  Lemma fs_scratch_range : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> AIMG_TOP <= fst iv /\ fst iv <= snd iv <= aceil.
  Proof.
    intros LF m iv R [->|(k & ff & fp & FF & E)]; cbn [fst snd].
    - pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4). unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)) as FZ. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [->|[->| ->]]; cbn [fst snd]; [lia| lia|].
      pose proof (sh_aapp_range _ _ (aapp_sub _ _ ff (fsz k) P9 ltac:(lia) ltac:(lia)) ltac:(lia)) as (S1 & S2 & S3).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. acb. unfold fshn, nsh, AIMG_TOP, AHI_LO in *. unfold fsz in S2.
      split; [lia|]. split; [lia|].
      assert (SC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia). 
      eapply Z.le_trans; [| apply Z.lt_le_incl; exact SC].
      eapply Z.le_trans; [| exact S2]. apply Z.add_le_mono_l. Z.div_mod_to_equations. nia.
  Qed.
  Lemma fs_scratch_range_Forall : forall LF m XS, as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv /\ fst iv <= snd iv <= aceil) XS.
  Proof. intros LF m XS R FA. eapply Forall_impl; [| exact FA]. intros iv. apply (fs_scratch_range LF m). exact R. Qed.
  Lemma fs_scratch_write_ok_Forall : forall LF LB XS, Forall (fs_scratch H LF) XS -> Forall (aclient_write_ok H LB) XS.
  Proof. intros LF LB XS FA. eapply Forall_impl; [| exact FA]. intros iv. apply fs_scratch_write_ok. Qed.
  (* [comment removed for export] *)
  Lemma RHEAP_after_scratch : forall s LB LF m m' lo hi XS W',
    as_RHEAP H s LB m -> munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> aceil <= lo ->
    Forall (fs_scratch H LF) XS -> Forall (aclient_write_ok H LB) W' -> as_RHEAP H s LB m'.
  Proof.
    intros s LB LF m m' lo hi XS W' HP MU WM CE FX FW. eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
    apply Forall_cons; [left; cbn; exact CE|]. apply Forall_app. split; [eapply fs_scratch_write_ok_Forall; exact FX| exact FW].
  Qed.
  Lemma athr_cells_after_scratch : forall s LB LF m m' lo hi XS W',
    as_RHEAP H s LB m -> munch ((lo, hi) :: XS ++ W') m m' -> wmono asegs m m' -> aceil <= lo ->
    Forall (fs_scratch H LF) XS -> Forall (aclient_write_ok H LB) W' -> athr_cells m'.
  Proof. intros. eapply (ah_thr H HH). eapply RHEAP_after_scratch; eassumption. Qed.
End FF.
