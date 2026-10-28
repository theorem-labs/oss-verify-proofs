(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen AModelC24.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_APopSec () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rounded"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec_map_size"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "ARUN_1.PopSec.Ls"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "ARUN_1.PopSec.newks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SE"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "ARUN_1.PopSec.cks"; "ARUN_1.PopSec.newsh"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "ARUN_1.PopSec.ms"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma sum_app : forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof. intros l1 l2. unfold sum. induction l1 as [|x l1 IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_req_facts : ltac2:(CDefT.buildp (gd_tbl_APopSec ()) "Pn,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+1<.)))P,(5.$6.(7.R2.)$8.)(1.(2.+?<01.R3.)(1.(5.$0.(9.R3.)+800.)(1.(5.$0.(:.R3.)(;.(<.R3.)+1000.))(1.(1.(2.R3.(<.R3.))(2.(<.R3.)(;.R3.+7.)))(1.(1.(2.(;.(:.R3.)+1000.)(=.R3.))(3.(=.R3.)(;.(:.R3.)+2000.)))(5.$0.(>.(=.R3.)+1000.)=))))))")
(* [comment removed for export] *).
Proof.
  intros n NB FP. pose proof FP as FP0.
  unfold from_primary, kMaxSize in FP. apply Z.leb_gt in FP.
  assert (RB : Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0).
  { unfold rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    split; [lia|]. apply Z_mod_mult. }
  assert (LO : 0xfc01 <= n).
  { destruct (Z_lt_ge_dec n 0xfc01) as [L|G]; [exfalso| clear - G; lia].
    unfold needed in FP.
    assert (rz_size n <= 1024).
    { unfold rz_size. assert (0 <= rz_log n <= 6).
      { unfold rz_log. destruct (Z.ltb_spec n 49); [lia|]. destruct (Z.ltb_spec n 97); [lia|]. destruct (Z.ltb_spec n 449); [lia|].
        destruct (Z.ltb_spec n 0xf81); [lia|]. destruct (Z.ltb_spec n 0x3f01); [lia|]. destruct (Z.ltb_spec n 0x7e01); [lia|].
        destruct (Z.ltb_spec n 0xfc01); lia. }
      assert (2 ^ rz_log n <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). change (2^6) with 64 in *. lia. }
    pose proof (rz_size_bound' n). destruct RB as [RB RM]. pose proof (Z.div_mod (rounded n) 8 ltac:(lia)) as DM. rewrite RM in DM. lia. }
  assert (R7 : rz_log n = 7).
  { unfold rz_log. destruct (Z.ltb_spec n 49); [lia|]. destruct (Z.ltb_spec n 97); [lia|]. destruct (Z.ltb_spec n 449); [lia|].
    destruct (Z.ltb_spec n 0xf81); [lia|]. destruct (Z.ltb_spec n 0x3f01); [lia|]. destruct (Z.ltb_spec n 0x7e01); [lia|].
    destruct (Z.ltb_spec n 0xfc01); [lia| reflexivity]. }
  assert (RZ : rz_size n = 2048) by (unfold rz_size; rewrite R7; reflexivity).
  assert (N2E : needed2 n = rounded n + 4096) by (unfold needed2, needed; rewrite FP0, RZ; lia).
  split; [exact LO|]. split; [exact RZ|]. split; [exact N2E|]. split; [lia|].
  unfold sec_map_size, round_up. rewrite N2E.
  pose proof (Z.div_mod (rounded n + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (rounded n + 4096 + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. rewrite Z.add_mod, Z_mod_mult, Z.add_0_l by lia. reflexivity.
Qed.

Section PopSec.
  Variable h : ahst.
  Variables (a n r' N' tf' : Z) (nb' bl' : list Z).
  Definition Ls := h_L h.
  Definition ms := sec_map_size n.
  Definition cks := s_chunks (h_sec h).
  Definition ncks := Z.of_nat (length cks).
  Definition nres := s_nres (h_sec h).
  Definition newsh : shdr := SH a ms (needed2 n).
  Definition newks : chunk := CK (a + 4096) n false 0 CHUNK_ALLOCATED.
  Definition sec_h : ahst := ltac2:(CDefT.buildp (gd_tbl_APopSec ()) "(?.$10.(11.Vh,)(12.Vh,)(13.Vh,)(14.$15.$16.(17.Vh,))(18.Vh,)(19.Vh,)(1:.(1;.$1<.$1=.(14.$1<.$1>.(1?.$1<.)))(20.+4000.Vr',))(21.VN',Vnb',Vtf',Vbl',)(22.Vh,)(23.Vh,)(20.+8.(20.+4000.Vr',))(;.(24.Vh,)(20.+2.Vn,))(25.Vh,))")
(* [comment removed for export] *).

  Hypothesis AWF : awf' h.
  Hypothesis NB : 0 <= n < 2^28.
  Hypothesis FP : from_primary n = false.
  (* [comment removed for export] *)
  Hypothesis A68 : 0x65f000 <= a.
  Hypothesis AAL : a mod 4096 = 0.
  Hypothesis ACE : a + ms <= ACEIL.
  Hypothesis ALH : a + ms <= 0x7fff7000 \/ kHighMemBeg <= a.
  (* [comment removed for export] *)
  Hypothesis OLDAP : Forall (fun k' => ck_end k' <= a \/ a + ms <= (if ck_prim k' then ck_ab k' else ck_map_beg k')) (h_chunks h).
  (* [comment removed for export] *)
  Hypothesis HR' : 0x4000 * r' = nres \/ (0x4000 * r' = nres + 0x4000 /\ ncks = nres).   (* [comment removed for export] *)
  Hypothesis ROOMP : ncks + 1 <= 0x4000 * r'.
  Hypothesis RMAX : 0x4000 * r' <= 2^20.
  Hypothesis NCKB : ncks + 0x4000 <= 2^20.     (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  #[using="NB FP"] Lemma SRF : ltac2:(CDefT.buildp (gd_tbl_APopSec ()) "(1.(2.+?<01.Vn,)(1.(5.$0.(9.Vn,)+800.)(1.(5.$0.(:.Vn,)(;.(<.Vn,)+1000.))(1.(1.(2.Vn,(<.Vn,))(2.(<.Vn,)(;.Vn,+7.)))(1.(1.(2.(;.(:.Vn,)+1000.)$26.)(3.$26.(;.(:.Vn,)+2000.)))(5.$0.(>.$26.+1000.)=))))))")
(* [comment removed for export] *).
  Proof. exact (sec_req_facts n NB FP). Qed.

  #[using="Type"] Lemma carved_sec : forall j, carved sec_h j = carved h j. Proof. intros j. reflexivity. Qed.
  #[using="Type"] Lemma chunk_set_sec : forall c, chunk_set sec_h c = chunk_set h c.
  Proof. intros c. unfold chunk_set. cbn [h_chunks sec_h h_L filter ck_prim newks andb]. reflexivity. Qed.
  #[using="Type"] Lemma owned_sec : forall c, owned sec_h c = owned h c.
  Proof. intros c. unfold owned, fa_set, cache_set, batch_set. rewrite chunk_set_sec. reflexivity. Qed.
  #[using="NB FP"] Lemma blocks_sec : blocks sec_h = (a + 4096 + 2048, n) :: blocks h.
  Proof.
    unfold blocks, live. cbn [h_chunks sec_h filter ck_st newks]. rewrite Z.eqb_refl. cbn [map ck_n newks].
    change (ck_user newks) with (a + 4096 + rz_size n). rewrite (proj1 (proj2 SRF)). reflexivity.
  Qed.
  
  (* [comment removed for export] *)
  #[using="N' tf' nb' bl' NB FP A68 OLDAP"] Lemma hdr_new_old_sec : forall k', In k' (h_chunks h) -> wf_chunk' h k' -> ck_hdr newks <> ck_hdr k'.
  Proof.
    intros k' Hk' W E. pose proof (hdr_in_slot h k' W) as [S1 S2]. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
    dpose SRF as (_ & RZ & N2 & RN & MSB & _).
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in E. cbn [ck_ab ck_n newks] in E. rewrite RZ in E.
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in S1, S2. lia.
  Qed.

  #[using="AWF NB FP A68 AAL ACE ALH OLDAP HR' ROOMP NCKB DN DTF DLN DWN DLB DWB DLNB DLBB"] Theorem awf'_sec : awf' sec_h.
  Proof.
    dpose AWF as (WL & WC & WR & (WKF & WKND & WKSEC) & WQ & WS & WD & WB & WBIG & WX & WG).
    dpose SRF as (NLO & RZ & N2 & RN & MSB & MSAL).
    ddestruct WS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8). fold cks nres in S1, S2, S3, S4, S5, S6, S7, S8. fold ncks in S1, S6.
    split; [exact WL|].
    split. { intros c' Hc'. pose proof (WC c' Hc') as X. cbn zeta in X |- *. cbn [h_cache h_cinit sec_h]. rewrite carved_sec. exact X. }
    split. { intros c' Hc'. pose proof (WR c' Hc') as X. cbn zeta in X |- *. cbn [h_reg sec_h]. rewrite carved_sec, owned_sec. exact X. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - constructor.
        + unfold wf_chunk'. cbn [ck_n ck_st ck_prim ck_cls ck_ab newks]. change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). cbn [s_chunks].
          split; [lia|]. split; [left; reflexivity|]. split; [symmetry; exact FP|].
          unfold ck_map_beg, ck_map_size. cbn [ck_ab ck_n newks]. replace (a + 4096 - 4096) with a by lia. fold ms.
          exists (length cks). split; [rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity|].
          split; [exact AAL|]. split; [lia|]. split; [exact ACE|]. unfold lowhigh. lia.
        + apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (W1 & W2 & W3 & W4).
          unfold wf_chunk'. rewrite carved_sec. change (h_L sec_h) with (h_L h). change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). cbn [s_chunks].
          split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
          destruct (ck_prim k'); [exact W4|]. ddestruct W4 as (i & Hi & REST). exists i. split; [| exact REST].
          rewrite nth_error_app1; [exact Hi|]. apply (proj1 (nth_error_Some _ _)). fold cks in Hi. rewrite Hi. discriminate.
      - cbn [map h_chunks sec_h ck_ab newks]. constructor; [| exact WKND].
        intros HIN. apply in_map_iff in HIN. ddestruct HIN as (k' & E & Hk').
        pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as W. pose proof (hdr_in_slot h k' W) as [T1 T2].
        unfold ck_hdr, ck_user, ck_rz, ck_map_beg, kChunkHeaderSize in *. pose proof (rz_size_bound' (ck_n k')).
        destruct (ck_prim k'); lia.
      - change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). cbn [s_chunks h_chunks sec_h]. intros i sh Hi.
        destruct (Nat.lt_ge_cases i (length cks)) as [LT|GE].
        + rewrite nth_error_app1 in Hi by exact LT. ddestruct (WKSEC i sh Hi) as (k' & Hk' & REST). exists k'. split; [right; exact Hk'| exact REST].
        + rewrite nth_error_app2 in Hi by exact GE. destruct (i - length cks)%nat as [|j] eqn:EJ; [| cbn in Hi; destruct j; discriminate Hi].
          cbn in Hi. injection Hi as <-. exists newks. split; [left; reflexivity|]. split; [reflexivity|].
          unfold ck_map_beg, ck_map_size. cbn [ck_ab ck_n newks s_map_beg s_map_size newsh]. fold ms. split; lia. }
    split. { (* [comment removed for export] *)
      assert (FB : forall b, wf_batch h b -> wf_batch sec_h b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. rewrite carved_sec. change (h_L sec_h) with (h_L h).
        cbn [h_chunks sec_h]. split; [exact B1|]. split; [| split].
        - rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. cbn [find].
          destruct (Z.eqb_spec (ck_hdr newks) e) as [E|NEQ]; [| reflexivity].
          exfalso. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & _ & Hh). apply (hdr_new_old_sec k0 Hk0 (proj1 (Forall_forall _ _) WKF k0 Hk0)). congruence.
        - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & R). exists k0. split; [right; exact Hk0| exact R].
        - exact B4. }
      ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND|]]].
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) T1 b Hb).
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - intros k0 [<-|Hk0] ST; [cbv in ST; discriminate ST|]. exact (UQ k0 Hk0 ST). }
    split. { (* [comment removed for export] *)
      unfold wf_sec. change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). cbn [s_chunks s_nres h_pa_committed sec_h].
      rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. fold ncks. change (Z.of_nat 1) with 1. unfold kPtrArrayChunks in *.
      split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
      split.
      - rewrite map_app. cbn [map s_map_beg newsh]. apply NoDup_app; [exact S7| constructor; [intros []| constructor]|].
        intros x Hx [<-|[]]. apply in_map_iff in Hx. ddestruct Hx as (sh & E & Hsh).
        destruct (In_nth_error _ _ Hsh) as [i Hi]. ddestruct (WKSEC i sh Hi) as (k' & Hk' & PK & EB & _).
        pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP. rewrite PK in AP.
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (_ & _ & _ & W4). rewrite PK in W4. ddestruct W4 as (_ & _ & _ & Bk & _ & LHk).
        unfold ck_end in AP. rewrite PK in AP. unfold ck_map_size, sec_map_size, round_up in *. rewrite EB, E in AP.
        pose proof (Z.div_mod (needed2 (ck_n k') + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed2 (ck_n k') + 4096 - 1) 4096 ltac:(lia)).
        assert (0 <= needed2 (ck_n k')).
        { unfold needed2, needed, rounded, round_up. pose proof (rz_size_bound' (ck_n k')).
          pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(lia)). destruct (from_primary (ck_n k')); lia. }
        fold ms in AP. lia.
      - apply Forall_app. split; [exact S8|]. constructor; [| constructor]. cbn [s_map_size s_size newsh]. fold ms. split; [exact MSAL|]. split; [lia|].
        unfold needed2, needed. rewrite FP, RZ. lia. }
    split. { (* [comment removed for export] *)
      ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep sec_h d_n d_nb s_total d_bl h_havol]. unfold kDepotNodesL2 in *.
      repeat split; try assumption; lia. }
    split. { (* [comment removed for export] *)
      ddestruct WB as (F1 & F2 & F3). split; [exact F1|]. cbn [h_havol sec_h].
      unfold SECC in *. change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). change (h_acct sec_h) with (h_acct h). cbn [s_chunks]. fold cks in F3.
      set (GH := sum (map sec_cost_ghost (a_sech (h_acct h)))) in *.
      rewrite map_app, sum_app. set (OLD := sum (map sec_cost_live cks)) in *.
      assert (NEWC : sum (map sec_cost_live [newsh]) <= 2 * n); [| split; lia].
      cbn [map sum fold_right]. unfold sec_cost_live, npg_shadow. cbn [s_map_size newsh].
      pose proof (Z.div_mod ms 32768 ltac:(lia)). pose proof (Z.mod_pos_bound ms 32768 ltac:(lia)). lia. }
    split. { (* [comment removed for export] *)
      ddestruct WBIG as (BG1 & BG2 & BG3). split; [| split; [exact BG2| exact BG3]].
      change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). cbn [s_chunks]. apply Forall_app. split; [exact BG1|].
      constructor; [| constructor]. cbn [s_map_size newsh]. fold ms. lia. }
    split. { (* [comment removed for export] *)
      ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). split; [| split; [exact X2| split; [exact X3|]]]; [intros c' Hc'; rewrite carved_sec; exact (X1 c' Hc')|].
      change (h_sec sec_h) with (SE (cks ++ [newsh]) (0x4000 * r')). change (h_havol sec_h) with (h_havol h + 2 * n). cbn [s_chunks s_nres].
      fold cks nres in X4, X5. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. fold ncks. fold ncks in X4. change (Z.of_nat 1) with 1.
      unfold kPtrArrayChunks in *.
      split; [clear - X4 X5 NLO HR' ROOMP S1 NB; lia|]. split; [clear - X4 X5 NLO HR' ROOMP S1 NB; lia|].
      (* [comment removed for export] *)
      split; [exact X6|]. split; [rewrite (csum_epi_frame h sec_h); [exact X7| intros; reflexivity| intros; reflexivity]|].
      (* [comment removed for export] *)
      split; [rewrite carved_sec; exact X8|]. rewrite blocks_sec, cnt24_cons. cbn [snd]. rewrite (secondary_not_win n FP). clear - X9. lia. }
    exact WG.
  Qed.
End PopSec.

End ARUN_1.
