(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg ShapeLaws SpinAlg Hoare AgentLib SymDrive SymDriveX RefMemcpyLib
  DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0Drv_defs_b Ba0RegionPoisoned_b Ba0DiagWritev_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation rom := (seg_rom ASEGS).

(* [comment removed for export] *)
Definition WV_KEEP : list reg := [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%bv.

Lemma wv_keep_cs : forall r, In r WV_KEEP -> In r callee_saved.
Proof. intros r Hr. unfold WV_KEEP in Hr. unfold callee_saved. cbn [In] in *. tauto. Qed.
Lemma wv_keep_not : forall r, In r WV_KEEP -> ~ In r [1; 18; 19; 20; 22]%bv.
Proof.
  intros r Hr. unfold WV_KEEP in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hr.
Qed.
Lemma wv_keep_of : forall Lr R R', keeps_but Lr R R' -> incl Lr [1; 18; 19; 20; 22]%bv -> forall r, In r WV_KEEP -> getr R' r = getr R r.
Proof. intros Lr R R' KB Hi r Hr. apply KB; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (Hi r X)). Qed.

Lemma sbm_fds' : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.

Lemma rdn_skipn_Z : forall (M : word -> option byte) a n bs k,
  rdn ASEGS M (Z_to_bv 64 a) (Z.to_nat n) = Some bs -> 0 <= k <= n -> 0 <= a ->
  rdn ASEGS M (Z_to_bv 64 (a + k)) (Z.to_nat (n - k)) = Some (skipn (Z.to_nat k) bs).
Proof.
  intros M a n bs k Hr Hk Ha.
  pose proof (SeqExec.rdn_skipn ASEGS M (Z.to_nat n) (Z_to_bv 64 a) bs (Z.to_nat k) Hr ltac:(lia)) as X.
  replace (Z.to_nat (n - k)) with (Z.to_nat n - Z.to_nat k)%nat by lia.
  replace (Z_to_bv 64 (a + k)) with (Z_to_bv 64 a + nat_to_word (Z.to_nat k))%bv; [exact X|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. rewrite Z2Nat.id by lia.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac cs_in := unfold callee_saved; cbn [In]; repeat first [left; reflexivity | right].
Lemma cs_not10 : forall r : reg, In r callee_saved -> r <> 10%bv.
Proof. intros r Hr ->. unfold callee_saved in Hr. cbn [In] in Hr. repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]). exact Hr. Qed.
Lemma incl_body : incl ([18; 20; 22]%bv : list reg) [1; 18; 19; 20; 22]%bv.
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Lemma incl_ret : incl ([1; 19]%bv : list reg) [1; 18; 19; 20; 22]%bv.
Proof. intros r Hr. cbn [In] in *. tauto. Qed.
Ltac cs_out := let X := fresh in intros X; cbn [In] in X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.

(* [comment removed for export] *)
Lemma pcE_af0 : v_addi (Z_to_bv 64 0x120258) 4 = (1180252%bv : word).  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b78 : v_addi (Z_to_bv 64 0x1202e0) 4 = (1180388%bv : word).  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_af8 : (1180260%bv : word) = Z_to_bv 64 0x120264.  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b84 : (1180400%bv : word) = Z_to_bv 64 0x1202f0.  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma pcE_b74 : (1180384%bv : word) = Z_to_bv 64 0x1202e0.  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rdn_frame_w : forall (MV MV' : word -> option byte) a (n : nat) bs,
  rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> MV' x = MV x) -> rdn ASEGS MV' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros MV MV' a n bs Hr Ha Hn FR. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite (u64_lit a) by lia. apply FR. rewrite u64_lit by lia. lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Section Loop.
  Variable H : word -> bool.
  Variable A : list (Z * Z).
  Hypothesis HH : H_off_segments ASEGS H.
  Variable lazy : list (word * word).
  Hypothesis HLC : lazy_cover H lazy A.
  Hypothesis HAwf : A_wf A.
  Variables f fd : Z.
  Hypothesis Hfd : 0 < fd < 2 ^ 31.
  Variables qlo qhi : Z.          (* [comment removed for export] *)
  Hypothesis Hq : 0 <= qlo /\ qlo <= qhi /\ qhi + 16 <= 2 ^ 47.
  Hypothesis Hf : 0 <= f /\ (f + 124 <= qlo \/ qhi + 16 <= f + 120) /\ f + 124 < 2 ^ 63.
  Hypothesis NLq : forall x, qlo <= x < qhi -> page_in_ranges (page_base_of x) lazy = false.
  Variable K : TSet.
  Hypothesis HK0 : K [].

  (* [comment removed for export] *)
  #[using="HH HLC HAwf"] Lemma msteps_vis : forall R (pc : word) M R' (pc' : word) MV' (model : Model) T,
    m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
    msteps ASEGS (mkst R pc (mrestrict H M) rom) (mkst R' pc' MV' rom) ->
    (forall a : word, mrestrict H M a <> None -> MV' a <> None) ->
    (forall M' (model' : Model), MInv A model' -> same_but_materialized model model' ->
        mrestrict H M' = MV' ->
        (forall a : word, MV' a = mrestrict H M a -> M' a = M a) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        srealizes ASEGS scfg (mkCfg (mkst R' pc' M' rom) model') T) ->
    srealizes ASEGS scfg (mkCfg (mkst R pc M rom) model) T.
  Proof.
    intros R pc M R' pc' MV' model T HL HI Hh MS GR KONT.
    apply (rz_msteps_lz ASEGS scfg H A R pc M R' pc' MV' model T HH asegs_wx ltac:(rewrite HL; exact HLC) HAwf HI Hh MS).
    intros model' HI' SBM VIS. apply (KONT _ model' HI' SBM VIS).
    - intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [reflexivity|]. rewrite Ha. unfold mrestrict. rewrite E. reflexivity.
    - intros a Ha. unfold munrestrict. destruct (H a) eqn:E; [exact Ha|]. apply GR. unfold mrestrict. rewrite E. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Definition wv_pc (s : bool) : word := if s then Z_to_bv 64 0x120258 else Z_to_bv 64 0x1202e0.
  Definition wv_regs (s : bool) (R : bvmap 5 word) (q c rem : Z) : Prop :=
    getr R 17%bv = Z_to_bv 64 66 /\ getr R 10%bv = Z_to_bv 64 fd /\ getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 c
    /\ getr R 9%bv = Z_to_bv 64 f /\ getr R 18%bv = Z_to_bv 64 c /\ getr R 22%bv = Z_to_bv 64 rem
    /\ getr R (if s then 19%bv else 20%bv) = Z_to_bv 64 q.

  (* [comment removed for export] *)
  Definition wv_buf (MV : word -> option byte) (b l : Z) (bs : list byte) : Prop :=
    0 <= b /\ 0 <= l /\ b + l <= 2 ^ 47 /\ (l = 0 \/ b + l <= qlo \/ qhi <= b)
    /\ rdn ASEGS MV (Z_to_bv 64 b) (Z.to_nat l) = Some bs
    /\ (forall x, b <= x < b + l -> page_in_ranges (page_base_of x) lazy = false).

  (* [comment removed for export] *)
  Definition wv_iov (MV : word -> option byte) (q c b1 l1 b2 l2 : Z) (bs1 bs2 : list byte) : Prop :=
    qlo <= q /\ q + 16 * c <= qhi /\ (c = 1 \/ c = 2)
    /\ rdn ASEGS MV (Z_to_bv 64 q) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b1))
    /\ rdn ASEGS MV (Z_to_bv 64 (q + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l1))
    /\ store_ok ASEGS MV (Z_to_bv 64 q) (Z.to_nat (16 * c)) = true
    /\ wv_buf MV b1 l1 bs1
    /\ (c = 1 -> l2 = 0 /\ bs2 = [])
    /\ (c = 2 -> rdn ASEGS MV (Z_to_bv 64 (q + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b2))
                 /\ rdn ASEGS MV (Z_to_bv 64 (q + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 l2))
                 /\ wv_buf MV b2 l2 bs2 /\ 1 <= l1 + l2).

  #[using="f Hq Hf"] Lemma wv_buf_tr : forall MV MV' b l bs, wv_buf MV b l bs ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV' (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) -> wv_buf MV' b l bs.
  Proof.
    intros MV MV' b l bs (B1 & B2 & B3 & B4 & B5 & B6) FR. repeat split; try assumption.
    rewrite <- B5. apply rdn_agree. intros j Hj. rewrite u64_lit by lia. apply FR; lia.
  Qed.

  #[using="f Hq Hf"] Lemma wv_buf_skip : forall MV b l bs k, wv_buf MV b l bs -> 0 <= k <= l -> wv_buf MV (b + k) (l - k) (skipn (Z.to_nat k) bs).
  Proof.
    intros MV b l bs k (B1 & B2 & B3 & B4 & B5 & B6) Hk. repeat split; try lia.
    - exact (rdn_skipn_Z MV b l bs k B5 Hk B1).
    - intros x Hx. apply B6. lia.
  Qed.

  Definition wv_done (R : bvmap 5 word) (M : word -> option byte) (model : Model) : Prop :=
    forall R' M' (model' : Model),
      MInv A model' -> same_but_materialized model model' ->
      (forall r, In r WV_KEEP -> getr R' r = getr R r) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> mrestrict H M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      (forall a : word, mrestrict H M a <> None -> mrestrict H M' a <> None) ->
      srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 0x120264) M' rom) model') K.

  #[using="Type"] Lemma wv_done_tr : forall R M model R1 M1 model1, wv_done R M model ->
    same_but_materialized model model1 ->
    (forall r, In r WV_KEEP -> getr R1 r = getr R r) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> mrestrict H M1 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M1 a <> None) ->
    (forall a : word, mrestrict H M a <> None -> mrestrict H M1 a <> None) ->
    wv_done R1 M1 model1.
  Proof.
    intros R M model R1 M1 model1 D SBM KR F1 F2 G1 G2 R' M' model' MI SBM' KR' F1' F2' G1' G2'.
    apply (D R' M' model' MI (same_but_materialized_trans _ _ _ SBM SBM')).
    - intros r Hr. rewrite (KR' r Hr). exact (KR r Hr).
    - intros a Ha Hn. rewrite (F1' a Ha Hn). exact (F1 a Ha Hn).
    - intros a Ha Hn. rewrite (F2' a Ha Hn). exact (F2 a Ha Hn).
    - intros a Ha. exact (G1' a (G1 a Ha)).
    - intros a Ha. exact (G2' a (G2 a Ha)).
  Qed.

  #[using="Type"] Lemma W64_out : forall (M : word -> option byte) a v (x : word), 0 <= a -> a + 8 <= 2 ^ 64 -> ~ (a <= bv_unsigned x < a + 8) -> W64 M a v x = M x.
  Proof.
    intros M a v x Ha Hb Hn. unfold W64. destruct (Z_lt_le_dec (bv_unsigned x) a) as [Lt|Ge].
    - apply wbytes_below; [rewrite u64_lit by lia; rewrite length_N_to_le_bytes; lia | rewrite u64_lit by lia; exact Lt].
    - apply wbytes_above. rewrite u64_lit by lia. rewrite length_N_to_le_bytes. lia.
  Qed.
  #[using="Type"] Lemma W64_hit : forall (M : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> rdn ASEGS (W64 M a v) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
  Proof. intros M a v Ha Hb. unfold W64. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
  #[using="Type"] Lemma W64_rdn_out : forall (M : word -> option byte) a v x (n : nat) bs, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
    (x + Z.of_nat n <= a \/ a + 8 <= x) -> rdn ASEGS M (Z_to_bv 64 x) n = Some bs -> rdn ASEGS (W64 M a v) (Z_to_bv 64 x) n = Some bs.
  Proof.
    intros M a v x n bs Ha Hb Hx Hn Hd Hr. rewrite <- Hr. apply rdn_agree. intros j Hj. rewrite u64_lit by lia.
    apply W64_out; [exact Ha | exact Hb |]. rewrite u64_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition wv_loop_stmt (n : nat) : Prop :=
    forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2,
      (length (bs1 ++ bs2) <= n)%nat ->
      m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
      fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
      wv_regs s R q c (l1 + l2) ->
      wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
      l1 + l2 <= 2 ^ 30 ->
      rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
      wv_done R M model ->
      srealizes ASEGS scfg (mkCfg (mkst R (wv_pc s) M rom) model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).

  #[using="Type"] Lemma wv_buf_len : forall MV b l bs, wv_buf MV b l bs -> length bs = Z.to_nat l.
  Proof. intros MV b l bs (_ & _ & _ & _ & B5 & _). exact (rdn_length _ _ _ _ _ B5). Qed.

  (* [comment removed for export] *)
  #[using="HH HLC HAwf Hfd Hq Hf HK0"] Lemma wv_after : forall (n : nat), (forall m, (m < n)%nat -> wv_loop_stmt m) ->
    forall (s : bool) R M (model : Model) q c b1 l1 b2 l2 bs1 bs2 (k : nat),
      (length (bs1 ++ bs2) <= n)%nat -> (k <= length (bs1 ++ bs2))%nat -> (1 <= k)%nat \/ l1 + l2 = 0 ->
      m_vm_lazy model = lazy -> MInv A model -> m_halted model = None ->
      fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
      wv_regs s R q c (l1 + l2) ->
      wv_iov (mrestrict H M) q c b1 l1 b2 l2 bs1 bs2 ->
      l1 + l2 <= 2 ^ 30 ->
      rdn ASEGS (mrestrict H M) (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
      wv_done R M model ->
      srealizes ASEGS scfg (mkCfg (mkst (regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))) (v_addi (wv_pc s) 4) M rom) model)
                (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K).
  Proof.
    intros n IH s R M model q c b1 l1 b2 l2 bs1 bs2 k Hn Hk Hk1 HL HI Hh FD RG IOV H30 HFD DONE.
    destruct RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
    destruct IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
    pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
    assert (LEN2 : length bs2 = Z.to_nat l2 /\ 0 <= l2).
    { destruct Hc as [->| ->]; [destruct (HC1 eq_refl) as (-> & ->); split; [reflexivity | lia]|].
      destruct (HC2 eq_refl) as (_ & _ & BUF2 & _). split; [exact (wv_buf_len _ _ _ _ BUF2) | exact (proj1 (proj2 BUF2))]. }
    destruct LEN2 as (LEN2 & Hl2). pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _).
    assert (LEN : Z.of_nat (length (bs1 ++ bs2)) = l1 + l2) by (rewrite length_app, LEN1, LEN2; lia).
    set (R1 := regupd R 10%bv (Z_to_bv 64 (Z.of_nat k))).
    assert (R1k : getr R1 10%bv = Z_to_bv 64 (Z.of_nat k)) by (unfold R1; apply getr_same; intros X; discriminate X).
    assert (R1o : forall r : reg, r <> 10%bv -> getr R1 r = getr R r) by (intros r Hr; unfold R1; apply getr_other; exact Hr).
    assert (Hq' : 0 <= q /\ q + 32 < 2 ^ 63) by lia.
    (* [comment removed for export] *)
    assert (RET : exists R2, msteps ASEGS (mkst R1 (v_addi (wv_pc s) 4) (mrestrict H M) rom)
                     (mkst R2 (if Z.eqb (Z.of_nat k) (l1 + l2) then Z_to_bv 64 0x120264 else Z_to_bv 64 0x1202f0) (mrestrict H M) rom)
                   /\ getr R2 10%bv = Z_to_bv 64 (Z.of_nat k) /\ getr R2 19%bv = Z_to_bv 64 q
                   /\ (forall r, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r)).
    { rewrite <- pcE_af8, <- pcE_b84. destruct s; cbn [wv_pc] in *; [rewrite pcE_af0 | rewrite pcE_b78].
      - destruct (wv_ret_A (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22))
          as (R2 & MS & V10 & KB).
        exists R2. split; [exact MS|]. split; [exact V10|]. split.
        + rewrite (KB 19%bv ltac:(cs_in) ltac:(cs_out)). rewrite R1o by (intros X; discriminate X). exact Gq.
        + intros r Hr Hn'. rewrite (KB r Hr) by (intros X; apply Hn'; cbn [In] in *; tauto). apply R1o. exact (cs_not10 r Hr).
      - destruct (wv_ret_B (mrestrict H M) rom q (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' R1 R1k ltac:(rewrite R1o by (intros X; discriminate X); exact G22)
                    ltac:(rewrite R1o by (intros X; discriminate X); exact Gq)) as (R2 & MS & V10 & V19 & KB).
        exists R2. split; [exact MS|]. split; [exact V10|]. split; [exact V19|].
        intros r Hr Hn'. rewrite (KB r Hr Hn'). apply R1o. exact (cs_not10 r Hr). }
    destruct RET as (R2 & MS2 & V10 & V19 & KB2).
    apply (msteps_vis R1 _ M R2 _ (mrestrict H M) model _ HL HI Hh MS2 (fun a Ha => Ha)).
    intros M2 model2 HI2 SBM2 VIS2 FRM2 GRM2.
    assert (EQ2 : forall a, M2 a = M a) by (intros a; apply FRM2; reflexivity).
    assert (DONE2 : wv_done R2 M2 model2).
    { apply (wv_done_tr R M model R2 M2 model2 DONE SBM2).
      - intros r Hr. apply KB2; [exact (wv_keep_cs r Hr)|]. intros X. exact (wv_keep_not r Hr (incl_ret r X)).
      - intros a _ _. apply EQ2.
      - intros a _ _. rewrite VIS2. reflexivity.
      - exact GRM2.
      - intros a Ha. rewrite VIS2. exact Ha. }
    assert (HL2 : m_vm_lazy model2 = lazy) by (rewrite (sbm_lazy_eq _ _ SBM2); exact HL).
    assert (Hh2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Hh).
    assert (FD2 : fd_lookup (m_fds model2) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) by (rewrite (sbm_fds' _ _ SBM2); exact FD).
    destruct (Z.eqb_spec (Z.of_nat k) (l1 + l2)) as [E|NE].
    - (* [comment removed for export] *)
      rewrite skipn_all2 by lia. cbn [map].
      apply (srz_conseq ASEGS scfg _ K); [|apply t_eq_sym; apply t_emit_nil_eq; exact HK0].
      apply (DONE2 R2 M2 model2 HI2 (same_but_materialized_refl _)); auto.
    - (* [comment removed for export] *)
      assert (Hk1' : (1 <= k)%nat) by (destruct Hk1 as [?|Z0]; [assumption | lia]).
      assert (NPOS : (0 < n)%nat) by lia.
      assert (R2o : forall r : reg, In r callee_saved -> ~ In r [1; 19]%bv -> getr R2 r = getr R r) by exact KB2.
      assert (V18 : getr R2 18%bv = Z_to_bv 64 c) by (rewrite (R2o 18%bv ltac:(cs_in) ltac:(cs_out)); exact G18).
      assert (V22 : getr R2 22%bv = Z_to_bv 64 (l1 + l2)) by (rewrite (R2o 22%bv ltac:(cs_in) ltac:(cs_out)); exact G22).
      assert (V9 : getr R2 9%bv = Z_to_bv 64 f) by (rewrite (R2o 9%bv ltac:(cs_in) ltac:(cs_out)); exact G9).
      assert (Hf' : 0 <= f /\ (f + 124 <= q \/ q + 32 <= f + 120) /\ f + 124 < 2 ^ 63) by lia.
      destruct (Z_le_gt_dec (Z.of_nat k) l1) as [LO|HI'].
      + (* [comment removed for export] *)
        assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 q) 16 = true).
        { apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * c))); [rewrite u64_lit by lia; lia | exact SOK | lia | rewrite u64_lit by lia; lia]. }
        destruct (wv_body_lo (mrestrict H M) rom f q c (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' b1 l1 fd Hf' ltac:(lia) HFD ltac:(lia) ltac:(lia)
                    R2 ltac:(lia) Hb1 ltac:(lia) C0 C8 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
          as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
        rewrite pcE_b84, pcE_b74 in MS3.
        set (MV3 := W64 (W64 (mrestrict H M) q (b1 + Z.of_nat k)) (q + 8) (l1 - Z.of_nat k)) in *.
        assert (FR3f : forall x : word, ~ (q <= bv_unsigned x < q + 16) -> MV3 x = mrestrict H M x).
        { intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
        assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
        { intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
        assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
        { intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
        rewrite <- VIS2 in MS3. 
        apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
        intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
        assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
        replace (skipn k (bs1 ++ bs2)) with (skipn k bs1 ++ bs2).
        2:{ rewrite skipn_app. replace (k - length bs1)%nat with 0%nat by lia. reflexivity. }
        replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia.
        apply (IHn false R3 M3 model3 q c (b1 + Z.of_nat k) (l1 - Z.of_nat k) b2 l2).
        * rewrite length_app, length_skipn, Nat2Z.id. rewrite length_app in Hn. lia.
        * rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
        * exact HI3.
        * rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
        * rewrite (sbm_fds' _ _ SBM3); exact FD2.
        * unfold wv_regs. replace (l1 - Z.of_nat k + l2) with (l1 + l2 - Z.of_nat k) by ring. repeat split; try assumption.
          rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
        * rewrite VIS3. unfold wv_iov. split; [exact Q1|]. split; [exact Q2|]. split; [exact Hc|].
          split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
          split; [unfold MV3; apply W64_hit; lia|].
          split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK]|].
          split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF1 | lia] | exact FR3]|].
          split; [exact HC1|].
          intros Hc2. destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). 
          split; [apply (rdn_frame_w _ MV3 _ _ _ C16); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
          split; [apply (rdn_frame_w _ MV3 _ _ _ C24); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia]|].
          split; [exact (wv_buf_tr _ MV3 _ _ _ BUF2 FR3) | lia].
        * lia.
        * rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
        * apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
          -- exact (wv_keep_of _ R2 R3 KB3 incl_body).
          -- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
          -- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
          -- exact GRM3.
          -- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
      + (* [comment removed for export] *)
        assert (Hc2 : c = 2) by (destruct Hc as [Hc|Hc]; [destruct (HC1 Hc) as (Z0 & _); lia | exact Hc]).
        destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). pose proof BUF2 as (Hb2 & _ & Hb2l & _). subst c.
        assert (SOK16 : store_ok ASEGS (mrestrict H M) (Z_to_bv 64 (q + 16)) 16 = true).
        { apply (store_ok_sub ASEGS _ (Z_to_bv 64 q) _ (Z.to_nat (16 * 2))); [rewrite u64_lit by lia; lia | exact SOK | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia]. }
        destruct (wv_body_hi (mrestrict H M) rom f q 2 (l1 + l2) (Z.of_nat k) ltac:(lia) ltac:(lia) Hq' l1 fd Hf' ltac:(lia) HFD b2 l2
                    R2 eq_refl ltac:(lia) ltac:(lia) Hb2 ltac:(lia) C8 C16 C24 SOK16 V10 V19 V18 V22 V9 ltac:(lia))
          as (R3 & MS3 & W17 & W10 & W11 & W12 & W20 & W18 & W22 & KB3).
        rewrite pcE_b84, pcE_b74 in MS3.
        set (d := Z.of_nat k - l1) in *.
        set (MV3 := W64 (W64 (mrestrict H M) (q + 16) (b2 + d)) (q + 24) (l2 - d)) in *.
        assert (FR3f : forall x : word, ~ (q + 16 <= bv_unsigned x < q + 32) -> MV3 x = mrestrict H M x).
        { intros x Hx. unfold MV3. rewrite !W64_out; [reflexivity | | | | | |]; lia. }
        assert (FR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (qlo <= a < qhi) -> MV3 (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a)).
        { intros a Ha Hna. apply FR3f. rewrite u64_lit by lia. lia. }
        assert (GR3 : forall a : word, mrestrict H M a <> None -> MV3 a <> None).
        { intros a Ha. unfold MV3, W64. apply wbytes_grows. apply wbytes_grows. exact Ha. }
        rewrite <- VIS2 in MS3.
        apply (msteps_vis R2 _ M2 R3 _ MV3 model2 _ HL2 HI2 Hh2 MS3 ltac:(rewrite VIS2; exact GR3)).
        intros M3 model3 HI3 SBM3 VIS3 FRM3 GRM3.
        assert (IHn : wv_loop_stmt (n - 1)) by (apply IH; lia).
        replace (skipn k (bs1 ++ bs2)) with (skipn (Z.to_nat d) bs2 ++ []).
        2:{ assert (E1 : skipn k bs1 = []) by (apply skipn_all2; lia). rewrite app_nil_r, skipn_app, E1. cbn [app]. f_equal. unfold d. lia. }
        apply (IHn false R3 M3 model3 (q + 16) 1 (b2 + d) (l2 - d) 0 0).
        * rewrite app_nil_r, length_skipn. rewrite length_app in Hn. unfold d. lia.
        * rewrite (sbm_lazy_eq _ _ SBM3); exact HL2.
        * exact HI3.
        * rewrite (sbm_halted_eq _ _ SBM3); exact Hh2.
        * rewrite (sbm_fds' _ _ SBM3); exact FD2.
        * unfold wv_regs. replace (l2 - d + 0) with (l1 + l2 - Z.of_nat k) by (unfold d; ring). repeat split; try assumption.
          rewrite (KB3 9%bv ltac:(cs_in) ltac:(cs_out)). exact V9.
        * rewrite VIS3. unfold wv_iov. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
          split; [unfold MV3; apply W64_rdn_out; [lia | lia | lia | cbn; lia | cbn; lia | apply W64_hit; lia]|].
          split; [replace (q + 16 + 8) with (q + 24) by ring; unfold MV3; apply W64_hit; lia|].
          split; [apply (store_ok_mono ASEGS _ (mrestrict H M) MV3); [exact GR3 | exact SOK16]|].
          split; [apply (wv_buf_tr (mrestrict H M) MV3); [apply wv_buf_skip; [exact BUF2 | unfold d; lia] | exact FR3]|].
          split; [intros _; split; reflexivity | intros X; discriminate X].
        * unfold d. lia.
        * rewrite VIS3. apply (rdn_frame_w _ MV3 _ _ _ HFD); [lia | cbn; lia | intros x Hx; apply FR3f; cbn in Hx; lia].
        * apply (wv_done_tr R2 M2 model2 R3 M3 model3 DONE2 SBM3).
          -- exact (wv_keep_of _ R2 R3 KB3 incl_body).
          -- intros a Ha Hna. apply FRM3. rewrite VIS2. apply FR3; assumption.
          -- intros a Ha Hna. rewrite VIS3, VIS2. apply FR3; assumption.
          -- exact GRM3.
          -- intros a Ha. rewrite VIS3. apply GR3. rewrite <- VIS2. exact Ha.
  Qed.

  #[using="Type"] Lemma fetch_wv_pc : forall s, fetch_word ASEGS (wv_pc s) = Some ECALLW.
  Proof. intros [|]; vm_compute; reflexivity. Qed.

  #[using="HH HLC HAwf Hfd Hq Hf NLq HK0"] Theorem wv_loop : forall n, wv_loop_stmt n.
  Proof.
    intros n. induction n as [n IH] using lt_wf_ind.
    intros s R M model q c b1 l1 b2 l2 bs1 bs2 Hn HL HI Hh FD RG IOV H30 HFD DONE.
    pose proof RG as (G17 & G10 & G11 & G12 & G9 & G18 & G22 & Gq).
    pose proof IOV as (Q1 & Q2 & Hc & C0 & C8 & SOK & BUF1 & HC1 & HC2).
    pose proof BUF1 as (Hb1 & Hl1 & Hb1l & _ & RD1 & NL1).
    pose proof (wv_buf_len _ _ _ _ BUF1) as LEN1.
    assert (NLI : forall m, m <= qhi - q -> nolazy_rng (m_vm_lazy model) (Z_to_bv 64 q) m).
    { intros m Hm j Hj. rewrite HL, u64_lit by lia. apply NLq. lia. }
    assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply u64_lit; lia).
    assert (C0f := rdn_of_mrestrict ASEGS H M HH _ _ _ C0). assert (C8f := rdn_of_mrestrict ASEGS H M HH _ _ _ C8).
    assert (RD1f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD1).
    destruct Hc as [Hc1|Hc2].
    - (* [comment removed for export] *)
      destruct (HC1 Hc1) as (-> & ->). subst c. rewrite app_nil_r in *. rewrite Z.add_0_r in *.
      destruct (Z.eq_dec l1 0) as [Z0|NZ].
      + (* [comment removed for export] *)
        subst l1. assert (bs1 = []) by (apply length_zero_iff_nil; exact LEN1). subst bs1.
        eapply (rz_writev1_zero_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1));
          [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
          | exact C0f | rewrite UQ; exact C8f | rewrite UQ; unfold TASK_SIZE; lia | rewrite u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia |].
        pose proof (wv_after n IH s R M model q 1 b1 0 b2 0 [] [] 0%nat) as X. cbn [app skipn Z.of_nat] in X. rewrite Z.add_0_r in X.
        apply X; try assumption; try lia.
      + eapply (rz_writev1_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 K);
          [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
          | exact C0f | rewrite UQ; exact C8f | unfold word_to_nat; rewrite u64_lit by lia; exact RD1f
          | rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | apply NLI; lia
          | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia | rewrite u64_lit by lia; lia | rewrite u64_lit by lia; lia | exact HK0 |].
        intros k Hk1 Hk2.
        pose proof (wv_after n IH s R M model q 1 b1 l1 b2 0 bs1 [] k) as X. rewrite app_nil_r, Z.add_0_r in X.
        apply X; try assumption; try lia.
    - (* [comment removed for export] *)
      destruct (HC2 Hc2) as (C16 & C24 & BUF2 & TOT). subst c.
      pose proof BUF2 as (Hb2 & Hl2 & Hb2l & _ & RD2 & NL2).
      assert (C16f := rdn_of_mrestrict ASEGS H M HH _ _ _ C16). assert (C24f := rdn_of_mrestrict ASEGS H M HH _ _ _ C24).
      assert (RD2f := rdn_of_mrestrict ASEGS H M HH _ _ _ RD2).
      eapply (rz_writev2_wall_lz ASEGS scfg R (wv_pc s) M model ECALLW fd (Z_to_bv 64 q) (Z_to_bv 64 b1) (Z_to_bv 64 l1) (Z_to_bv 64 b2) (Z_to_bv 64 l2) bs1 bs2 K);
        [apply fetch_wv_pc | apply is_ecall_ECALLW | exact Hh | exact FD | exact Hfd | exact G17 | exact G10 | exact G11 | exact G12
        | exact C0f | rewrite UQ; exact C8f | rewrite UQ; exact C16f | rewrite UQ; exact C24f
        | unfold word_to_nat; rewrite u64_lit by lia; exact RD1f | unfold word_to_nat; rewrite u64_lit by lia; exact RD2f
        | rewrite UQ; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia | rewrite !u64_lit by lia; unfold TASK_SIZE; lia
        | apply NLI; lia
        | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL1; lia
        | intros j Hj; rewrite HL; rewrite !u64_lit in * by lia; apply NL2; lia
        | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; lia | exact HK0 |].
      intros k Hk1 Hk2.
      apply (wv_after n IH s R M model q 2 b1 l1 b2 l2 bs1 bs2 k); try assumption. left; exact Hk1.
  Qed.
End Loop.
End FPX_1.
