(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_hkit3A Atp_hkit5A Atp_hkit6A Atp_pidwA Atp_h_defsA Atp_h_vkitA Atp_pidiA Atp_pid1A Atp_pid0A Atp_pdtorA RT_rtf Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA El_phasesA El_frontA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma el_els_view : forall D dd e, In e (atp_elsA D dd) -> e = (0, 0) \/ (exists o k : nat, e = (D + Z.of_nat o, Z.of_nat k) /\ (o + k <= length dd)%nat).
Proof.
  intros D dd e Hin. unfold atp_elsA in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply in_map_iff in Hin. destruct Hin as ([o k] & <- & Hin). right. exists o, k. split; [reflexivity| exact (poffs_bound dd (o, k) Hin)].
  - left. apply repeat_spec in Hin. exact Hin.
Qed.

Lemma el_els_two : forall d bs, exists rest, el_elsA d bs = el_s0A d bs :: el_s1A d bs :: rest /\ length (el_elsA d bs) = el_PA bs.
Proof.
  intros d bs. unfold el_s0A, el_s1A, el_elsA, el_PA. pose proof (atp_elsA_length (el_fddA d (Z.of_nat (length bs))) (chars (el_remA bs))) as L.
  pose proof (atp_P_ge2 (chars (el_remA bs))) as G.
  destruct (atp_elsA _ _) as [|e0 [|e1 rest]]; cbn [length] in L; [lia| lia|]. exists rest. split; [reflexivity| exact L].
Qed.

Lemma el_els_rng : forall d bs e, 0 < d -> 10 <= Z.of_nat (length bs) -> In e (el_elsA d bs) ->
  e = (0, 0) \/ (d + 10 <= fst e /\ 0 <= snd e /\ fst e + snd e <= d + Z.of_nat (length bs)).
Proof.
  intros d bs e D0 N10 Hin. unfold el_elsA in Hin. destruct (el_els_view _ _ _ Hin) as [E|(o & k & -> & B)]; [left; exact E| right].
  cbn [fst snd]. unfold el_fddA. pose proof (el_remA_length bs) as L. unfold el_fdsA in L.
  destruct (Z.leb_spec 10 (Z.of_nat (length bs))); [| lia]. unfold chars in B. rewrite length_map in B. lia.
Qed.

Lemma padded_bytes_chars : forall bs0 : list byte, padded_bytes (map bv_unsigned bs0) = bs0 ++ repeat z8 64.
Proof.
  intros bs0. unfold padded_bytes. f_equal. change (zbytes (map bv_unsigned bs0)) with (to_bytes (chars bs0)). apply to_bytes_chars.
Qed.

Lemma pid_costA_bound : forall len, 0 <= len <= 1048512 -> pid_costA len <= 2^27.
Proof.
  intros len H. unfold pid_costA, pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT.
  set (cap := Z.max len 32). assert (C : 32 <= cap <= 1048512) by lia.
  pose proof (al_sbuf_bounds cap ltac:(lia)) as B1. pose proof (al_tape_bounds cap ltac:(lia)) as B2. pose proof (sc_idx_bounds cap ltac:(lia)) as B3.
  assert (U1 : al_sbuf cap <= 2 * 1048512) by (unfold al_sbuf, roundup64; Z.div_mod_to_equations; lia).
  assert (U2 : al_tape cap <= 9 * 1048512) by (unfold al_tape, roundup64; Z.div_mod_to_equations; lia).
  assert (U3 : sc_idx cap <= 5 * 1048512) by (unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
  pose proof (Atp_hkit5A.mcost_le (al_sbuf cap) ltac:(lia)). pose proof (Atp_hkit5A.mcost_le (al_tape cap) ltac:(lia)). pose proof (Atp_hkit5A.mcost_le (sc_idx cap) ltac:(lia)).
  pose proof (Atp_hkit5A.mcost_le 96 ltac:(lia)). pose proof (Atp_hkit5A.mcost_le 8192 ltac:(lia)). pose proof (Atp_hkit5A.mcost_le 1024 ltac:(lia)). pose proof (Atp_hkit5A.mcost_le (len + 64) ltac:(lia)).
  lia.
Qed.
Lemma mcost_pad_bound : forall len, 0 <= len <= 1048512 -> mcost (len + 64) <= 2^27.
Proof. intros len H. pose proof (Atp_hkit5A.mcost_le (len + 64) ltac:(lia)). lia. Qed.

Lemma vblockA_length : forall A c sz, (length (vblockA A c sz) <= 3)%nat.
Proof. intros A c sz. unfold vblockA. destruct (c =? 0); [cbn; lia| apply ann_block_length]. Qed.

Lemma live_remove_comm : forall p q (l : list (Z * Z)), live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
  intros p q l. induction l as [|e l IH]; [reflexivity|]. rewrite !live_remove_cons'.
  destruct (fst e =? q) eqn:Eq; destruct (fst e =? p) eqn:Ep; rewrite ?live_remove_cons', ?Eq, ?Ep, IH; reflexivity.
Qed.

Lemma el_shadow_split3 : forall m f v p e os t,
  rw_cells asegs m (shad f) (el_shadowA v p e os t) ->
  rw_cells asegs m (shad f + 12) (repeat (C1 (Z_to_bv 8 p)) 10) /\ rw_cells asegs m (shad f + 26) [C1 (Z_to_bv 8 e); C1 (Z_to_bv 8 e)]
  /\ rw_cells asegs m (shad f + 4) [C1 (Z_to_bv 8 v); C1 (Z_to_bv 8 v); C1 (Z_to_bv 8 v)].
Proof.
  intros m f v p e os t FS. unfold el_shadowA, el_shbytesA in FS. cbn [map app repeat] in FS.
  lazymatch type of FS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 ::
                                        ?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: ?e0 :: ?e1 :: ?e2 :: ?e3 :: ?g0 :: ?g1 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: e0 :: e1 :: e2 :: e3 :: g0 :: g1 :: rest)
      with ([c0; c1; c2; c3] ++ [c4; c5; c6] ++ [c7; c8; c9; c10; c11] ++ [d0; d1; d2; d3; d4; d5; d6; d7; d8; d9] ++ [e0; e1; e2; e3] ++ [g0; g1] ++ rest) in FS end.
  apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [_ FS]. apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FV FS].
  apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [_ FS]. apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FP FS].
  apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [_ FS]. apply Sj_stage1_kit.rw_cells_app in FS. destruct FS as [FE _].
  cbn [cells_size csize Nat.add app] in FV, FP, FE.
  replace (shad f + Z.of_nat 4 + Z.of_nat 3 + Z.of_nat 5) with (shad f + 12) in FP by lia.
  replace (shad f + Z.of_nat 4 + Z.of_nat 3 + Z.of_nat 5 + Z.of_nat 10 + Z.of_nat 4) with (shad f + 26) in FE by lia.
  replace (shad f + Z.of_nat 4) with (shad f + 4) in FV by lia.
  exact (conj FP (conj FE FV)).
Qed.

Section K.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma el_parser_fobj : forall (Σ : rts RT) (m : mem) (f : Z) v e os t,
  rw_cells asegs m (shad f) (el_shadowA v 0 e os t) -> rt_frames RT Σ = [(f, 4%nat)] -> 0 < f -> f mod 64 = 0 -> fobj RT Σ m (f + 96) 80.
Proof.
  intros Σ m f v e os t FS FRS FPOS F64. destruct (el_shadow_split3 m f v 0 e os t FS) as (FP & _ & _).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((80 + 7) / 8) with 10.
  split; [exists f, 4%nat; rewrite FRS; change (fs_size 4) with 1024; split; [left; reflexivity| lia]|].
  replace (shad (f + 96)) with (shad f + 12) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  destruct FP as [[_ HB] _]. exact HB.
Qed.

Lemma el_elem_fobj : forall (Σ : rts RT) (m : mem) (f : Z) v p os t,
  rw_cells asegs m (shad f) (el_shadowA v p 0 os t) -> rt_frames RT Σ = [(f, 4%nat)] -> 0 < f -> f mod 64 = 0 -> fobj RT Σ m (f + 208) 16.
Proof.
  intros Σ m f v p os t FS FRS FPOS F64. destruct (el_shadow_split3 m f v p 0 os t FS) as (_ & FE & _).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((16 + 7) / 8) with 2.
  split; [exists f, 4%nat; rewrite FRS; change (fs_size 4) with 1024; split; [left; reflexivity| lia]|].
  replace (shad (f + 208)) with (shad f + 26) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  destruct FE as [[_ HB] _]. exact HB.
Qed.

Lemma el_vec_fobj : forall (Σ : rts RT) (m : mem) (f : Z) p e os t,
  rw_cells asegs m (shad f) (el_shadowA 0 p e os t) -> rt_frames RT Σ = [(f, 4%nat)] -> 0 < f -> f mod 64 = 0 -> fobj RT Σ m (f + 32) 24.
Proof.
  intros Σ m f p e os t FS FRS FPOS F64. destruct (el_shadow_split3 m f 0 p e os t FS) as (_ & _ & FV).
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
  split; [exists f, 4%nat; rewrite FRS; change (fs_size 4) with 1024; split; [left; reflexivity| lia]|].
  replace (shad (f + 32)) with (shad f + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  destruct FV as [[_ HB] _]. exact HB.
Qed.

Lemma el_fobj_dst : forall (Σ : rts RT) (m : mem) (sp : word) (f a n dd nn : Z),
  fobj RT Σ m a n -> 0 <= a -> rt_frames RT Σ = [(f, 4%nat)] -> wr_at asegs m dd nn ->
  a <= dd -> dd + nn <= a + n -> f <= a -> a + n <= f + 1016 -> 0 < nn ->
  checked_dst RT Σ m sp dd nn.
Proof.
  intros Σ m sp f a n dd nn (A8 & N0 & _ & HB) A0 FRS WR D1 D2 F1 F2 NP.
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (acc_zero_run asegs m a _ A8 A0 HB) as AC. rewrite Z2Nat.id in AC by (Z.div_mod_to_equations; lia).
  split; [| split; [| exact WR]].
  - intros _. split; [apply (acc_sub asegs m a (8 * ((n + 7) / 8))); [exact AC| lia| Z.div_mod_to_equations; lia]|].
    right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| lia].
  - intros i Hi. right; right; right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| lia].
Qed.

Lemma pdone_fp : forall (Σ Σ' : rts RT) (m m' : mem) (P : Z) (L : list (Z * Z)),
  pdone RT Σ m P L -> rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ ->
  agree_on (fun a => (P <= a < P + 80) \/ (shad P <= a < shad P + 10) \/ in_live (rt_live RT Σ) a) m m' ->
  pdone RT Σ' m' P L.
Proof.
  intros Σ Σ' m m' P L PD FRS LV AG.
  destruct PD as (impl & tape & sbuf & idx & oc & ia & nt & ns & nidx & noc & nia & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & REST).
  exists impl, tape, sbuf, idx, oc, ia, nt, ns, nidx, noc, nia, dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
  rewrite LV. split; [| split; [| split; [exact INM| split; [exact I8| split; [| exact (conj INS (conj INT (conj INA (conj INO (conj INX REST)))))]]]]].
  - destruct FOBJ as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [rewrite FRS; exact B3|].
    eapply bytes_at_agree; [exact B4|]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite repeat_length in Hx.
    change (Z.to_nat ((80 + 7) / 8)) with 10%nat in Hx. right; left. lia.
  - eapply rw_cells_agree_nw; [exact PC|]. eapply agree_sub; [exact AG|]. intros x Hx. unfold pd_cells in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. left. lia.
  - eapply rw_cells_agree_nw; [exact IC|]. eapply agree_sub; [exact AG|]. intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
    right; right. exists impl, 96. split; [exact INM| lia].
Qed.

Lemma pdone_free : forall (Σp Σd : rts RT) (m m' : mem) (P buf nb sp : Z) (ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf : Z) (Lr : list (Z * Z)),
  pdone RT Σp m P ((buf, nb) :: Lr) -> ART RT Σp m ->
  rt_live RT Σp = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: (buf, nb) :: Lr ->
  0 < nia -> 0 < noc -> 0 < nidx -> 0 < nimpl -> 0 < ntape -> 0 < nsbuf -> 0 < nb -> lposx Lr ->
  rt_live RT Σd = live_remove buf (rt_live RT Σp) -> rt_frames RT Σd = rt_frames RT Σp ->
  rt_pres (rt_live RT Σd) (rt_frames RT Σp) sp m m' ->
  pdone RT Σd m' P Lr
  /\ rt_live RT Σd = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: Lr.
Proof using AF.
  intros Σp Σd m m' P buf nb sp ia oc idx impl tape sbuf nia noc nidx nimpl ntape nsbuf Lr PD ARTp LVp P1 P2 P3 P4 P5 P6 PB HL LVd FRSd PRES.
  destruct (pos_prefix_facts RT AF Σp m [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf); (buf, nb)] [] Lr ARTp
              ltac:(rewrite LVp; reflexivity)
              ltac:(intros e He; cbn [In] in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [snd]; assumption) HL) as [ND NI].
  cbn [map fst] in ND.
  assert (NB6 : forall e, In e [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] -> fst e <> buf).
  { pose proof (fun i x => @nodup_nth_neq Z _ i 6%nat x buf ND) as NN.
    intros e He. cbn [In] in He.
    destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst];
      [exact (NN 0%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 1%nat _ eq_refl eq_refl ltac:(discriminate))
      | exact (NN 2%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 3%nat _ eq_refl eq_refl ltac:(discriminate))
      | exact (NN 4%nat _ eq_refl eq_refl ltac:(discriminate))| exact (NN 5%nat _ eq_refl eq_refl ltac:(discriminate))]. }
  assert (NBL : forall e, In e Lr -> fst e <> buf).
  { intros e He E. apply (NI (buf, nb) e ltac:(cbn [In]; tauto) He). cbn [fst]. rewrite E. reflexivity. }
  assert (LVd' : rt_live RT Σd = (ia, nia) :: (oc, noc) :: (idx, nidx) :: (impl, nimpl) :: (tape, ntape) :: (sbuf, nsbuf) :: Lr).
  { rewrite LVd, LVp. pose proof (live_remove_one buf nb [(ia, nia); (oc, noc); (idx, nidx); (impl, nimpl); (tape, ntape); (sbuf, nsbuf)] [] Lr
                                      NB6 ltac:(intros e []) NBL) as R. cbn [app] in R. exact R. }
  split; [| exact LVd'].
  destruct PD as (impl' & tape' & sbuf' & idx' & oc' & ia' & nt & ns & nidx' & noc' & nia' & dcap & pre8 & mid & mid2 & rest & ipre8 & imid & irest
                  & FOBJ & PC & INM & I8 & IC & INS & INT & INA & INO & INX & NS0 & NT0 & NA0 & NO0 & NX0 & ND6 & EL).
  assert (KEEP : forall p n, In (p, n) (rt_live RT Σp) -> p <> buf -> In (p, n) (rt_live RT Σd)).
  { intros p n Hin NE. rewrite LVd. apply (live_remove_keep _ _ (p, n) Hin). cbn [fst]. exact NE. }
  assert (HB : forall p, In p [impl'; idx'; oc'; ia'; tape'; sbuf'] -> p <> buf).
  { intros p Hp E. subst p.
    assert (X : ~ In (buf, nb) (live_remove impl' (live_remove idx' (live_remove oc' (live_remove ia' (live_remove tape' (live_remove sbuf' (rt_live RT Σp)))))))).
    { cbn [In] in Hp. intros Hin.
      repeat match goal with H : In _ (live_remove ?p ?l) |- _ =>
        let N := fresh "NEQ" in pose proof (live_remove_neq l p _ H) as N; apply live_remove_sub in H; cbn [fst] in N end.
      intuition congruence. }
    apply X. rewrite EL. left. reflexivity. }
  cbn [In] in HB.
  exists impl', tape', sbuf', idx', oc', ia', nt, ns, nidx', noc', nia', dcap, pre8, mid, mid2, rest, ipre8, imid, irest.
  split. { apply (fobj_pres RT AF Σp Σd (rt_live RT Σd) sp m m' P 80 ARTp FOBJ PRES FRSd). }
  split. { apply (rw_cells_agree_nw asegs m m' _ _ PC). apply (agree_of_pres _ _ _ _ _ _ PRES). destruct FOBJ as (_ & _ & (f & c & Hf & FL & FH) & _).
           intros x Hx. unfold pd_cells in Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, c. split; [exact Hf|].
           change ((80 + 7) / 8) with 10 in FH. lia. }
  split; [apply KEEP; [exact INM| apply HB; tauto]|]. split; [exact I8|].
  split. { apply (rw_cells_agree_nw asegs m m' _ _ IC). apply (agree_of_pres _ _ _ _ _ _ PRES). intros x Hx. unfold dl_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
           right; right; left. exists impl', 96. split; [apply KEEP; [exact INM| apply HB; tauto]| lia]. }
  split; [apply KEEP; [exact INS| apply HB; tauto]|]. split; [apply KEEP; [exact INT| apply HB; tauto]|].
  split; [apply KEEP; [exact INA| apply HB; tauto]|]. split; [apply KEEP; [exact INO| apply HB; tauto]|]. split; [apply KEEP; [exact INX| apply HB; tauto]|].
  split; [exact NS0|]. split; [exact NT0|]. split; [exact NA0|]. split; [exact NO0|]. split; [exact NX0|]. split; [exact ND6|].
  rewrite LVd. rewrite (live_remove_comm sbuf' buf), (live_remove_comm tape' buf), (live_remove_comm ia' buf), (live_remove_comm oc' buf),
    (live_remove_comm idx' buf), (live_remove_comm impl' buf), EL.
  rewrite live_remove_cons'. cbn [fst]. rewrite Z.eqb_refl. exact (live_remove_none' buf Lr NBL).
Qed.

Lemma pidA_st_xfer : forall (Σ Σ' : rts RT) (m m' : mem) (P impl idx oc ia tape sbuf cap : Z),
  pidA_st RT Σ m P impl idx oc ia tape sbuf cap -> ART RT Σ m ->
  rt_frames RT Σ' = rt_frames RT Σ -> In (impl, 96) (rt_live RT Σ') ->
  agree_on (fun a => (P <= a < P + 80) \/ (shad P <= a < shad P + 10) \/ (impl <= a < impl + 96)) m m' ->
  pidA_st RT Σ' m' P impl idx oc ia tape sbuf cap.
Proof.
  intros Σ Σ' m m' P impl idx oc ia tape sbuf cap (FOBJ & (p1 & p17 & p57 & PC) & (nsi & p12 & nxt & p28 & p50 & bufv & lenv & docv & IC)) ARTm FRS INM AG.
  split.
  { destruct FOBJ as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [rewrite FRS; exact B3|].
    eapply bytes_at_agree; [exact B4|]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite repeat_length in Hx.
    change (Z.to_nat ((80 + 7) / 8)) with 10%nat in Hx. right; left. lia. }
  split. { exists p1, p17, p57. apply (rw_cells_agree_nw asegs m m' _ _ PC). eapply agree_sub; [exact AG|]. intros x Hx.
           unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. left. lia. }
  exists nsi, p12, nxt, p28, p50, bufv, lenv, docv. apply (rw_cells_agree_nw asegs m m' _ _ IC). eapply agree_sub; [exact AG|]. intros x Hx.
  unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. right; right. lia.
Qed.

Lemma el_libA_pid : forall m m', el_libA m -> sj_lib m' -> agree_on (fun x => el_lib_rng x /\ outside SJ_W x) m m' -> el_libA m'.
Proof.
  intros m m' [(S & L & LW) (E & U & T)] S' AG. split; [split; [exact S'| split]| split; [| split]].
  - eapply pj_locA_agree; [exact L|]. intros a Ha. apply AG. split; [left; exact (loc_rng_fp _ Ha)|].
    unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha. unfold SJ_W. cbn [outside]. repeat split; lia.
  - eapply lockwA_agree; [exact LW|]. intros a Ha. apply AG. split; [left; exact (lock_rng_fp _ Ha)|].
    unfold PJ_LOCKW_A in Ha. unfold SJ_W. cbn [outside]. repeat split; lia.
  - eapply rw_cells_agree_nw; [exact E|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. unfold EL_EHG_A in Ha. split; [right; left; unfold EL_EHG_A; lia|].
    unfold SJ_W. cbn [outside]. repeat split; lia.
  - destruct U as [uw U]. exists uw. eapply rw_cells_agree_nw; [exact U|]. intros a Ha. apply AG. rewrite uw_cellsA_size in Ha. unfold EL_UNW_A in Ha.
    split; [left; apply unw_rng_fp; unfold EL_UNW_A; lia|]. unfold SJ_W. cbn [outside]. repeat split; lia.
  - eapply rw_cells_agree_nw; [exact T|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. unfold EL_TPLOC_A, TPV_A in Ha.
    split; [right; right; unfold EL_TPLOC_A, TPV_A; lia|]. unfold SJ_W. cbn [outside]. repeat split; lia.
Qed.
End K.

Definition el_locals4 (j0 : list byte) (p0 l0 : Z) (idx : word) (act : Z) (j8 : list byte) (f : Z) (j10 : list byte) (sel fdv : Z) (j15 jr : list byte) : list cell :=
  [CB 24 j0; C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 l0); C8 idx; C8 (Z_to_bv 64 (f + 240)); C8 (Z_to_bv 64 act); CB 24 j8; C8 (Z_to_bv 64 f); CB 24 jr;
   CB 4 j10; C4 (Z_to_bv 64 sel); C8 (Z_to_bv 64 fdv); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j15].

Section Cuts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition cutP4 (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 : list byte) (idx : word) (act sel A : Z),
    el_baseA RT Σ0 Σ m0 m X d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 ->
    rw_cells asegs m (lf_S1 X) (el_locals4 j0 (fst (el_s0A d bs)) (snd (el_s0A d bs)) idx act j8 (lf_F X) j10 sel (el_fddA d (Z.of_nat (length bs)) + el_fdsA (Z.of_nat (length bs))) j15 jr) ->
    0 <= act < 32 -> 0 <= sel < 8 -> 10 <= Z.of_nat (length bs) ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 0 0 (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) ->
    rw_cells asegs m (lf_F X + 56) [CB 40 j56] -> rw_cells asegs m (lf_F X + 96) (parser_init q1 q17 q57) ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] -> rw_cells asegs m (lf_F X + 208) [C8 (wz 0); C8 (wz 0)] -> rw_cells asegs m (lf_F X + 224) [CB 16 j224] ->
    rw_cells asegs m (lf_F X + 240) [CB 288 jos] -> rw_cells asegs m (lf_F X + 528) [CB 488 j528] ->
    vliveA (rt_live RT Σ) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (rt_live RT Σ0) ->
    rt_credit RT Σ0 - el_vcostA bs <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) (wz (lf_F X + 208)) (wz SHB)
                    (wz (lf_F X)) (wz A) x10 (wz (lf_F X + 120)) t3 t4 t5 t6)
               F (wz 0xb19b0) fc None m (seg_rom asegs)).

Definition cutP7 (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (j0 j8 j10 j15 jr h3 t j56 j176 j224 jos j528 q1 q17 q57 : list byte) (idx : word) (act sel A buf : Z) (doc : list byte),
    el_baseA RT Σ0 Σ m0 m X d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 ->
    rw_cells asegs m (lf_S1 X) (el_locals4 j0 (fst (el_s0A d bs)) (snd (el_s0A d bs)) idx act j8 (lf_F X) j10 sel (el_fddA d (Z.of_nat (length bs)) + el_fdsA (Z.of_nat (length bs))) j15 jr) ->
    0 <= act < 32 -> 0 <= sel < 8 -> 10 <= Z.of_nat (length bs) ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 0 0 (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) ->
    rw_cells asegs m (lf_F X + 56) [CB 40 j56] -> rw_cells asegs m (lf_F X + 96) (parser_init q1 q17 q57) ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] -> rw_cells asegs m (lf_F X + 208) [C8 (wz 0); C8 (wz 0)] -> rw_cells asegs m (lf_F X + 224) [CB 16 j224] ->
    rw_cells asegs m (lf_F X + 240) [CB 288 jos] -> rw_cells asegs m (lf_F X + 528) [CB 488 j528] ->
    ((buf = 0 /\ doc = [] /\ vliveA (rt_live RT Σ) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (rt_live RT Σ0))
     \/ (0 < buf /\ buf mod 16 = 0 /\ Z.of_nat (length doc) <= 1048512 /\ buf + Z.of_nat (length doc) + 64 < USTACK_TOP
         /\ bytes_at asegs m buf (padded_bytes (map bv_unsigned doc))
         /\ rt_live RT Σ = (buf, Z.of_nat (length doc) + 64) :: vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0)) ->
    rt_credit RT Σ0 - el_vcostA bs - 2^27 <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) (wz (lf_F X + 208)) x7
                    (wz (lf_F X)) (wz buf) (wz (Z.of_nat (length doc))) (wz (lf_F X + 120)) t3 t4 t5 t6)
               F (wz 0xb1a34) fc None m (seg_rom asegs)).
End Cuts.
