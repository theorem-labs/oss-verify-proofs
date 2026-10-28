(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout GDesc RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame ApErrKitA ApErrKitA2 W_locks W_tlocalA Fr_init_base W_get_stateA I_strcpyA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module EK := OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP.ApErrKit.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac pstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac es_store WR :=
  let HS := fresh "HS" in let ESn := fresh "ESn" in
  destruct WR as [HS ESn]; unfold MallocRep.wz, ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP in HS, ESn; step;
  lazymatch type of ESn with es_raw (write_to_mem ?m ?a ?bs) _ _ =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a2 ?bs2) _) =>
      first [ constr_eq a a2; constr_eq bs bs2
            | replace (write_to_mem m a2 bs2) with (write_to_mem m a bs) by (unfold wa; f_equal; first [reflexivity | word_eq_tac | vm_compute; reflexivity]) ]
    end;
    try match goal with H : es_raw m _ _ |- _ => clear H end
  end;
  store_done; rename ESn into ES;
  try lazymatch goal with
  | ES : es_raw _ _ ?g, GL : g_len _ |- _ =>
      let GLn := fresh "GLn" in
      assert (GLn : g_len g)
        by (let H := fresh in pose proof GL as H; unfold CtRepP.ApErrKit.g_len in H |- *;
            cbn [EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot
                 EK.set_g_fl EK.set_g_ma EK.set_g_bu EK.set_g_da EK.set_g_ds EK.set_g_df EK.set_g_fi EK.set_g_li EK.set_g_fu EK.set_g_top EK.set_g_bot] in H |- *;
            rewrite ?upd_length in H; rewrite ?upd_length; exact H);
      clear GL; rename GLn into GL
  end.

Definition SD_STK : Z := 96 + GET_STATE_STACK.     (* [comment removed for export] *)
Definition SD_RA1 : Z := 0x1fd898.                (* [comment removed for export] *)
Definition SD_MID1 : Z := 0x1fd8e8.               (* [comment removed for export] *)
Definition SD_SL1_RA : Z := 0x1fd90c.
Definition SD_MID2 : Z := 0x1fd91c.               (* [comment removed for export] *)
Definition SD_CPY1_RA : Z := 0x1fd934.
Definition SD_MID3 : Z := 0x1fd98c.               (* [comment removed for export] *)
Definition SD_SL2_RA : Z := 0x1fd9b0.
Definition SD_TAIL : Z := 0x1fd9c0.               (* [comment removed for export] *)
Definition SD_LIT : Z := 0x49860.                 (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_okA (a : Z) (str slack : list byte) (n : Z) : Prop :=
  ro_bytes_b ctasegs a (str ++ Z_to_bv 8 0 :: slack) = true /\ ~ In (Z_to_bv 8 0) str /\ str <> []
  /\ (- (a + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ Z.of_nat (length str) + 1 = n
  /\ ((exists g, In g GDESC /\ gd_beg g <= a /\ a + n <= gd_beg g + gd_size g) \/ In (a, n) ACC_LITS)   (* [comment removed for export] *)
  /\ 0x10000 <= a /\ a + n + Z.of_nat (length slack) <= 0x600000 /\ n <= 64512.

Lemma lit_bytes_atA : forall m a str slack n, mem_inv ctasegs m -> lit_okA a str slack n -> bytes_at ctasegs m a (str ++ Z_to_bv 8 0 :: slack).
Proof.
  intros m a str slack n MI (RO & _ & _ & _ & LEN & _ & LO & HI & _).
  pose proof (ro_cells_image ctasegs m a _ MI RO ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) as RC.
  pose proof (ro_cells_bytes_at ctasegs m a _ RC) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma lit_firstA : forall a str slack n, lit_okA a str slack n -> exists c str', str = c :: str' /\ bv_unsigned c <> 0.
Proof.
  intros a str slack n (_ & NN & NE & _). destruct str as [|c str']; [congruence|]. exists c, str'. split; [reflexivity|].
  intros Hc. apply NN. left. apply bv_eq. rewrite Hc. reflexivity.
Qed.

Definition gd_find (a : Z) : option gdesc := find (fun g => (gd_beg g <=? a) && (a <? gd_beg g + gd_size g)) GDESC.

(* [comment removed for export] *)
Definition lit_autoA (a n : Z) : bool :=
  match image_bytes ctasegs a (Z.to_nat (n - 1)), image_bytes ctasegs (a + n) 8 with
  | Some s, Some k =>
      ro_bytes_b ctasegs a (s ++ Z_to_bv 8 0 :: k) && forallb (fun b : byte => negb (bv_eqb b (Z_to_bv 8 0))) s
      && (2 <=? n) && (n <=? 64512) && (0x10000 <=? a) && (a + n + 8 <=? 0x600000)
      && match gd_find a with
         | Some g => (a + n <=? gd_beg g + gd_size g)
         | None => existsb (fun r => (fst r =? a) && (snd r =? n)) ACC_LITS      (* [comment removed for export] *)
         end
  | _, _ => false
  end.

Lemma lit_okA_auto : forall a n, lit_autoA a n = true -> exists s k, lit_okA a s k n.
Proof.
  intros a n H. unfold lit_autoA in H.
  destruct (image_bytes ctasegs a (Z.to_nat (n - 1))) as [s|] eqn:ES; [|discriminate].
  destruct (image_bytes ctasegs (a + n) 8) as [k|] eqn:EK; [|discriminate].
  apply andb_prop in H as [H G2]. apply andb_prop in H as [H R2]. apply andb_prop in H as [H R1]. apply andb_prop in H as [H N3]. apply andb_prop in H as [H N2].
  apply andb_prop in H as [RO NN].
  apply Z.leb_le in R2. apply Z.leb_le in R1. apply Z.leb_le in N3. apply Z.leb_le in N2.
  assert (GD : (exists g, In g GDESC /\ gd_beg g <= a /\ a + n <= gd_beg g + gd_size g) \/ In (a, n) ACC_LITS).
  { destruct (gd_find a) as [g|] eqn:EG.
    - left. apply Z.leb_le in G2. unfold gd_find in EG. apply find_some in EG. destruct EG as [ING PG]. apply andb_prop in PG as [PG1 PG2].
      apply Z.leb_le in PG1. apply Z.ltb_lt in PG2. exists g; split; [exact ING|]; split; lia.
    - right. apply existsb_exists in G2. destruct G2 as ([ra rn] & Hin & E). cbn [fst snd] in E. apply andb_prop in E as [E1 E2].
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst ra rn. exact Hin. }
  pose proof (image_bytes_length ctasegs _ _ _ ES) as LS. pose proof (image_bytes_length ctasegs _ _ _ EK) as LK.
  exists s, k. unfold lit_okA. rewrite LS, LK. split; [exact RO|]. split.
  { intros Hin. pose proof (proj1 (forallb_forall _ _) NN _ Hin) as X. cbn in X. unfold bv_eqb in X. rewrite Z.eqb_refl in X. discriminate. }
  split; [destruct s; [cbn in LS; lia|discriminate]|]. split; [pose proof (Z.mod_pos_bound (- (a + Z.of_nat (Z.to_nat (n - 1)) + 1)) 8 ltac:(lia)); lia|].
  split; [lia|]. split; [exact GD|]. split; [lia|]. split; lia.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition ERR_set_debug_specA (rs : rsite) (file func : Z) : Prop :=
  forall (bo0 : Z * Z) (fstr fslack nstr nslack : list byte),
  lit_okA file fstr fslack (rs_flen rs) -> lit_okA func nstr nslack (rs_fnlen rs) ->
  ap_stmtA ERR_SET_DEBUG ERR_SET_DEBUG_STACK ERR_SET_DEBUG_COST ERR_SET_DEBUG_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz file /\ a1 = wz (rs_line rs) /\ a2 = wz func /\ bo = bo0)
           (err_set_debug rs)
           (fun r OW' m' a0' bo' => bo' = bo0).

(* [comment removed for export] *)
Lemma ids_in_introA : forall st m OW E bo, ap_state st m OW E bo -> ids_in E st OW.
Proof.
  intros st m OW E bo AS q Hq. pose proof AS as (HE & _ & HC & _ & _ & _ & (_ & _ & F1 & F2 & F3)).
  apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
  - unfold es_ids, st_blocks in Hq. rewrite !map_app, !in_app_iff in Hq.
    assert (FM : forall l, Forall (optb_ok OW) l -> In q (map fst (fm l)) -> In q (map blk_id OW)).
    { intros l Hl Hin. apply in_map_iff in Hin. destruct Hin as ([q' n] & E1 & Hin). cbn in E1. subst q'.
      induction l as [|o l IH]; [destruct Hin|]. apply Forall_cons_iff in Hl. destruct Hl as [Ho Hl].
      rewrite fm_cons in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [|apply IH; assumption].
      destruct o as [[q' n']|]; [|destruct Hin]. destruct Hin as [Hin|[]]. injection Hin as -> ->. cbn in Ho. destruct Ho as [Ho _].
      change q with (blk_id (q, badr OW q, n)). apply in_map. exact Ho. }
    destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [apply (FM _ F1 Hq)|apply (FM _ F2 Hq)|apply (FM _ F3 Hq)|].
    destruct (as_cnf st) as [[[lk lh] bk]|]; cbn [ap_statics_cnf cnf_blocks map fst In] in HC, Hq; [|destruct Hq].
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & I3 & _).   (* [comment removed for export] *)
    destruct Hq as [<-|[<-|[<-|[]]]]; [change lk with (blk_id (lk, badr OW lk, CtRepP.ApRepDefs.SZ_OBJ_LOCK))|change lh with (blk_id (lh, badr OW lh, CtRepP.ApRepDefs.SZ_ADDED))
                                    |change bk with (blk_id (bk, badr OW bk, CtRepP.ApRepDefs.SZ_ADDED_BUCKETS))]; apply in_map; assumption.
  - destruct HE as (HF & _ & _). unfold env_ids in Hq. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map.
    exact (proj1 (Forall_forall _ _) HF b Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_checked_src : forall Σ OW LB m sp lo a str slack n,
  AHEAP Σ OW LB m -> ACEIL <= lo -> lit_okA a str slack n -> checked_src RT Σ m sp lo a n.
Proof.
  intros Σ OW LB m sp lo a str slack n HEAP CEIL (_ & _ & _ & _ & LEN & GD & LO & HI & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A in C1.
  split; [| left; clear - CEIL C1 HI; lia]. intros _. split.
  - exact (af_lit_acc RT AF Σ m a n (AH_art _ _ _ _ HEAP) GD).
  - right; right; right. unfold SEGTOP_A. clear - LO HI; lia.
Qed.

Lemma strlen_lit_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo s : Z) (str slack : list byte) (n : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  lit_okA s str slack n -> a0 = wz s ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_strlen) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (n - 1)) Σ OW LB lo 0 0 m (fun _ => True))).
Proof.
  intros until n. intros HEAP ST CEIL LO SPT SP16 MI -> LIT ->.
  pose proof LIT as (RO & NN & NE & PAD & LEN & GG & SLO & SHI & N64).
  pose proof (lit_bytes_atA m s str slack n MI LIT) as HS.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  replace (n - 1) with (Z.of_nat (length str)) by (clear - LEN; lia).
  eapply cps_conseq; [ eapply (rc_strlen RT (@ar_RC AR) Σ PMc) with (s := s) (str := str) (slack := slack) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact HS.
  - exact NN.
  - clear - LEN N64. lia.
  - exact PAD.
  - clear - SLO SHI LEN. lia.
  - left. unfold BnHeapA.ACEIL in *. clear - CEIL C1 SHI LEN. lia.
  - rewrite LEN. exact (lit_checked_src Σ OW LB m sp lo s str slack n HEAP CEIL LIT).
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply AH_same_ex; [exact HEAP| exact ART2| exact WM2| exact PRES| right; right; clear; lia]. }
    split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    exact I.
Qed.

Section WithStrcpy.
Hypothesis STRCPY : strcpy_icontract RT.

(* [comment removed for export] *)
Lemma strcpy_lit_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo d s : Z) (str slack : list byte) (n : Z) (bd : block),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  lit_okA s str slack n ->
  In bd (OW ++ LB) -> blk_addr bd <= d -> d + n <= blk_addr bd + blk_size bd ->
  a0 = wz d -> a1 = wz s ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_strcpy) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz d) Σ OW LB lo d n m
                        (fun m' => bytes_at ctasegs m' d (str ++ [Z_to_bv 8 0]) /\ wr_at ctasegs m' d n))).
Proof.
  intros until bd. intros HEAP ST CEIL LO SPT SP16 MI -> LIT IND D1 D2 -> ->.
  pose proof LIT as (RO & NN & NE & PAD & LEN & GG & SLO & SHI & N64).
  pose proof (lit_bytes_atA m s str slack n MI LIT) as HS.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & BDI).
  pose proof (blk_checked_dst Σ OW LB m sp bd d n HEAP IND D1 D2 ltac:(clear - LEN; lia)) as CD.
  eapply cps_conseq; [ eapply (STRCPY Σ PMc) with (d := d) (s := s) (str := str) (slack := slack) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact HS.
  - exact NN.
  - clear - LEN N64. lia.
  - exact PAD.
  - clear - SLO SHI LEN. lia.
  - unfold BnHeapA.ACEIL in *. clear - BD0 BDC D1 D2 LEN C3. lia.
  - left. unfold BnHeapA.ACEIL in *. clear - CEIL C1 SHI LEN. lia.
  - rewrite LEN. exact (lit_checked_src Σ OW LB m sp lo s str slack n HEAP CEIL LIT).
  - rewrite LEN. exact CD.
  - rewrite ?LEN. unfold BnHeapA.ACEIL in *. clear - BDI D1 D2 SLO SHI LEN. lia.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc. rewrite ?LEN.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same' _ _ _ _ _ _ _ _ bd HEAP ART2 WM2 PRES IND D1 D2)|]. split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    split; [exact BZ|]. destruct CD as (_ & _ & W). exact (wr_at_transport ctasegs m m2 d _ W WM2).
Qed.

End WithStrcpy.

Local Notation E_free1 := (E_ERR_set_debug_1f902c : uk_call 0x1fd844 0x1fd8e8 0x1fd334).     (* [comment removed for export] *)
Local Notation E_malloc1 := (E_ERR_set_debug_1f9060 : uk_call 0x1fd844 0x1fd91c 0x1fce24).   (* [comment removed for export] *)
Local Notation E_free2 := (E_ERR_set_debug_1f90e8 : uk_call 0x1fd844 0x1fd98c 0x1fd334).     (* [comment removed for export] *)
Local Notation E_malloc2 := (E_ERR_set_debug_1f911c : uk_call 0x1fd844 0x1fd9c0 0x1fce24).   (* [comment removed for export] *)

Section WithStrcpy2.
Hypothesis STRCPY : strcpy_icontract RT.

  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo : Z).
  Variables (rs : rsite) (Lf Ln : Z) (fstr fslack nstr nslack : list byte).
  Hypothesis IDS : ids_ok E st.
  Hypothesis CEIL : ACEIL <= lo.
  Hypothesis ACE : ACEIL + STACK_WIN <= USTACK_TOP.
  Hypothesis LO : lo <= bv_unsigned sp - SD_STK.
  Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
  Hypothesis AL16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESB : e_es E + 904 < 2 ^ 63.
  Hypothesis EES16 : e_es E mod 16 = 0.   (* [comment removed for export] *)
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists mI, ap_state st mI OW E bo0.
  Hypothesis IDIN : ids_in E st OW.
  Hypothesis LITF : lit_okA Lf fstr fslack (rs_flen rs).
  Hypothesis LITN : lit_okA Ln nstr nslack (rs_fnlen rs).
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Variables (COST : Z).
  Hypothesis COST1 : 1 <= COST.
  Hypothesis FRM : Z.of_nat (length FR) + 0 <= Z.of_nat FRAMES_MAX.
  (* [comment removed for export] *)
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ERR_SET_DEBUG (bv_unsigned ra :: ras).

  Let tn : nat := as_top st.
  Let line : Z := rs_line rs.
  Let flen : Z := rs_flen rs.
  Let fnlen : Z := rs_fnlen rs.
  (* [comment removed for export] *)
  Let st_a : ap_st bptr := set_file tn None st.
  Definition st_b (pf : bptr) : ap_st bptr := set_line tn line (set_file tn (Some (pf, flen)) st_a).
  Definition st_c (pf : bptr) : ap_st bptr := set_func tn None (st_b pf).
  Definition st_fin (pf pn : bptr) : ap_st bptr := set_func tn (Some (pn, fnlen)) (st_c pf).
  (* [comment removed for export] *)
  Local Notation W2 := ([(bv_unsigned sp - SD_STK, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Local Notation SB := (seg_baseA m OW st E bo0 LB K (bv_unsigned sp) Σ) (only parsing).
  Let POST := ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K COST
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).
  (* [comment removed for export] *)
  Definition sd_frame (j0 : list byte) : list cell := [CB 8 j0; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma TNB : (tn < 16)%nat.
  Proof. pose proof (ids_ok_top _ _ IDS) as [T _]. exact T. Qed.
  Lemma LOSP : lo <= bv_unsigned sp.
  Proof. clear - LO. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LO. lia. Qed.
  Lemma TOP' : bv_unsigned sp <= USTACK_TOP.
  Proof. clear - TOP. lia. Qed.

  (* [comment removed for export] *)
  Definition g1 (A1 : Z) : esg := EK.set_g_fi (upd (EK.g_fi (g_of st (badr OW))) tn (Z_to_bv 64 A1)) (g_of st (badr OW)).
  Definition g2 (A1 : Z) : esg := EK.set_g_li (upd (EK.g_li (g1 A1)) tn (Z_to_bv 64 line)) (g1 A1).
  Definition gfin (A1 A2 : Z) : esg := EK.set_g_fu (upd (EK.g_fu (g2 A1)) tn (Z_to_bv 64 A2)) (g2 A1).

  (* [comment removed for export] *)
  Definition REST3 : @AM bptr unit := abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen)))).
  Definition REST2 (pf : bptr) : @AM bptr unit :=
    abind (amodify (fun s1' : ap_st bptr => set_line tn line (set_file tn (Some (pf, flen)) s1'))) (fun _ =>
      abind (free_func_slot tn) (fun _ =>
        abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen)))))).
  Definition REST1 : @AM bptr unit :=
    abind (amalloc flen) (fun pf =>
      abind (amodify (fun s1' : ap_st bptr => set_line tn line (set_file tn (Some (pf, flen)) s1'))) (fun _ =>
        abind (free_func_slot tn) (fun _ =>
          abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen))))))).

  (* [comment removed for export] *)
  Lemma fin_pureA : forall (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z),
    let OW1 := lremove (get_file tn st) OW in
    let OW2 := (pf, A1, flen) :: OW1 in
    let OW3 := lremove (get_func tn st) OW2 in
    let OW4 := (pn, A2, fnlen) :: OW3 in
    ~ In pf (map blk_id (OW1 ++ LB)) -> ablock_range A1 flen -> ~ In pn (map blk_id (OW3 ++ LB)) -> ablock_range A2 fnlen ->
    ids_ok E (st_fin pf pn) /\ ids_in E (st_fin pf pn) OW4
    /\ g_of (st_fin pf pn) (badr OW4) = gfin A1 A2
    /\ Forall (optb_ok OW4) (as_file (st_fin pf pn)) /\ Forall (optb_ok OW4) (as_func (st_fin pf pn)) /\ Forall (optb_ok OW4) (as_data (st_fin pf pn))
    /\ (forall mX, ap_restA mX OW E bo0 (as_cnf st) -> ap_restA mX OW4 E bo0 (as_cnf (st_fin pf pn)))
    /\ (forall i q k, get_data i st = Some (q, k) -> badr OW4 q = badr OW q)
    /\ (forall b, In b K -> ~ In (blk_id b) (es_ids (st_fin pf pn)))
    /\ es_shape (st_fin pf pn).
  Proof.
    intros pf A1 pn A2. cbn zeta. intros NI1 BR1 NI2 BR2.
    set (OW1 := lremove (get_file tn st) OW). set (OW2 := (pf, A1, flen) :: OW1). set (OW3 := lremove (get_func tn st) OW2). set (OW4 := (pn, A2, fnlen) :: OW3).
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB].
    pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    pose proof BR1 as (BP1 & BP2 & BP3 & BP4 & BP5). pose proof BR2 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    assert (C63 : ACEIL < 2 ^ 62) by (clear - ACE; unfold STACK_WIN, USTACK_TOP in ACE; lia).
    (* [comment removed for export] *)
    assert (QF : forall q n, get_file tn st = Some (q, n) -> In (q, badr OW q, n) OW /\ In q (es_ids st) /\ In q (map blk_id OW)).
    { intros q n GF. pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. split; [exact HIn|]. split; [eapply es_ids_file; exact GF|].
      change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn. }
    assert (QN : forall q n, get_func tn st = Some (q, n) -> In (q, badr OW q, n) OW1 /\ In q (es_ids st) /\ In q (map blk_id OW1)).
    { intros q n GN. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn.
      assert (HIn1 : In (q, badr OW q, n) OW1).
      { subst OW1. apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
      split; [exact HIn1|]. split; [eapply es_ids_func; exact GN|]. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn1. }
    (* [comment removed for export] *)
    assert (PF1 : forall b, In b OW1 -> blk_id b <> pf).
    { intros b Hb EQ. apply NI1. rewrite <- EQ, map_app. apply in_app_iff. left. apply in_map. exact Hb. }
    assert (PFQN : forall q n, get_func tn st = Some (q, n) -> pf <> q).
    { intros q n GN ->. exact (PF1 _ (proj1 (QN q n GN)) eq_refl). }
    assert (IN3 : forall b, In b OW1 -> (forall q n, get_func tn st = Some (q, n) -> blk_id b <> q) -> In b OW3).
    { intros b Hb Hq. subst OW3 OW2. apply lremove_keep; [right; exact Hb|exact Hq]. }
    assert (PF3 : In (pf, A1, flen) OW3).
    { subst OW3 OW2. apply lremove_keep; [left; reflexivity|]. intros q n GN. cbn. eapply PFQN. exact GN. }
    assert (PN3 : forall b, In b OW3 -> blk_id b <> pn).
    { intros b Hb EQ. apply NI2. rewrite <- EQ, map_app. apply in_app_iff. left. apply in_map. exact Hb. }
    assert (NEP : pn <> pf) by (intros EQ; exact (PN3 _ PF3 (eq_sym EQ))).
    (* [comment removed for export] *)
    set (stc' := set_func tn None st_a).
    assert (LFa : (tn < length (as_file st))%nat) by (rewrite L5; exact TNB').
    assert (LNa : (tn < length (as_func st_a))%nat) by (unfold st_a; cbn [as_func set_file]; rewrite L7; exact TNB').
    pose proof (st_blocks_set_file tn None st LFa) as P1. cbn [optb] in P1. rewrite app_nil_l in P1 || idtac. fold st_a in P1.
    pose proof (st_blocks_set_func tn None st_a LNa) as P1'. cbn [optb] in P1'. rewrite app_nil_l in P1' || idtac. fold stc' in P1'.
    assert (GNa : get_func tn st_a = get_func tn st) by reflexivity. rewrite GNa in P1'.
    assert (PC : Permutation ((optb (get_file tn st) ++ optb (get_func tn st)) ++ st_blocks stc') (st_blocks st)).
    { rewrite <- app_assoc. eapply Permutation_trans; [|exact P1]. apply Permutation_app_head. exact P1'. }
    assert (NOT4 : forall p, In p (es_ids stc') ->
              (forall q n, get_file tn st = Some (q, n) -> p <> q) /\ (forall q n, get_func tn st = Some (q, n) -> p <> q) /\ In p (es_ids st)).
    { intros p Hp. pose proof (ids_pre_disjoint E st stc' _ p IDS PC Hp) as NI. rewrite !map_app, !in_app_iff in NI.
      split; [|split; [|eapply es_ids_sub_perm; [exact PC|exact Hp]]]; intros q n G ->; apply NI; rewrite G; cbn; tauto. }
    assert (SURV : forall p b, In p (es_ids stc') -> In b OW -> blk_id b = p -> In b OW4 /\ badr OW4 p = badr OW p /\ p <> pf /\ p <> pn).
    { intros p b Hp Hb Hid. destruct (NOT4 p Hp) as (N1 & N2 & N3).
      assert (Hb1 : In b OW1) by (subst OW1; apply lremove_keep; [exact Hb|]; intros q n G; rewrite Hid; exact (N1 q n G)).
      assert (Npf : p <> pf) by (rewrite <- Hid; exact (PF1 b Hb1)).
      assert (Hb3 : In b OW3) by (apply IN3; [exact Hb1|]; intros q n G; rewrite Hid; exact (N2 q n G)).
      assert (Npn : p <> pn) by (rewrite <- Hid; exact (PN3 b Hb3)).
      split; [right; exact Hb3|]. split; [|split; [exact Npf|exact Npn]].
      subst OW4 OW3 OW2 OW1. rewrite badr_cons, (bptr_eqb_neq pn p ltac:(congruence)).
      rewrite badr_lremove by (intros q n G; exact (N2 q n G)). rewrite badr_cons, (bptr_eqb_neq pf p ltac:(congruence)).
      rewrite badr_lremove by (intros q n G; exact (N1 q n G)). reflexivity. }
    (* [comment removed for export] *)
    assert (BPN : badr OW4 pn = A2) by (subst OW4; rewrite badr_cons, bptr_eqb_refl; reflexivity).
    assert (BPF : badr OW4 pf = A1).
    { subst OW4 OW3 OW2. rewrite badr_cons, (bptr_eqb_neq pn pf NEP). rewrite badr_lremove by (intros q n G; eapply PFQN; exact G).
      rewrite badr_cons, bptr_eqb_refl. reflexivity. }
    (* [comment removed for export] *)
    assert (GFa : get_file tn st_a = None) by (unfold st_a, get_file; cbn [as_file set_file]; apply nth_lset_same; rewrite L5; exact TNB').
    assert (LFa' : (tn < length (as_file st_a))%nat) by (unfold st_a; cbn [as_file set_file]; rewrite lset_length, L5; exact TNB').
    assert (P2 : Permutation (st_blocks (st_b pf)) ((pf, flen) :: st_blocks st_a)).
    { unfold st_b. rewrite st_blocks_set_line. pose proof (st_blocks_set_file tn (Some (pf, flen)) st_a LFa') as P. rewrite GFa in P. cbn [optb app] in P. exact P. }
    assert (GNb : get_func tn (st_b pf) = get_func tn st) by reflexivity.
    assert (LNb : (tn < length (as_func (st_b pf)))%nat) by (unfold st_b, st_a; cbn [as_func set_line set_file]; rewrite L7; exact TNB').
    pose proof (st_blocks_set_func tn None (st_b pf) LNb) as P3. rewrite GNb in P3. cbn [optb] in P3. rewrite app_nil_l in P3 || idtac.
    change (set_func tn None (st_b pf)) with (st_c pf) in P3.
    assert (GNc : get_func tn (st_c pf) = None) by (unfold st_c, get_func; cbn [as_func set_func]; apply nth_lset_same; exact LNb).
    assert (LNc : (tn < length (as_func (st_c pf)))%nat) by (unfold st_c; cbn [as_func set_func]; rewrite lset_length; exact LNb).
    assert (P4 : Permutation (st_blocks (st_fin pf pn)) ((pn, fnlen) :: st_blocks (st_c pf))).
    { unfold st_fin. pose proof (st_blocks_set_func tn (Some (pn, fnlen)) (st_c pf) LNc) as P. rewrite GNc in P. cbn [optb app] in P. exact P. }
    (* [comment removed for export] *)
    assert (IDINa : ids_in E st_a OW1).
    { subst OW1. destruct (get_file tn st) as [[qf nf]|] eqn:GF; cbn [lremove optb app] in P1 |- *.
      - eapply ids_in_remove; [exact IDS|exact P1|exact IDIN].
      - intros q Hq. apply IDIN. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left|right; exact Hq].
        unfold es_ids in *. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map. eapply Permutation_in; [exact P1|exact Hb]. }
    assert (IDSa : ids_ok E st_a) by (eapply ids_ok_sub; [exact P1|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDS]).
    pose proof (fresh_not_ids E st_a OW1 LB pf IDINa NI1) as FRF.
    assert (IDSb : ids_ok E (st_b pf)) by (eapply ids_ok_add; [exact P2|exact FRF|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSa]).
    assert (IDINb : ids_in E (st_b pf) OW2) by (subst OW2; eapply ids_in_add; [exact P2|exact IDINa]).
    assert (IDINc : ids_in E (st_c pf) OW3).
    { subst OW3. destruct (get_func tn st) as [[qn nn]|] eqn:GN; cbn [lremove optb app] in P3 |- *.
      - eapply ids_in_remove; [exact IDSb|exact P3|exact IDINb].
      - intros q Hq. apply IDINb. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left|right; exact Hq].
        unfold es_ids in *. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map. eapply Permutation_in; [exact P3|exact Hb]. }
    assert (IDSc : ids_ok E (st_c pf)) by (eapply ids_ok_sub; [exact P3|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSb]).
    pose proof (fresh_not_ids E (st_c pf) OW3 LB pn IDINc NI2) as FRN.
    assert (IDSf : ids_ok E (st_fin pf pn)) by (eapply ids_ok_add; [exact P4|exact FRN|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSc]).
    assert (IDINf : ids_in E (st_fin pf pn) OW4) by (subst OW4; eapply ids_in_add; [exact P4|exact IDINc]).
    split; [exact IDSf|]. split; [exact IDINf|].
    (* [comment removed for export] *)
    assert (OFc : Forall (optb_ok OW) (as_file stc')) by (unfold stc', st_a; cbn [as_file set_func set_file]; apply optb_ok_lset_none; exact OF).
    assert (ONc : Forall (optb_ok OW) (as_func stc')) by (unfold stc', st_a; cbn [as_func set_func set_file]; apply optb_ok_lset_none; exact OFN).
    assert (ODc : Forall (optb_ok OW) (as_data stc')) by (unfold stc', st_a; cbn [as_data set_func set_file]; exact OD).
    assert (GEN : forall l, Forall (optb_ok OW) l -> (forall p n, In (Some (p, n)) l -> In p (es_ids stc')) ->
                  Forall (optb_ok OW4) l /\ (forall p n, In (Some (p, n)) l -> badr OW p = badr OW4 p)).
    { intros l Hl Hids.
      assert (ONE : forall p n, In (Some (p, n)) l -> In (p, badr OW p, n) OW4 /\ badr OW4 p = badr OW p /\ 0 < badr OW p).
      { intros p n Hin. pose proof (proj1 (Forall_forall _ _) Hl _ Hin) as [HIn Hpos]. cbn in HIn, Hpos.
        destruct (SURV p (p, badr OW p, n) (Hids p n Hin) HIn eq_refl) as (I4 & E4 & _). split; [exact I4|]. split; [exact E4|exact Hpos]. }
      split.
      - apply Forall_forall. intros [[p n]|] Hin; cbn -[badr]; [|exact I]. destruct (ONE p n Hin) as (I4 & E4 & Hpos). rewrite E4. split; [exact I4|exact Hpos].
      - intros p n Hin. symmetry. exact (proj1 (proj2 (ONE p n Hin))). }
    destruct (GEN (as_file stc') OFc ltac:(intros p n Hin; eapply es_ids_in; left; exact Hin)) as [OF4 EF4].
    destruct (GEN (as_func stc') ONc ltac:(intros p n Hin; eapply es_ids_in; right; left; exact Hin)) as [ON4 EN4].
    destruct (GEN (as_data stc') ODc ltac:(intros p n Hin; eapply es_ids_in; right; right; exact Hin)) as [OD4 ED4].
    (* [comment removed for export] *)
    split.
    { change (st_fin pf pn) with (set_func tn (Some (pn, fnlen)) (set_line tn line (set_file tn (Some (pf, flen)) stc'))).
      rewrite g_of_set_func, g_of_set_line, g_of_set_file.
      rewrite (g_of_adr_ext stc' (badr OW4) (badr OW)) by (intros p n Hin; symmetry; eauto).
      unfold stc', st_a. rewrite g_of_set_func, g_of_set_file. unfold gfin, g2, g1.
      cbn [EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot EK.set_g_fi EK.set_g_li EK.set_g_fu as_file as_func set_func set_file set_line optr].
      unfold MallocRep.wz. rewrite BPN, BPF, !upd_upd_same. reflexivity. }
    (* [comment removed for export] *)
    split.
    { change (as_file (st_fin pf pn)) with (lset (as_file stc') tn (Some (pf, flen))). apply optb_ok_lset_some; [exact OF4| |rewrite BPF; exact BP1].
      rewrite BPF. subst OW4. right. exact PF3. }
    split.
    { change (as_func (st_fin pf pn)) with (lset (as_func stc') tn (Some (pn, fnlen))). apply optb_ok_lset_some; [exact ON4| |rewrite BPN; exact BQ1].
      rewrite BPN. subst OW4. left. reflexivity. }
    split; [change (as_data (st_fin pf pn)) with (as_data stc'); exact OD4|].
    (* [comment removed for export] *)
    split.
    { intros mX HR. change (as_cnf (st_fin pf pn)) with (as_cnf st). subst OW4. apply rest_OW_consA; [| |exact BQ1|clear - BQ4 C63; lia|exact BQ2].
      - subst OW3. apply rest_lremoveA.
        + subst OW2. apply rest_OW_consA; [| |exact BP1|clear - BP4 C63; lia|exact BP2].
          * subst OW1. apply rest_lremoveA; [exact HR|]. intros q n GF. split; [eapply file_not_rest; [exact IDS|exact GF]|eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]].
          * intros Hin. apply NI1. rewrite map_app. apply in_app_iff. left. exact Hin.
        + intros q n GN. split; [eapply func_not_rest; [exact IDS|exact GN]|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]].
      - intros Hin. apply NI2. rewrite map_app. apply in_app_iff. left. exact Hin. }
    (* [comment removed for export] *)
    split.
    { intros i q k Hd. symmetry. eapply (ED4 q k). unfold get_data in Hd. rewrite <- Hd. apply nth_In.
      destruct (Nat.lt_ge_cases i (length (as_data st))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ None Hl) in Hd. discriminate. }
    (* [comment removed for export] *)
    split.
    { intros b Hb Hin.
      assert (CASES : blk_id b = pn \/ blk_id b = pf \/ In (blk_id b) (es_ids st)).
      { unfold es_ids in Hin. apply in_map_iff in Hin. destruct Hin as (x & Ex & Hx).
        pose proof (Permutation_in _ P4 Hx) as [<-|Hx1]; [left; symmetry; exact Ex|].
        assert (Hx2 : In x (st_blocks (st_b pf))) by (eapply Permutation_in; [exact P3|]; apply in_app_iff; right; exact Hx1).
        pose proof (Permutation_in _ P2 Hx2) as [<-|Hx3]; [right; left; symmetry; exact Ex|].
        right. right. rewrite <- Ex. unfold es_ids. apply in_map. eapply Permutation_in; [exact P1|]. apply in_app_iff. right. exact Hx3. }
      pose proof (KIDS b Hb) as NK. rewrite in_app_iff in NK.
      assert (Hb1 : In b OW1).
      { subst OW1. apply lremove_keep; [apply KOW; exact Hb|]. intros q n GF EQ. apply NK. left. rewrite EQ. eapply es_ids_file. exact GF. }
      assert (Hb3 : In b OW3).
      { apply IN3; [exact Hb1|]. intros q n GN EQ. apply NK. left. rewrite EQ. eapply es_ids_func. exact GN. }
      destruct CASES as [C|[C|C]]; [exact (PN3 b Hb3 C)|exact (PF1 b Hb1 C)|apply NK; left; exact C]. }
    (* [comment removed for export] *)
    unfold st_fin, st_c, st_b, st_a. repeat apply es_shape_setters. exact SH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma HW2 : forall (L : list block) (P : bptr -> Prop), In (p_es E, e_es E, 904) L -> P (p_es E) ->
    Forall (segW (L ++ LB) lo (bv_unsigned sp) P) W2.
  Proof.
    intros L P HIN HP. constructor; [left; cbn; clear - LO; unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in *; lia|]. constructor; [| constructor].
    right; right. exists (p_es E), (e_es E), 904. split; [apply in_app_iff; left; exact HIN|]. split; [exact HP | cbn; clear; lia].
  Qed.
  Lemma es_seg_writable : seg_writableA OW st E K (p_es E).
  Proof. exact (es_writableA OW st E bo0 K IDS AS0 KIDS). Qed.
  Lemma es_in1 : In (p_es E, e_es E, 904) (lremove (get_file tn st) OW).
  Proof. apply lremove_keep; [exact IES|]. intros q n GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. Qed.
  Lemma es_in3 : forall pf A1, In (p_es E, e_es E, 904) (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)).
  Proof.
    intros pf A1. apply lremove_keep; [right; apply es_in1|]. intros q n GN. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN].
  Qed.

  Lemma sb_munch : forall c Σc OWc mb mc, SB c Σc OWc mb -> munch W2 mb mc -> wmono ctasegs mb mc -> SB c Σc OWc mc.
  Proof.
    intros c Σc OWc mb mc SBb MU WM. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBb) as IESc.
    eapply (seg_baseA_munch m OW st E bo0 LB K (bv_unsigned sp) lo Σ CEIL LOSP TOP'); [exact SBb|exact MU|exact WM|].
    apply HW2; [exact IESc|]. split; [exact es_seg_writable|]. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map. exact IESc.
  Qed.

  (* [comment removed for export] *)
  Lemma sb_icall : forall c Σc OWc mb mc (bd : block) D N SP',
    SB c Σc OWc mb -> ACEIL <= SP' -> SP' <= bv_unsigned sp ->
    (N <= 0 \/ (In bd OWc /\ seg_writableA OW st E K (blk_id bd) /\ blk_id bd <> p_es E /\ blk_addr bd <= D /\ D + N <= blk_addr bd + blk_size bd)) ->
    agree_on (fun a => aclient_addr (OWc ++ LB) SP' a /\ ~ (D <= a < D + N)) mb mc -> AHEAP Σc OWc LB mc ->
    SB c Σc OWc mc.
  Proof.
    intros c Σc OWc mb mc bd D N SP' SBb CSP HSP HB AG HEAP'.
    pose proof SBb as (HEAP & AX & HAR & RB & DC & DIN & KP & KOWc & IESc & CR). pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    (* [comment removed for export] *)
    set (ok := fun b : block => N <= 0 \/ blk_id b <> blk_id bd).
    assert (AGS : agree_on (fun a => (SP' <= a < USTACK_TOP) \/ client_static a \/ (exists b, In b (OWc ++ LB) /\ ok b /\ blk_addr b <= a < blk_addr b + blk_size b)) mb mc).
    { eapply agree_on_mono; [exact AG|]. intros a Ha.
      destruct HB as [HN|(INb & _ & _ & B1 & B2)].
      { split; [|clear - HN; lia]. destruct Ha as [Ha|[Ha|(b & Hb & _ & Hr)]]; [left; exact Ha|right; left; exact Ha|right; right; exists b; split; [exact Hb|exact Hr]]. }
      assert (INb' : In bd (OWc ++ LB)) by (apply in_app_iff; left; exact INb).
      pose proof (AH_range_gen _ _ _ _ bd HEAP INb') as (_ & _ & _ & BC & _).
      destruct Ha as [Ha|[Ha|(b & Hb & Hok & Hr)]].
      - split; [left; exact Ha|]. clear - Ha CSP BC B1 B2. lia.
      - split; [right; left; exact Ha|]. intros Hd. apply (blk_not_static _ _ _ _ bd a HEAP INb'); [clear - Hd B1 B2; lia| exact Ha].
      - split; [right; right; exists b; split; [exact Hb|exact Hr]|]. destruct Hok as [HN|NE]; [clear - HN; lia|].
        pose proof (AH_disjoint_gen _ _ _ _ b bd HEAP Hb INb' NE) as DJ. unfold blk_apart in DJ. clear - DJ Hr B1 B2. lia. }
    assert (OKid : forall b, In b (OWc ++ LB) -> (N <= 0 \/ blk_id b <> blk_id bd) -> ok b) by (intros b _ H; exact H).
    split; [exact HEAP'|]. split.
    { eapply ax_pres_trans; [exact AX|]. unfold ax_pres. eapply agree_on_mono; [exact AGS|]. intros a [NA Ha].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha HSP; lia|right; left; exact Ha|right; right].
      exists b. assert (HbL : In b (OWc ++ LB)) by (apply in_app_iff; right; exact Hb). split; [exact HbL|]. split; [|exact Hr].
      destruct HB as [HN|(INb & _)]; [left; exact HN|right]. intros EQ.
      apply (nodup_app_disj (map blk_id OWc) (map blk_id LB) (blk_id b)); [rewrite <- map_app; exact ND| rewrite EQ; apply in_map; exact INb| apply in_map; exact Hb]. }
    split.
    { eapply rest_agreeA; [exact HAR|]. eapply agree_on_mono; [exact AGS|]. intros a [Ha|(b & Hb & Hr)].
      - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Ha)).
      - right; right. exists b. split; [exact (RB b Hb)|]. split; [|exact Hr]. destruct HB as [HN|(INb & (W1 & _) & _)]; [left; exact HN|right].
        intros EQ. apply W1. rewrite <- EQ. apply in_map. exact Hb. }
    split; [exact RB|]. split.
    { destruct DC as [DC1 DF]. split; [|exact DF]. intros i q k Hd. destruct (DC1 i q k Hd) as [Hk [junk HC]]. split; [exact Hk|]. exists junk.
      eapply rw_cells_agree; [exact AGS|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - Hk; lia).
      right; right. exists (q, badr OW q, k). split; [exact (DIN i q k Hd)|]. split; [|cbn; clear - Ha; lia].
      destruct HB as [HN|(INb & (_ & W2' & _) & _)]; [left; exact HN|right]. cbn. intros EQ. exact (W2' i q k Hd EQ). }
    split; [exact DIN|]. split.
    { eapply kept_trans; [exact KP|]. intros a Ha (b & Hb & Hr). apply (AGS a Ha). right; right. exists b.
      split; [apply in_app_iff; left; apply KOWc; exact Hb|]. split; [|exact Hr].
      destruct HB as [HN|(INb & (_ & _ & W3) & _)]; [left; exact HN|right]. intros EQ. apply W3. rewrite <- EQ. apply in_map. exact Hb. }
    split; [exact KOWc|]. split; [exact IESc|exact CR].
  Qed.

  Lemma mcost_small : forall n, n <= 64512 -> mcost n = 0.
  Proof. intros n H. unfold mcost. replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_finish : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (Σc : rts RT) (m9 : mem)
      (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z),
    SB 1 Σc ((pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) m9 ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> ablock_range A1 flen ->
    ~ In pn (map blk_id (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB)) -> ablock_range A2 fnlen ->
    es_raw m9 (e_es E) (gfin A1 A2) -> stk ctasegs m9 lo (bv_unsigned sp) -> mem_inv ctasegs m9 ->
    POST (tt, st_fin pf pn) Σc
         (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 A2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m9 (seg_rom ctasegs)).
  Proof.
    intros until A2. intros SB9 NI1 BR1 NI2 BR2 ES ST MI.
    set (OW4 := (pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) in *.
    destruct SB9 as (HEAP9 & AX9 & AR9 & RB9 & DC9 & DIN9 & KP9 & KOW9 & IES9 & CR9).
    destruct (fin_pureA pf A1 pn A2 NI1 BR1 NI2 BR2) as (IDS' & IDIN' & GEQ & OF' & OFN' & OD' & REST' & BD' & KIDS' & SH').
    fold OW4 in IDIN', GEQ, OF', OFN', OD', REST', BD'.
    assert (AS9 : ap_state (st_fin pf pn) m9 OW4 E bo0).
    { apply ap_state_joinA; [apply REST'; exact AR9|exact SH'|rewrite GEQ; exact ES|exact OF'|exact OFN'|exact OD']. }
    assert (DC9' : data_cells m9 OW4 (st_fin pf pn)).
    { apply (data_cells_subA m9 OW4 st); [|intros i q k Hd; exists i; exact Hd|eapply dflags_ok_same; [reflexivity|reflexivity|eapply data_cells_dflagsA; exact DC9]].
      eapply data_cells_OWA; [exact DC9|exact BD']. }
    revert AS9 DC9' IDS' KIDS'. generalize (st_fin pf pn). intros FIN' AS9 DC9' IDS9 KID9. clearbody OW4.
    unfold POST, ap_postA.
    exists t0, t1, t2, (Z_to_bv 64 A2), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F', fc', m9, OW4, bo0.
    split; [reflexivity|].
    split.
    { unfold ap_preA. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS9|]. split; [exact DC9'|]. split; [exact ST|]. split; [exact CEIL|].
      split; [pose proof LOSP as X; clear - X; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [exact MI|].
      split; [pose proof (af_credit_nonneg RT AF Σc m9 (AH_art _ _ _ _ HEAP9)) as X; clear - X; lia|]. split; [clear; lia|]. clear - FRM. lia. }
    split; [exact AX9|].
    split; [clear - CR9 COST1; lia|].
    split; [| reflexivity].
    split; [exact KOW9|]. split; [exact KID9 | exact KP9].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_tail : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mc : mem) (j0 : list byte)
      (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z),
    SB 1 Σc ((pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> ablock_range A1 flen ->
    ~ In pn (map blk_id (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB)) -> ablock_range A2 fnlen ->
    seg_writableA OW st E K pn ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) (sd_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g2 A1) ->
    implAp (ARet (tt, st_fin pf pn)) Σc POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 Ln) (Z_to_bv 64 A2) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 768)) (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 768) 3 + SHB)) x20 x21 (Z_to_bv 64 SHB)
               (Z_to_bv 64 (e_es E + Z.of_nat tn * 8)) x24 x25 s10 s11 x28 x29 x30 x31)   (* [comment removed for export] *)
          F (wz SD_TAIL) fc None mc (seg_rom ctasegs)).
  Proof.
    intros until A2. intros SBc NI1 BR1 NI2 BR2 FWn FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW4 := (pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) in *.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as HEAPc. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as IESc.
    pose proof (AH_ceil _ _ _ _ HEAPc) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITN as (_ & _ & _ & _ & LENN & _ & LNL & LNH & LN64).
    assert (GL : g_len (g2 A1)).
    { unfold g2, g1. pose proof (g_len_of st (badr OW) SH) as GL0.
      unfold CtRepP.ApErrKit.g_len in GL0 |- *; cbn [EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot EK.set_g_fi EK.set_g_li] in GL0 |- *; rewrite ?upd_length; exact GL0. }
    pose proof BR2 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    assert (EA2 : bv_unsigned (Z_to_bv 64 A2) = A2) by (apply unsigned_lit; clear - BQ1 BQ3 BQ4 C3; alia).
    assert (IESc' : In (p_es E, e_es E, 904) (OW4 ++ LB)) by (apply in_app_iff; left; exact IESc).
    assert (INpn : In (pn, A2, fnlen) OW4) by (subst OW4; left; reflexivity).
    assert (NEpn : pn <> p_es E).
    { intros EQ. apply NI2. rewrite EQ, map_app. apply in_app_iff. left. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map. apply es_in3. }
    pose proof (blk_disjointA _ _ _ _ pn A2 fnlen (p_es E) (e_es E) 904 HEAPc ltac:(apply in_app_iff; left; exact INpn) IESc' NEpn) as DJ2.
    pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPc IESc') as (_ & _ & EESC & EESI & _).
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPc IESc') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPc IESc' ACCE OFFE.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z mc) as MU. pose proof (wmono_refl ctasegs mc) as WM.
    unfold sd_frame in FR. unfold SD_TAIL, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_fu mc (e_es E) _ tn (Z_to_bv 64 A2) ES GL TNB'). name_mem m1.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?EA2 in KK; clear - KK BQ1; lia|]. clear KK. (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. do 11 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    pose proof (sb_munch _ _ _ _ _ SBc MU WM) as SB1. pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB1) as HEAP1.
    clear MU WM ACCE.
    apply evt_done. eapply implAp_step_same.
    { eapply (strcpy_lit_cpsA STRCPY) with (d := A2) (s := Ln) (str := nstr) (slack := nslack) (n := fnlen) (bd := (pn, A2, fnlen)) (lo := lo) (OW := OW4) (LB := LB);
        [exact HEAP1 | exact ST | exact CEIL | unfold RT_STACK; clear - LOu; lia | exact TOP | exact AL16 | exact MI | reflexivity | exact LITN
        | apply in_app_iff; left; exact INpn | cbn; clear; lia | cbn; clear; lia | reflexivity | reflexivity ]. }
    intros ms9 PO. unfold icall_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F9 & fc9 & m9 & -> & MI9 & ST9 & HEAP9 & WM9 & AG9 & BZ9 & WR9).
    assert (SB9 : SB 1 Σc OW4 m9).
    { eapply (sb_icall 1 Σc OW4 m1 m9 (pn, A2, fnlen) A2 fnlen (bv_unsigned sp)); [exact SB1 | clear - CEIL LOu; lia | clear; lia | | exact AG9 | exact HEAP9].
      right. split; [exact INpn|]. split; [exact FWn| split; [exact NEpn | cbn; clear; lia]]. }
    eapply es_raw_agree in ES; [|exact GL|exact AG9|].
    2:{ intros a Ha. split; [right; right; exists (p_es E, e_es E, 904); split; [exact IESc'|cbn; clear - Ha; lia] | cbn in Ha; clear - Ha DJ2; lia]. }
    apply implAp_ret. unfold MallocRep.wz.
    change (EK.set_g_fu (upd (EK.g_fu (g2 A1)) tn (Z_to_bv 64 A2)) (g2 A1)) with (gfin A1 A2) in ES.
    eapply (sd_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ F9 fc9 Σc m9 pf A1 pn A2); [exact SB9|exact NI1|exact BR1|exact NI2|exact BR2|exact ES|exact ST9|exact MI9].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_mid3 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mc : mem) (j0 : list byte)
      (pf : bptr) (A1 : Z),
    SB 1 Σc (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> ablock_range A1 flen ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) (sd_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g2 A1) ->
    implAp (REST3 (st_c pf)) Σc POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 Ln) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 768)) (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 768) 3 + SHB)) x20 x21 (Z_to_bv 64 SHB)
               (Z_to_bv 64 (e_es E + Z.of_nat tn * 8)) x24 x25 s10 s11 x28 x29 x30 x31)   (* [comment removed for export] *)
          F (wz SD_MID3) fc None mc (seg_rom ctasegs)).
  Proof.
    intros until A1. intros SBc NI1 BR1 FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW3 := lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) in *.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as HEAPc. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as IESc.
    pose proof (AH_ceil _ _ _ _ HEAPc) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITN as (_ & _ & _ & _ & LENN & GDN & LNL & LNH & LN64).
    assert (GL : g_len (g2 A1)).
    { unfold g2, g1. pose proof (g_len_of st (badr OW) SH) as GL0.
      unfold CtRepP.ApErrKit.g_len in GL0 |- *; cbn [EK.g_fl EK.g_ma EK.g_bu EK.g_da EK.g_ds EK.g_df EK.g_fi EK.g_li EK.g_fu EK.g_top EK.g_bot EK.set_g_fi EK.set_g_li] in GL0 |- *; rewrite ?upd_length; exact GL0. }
    destruct (lit_firstA _ _ _ _ LITN) as (c0 & nstr' & EN & C0).
    pose proof (lit_bytes_atA mc Ln nstr nslack fnlen MI LITN) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    assert (IESc' : In (p_es E, e_es E, 904) (OW3 ++ LB)) by (apply in_app_iff; left; exact IESc).
    (* [comment removed for export] *)
    pose proof (af_lit_acc RT AF Σc mc Ln fnlen (AH_art _ _ _ _ HEAPc) GDN) as ACCL.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z mc) as MU. pose proof (wmono_refl ctasegs mc) as WM.
    assert (OFF1 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
    unfold sd_frame in FR. unfold SD_MID3, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - LNL LNH; lia); clear - KK LNL; lia|]. clear KK.
    pose proof (u8ro_read ctasegs mc Ln _ 0 c0 (wa (Ln + 0)) HS ltac:(rewrite EN; reflexivity) ltac:(clear; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - C0R; lia); exact (C0 KK)|]. clear KK.
    (* [comment removed for export] *)
    zstep. zstep.
    clear MU WM.
    apply evt_done. eapply implAp_step_same.
    { eapply strlen_lit_cpsA with (s := Ln) (str := nstr) (slack := nslack) (n := fnlen) (lo := lo) (OW := OW3) (LB := LB);
        [exact HEAPc | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold RT_STACK; clear - LOu; lia | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia
        | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact LITN | reflexivity ]. }
    intros msL PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & WM3 & AG3 & _).
    rewrite (ret_pc_even SD_SL2_RA) by (clear; unfold SD_SL2_RA; lia). unfold SD_SL2_RA, MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; split; [left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia | clear; lia]].
    eapply es_raw_agree in ES; [|exact GL|exact AG3|].
    2:{ intros a Ha. split; [right; right; exists (p_es E, e_es E, 904); split; [exact IESc'|cbn; clear - Ha; lia] | clear; lia]. }
    assert (SB3 : SB 1 Σc OW3 m3).
    { eapply (sb_icall 1 Σc OW3 mc m3 (p_es E, e_es E, 904) 0 0 (bv_unsigned sp + -96)); [exact SBc | clear - CEIL LOu; lia | clear; lia | left; clear; lia | exact AG3 | exact HEAP3]. }
    pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) as CS3.
    clear AG3 HS SBc HEAPc MI ST ACCL. 
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. setreg 10 (Z_to_bv 64 fnlen) ltac:(f_equal; clear - LENN; lia).
    zstep. zstep. zstep.
    clear MU WM.
    apply evt_done. unfold REST3. unfold abind at 1. unfold amalloc at 1. cbn [apbind].
    eapply CRYPTO_malloc_walkAp with (n := fnlen) (lo := lo) (OW := OW3) (LB := LB);
      [exact HEAP3 | rewrite ESP; exact ST3 | exact CEIL | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI3 | reflexivity | exact CS3 | reflexivity
      | clear - LENN LN64 SBD; lia | rewrite (mcost_small fnlen LN64); pose proof (af_credit_nonneg RT AF Σc m3 (AH_art _ _ _ _ HEAP3)) as X; clear - X; lia
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB3)) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_malloc2 CTX) | ].
    intros pn Σ4 ms4 Hpn PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & m4 & A2 & -> & MI4 & ST4 & AG4 & CR4 & BR4 & HEAP4 & ACC4 & (junk & HBLK)).
    rewrite ESP in ST4, AG4. rewrite (ret_pc_even SD_TAIL) by (clear; unfold SD_TAIL; lia). cbn [apbind fst snd].
    unfold amodify. change (set_func tn (Some (pn, fnlen)) (st_c pf)) with (st_fin pf pn).
    (* [comment removed for export] *)
    assert (SB4 : SB 1 Σ4 ((pn, A2, fnlen) :: OW3) m4).
    { pose proof (seg_baseA_malloc m OW st E bo0 LB K (bv_unsigned sp) Σ 1 Σc Σ4 OW3 m3 m4 pn A2 fnlen (bv_unsigned sp + -96) fnlen SB3 AG4 ltac:(clear; lia) HEAP4 CR4) as X.
      rewrite (mcost_small fnlen LN64), Z.add_0_r in X. exact X. }
    pose proof (fresh_writableA m OW st E bo0 LB K (bv_unsigned sp) Σ _ _ _ _ pn SB3 Hpn) as FWn.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [exact IESc'|cbn; clear - Ha; lia]. }
    eapply (sd_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 Σ4 m4 j0 pf A1 pn A2);
      [exact SB4|exact NI1|exact BR1|exact Hpn|exact BR4|exact FWn|exact FR|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_mid2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mc : mem) (j0 : list byte)
      (pf : bptr) (A1 : Z),
    SB 1 Σc ((pf, A1, flen) :: lremove (get_file tn st) OW) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> ablock_range A1 flen -> seg_writableA OW st E K pf ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) (sd_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implAp (REST2 pf st_a) Σc POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 Ln) (Z_to_bv 64 A1) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 line) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 Lf) (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 576)) (Z_to_bv 64 SHB)
               (Z_to_bv 64 (e_es E + Z.of_nat tn * 8)) (Z_to_bv 64 (Z.of_nat tn)) (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 576) 3 + SHB)) s10 s11 x28 x29 x30 x31)
          F (wz SD_MID2) fc None mc (seg_rom ctasegs)).
  Proof using ACE AL16 AS0 BE CEIL COST1 CTX EES16 EESB EESP FRM IDIN IDS IES KIDS KOW LITF LITN LO OD OF OFN SH STRCPY TOP UW.
    intros until A1. intros SBc NI1 BR1 FW1 FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW2 := (pf, A1, flen) :: lremove (get_file tn st) OW) in *.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as HEAPc. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as IESc.
    pose proof (AH_ceil _ _ _ _ HEAPc) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITF as (_ & _ & _ & _ & LENF & _ & LFL & LFH & LF64).
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    pose proof BR1 as (BP1 & BP2 & BP3 & BP4 & BP5).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    assert (EA1 : bv_unsigned (Z_to_bv 64 A1) = A1) by (apply unsigned_lit; clear - BP1 BP3 BP4 C3; alia).
    assert (IESc' : In (p_es E, e_es E, 904) (OW2 ++ LB)) by (apply in_app_iff; left; exact IESc).
    assert (INpf : In (pf, A1, flen) OW2) by (subst OW2; left; reflexivity).
    assert (NEpf : pf <> p_es E).
    { intros EQ. apply NI1. rewrite EQ, map_app. apply in_app_iff. left. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map. apply es_in1. }
    pose proof (blk_disjointA _ _ _ _ pf A1 flen (p_es E) (e_es E) 904 HEAPc ltac:(apply in_app_iff; left; exact INpf) IESc' NEpf) as DJ1.
    pose proof (blk_boundsA _ _ _ _ _ _ _ HEAPc IESc') as (_ & _ & EESC & EESI & _).
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAPc IESc') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAPc IESc' ACCE OFFE.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z mc) as MU. pose proof (wmono_refl ctasegs mc) as WM.
    unfold sd_frame in FR. unfold SD_MID2, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    es_store (es_wr_fi mc (e_es E) _ tn (Z_to_bv 64 A1) ES GL TNB'). name_mem m1.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?EA1 in KK; clear - KK BP1; lia|]. clear KK. (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (sb_munch _ _ _ _ _ SBc MU WM) as SB1. pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB1) as HEAP1.
    clear MU WM ACCE.
    apply evt_done. eapply implAp_step_same.
    { eapply (strcpy_lit_cpsA STRCPY) with (d := A1) (s := Lf) (str := fstr) (slack := fslack) (n := flen) (bd := (pf, A1, flen)) (lo := lo) (OW := OW2) (LB := LB);
        [exact HEAP1 | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold RT_STACK; clear - LOu; lia | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia
        | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact LITF
        | apply in_app_iff; left; exact INpf | cbn; clear; lia | cbn; clear; lia | reflexivity | reflexivity ]. }
    intros ms2 PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2' & fc2' & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ2 & WR2).
    rewrite (ret_pc_even SD_CPY1_RA) by (clear; unfold SD_CPY1_RA; lia). unfold SD_CPY1_RA, MallocRep.wz.
    assert (SB2 : SB 1 Σc OW2 m2).
    { eapply (sb_icall 1 Σc OW2 m1 m2 (pf, A1, flen) A1 flen (bv_unsigned sp + -96)); [exact SB1 | clear - CEIL LOu; lia | clear; lia | | exact AG2 | exact HEAP2].
      right. split; [exact INpf|]. split; [exact FW1| split; [exact NEpf | cbn; clear; lia]]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOPu; lia | clear - Ha BP4 CEIL LOu; alia]].
    eapply es_raw_agree in ES; [|exact GL|exact AG2|].
    2:{ intros a Ha. split; [right; right; exists (p_es E, e_es E, 904); split; [exact IESc'|cbn; clear - Ha; lia] | cbn in Ha; clear - Ha DJ1; lia]. }
    clear AG2 SB1 HEAP1 MI ST SBc HEAPc OFFE. rename ST2 into ST. rename MI2 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU3. pose proof (wmono_refl ctasegs m2) as WM3.
    ablock HEAP2 IESc' ACCE OFFE.
    apply implAp_from_evt.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia). (* [comment removed for export] *)
    (* [comment removed for export] *)
    es_store (es_wr_li m2 (e_es E) _ tn (Z_to_bv 64 line) ES GL TNB'). name_mem m3.
    pose proof (es_rd_fu m3 (e_es E) _ tn (wa (e_es E + 768 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD. setreg 18 (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 768)) ltac:(f_equal; clear - TOPB; lia). setreg 19 (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 768) 3 + SHB)) ltac:(replace (e_es E + Z.of_nat tn * 8 + 768) with (e_es E + 8 * Z.of_nat tn + 768) by (clear; lia); reflexivity).
    setreg 10 (Z_to_bv 64 (optr (badr OW) (get_func tn st))) ltac:(cbn [EK.g_fu EK.g_of EK.set_g_fi EK.set_g_li]; rewrite nth_wl_optr; reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    pose proof (sb_munch _ _ _ _ _ SB2 MU3 WM3) as SB3.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) as HEAP3. pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) as CS3.
    clear MU3 WM3 ACCE.
    apply evt_done.
    unfold REST2. unfold abind at 1. unfold amodify. cbn [apbind fst snd].
    change (set_line tn line (set_file tn (Some (pf, flen)) st_a)) with (st_b pf).
    unfold abind at 1. rewrite free_func_slot_tree, apbind_ofree. cbn [apbind fst snd].
    change (get_func tn (st_b pf)) with (get_func tn st). change (set_func tn None (st_b pf)) with (st_c pf).
    change (abind (amalloc fnlen) _ (st_c pf)) with (REST3 (st_c pf)).
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_func tn st) (adr := badr OW) (OW := OW2) (LB := LB);
      [exact HEAP3 | | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS3 | reflexivity
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB3)) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free2 CTX) | ].
    { destruct (get_func tn st) as [[qn nn]|] eqn:GN; [|exact I]. subst OW2. right.
      apply lremove_keep; [exact (proj1 (optb_ok_nth OW _ tn qn nn OFN GN))|].
      intros q n GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    intros Σ4 ms4 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
    rewrite (ret_pc_even SD_MID3) by (clear; unfold SD_MID3; lia).
    (* [comment removed for export] *)
    assert (SB4 : SB 1 Σ4 (lremove (get_func tn st) OW2) m4).
    { eapply (seg_baseA_free m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact SB3| |exact AG4|clear; lia|exact HEAP4|exact CR4].
      intros q n GN. split; [|split].
      - subst OW2. cbn [map blk_id fst snd]. right. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map.
        apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN].
      - split; [eapply func_not_rest; [exact IDS|exact GN]|]. split; [intros i q' k Hd EQ; subst q'; exact (ids_func_data_ne E st tn i q n q k IDS GN Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]. }
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; apply es_in3|cbn; clear - Ha; lia]. }
    change (EK.set_g_li (upd (EK.g_li (EK.set_g_fi (upd (EK.g_fi (g_of st (badr OW))) tn (Z_to_bv 64 A1)) (g_of st (badr OW)))) tn (Z_to_bv 64 line))
              (EK.set_g_fi (upd (EK.g_fi (g_of st (badr OW))) tn (Z_to_bv 64 A1)) (g_of st (badr OW)))) with (g2 A1) in ES.
    eapply (sd_mid3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 Σ4 m4 j0 pf A1); [exact SB4|exact NI1|exact BR1|exact FR|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_mid1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Σc : rts RT) (mc : mem) (j0 : list byte),
    SB 1 Σc (lremove (get_file tn st) OW) mc ->
    rw_cells ctasegs mc (bv_unsigned sp + -96) (sd_frame j0) ->
    stk ctasegs mc lo (bv_unsigned sp + -96) -> mem_inv ctasegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implAp (REST1 st_a) Σc POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 Ln) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 line) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 Lf) (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 576)) (Z_to_bv 64 SHB)
               (Z_to_bv 64 (e_es E + Z.of_nat tn * 8)) (Z_to_bv 64 (Z.of_nat tn)) (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 576) 3 + SHB)) s10 s11 x28 x29 x30 x31)
          F (wz SD_MID1) fc None mc (seg_rom ctasegs)).
  Proof using ACE AL16 AS0 BE CEIL COST1 CTX EES16 EESB EESP FRM IDIN IDS IES KIDS KOW LITF LITN LO OD OF OFN SH STRCPY TOP UW.
    intros until j0. intros SBc FR ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW1 := lremove (get_file tn st) OW) in *.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as HEAPc. pose proof (seg_baseA_es _ _ _ _ _ _ _ _ _ _ _ _ _ SBc) as IESc.
    pose proof (AH_ceil _ _ _ _ HEAPc) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITF as (_ & _ & _ & _ & LENF & GDF & LFL & LFH & LF64).
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    destruct (lit_firstA _ _ _ _ LITF) as (c0 & fstr' & EF & C0).
    pose proof (lit_bytes_atA mc Lf fstr fslack flen MI LITF) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    assert (IESc' : In (p_es E, e_es E, 904) (OW1 ++ LB)) by (apply in_app_iff; left; exact IESc).
    pose proof (af_lit_acc RT AF Σc mc Lf flen (AH_art _ _ _ _ HEAPc) GDF) as ACCL.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z mc) as MU. pose proof (wmono_refl ctasegs mc) as WM.
    assert (OFF1 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
    unfold sd_frame in FR. unfold SD_MID1, MallocRep.wz in *.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - LFL LFH; lia); clear - KK LFL; lia|]. clear KK.
    pose proof (u8ro_read ctasegs mc Lf _ 0 c0 (wa (Lf + 0)) HS ltac:(rewrite EF; reflexivity) ltac:(clear; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - C0R; lia); exact (C0 KK)|]. clear KK.
    (* [comment removed for export] *)
    zstep. zstep.
    clear MU WM.
    apply evt_done. eapply implAp_step_same.
    { eapply strlen_lit_cpsA with (s := Lf) (str := fstr) (slack := fslack) (n := flen) (lo := lo) (OW := OW1) (LB := LB);
        [exact HEAPc | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold RT_STACK; clear - LOu; lia | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia
        | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact LITF | reflexivity ]. }
    intros msL PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MI3 & ST3 & HEAP3 & WM3 & AG3 & _).
    rewrite (ret_pc_even SD_SL1_RA) by (clear; unfold SD_SL1_RA; lia). unfold SD_SL1_RA, MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; split; [left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia | clear; lia]].
    eapply es_raw_agree in ES; [|exact GL|exact AG3|].
    2:{ intros a Ha. split; [right; right; exists (p_es E, e_es E, 904); split; [exact IESc'|cbn; clear - Ha; lia] | clear; lia]. }
    assert (SB3 : SB 1 Σc OW1 m3).
    { eapply (sb_icall 1 Σc OW1 mc m3 (p_es E, e_es E, 904) 0 0 (bv_unsigned sp + -96)); [exact SBc | clear - CEIL LOu; lia | clear; lia | left; clear; lia | exact AG3 | exact HEAP3]. }
    pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) as CS3.
    clear AG3 HS SBc HEAPc MI ST ACCL.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. setreg 10 (Z_to_bv 64 flen) ltac:(f_equal; clear - LENF; lia).
    zstep. zstep. zstep.
    clear MU WM.
    apply evt_done. unfold REST1. unfold abind at 1. unfold amalloc at 1. cbn [apbind].
    eapply CRYPTO_malloc_walkAp with (n := flen) (lo := lo) (OW := OW1) (LB := LB);
      [exact HEAP3 | rewrite ESP; exact ST3 | exact CEIL | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI3 | reflexivity | exact CS3 | reflexivity
      | clear - LENF LF64 SBD; lia | rewrite (mcost_small flen LF64); pose proof (af_credit_nonneg RT AF Σc m3 (AH_art _ _ _ _ HEAP3)) as X; clear - X; lia
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB3) FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB3)) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_malloc1 CTX) | ].
    intros pf Σ4 ms4 Hpf PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & m4 & A1 & -> & MI4 & ST4 & AG4 & CR4 & BR4 & HEAP4 & ACC4 & (junk & HBLK)).
    rewrite ESP in ST4, AG4. rewrite (ret_pc_even SD_MID2) by (clear; unfold SD_MID2; lia). cbn [apbind fst snd].
    change (abind _ _ st_a) with (REST2 pf st_a).
    (* [comment removed for export] *)
    assert (SB4 : SB 1 Σ4 ((pf, A1, flen) :: OW1) m4).
    { pose proof (seg_baseA_malloc m OW st E bo0 LB K (bv_unsigned sp) Σ 1 Σc Σ4 OW1 m3 m4 pf A1 flen (bv_unsigned sp + -96) flen SB3 AG4 ltac:(clear; lia) HEAP4 CR4) as X.
      rewrite (mcost_small flen LF64), Z.add_0_r in X. exact X. }
    pose proof (fresh_writableA m OW st E bo0 LB K (bv_unsigned sp) Σ _ _ _ _ pf SB3 Hpf) as FWf.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [exact IESc'|cbn; clear - Ha; lia]. }
    eapply (sd_mid2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 Σ4 m4 j0 pf A1); [exact SB4|exact Hpf|exact BR4|exact FWf|exact FR|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_act : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    AHEAP Σ OW LB m -> ap_state st m OW E bo0 -> data_cells m OW st ->
    stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> tp = wz TP_A ->
    (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    implAp (err_set_debug rs st) Σ POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Lf) (wz line) (wz Ln) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_SET_DEBUG) fc None m (seg_rom ctasegs)).
  Proof.
    intros until fc. intros HEAP AS DC ST MI -> FLEN CRED.
    unfold ERR_SET_DEBUG, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
    pose proof TOP as TOPu. unfold USTACK_TOP in TOPu. pose proof LO as LOu. unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK in LOu.
    pose proof LITF as (_ & _ & _ & _ & LENF & _ & LFL & LFH & LF64). pose proof LITN as (_ & _ & _ & _ & LENN & _ & LNL & LNH & LN64).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    assert (IES' : In (p_es E, e_es E, 904) (OW ++ LB)) by (apply INCL; exact IES).
    unfold err_set_debug. unfold abind at 1. unfold aget. cbn [apbind fst snd].
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z) by (cbn [offshW]; alia).
    apply implAp_from_evt.
    carve_frame 96%nat ST. do 13 zstep. do 2 zstep.
    zstep. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    name_mem m0.
    assert (HW0 : Forall (segW (OW ++ LB) lo (bv_unsigned sp) (fun _ => False)) [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (12227404, 12227404 + 4)]%Z).
    { constructor; [left; cbn; clear - LOu; lia|]. constructor; [right; left; reflexivity | constructor]. }
    destruct (seg_closeA Σ OW LB _ m m0 lo (bv_unsigned sp) (fun _ => False) HEAP CEIL ltac:(clear - LOu; lia) ltac:(clear - TOPu; unfold USTACK_TOP; lia) MU WM HW0 ltac:(intros p A n _ []))
      as [HEAP0 AX0].
    assert (AS0' : ap_state st m0 OW E bo0) by (eapply (ap_state_of_munchA Σ st m m0); [exact AS | exact HEAP | exact CEIL | exact MU | exact HW0]).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; clear - SPR LOu CEIL C1; lia).
    destruct (errno_cellA m0) as [errv HERR].
    apply evt_done. intros X Φ D SAFE LINK.
    eapply (get_state_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (E := E) (st := st) (bo := bo0) (v := 1);
      [exact HEAP0 | exact AS0' | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact FLEN | exact CRED
      | exact HERR | right; reflexivity | reflexivity |].
    intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 errv2 HEAP2 CR2 EL2 ST2 MI2 AG2 HERR2.
    rewrite ESP in ST2, AG2. rewrite (ret_pc_even SD_RA1) by (clear; unfold SD_RA1; lia). unfold SD_RA1.
    match goal with |- cps _ (ASTA _ _ _ (eq ?ms)) _ => eapply (implAp_elim _ Σ Σ2 POST ms X Φ D); [| exact SAFE | exact LINK | exact EL2] end.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; split; [left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia | cbn [cells_size csize Nat.add] in Ha; unfold ERRNO_A, TP_A; clear - Ha LOu CEIL C1; lia]].
    pose proof (lib_agree_of_ex_errno Σ OW LB m0 m0 m2 _ HEAP0 AG2) as LAG2.
    assert (AXb : ax_pres LB (bv_unsigned sp) LIBW_A m m2) by (eapply ax_pres_trans; [exact AX0 | eapply (ax_pres_of_ex_errno OW LB); [exact AG2 | clear; lia]]).
    assert (AS2 : ap_state st m2 OW E bo0) by (eapply ap_state_agree; [exact AS0' | exact LAG2]).
    assert (DCb : data_cells m2 OW st).
    { eapply data_cells_agree; [| exact LAG2 | exact OD]. eapply (data_cells_of_munchA Σ OW LB _ m m0); [exact DC | | exact HEAP | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []].
      intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (KPb : kept K m m2).
    { eapply kept_trans; [| eapply kept_of_lib_agree; [exact KOW | exact LAG2]].
      eapply (kept_of_munchA Σ OW LB _ m m0 K lo); [exact HEAP | intros b Hb; apply INCL; apply KOW; exact Hb | exact CEIL | exact MU | eapply segW_mono; [| exact HW0]; intros p []]. }
    assert (SB2 : SB 1 Σ2 OW m2).
    { eapply (seg_baseA_intro m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact HEAP2|exact AXb|exact AS2|exact DCb|exact KPb|exact KOW|rewrite CR2; clear; lia]. }
    pose proof (ap_state_esA _ _ _ _ _ AS2) as (ES & GL & _).
    clear MU WM OFF HW0 HEAP0 AX0 AS0' AS HEAP DC HERR LAG2 MI ST AG2 AXb DCb KPb. try clear SHB1_ SHB2_. clear m0.
    pose proof (munch_refl [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3.
    assert (OFF2 : offshW [(bv_unsigned sp - (96 + (48 + (112 + 65536))), bv_unsigned sp); (e_es E, e_es E + 904)]%Z).
    { pose proof (AH_offsh _ _ _ _ _ HEAP2 IES') as OFFE. cbn [blk_addr blk_size fst snd] in OFFE. cbn [offshW]. alia. }
    ablock HEAP2 IES' ACCE OFFE. pose proof (blk_boundsA _ _ _ _ _ _ _ HEAP2 IES') as (_ & _ & EESC & EESI & _).
    unfold MallocRep.wz. apply implAp_from_evt.
    zstep. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by (clear - EESP EESB; lia); clear - KK EESP EESB; lia|]. clear KK. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (es_rd_top m2 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD. zstep. clear RD.
    pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    cbn [EK.g_top EK.g_of]. rewrite !sx32_small by (clear - TOPB; lia). fold tn.
    (* [comment removed for export] *)
    zstep. rewrite ?(unsigned_lit (Z.of_nat tn)) by (clear - TOPB; lia). rewrite ?Z.shiftl_mul_pow2 by (clear; lia).
    pose proof TNB as TNB'.
    pstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (es_rd_fi m2 (e_es E) _ tn (wa (e_es E + 576 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. zstep. clear RD.
    setreg 21 (Z_to_bv 64 (e_es E + 8 * Z.of_nat tn + 576)) ltac:(f_equal; clear - TOPB; lia).
    try setreg 25 (Z_to_bv 64 (Z.shiftr (e_es E + 8 * Z.of_nat tn + 576) 3 + SHB))
          ltac:(rewrite ?unsigned_lit by (clear - TOPB EESP EESB; lia); replace (e_es E + Z.of_nat tn * 8 + 576) with (e_es E + 8 * Z.of_nat tn + 576) by (clear; lia); reflexivity).
    setreg 10 (Z_to_bv 64 (optr (badr OW) (get_file tn st))) ltac:(cbn [EK.g_fi EK.g_of]; rewrite nth_wl_optr; reflexivity).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    pose proof (sb_munch _ _ _ _ _ SB2 MU2 WM2) as SB2'.
    pose proof (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB2') as HEAP2'. pose proof (seg_baseA_crypto_statics _ _ _ _ _ _ _ _ _ _ _ _ _ SB2') as CS2.
    clear MU2 WM2 ACCE.
    apply evt_done.
    unfold abind at 1. rewrite free_file_slot_tree, apbind_ofree. cbn [apbind fst snd].
    change (abind (amalloc (rs_flen rs)) _ st_a) with (REST1 st_a).
    eapply CRYPTO_free_opt_walkAp with (lo := lo) (od := get_file tn st) (adr := badr OW) (OW := OW) (LB := LB);
      [exact HEAP2' | | rewrite ESP; exact ST2 | exact CEIL | rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOu; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | exact MI2 | reflexivity | exact CS2 | reflexivity
      | rewrite ESP; uw_call_ax_tac m 96 UW (seg_baseA_ax _ _ _ _ _ _ _ _ _ _ _ _ _ SB2') FR;
          [clear; lia | pose proof (AH_ceil _ _ _ _ (seg_baseA_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SB2')) as (Cq1 & _ & _); unfold SEGTOP_A in *; clear - LOu CEIL Cq1; unfold BnHeapA.ACEIL in *; lia
          | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOPu; unfold USTACK_TOP; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_free1 CTX) | ].
    { destruct (get_file tn st) as [[qf nf]|] eqn:GF; [|exact I]. exact (proj1 (optb_ok_nth OW _ tn qf nf OF GF)). }
    intros Σ3 ms3 PO. unfold ofree_postA in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
    rewrite (ret_pc_even SD_MID1) by (clear; unfold SD_MID1; lia).
    (* [comment removed for export] *)
    assert (SB3 : SB 1 Σ3 (lremove (get_file tn st) OW) m3).
    { eapply (seg_baseA_free m OW st E bo0 LB K (bv_unsigned sp) Σ); [exact SB2'| |exact AG3|clear; lia|exact HEAP3|exact CR3].
      intros q n GF. split; [|split].
      - pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn.
      - split; [eapply file_not_rest; [exact IDS|exact GF]|]. split; [intros i q' k Hd EQ; subst q'; exact (ids_file_data_ne E st tn i q n q k IDS GF Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOPu; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG3|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [apply in_app_iff; left; apply es_in1|cbn; clear - Ha; lia]. }
    eapply (sd_mid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 Σ3 m3 _); [exact SB3|exact FR|exact ST3|exact MI3|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_set_debug_walkA : forall rs file func, ERR_set_debug_specA rs file func.
  Proof.
    intros rs file func bo0 fstr fslack nstr nslack LITF LITN. unfold ap_stmtA. intros until K. intros ras PRE TP UW CTX NE (A0 & A1 & A2 & EBO) KOW KIDS. subst bo a0 a1 a2.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP' & TOP & AL16 & MI & CRED & FRM).
    unfold ERR_SET_DEBUG_STACK, ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES in *.
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    pose proof (ids_in_introA _ _ _ _ _ AS) as IDIN.
    pose proof (AH_ceil _ _ _ _ HEAP) as (_ & _ & ACE).
    eapply (sd_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ st OW LB E bo0 lo rs file func fstr fslack nstr nslack
              IDS CEIL ACE ltac:(unfold SD_STK, GET_STATE_STACK, IB_STACK, IB_FRAME; clear - LOSP'; lia) TOP AL16 SH IES EESP EESB EES16 OF OFN OD (ex_intro _ m AS) IDIN LITF LITN K KOW KIDS
              ERR_SET_DEBUG_COST ltac:(unfold ERR_SET_DEBUG_COST; clear; lia) ltac:(clear - FRM; lia) ras UW CTX);
      [exact HEAP | exact AS | exact DC | exact ST | exact MI | exact TP | clear - FRM; unfold FRAMES_MAX in *; lia | clear - CRED; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_specA_stmt : forall rs file func fstr fslack nstr nslack,
    lit_okA file fstr fslack (rs_flen rs) -> lit_okA func nstr nslack (rs_fnlen rs) ->
    ERR_set_debug_specA rs file func -> ERR_set_debug_stmtA rs file func.
  Proof.
    intros rs file func fstr fslack nstr nslack LF LN H. unfold ERR_set_debug_stmtA, ERR_set_debug_specA, ap_stmtA in *. intros until K. intros ras PRE TP UW CTX NE (A0 & A1 & A2) KOW KIDS.
    eapply implAp_mono; [eapply (H bo fstr fslack nstr nslack LF LN); [exact PRE|exact TP|exact UW|exact CTX|exact NE|repeat split; assumption|exact KOW|exact KIDS]|].
    intros [a st'] Σ' ms' PO. cbv beta in PO |- *.
    destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & E1 & PRE2 & AXP2 & CRED2 & KEPT2 & RES2).
    do 17 eexists. exists m2, OW2, bo2. repeat (split; [eassumption|]). exact I.
  Qed.

  Theorem ERR_set_debug_closedA : forall rs file func fstr fslack nstr nslack,
    lit_okA file fstr fslack (rs_flen rs) -> lit_okA func nstr nslack (rs_fnlen rs) -> ERR_set_debug_stmtA rs file func.
  Proof. intros rs file func fstr fslack nstr nslack LF LN. eapply ERR_set_debug_specA_stmt; [exact LF|exact LN|apply ERR_set_debug_walkA]. Qed.

End WithStrcpy2.
End WithRT.
