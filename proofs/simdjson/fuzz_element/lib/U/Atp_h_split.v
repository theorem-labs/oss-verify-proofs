(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_defs Atp_arrl Atp_obje Atp_h_defs Atp_h_push Atp_h_find.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition split_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (V D : Z) (d : list Z) (m : mem)
    (v' : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' cap' : Z) (blk' : option bptr) (jr' : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ v' = (cap', zlength (poffs d), blk') /\ blk' <> None /\ cap' <= 2 * zlength (poffs d)
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (vblocks blk' A' cap' ++ LB0) m'
    /\ vrep m' V A' v' (map (pview D) (poffs d)) jr'
    /\ lx_pres LB0 q [(V, V + 24)] m m'.

Lemma rw_cells_split_at : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma frame_junk3 : forall m A (x y z : cell) rest, rw_cells usegs m A (x :: y :: z :: rest) ->
  csize x = 8%nat -> csize y = 8%nat -> csize z = 8%nat ->
  rw_cells usegs m A (CB 8 (cbytes x) :: CB 8 (cbytes y) :: CB 8 (cbytes z) :: rest).
Proof.
  intros m A x y z rest H Ex Ey Ez. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn [cells_wf] in Hwf. destruct Hwf as (Wx & Wy & Wz & Wr).
  eapply rw_cells_recast; [exact H| | |].
  - cbn [cells_wf cell_wf]. rewrite !cbytes_length by assumption. repeat split; try assumption; congruence.
  - reflexivity.
  - cbn [cells_size csize]. rewrite Ex, Ey, Ez. reflexivity.
Qed.

Lemma pview_fst : forall D e, fst (pview D e) = D + Z.of_nat (fst e). Proof. intros D [a b]; reflexivity. Qed.
Lemma pview_snd : forall D e, snd (pview D e) = Z.of_nat (snd e). Proof. intros D [a b]; reflexivity. Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (s : PState) (LB0 : list block) (q lo B V D : Z) (d : list Z) (m : mem).
  Notation POST := (split_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B V D d m).

  Notation FRAME c0 p8 p16 cd cl := ([CB 8 c0; CB 8 p8; CB 8 p16; C8 (Z_to_bv 64 cd); C8 (Z_to_bv 64 cl); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Hypothesis DNE : d <> [].
  Hypothesis DBYT : Forall (fun c => 0 <= c < 256) d.
  Hypothesis D0 : 0 < D.
  Hypothesis DIN : exists b, In b LB0 /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b.
  Hypothesis NB : zlength d < 2^26.
  Hypothesis QB : q <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOQ : lo <= q - (80 + 128 + RMALLOC_STACK).
  Hypothesis QV : q <= V.
  Hypothesis VB : V + 24 <= B.

  Lemma parts_bound : 4 * (zlength (poffs d) - 1) <= zlength d.
  Proof.
    unfold zlength. rewrite poffs_length. unfold atp_parts. destruct d as [|c d']; [cbn; lia|].
    pose proof (split_go_count (S (length (c :: d'))) (c :: d')). lia.
  Qed.

  Lemma poffs_d : poffs d = poffs_of 0 d.
  Proof. rewrite poffs_eq. destruct d; [exfalso; exact (DNE eq_refl)| reflexivity]. Qed.

  Lemma done_bound : forall done (off : nat) cur, poffs_of 0 d = done ++ poffs_of off cur -> zlength done + 1 <= zlength (poffs d) /\ 4 * zlength done <= zlength d.
  Proof.
    intros done off cur H. pose proof parts_bound as PB. rewrite poffs_d in PB |- *. unfold zlength in *. rewrite H, length_app in PB |- *.
    pose proof (poffs_of_nonnil off cur) as NN. destruct (poffs_of off cur) as [|e r] eqn:E; [congruence|]. cbn [length] in *. lia.
  Qed.

  Lemma blocks_below : forall st LB mm a, RHEAP st LB mm -> in_block LB a -> a < alloc_ceiling.
  Proof.
    intros st LB mm a H (b0 & Hb & Hr). pose proof (LH_block_range _ _ _ _ H Hb) as (_ & _ & _ & BC & _).
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia.
  Qed.

  Lemma payload_agree : forall LBx (P : Z -> Prop) m1 m2, agree_on P m1 m2 -> (forall a, in_block LB0 a -> P a) ->
    bytes_at usegs m1 D (to_bytes d) -> LBx = LB0 -> bytes_at usegs m2 D (to_bytes d).
  Proof.
    intros LBx P m1 m2 AG HB H _. destruct DIN as (b0 & Hb & H1 & H2). eapply bytes_at_agree; [exact AG| exact H|].
    rewrite to_bytes_length. intros a Ha. apply HB. exists b0. split; [exact Hb| unfold zlength in H2; lia].
  Qed.

  Lemma split_final : forall (cur : list Z) (off : nat) (done : list (nat * nat))
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs1 xs2 t3 t4 t5 t6 : word) (m1 : mem) (st1 : PState) (errv1 : word)
      (A cap : Z) (blk : option bptr) (jr : list byte) (c0 p8 p16 : list byte),
    cur = skipn off d -> Z.of_nat off + zlength cur = zlength d -> find_sep cur = None ->
    poffs_of 0 d = done ++ poffs_of off cur ->
    vrep m1 V A (cap, zlength done, blk) (map (pview D) done) jr -> cap <= Z.max 1 (2 * zlength done) ->
    RHEAP st1 (vblocks blk A cap ++ LB0) m1 -> rauxv_ok m1 B -> mem_inv usegs m1 -> stk usegs m1 lo (q + -80) ->
    rw_cells usegs m1 LX_ERRNO [C4 errv1] -> ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> lx_pres LB0 q [(V, V + 24)] m m1 ->
    rw_cells usegs m1 (q + -80) (FRAME c0 p8 p16 (D + Z.of_nat off) (zlength d - Z.of_nat off)) ->
    implM usegs (vpushes lops (length (parts_of cur)) (cap, zlength done, blk)) st1 POST
      (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) xs1 a0 a1 a2 a3 a4 a5 a6 a7
               xs2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3e2fc) fc None m1 (seg_rom usegs)).
  Proof.
    intros until p16; intros HCUR OFFN HN HPO VR CAPB HEAP AUX MI ST ERR FA SO PRES FR.
    unfold RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (done_bound _ _ _ HPO) as [DB1 DB2]. pose proof parts_bound as PBD. pose proof NB as NB'. change (2^26) with 67108864 in NB'.
    assert (N0 : 0 <= zlength cur) by (unfold zlength; lia).
    assert (DL : 0 <= zlength done) by (unfold zlength; lia).
    assert (DR : 0 < D /\ D + zlength d <= alloc_ceiling).
    { destruct DIN as (b0 & Hb & Hb1 & Hb2). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & _ & _ & R4 & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia. }
    rewrite parts_of_unfold, HN. cbn [length]. rewrite vpushes_S.
    pose proof (munch_refl [(q - 80, q)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    destruct (rw_cells_split_at _ _ _ 3%nat FR) as [FRA FRB]. cbn [firstn skipn cells_size csize Nat.add] in FRA, FRB.
    destruct (rw_cells_split_at _ _ _ 2%nat FRB) as [FRX FRC]. cbn [firstn skipn cells_size csize Nat.add] in FRX, FRC. clear FRB FR.
    replace (q + -80 + Z.of_nat 24) with (q + -56) in FRX by lia. replace (q + -80 + Z.of_nat 24 + Z.of_nat 16) with (q + -40) in FRC by lia.
    unfold implM. iprefix.

    step. step. step.
    ihere. to_implM. eapply implM_bind.
    { eapply (push2_spec HM HF) with (B := B) (lo := lo) (els := map (pview D) done) (jr := jr) (X := q + -56) (xd := D + Z.of_nat off) (xl := zlength d - Z.of_nat off);
        [exact HEAP| exact AUX| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR| exact MI
        | lia| lia| lia| lia| lia| exact VR| clear - CAPB DB1 PBD NB'; lia| lia| lia| exact FRX]. }
    cbv beta. intros v' st' ms' PO. unfold push_post in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                    & -> & Ev' & Ecap2 & BNN & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & PRES2).
    replace (ret_pc (Z_to_bv 64 0x3e308)) with (Z_to_bv 64 0x3e308) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2. subst v'. rewrite vpushes_O.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
    assert (FRCL : forall a, q + -80 <= a < q -> lx_client LB0 (q + -80) [(V, V + 24)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRA; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRX; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRC; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    pose proof (rw_cells_join _ _ _ _ _ FRA FRX ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 FRC ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR. clear J1 FRA FRX FRC.
    clear MU WM. pose proof (munch_refl [(q - 80, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    apply implM_ret.

    do 5 step. step. release_frame FR ST2 q. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    destruct VR2 as (ELS2 & SZ2 & SV2 & BLK2).
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a Ha. eapply (blocks_below _ _ _ a HEAP2). eapply in_block_incl; [| exact Ha]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    apply evt_done. unfold split_post. do 15 eexists. exists m3, errv2, A2, cap2, blk2, jr2.
    split; [cbv delta [mkR]; reflexivity|].
    assert (EPO : poffs d = done ++ [(off, length cur)]) by (rewrite poffs_d, HPO, poffs_of_unfold, HN; reflexivity).
    assert (ELEN : zlength (poffs d) = zlength done + 1) by (rewrite EPO; unfold zlength; rewrite length_app; cbn [length]; lia).
    split; [rewrite ELEN; reflexivity|]. split; [exact BNN|]. split; [rewrite ELEN, Ecap2; unfold vcap_next; destruct (Z.ltb_spec (zlength done) cap); lia|].
    split; [assumption|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    split; [congruence|]. split; [congruence|].
    split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    split.
    { rewrite EPO, map_app. change (map (pview D) [(off, length cur)]) with [(D + Z.of_nat off, Z.of_nat (length cur))].
      replace (Z.of_nat (length cur)) with (zlength d - Z.of_nat off) by (unfold zlength in *; lia).
      exact (conj ELS2 (conj SZ2 (conj SV2 BLK2))). }
    eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_trans.
    { eapply (lx_pres_sub LB0 q _ _ _ _ _ _ PRES2); [lia| intros b0 Hb0; exact Hb0|]. intros a Ha NX. exfalso. exact (NX Ha). }
    eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia].
  Qed.

  Lemma split_loop : forall (k : nat) (cur : list Z) (off : nat) (i : nat) (done : list (nat * nat))
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (st1 : PState) (errv1 : word)
      (A cap : Z) (blk : option bptr) (jr : list byte) (c0 p8 p16 : list byte),
    (length cur <= k)%nat -> cur = skipn off d -> Z.of_nat off + zlength cur = zlength d -> find_sep cur = Some i ->
    poffs_of 0 d = done ++ poffs_of off cur ->
    vrep m1 V A (cap, zlength done, blk) (map (pview D) done) jr -> cap <= Z.max 1 (2 * zlength done) ->
    RHEAP st1 (vblocks blk A cap ++ LB0) m1 -> rauxv_ok m1 B -> mem_inv usegs m1 -> stk usegs m1 lo (q + -80) ->
    rw_cells usegs m1 LX_ERRNO [C4 errv1] -> ps_fa st1 = ps_fa s -> ps_so st1 = ps_so s -> lx_pres LB0 q [(V, V + 24)] m m1 ->
    bytes_at usegs m1 D (to_bytes d) ->
    rw_cells usegs m1 (q + -80) (FRAME c0 p8 p16 (D + Z.of_nat off) (zlength d - Z.of_nat off)) ->
    implM usegs (vpushes lops (length (parts_of cur)) (cap, zlength done, blk)) st1 POST
      (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 V) (Z_to_bv 64 ATP_SEP) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3e2a4) fc None m1 (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until p16; intros HK HCUR OFFN HS HPO VR CAPB HEAP AUX MI ST ERR FA SO PRES PB FR.
    { exfalso. destruct cur; [cbn in HS; discriminate| cbn [length] in HK; lia]. }
    unfold RMALLOC_STACK, GLOBALS_TOP, ATP_SEP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof (done_bound _ _ _ HPO) as [DB1 DB2]. pose proof parts_bound as PBD. pose proof NB as NB'. change (2^26) with 67108864 in NB'.
    assert (N0 : 0 <= zlength cur) by (unfold zlength; lia).
    assert (DL : 0 <= zlength done) by (unfold zlength; lia).
    assert (DR : 0 < D /\ D + zlength d <= alloc_ceiling).
    { destruct DIN as (b0 & Hb & Hb1 & Hb2). pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & _ & _ & R4 & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia. }
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a Ha. eapply (blocks_below _ _ _ a HEAP). eapply in_block_incl; [| exact Ha]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    pose proof (find_sep_spec _ _ HS) as IB.
    assert (ZC : zlength cur = Z.of_nat (length cur)) by reflexivity. assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    rewrite parts_of_unfold, HS. cbn [length]. rewrite vpushes_S.
    pose proof (munch_refl [(q - 80, q)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    destruct (rw_cells_split_at _ _ _ 1%nat FR) as [FRA FRB]. cbn [firstn skipn cells_size csize Nat.add] in FRA, FRB.
    destruct (rw_cells_split_at _ _ _ 2%nat FRB) as [FRX FRC]. cbn [firstn skipn cells_size csize Nat.add] in FRX, FRC. clear FRB FR.
    replace (q + -80 + Z.of_nat 8) with (q + -72) in FRX by lia. replace (q + -80 + Z.of_nat 8 + Z.of_nat 16) with (q + -56) in FRC by lia.
    destruct (rw_cells_split_at _ _ _ 2%nat FRC) as [FRX2 FRD]. cbn [firstn skipn cells_size csize Nat.add] in FRX2, FRD. clear FRC.
    replace (q + -56 + Z.of_nat 16) with (q + -40) in FRD by lia.
    destruct VR as (ELS & SZ & SV & BLK). hide SV. hide BLK.
    unfold implM. iprefix.

    astep. step. step. step.
    eapply substr_cps_le with (SV := q + -56) (A := D + Z.of_nat off) (n := zlength d - Z.of_nat off) (pos := 0) (cnt := Z.of_nat i) (RA := 0x3e2b4);
      [exact FRX2| lia| lia| lia| lia| lia| lia| reflexivity| lia| reflexivity|].
    intros ya3 ya4 ya5. replace (D + Z.of_nat off + 0) with (D + Z.of_nat off) by lia.

    step. step. astep. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
    assert (HEAP0 : RHEAP st1 (vblocks blk A cap ++ LB0) m1').
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX0 : rauxv_ok m1' B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES0 : lx_pres LB0 q [(V, V + 24)] m m1').
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    unhide SV. unhide BLK.
    assert (VR0 : vrep m1' V A (cap, zlength done, blk) (map (pview D) done) jr).
    { eapply vrep_agree; [exact AG0| | | exact (conj ELS (conj SZ (conj SV BLK)))].
      - intros a Ha. cbn [outside]. lia.
      - intros a Hb Ha. cbn [outside]. destruct blk as [b0|]; [| congruence]. unfold vblk in BLK. destruct BLK as (_ & _ & (A00 & _ & _ & A0C & _) & _).
        unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in A0C. lia. }
    clear SV BLK MU WM AG0.
    ihere. to_implM. eapply implM_bind.
    { eapply (push1_spec HM HF) with (B := B) (lo := lo) (els := map (pview D) done) (jr := jr) (X := q + -72) (xd := D + Z.of_nat off) (xl := Z.of_nat i);
        [exact HEAP0| exact AUX0| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| rewrite ELX; eassumption| assumption
        | lia| lia| lia| lia| lia| exact VR0| clear - CAPB DB1 PBD NB'; lia| lia| lia| exact FRX]. }
    cbv beta. intros v' st' ms' PO. unfold push_post in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                    & -> & Ev' & Ecap2 & BNN & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & PRES2).
    replace (ret_pc (Z_to_bv 64 0x3e2c8)) with (Z_to_bv 64 0x3e2c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR2. subst v'.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
    assert (FRCL : forall a, q + -80 <= a < q -> lx_client LB0 (q + -80) [(V, V + 24)] a).
    { intros a Ha. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRA; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRX; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRX2; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    lazymatch goal with PBx : bytes_at usegs _ D _ |- _ =>
      apply (bytes_at_agree _ _ _ _ _ AG2) in PBx; [rename PBx into PB2| rewrite LBL; intros a Ha; destruct DIN as (b0 & Hb & Hb1 & Hb2); split;
        [cbn [rin_ivs fst snd]; unfold zlength in Hb2; lia| right; left; exists b0; split; [exact Hb| unfold zlength in Hb2; lia]]] end.
    assert (BLB2 : forall a, in_block LB0 a -> a < alloc_ceiling).
    { intros a Ha. eapply (blocks_below _ _ _ a HEAP2). eapply in_block_incl; [| exact Ha]. intros b0 Hb0. apply in_or_app. right. exact Hb0. }
    assert (PRES2' : lx_pres LB0 q [(V, V + 24)] m m2).
    { eapply lx_pres_trans; [exact PRES0|]. eapply (lx_pres_sub LB0 q _ _ _ _ _ _ PRES2); [lia| intros b0 Hb0; exact Hb0|]. intros a Ha NX. exfalso. exact (NX Ha). }
    destruct VR2 as (ELS2 & SZ2 & SV2 & BLK2). hide SV2. hide BLK2.
    clear AG2 PRES2 HEAP0 AUX0 PRES0 VR0 HEAP AUX MI ERR ST PRES.
    pose proof (munch_refl [(q - 80, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix.

    astep. astep. astep. step.
    eapply substr_cps with (SV := q + -56) (A := D + Z.of_nat off) (n := zlength d - Z.of_nat off) (pos := Z.of_nat i + 4) (RA := 0x3e2d8);
      [exact FRX2| lia| lia| lia| | lia| lia| reflexivity| lia| reflexivity|].
    { match goal with |- _ < bv_unsigned ?w => let v := eval vm_compute in (bv_unsigned w) in change (bv_unsigned w) with v end. lia. }
    intros yb3 yb4 yb5.

    step. step. astep. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.

    set (off' := (off + i + 4)%nat). set (cur' := skipn (i + 4) cur).
    assert (HCUR' : cur' = skipn off' d) by (subst cur' off'; rewrite HCUR, skipn_skipn; f_equal; lia).
    assert (LC' : length cur' = (length cur - (i + 4))%nat) by (subst cur'; rewrite length_skipn; lia).
    assert (ZC' : zlength cur' = Z.of_nat (length cur')) by reflexivity.
    lazymatch goal with H : rw_cells usegs m3 (q + -56) _ |- _ => rename H into FRX2 end.
    replace (Z_to_bv 64 (D + Z.of_nat off + (Z.of_nat i + 4))) with (Z_to_bv 64 (D + Z.of_nat off')) in FRX2 by (f_equal; lia).
    replace (Z_to_bv 64 (zlength d - Z.of_nat off - (Z.of_nat i + 4))) with (Z_to_bv 64 (zlength cur')) in FRX2 by (f_equal; lia).
    try replace (Z_to_bv 64 (zlength d - Z.of_nat off + - (Z.of_nat i + 4))) with (Z_to_bv 64 (zlength cur')) in FRX2 by (f_equal; lia).
    assert (PB3 : bytes_at usegs m3 (D + Z.of_nat off') (to_bytes cur')).
    { rewrite HCUR', to_bytes_skipn. replace (D + Z.of_nat off') with (D + Z.of_nat off') by reflexivity.
      lazymatch goal with PBx : bytes_at usegs m3 D _ |- _ => apply (bytes_at_skipn m3 D (to_bytes d) off' PBx); rewrite LBL; lia end. }
    eapply evt_cut.
    { eapply find_spec with (lo := lo) (l := cur') (P := D + Z.of_nat off') (X := q + -56);
        [assumption| eassumption| lia| lia| lia| lia| lia| exact FRX2| exact PB3| subst cur'; rewrite HCUR; apply Forall_skipn', Forall_skipn'; exact DBYT| lia| lia]. }
    cbv beta. intros ms' PO. unfold find_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & -> & MU4 & WM4 & MI4 & ST4).
    replace (ret_pc (Z_to_bv 64 0x3e2f4)) with (Z_to_bv 64 0x3e2f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    hide MU. hide WM. transport_after_call usegs m3 m4 MU4 WM4. unhide MU. unhide WM.
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    assert (HEAP4 : RHEAP st' (vblocks blk2 A2 cap2 ++ LB0) m4).
    { eapply LH_frame; [eapply LH_frame; [exact HEAP2| exact MU| exact WM|]| exact MU4| exact WM4|]; (constructor; [apply W_ok_stack; cbn; lia| constructor]). }
    assert (AUX4 : rauxv_ok m4 B).
    { eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]| exact MU4| exact WM4|]; (constructor; [cbn; unfold RAUXV_CELL; lia| constructor]). }
    assert (PRES4 : lx_pres LB0 q [(V, V + 24)] m m4).
    { eapply lx_pres_trans; [exact PRES2'|]. eapply lx_pres_trans.
      - eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB2 a HC); lia| lia].
      - eapply lx_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB2 a HC); lia| lia]. }
    unhide SV2. unhide BLK2.
    assert (BKR : forall a, blk2 <> None -> A2 <= a < A2 + 16 * cap2 -> a < alloc_ceiling).
    { intros a Hb Ha. destruct blk2 as [b0|]; [| congruence]. unfold vblk in BLK2. destruct BLK2 as (_ & _ & (A00 & _ & _ & A0C & _) & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in A0C. lia. }
    assert (VR3 : vrep m3 V A2 (cap2, zlength done + 1, blk2) (map (pview D) done ++ [(D + Z.of_nat off, Z.of_nat i)]) jr2).
    { eapply vrep_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | | exact (conj ELS2 (conj SZ2 (conj SV2 BLK2)))].
      - intros a Ha. cbn [outside]. lia.
      - intros a Hb Ha. specialize (BKR a Hb Ha). cbn [outside]. lia. }
    assert (VR4 : vrep m4 V A2 (cap2, zlength done + 1, blk2) (map (pview D) done ++ [(D + Z.of_nat off, Z.of_nat i)]) jr2).
    { eapply vrep_agree; [exact AG4| | | exact VR3].
      - intros a Ha. cbn [outside]. lia.
      - intros a Hb Ha. specialize (BKR a Hb Ha). cbn [outside]. lia. }
    clear SV2 BLK2 MU WM MU4 WM4 AG4 HEAP2 AUX2 PRES2' VR3 BKR. try clear MI2. try clear ST2.
    pose proof (munch_refl [(q - 80, q)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.

    pose proof (rw_cells_join _ _ _ _ _ FRA FRX ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 FRX2 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 FRD ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR. clear J1 J2 FRA FRX FRX2 FRD.
    replace (Z_to_bv 64 (zlength cur')) with (Z_to_bv 64 (zlength d - Z.of_nat off')) in FR by (f_equal; lia).
    assert (HPO' : poffs_of 0 d = (done ++ [(off, i)]) ++ poffs_of off' cur').
    { rewrite HPO, (poffs_of_unfold off cur), HS, <- app_assoc. subst cur' off'. reflexivity. }
    assert (EMAP : map (pview D) done ++ [(D + Z.of_nat off, Z.of_nat i)] = map (pview D) (done ++ [(off, i)])) by (rewrite map_app; reflexivity).
    rewrite EMAP in VR4.
    assert (ELEN : zlength done + 1 = zlength (done ++ [(off, i)])) by (unfold zlength; rewrite length_app; cbn [length]; lia).
    rewrite ELEN in VR4. rewrite ELEN.
    assert (CAPB' : (if zlength done <? cap then cap else vcap_next cap (zlength done)) <= Z.max 1 (2 * zlength (done ++ [(off, i)])))
      by (rewrite <- ELEN; unfold vcap_next; destruct (Z.ltb_spec (zlength done) cap); lia).

    step.
    destruct (find_sep cur') as [i'|] eqn:HS'.
    -
      pose proof (find_sep_spec _ _ HS') as IB'.
      unfold find_res. rewrite HS'. step. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply frame_junk3 in FR; [| reflexivity| reflexivity| reflexivity].
      ihere. to_implM. eapply (IH cur' off' i' (done ++ [(off, i)])); try eassumption; try lia; congruence.
    -
      unfold find_res. rewrite HS'. step. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
      apply frame_junk3 in FR; [| reflexivity| reflexivity| reflexivity].
      ihere. to_implM. eapply (split_final cur' off' (done ++ [(off, i)])); try eassumption; try lia; congruence.
  Qed.

  Lemma split_spec_s : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word) (v0 v8 v16 : list byte),
    RHEAP s LB0 m -> rauxv_ok m B -> mem_inv usegs m -> stk usegs m lo q -> rw_cells usegs m LX_ERRNO [C4 errv] ->
    bytes_at usegs m D (to_bytes d) ->
    rw_cells usegs m V [CB 8 v0; CB 8 v8; CB 8 v16] ->
    implM usegs (vpushes lops (length (parts_of d)) vec0) s POST
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 D) (Z_to_bv 64 (zlength d)) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_SPLIT) fc None m (seg_rom usegs)).
  Proof.
    intros until v16; intros HEAP AUX MI ST ERR PB XV.
    unfold RMALLOC_STACK, GLOBALS_TOP, ATP_SPLIT in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
    pose proof parts_bound as PBD. pose proof NB as NB'. change (2^26) with 67108864 in NB'.
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity.
    assert (DR : 0 < D /\ D + zlength d <= alloc_ceiling).
    { destruct DIN as (b0 & Hb & Hb1 & Hb2). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (R1 & _ & _ & R4 & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in R4. lia. }
    assert (BLB : forall a, in_block LB0 a -> a < alloc_ceiling) by (intros a Ha; exact (blocks_below _ _ _ a HEAP Ha)).
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    pose proof (munch_refl [(q - 80, q); (V, V + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

    do 5 step. step. if_lia. step. hstep. hstep. hstep. step. step.

    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB0 m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB0 q [(V, V + 24)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX. cbn [outside]. split; [| split; [clear - HX; lia| exact I]].
      destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    destruct (rw_cells_split_at _ _ _ 3%nat FR) as [FRA FRB]. cbn [firstn skipn cells_size csize Nat.add] in FRA, FRB.
    destruct (rw_cells_split_at _ _ _ 2%nat FRB) as [FRX FRC]. cbn [firstn skipn cells_size csize Nat.add] in FRX, FRC. clear FRB FR.
    replace (q + -80 + Z.of_nat 24) with (q + -56) in FRX by lia. replace (q + -80 + Z.of_nat 24 + Z.of_nat 16) with (q + -40) in FRC by lia.
    hide MU. hide WM.
    eapply evt_cut.
    { eapply find_spec with (lo := lo) (l := d) (P := D) (X := q + -56);
        [assumption| eassumption| lia| lia| lia| lia| lia| exact FRX| eassumption| exact DBYT| lia| lia]. }
    cbv beta. intros ms' PO. unfold find_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 0x3e290)) with (Z_to_bv 64 0x3e290) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    transport_after_call usegs m1 m2 MU2 WM2. unhide MU. unhide WM.
    assert (HEAP2 : RHEAP s LB0 m2).
    { eapply LH_frame; [exact HEAP1| exact MU2| exact WM2|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX2 : rauxv_ok m2 B).
    { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES2 : lx_pres LB0 q [(V, V + 24)] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_of_munch; [exact MU2| exact WM2|].
      intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }

    lazymatch goal with XVx : rw_cells usegs m2 V _ |- _ => rename XVx into XV2 end.
    assert (VR2 : vrep m2 V 0 vec0 (map (pview D) []) []).
    { unfold vec0, vrep. split; [reflexivity|]. split; [lia|]. split; [cbn; exact XV2|]. cbn. split; reflexivity. }
    assert (HPO : poffs_of 0 d = [] ++ poffs_of 0 d) by reflexivity.
    clear MU WM MU2 WM2 HEAP1 AUX1 PRES1 HEAP AUX MI.
    pose proof (munch_refl [(q - 80, q)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (rw_cells_join _ _ _ _ _ FRA FRX ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 FRC ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR. clear J1 FRA FRX FRC XV2.
    replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + Z.of_nat 0)) in FR by (f_equal; lia).
    replace (Z_to_bv 64 (zlength d)) with (Z_to_bv 64 (zlength d - Z.of_nat 0)) in FR by (f_equal; lia).

    step.
    destruct (find_sep d) as [i|] eqn:HS.
    - pose proof (find_sep_spec _ _ HS) as IB.
      unfold find_res. rewrite HS. step. if_cases K2; zify_cond K2; [exfalso; lia|].

      step. step. step.
      ihere. to_implM. change vec0 with (0, zlength (@nil (nat * nat)), @None bptr).
      apply frame_junk3 in FR; [| reflexivity| reflexivity| reflexivity].
      eapply (split_loop (S (length d)) d 0 i []); try eassumption; try lia; try reflexivity.
    - unfold find_res. rewrite HS. step. if_cases K2; zify_cond K2; [| exfalso; clear - K2; lia].
      ihere. to_implM. change vec0 with (0, zlength (@nil (nat * nat)), @None bptr).
      apply frame_junk3 in FR; [| reflexivity| reflexivity| reflexivity].
      eapply (split_final d 0 []); try eassumption; try lia; try reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
