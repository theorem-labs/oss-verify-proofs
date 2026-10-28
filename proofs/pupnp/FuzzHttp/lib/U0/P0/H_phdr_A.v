(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_strncasecmp H_httpmsg_compare H_ListFind H_list_access H_memptr_cmp H_membuffer_assign H_obj H_freelist H_ListAddTail.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma first_nul : forall (l : list byte) z, In z l -> exists s r, l = s ++ z :: r /\ ~ In z s.
Proof.
  induction l as [|a l IH]; intros z H; [destruct H|].
  destruct (base.decide (a = z)) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct H as [->|H]; [congruence|]. destruct (IH z H) as (s & r & -> & NI).
    exists (a :: s), r. split; [reflexivity|]. intros [E|X]; [exact (NE E)| exact (NI X)].
Qed.

Lemma bytes_at_snoc : forall m a bs b,
  bytes_at rsegs m a bs -> mrd rsegs m (wa (a + Z.of_nat (length bs))) = Some b -> (a + Z.of_nat (length bs) + 1 <= 2^64)%Z ->
  bytes_at rsegs m a (bs ++ [b]).
Proof.
  intros m a bs b (H0 & H1 & HB) RD HI. split; [exact H0|]. rewrite length_app. cbn [length]. split; [lia|].
  intros i Hi. destruct (Nat.lt_ge_cases i (length bs)).
  - rewrite nth_error_app1 by lia. apply HB. lia.
  - assert (i = length bs) by lia. subst i. rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact RD.
Qed.

Lemma bytes_at_extend : forall k m a bs,
  bytes_at rsegs m a bs ->
  (forall x, (a + Z.of_nat (length bs) <= x < a + Z.of_nat (length bs) + Z.of_nat k)%Z -> exists v, mrd rsegs m (wa x) = Some v) ->
  (a + Z.of_nat (length bs) + Z.of_nat k <= 2^64)%Z ->
  exists sl, bytes_at rsegs m a (bs ++ sl) /\ length sl = k.
Proof.
  induction k as [|k IH]; intros m a bs B RD HI.
  - exists []. rewrite app_nil_r. split; [exact B| reflexivity].
  - destruct (RD (a + Z.of_nat (length bs))%Z ltac:(lia)) as [v Hv].
    pose proof (bytes_at_snoc m a bs v B Hv ltac:(lia)) as B1.
    destruct (IH m a (bs ++ [v]) B1) as (sl & B2 & L2).
    + intros x Hx. apply RD. rewrite length_app in Hx. cbn [length] in Hx. lia.
    + rewrite length_app. cbn [length]. lia.
    + exists (v :: sl). rewrite <- app_assoc in B2. cbn [app] in B2. split; [exact B2| cbn; lia].
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation dlseg := (dlseg AI).
  Notation hdrs_mem := (hdrs_mem AI).
  Notation hd_addr := (hd_addr AI).

  #[using="Type"] Lemma block_slack_bytes : forall s LB m (b : BLK) bs,
    RHEAP rsegs AI s LB m -> In b LB -> bytes_at rsegs m (blk_addr b) bs -> Z.of_nat (length bs) = blk_size b ->
    exists sl, bytes_at rsegs m (blk_addr b) (bs ++ sl) /\ Z.of_nat (length sl) = (round_up8 (blk_addr b + blk_size b) - (blk_addr b + blk_size b))%Z.
  Proof.
    intros s LB m b bs HR HIN B L.
    destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _).
    assert (RU : (blk_addr b + blk_size b <= round_up8 (blk_addr b + blk_size b) <= blk_addr b + blk_size b + 7)%Z) by (unfold round_up8; Z.div_mod_to_equations; lia).
    destruct (bytes_at_extend (Z.to_nat (round_up8 (blk_addr b + blk_size b) - (blk_addr b + blk_size b))) m (blk_addr b) bs B) as (sl & B2 & L2).
    - intros x Hx. eapply (ai_block_slack rsegs AI); [exact HR| exact HIN| lia].
    - pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. lia.
    - exists sl. split; [exact B2| lia].
  Qed.

  Fixpoint lf_nodes (ns : list (BLK * Z)) (hs : list (hdr AI)) : list (Z * Z * Z) :=
    match ns, hs with
    | (b, it) :: ns', h :: hs' => (blk_addr b, it, hid AI h) :: lf_nodes ns' hs'
    | _, _ => []
    end.

  #[using="Type"] Lemma lf_lseg : forall ns hs m pv TAIL,
    dlseg m ns pv TAIL -> hdrs_mem m hs -> map snd ns = map (hA AI) hs -> (forall b it, In (b, it) ns -> it <> 0) ->
    lseg m (lf_nodes ns hs) (hd_addr ns TAIL) pv TAIL.
  Proof.
    induction ns as [|[b it] ns IH]; intros [|h hs] m pv TAIL DL HS IT ITNZ; cbn in *; try reflexivity; try discriminate.
    injection IT as E1 IT'. destruct DL as (SZ & NZ & NT & ITR & NC & DL'). destruct HS as (HM & HP & HS').
    destruct HM as ([pad HC] & _). unfold hdro_pure in HP.
    split; [reflexivity|]. split; [exact NT|]. split; [exact NZ|]. split; [eapply ITNZ; left; reflexivity|].
    split; [lia|]. exists (hd_addr ns TAIL), (wz (nA AI h)), (wz (nlen AI h)), pad. split; [exact NC|]. split; [rewrite E1; exact HC|].
    eapply IH; eauto.
  Qed.

  #[using="Type"] Lemma lf_nodes_in : forall ns hs N it id, In (N, it, id) (lf_nodes ns hs) ->
    exists b h, In (b, it) ns /\ In h hs /\ N = blk_addr b /\ id = hid AI h.
  Proof.
    induction ns as [|[b it0] ns IH]; intros [|h hs] N it id H; cbn in H; try destruct H.
    - injection H as <- <- <-. exists b, h. repeat split; try (left; reflexivity).
    - destruct (IH hs N it id H) as (b' & h' & H1 & H2 & H3 & H4). exists b', h'. repeat split; auto; right; auto.
  Qed.

  #[using="Type"] Lemma lf_nodes_in2 : forall ns hs N it id, map snd ns = map (hA AI) hs -> In (N, it, id) (lf_nodes ns hs) ->
    exists b h, In (b, it) ns /\ In h hs /\ N = blk_addr b /\ id = hid AI h /\ it = hA AI h.
  Proof.
    induction ns as [|[b it0] ns IH]; intros [|h hs] N it id IT H; cbn in H, IT; try destruct H; try discriminate.
    - injection H as <- <- <-. injection IT as E _. exists b, h. repeat split; try (left; reflexivity). exact E.
    - injection IT as _ IT'. destruct (IH hs N it id IT' H) as (b' & h' & H1 & H2 & H3 & H4 & H5). exists b', h'. repeat split; auto; right; auto.
  Qed.

  #[using="Type"] Lemma ListFind_call : forall (qq lo L IT qid last size flh fk ffree : Z) (ns : list (Z * Z * Z)) (ja : list byte)
      ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m (first : Z),
    rw_cells rsegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entry) ->
    lseg m ns first L (L + 24) ->
    rw_cells rsegs m IT [CB 16%nat ja; C4 (wz qid)] -> (- 2^31 <= qid < 2^31)%Z ->
    L <> 0%Z -> (L + 96 < 2^64)%Z -> IT <> 0%Z ->
    stk rsegs m lo qq -> (64 <= lo)%Z -> (lo + 48 <= qq)%Z -> (128 <= qq < 2^64)%Z ->
    (qq <= L)%Z -> (qq <= IT)%Z ->
    (forall N it id, In (N, it, id) ns -> N + 24 <= lo /\ it + 24 <= lo)%Z ->
    (L mod 8 = 0)%Z -> (IT mod 8 = 0)%Z -> (forall N it id, In (N, it, id) ns -> N mod 8 = 0 /\ it mod 8 = 0)%Z ->
    mem_inv rsegs m -> a0 = wz L -> a1 = wz 0 -> a2 = wz IT ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (r : Z),
        ms' = MS (mkR ra (wz qq) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(qq - 48, qq)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo qq
        /\ (r = 0 \/ exists it, In (r, it, qid) ns)%Z)
      (MS (mkR ra (wz qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListFind_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until first. intros LC LS ITC QID LNZ LHI ITNZ ST LO0 LO QQ LL LIT SEPN AL AIT AN MI -> -> ->.
    assert (E : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
    destruct (stk_split rsegs _ _ (qq - 48)%Z _ ST ltac:(lia)) as [STlo SThi].
    eapply evt_mono.
    { eapply (ListFind_spec L IT qid last size flh fk ffree ns ja _ (Z_to_bv 64 qq)); rewrite ?E; eauto; try lia.
      intros N it id H. destruct (SEPN N it id H). lia. }
    intros ms' Q. unfold ListFind_post in Q. rewrite !E in Q. destruct_exs Q. destruct Q as (-> & MU & WM & MI' & ST' & RES).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [| exact RES]. eapply stk_merge; [| exact ST'| lia]. eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|]. cbn. lia.
  Qed.

  #[using="Type"] Lemma llist_split : forall m L first last size flh fk ffree fcmp,
    rw_cells rsegs m L (llist_cells first last size flh fk ffree fcmp) <->
    rw_cells rsegs m L (lhead_cells first last size) /\ rw_cells rsegs m (L + 56) (fl_cells flh fk) /\ rw_cells rsegs m (L + 80) [C8 (wz ffree); C8 (wz fcmp)].
  Proof.
    intros. unfold llist_cells, lhead_cells, fl_cells, LISTNODE_SIZEOF, FREELISTSIZE.
    rewrite (rw_cells_app rsegs m L [C8 (wz 0); C8 (wz first); C8 (wz 0); C8 (wz last); C8 (wz 0); C8 (wz 0); C8 (wz size)]
                               [C8 (wz flh); C8 (wz 24); C4 (wz 100); C4 (wz fk); C8 (wz ffree); C8 (wz fcmp)]).
    rewrite (rw_cells_app rsegs m (L + Z.of_nat (cells_size [C8 (wz 0); C8 (wz first); C8 (wz 0); C8 (wz last); C8 (wz 0); C8 (wz 0); C8 (wz size)]))
                               [C8 (wz flh); C8 (wz 24); C4 (wz 100); C4 (wz fk)] [C8 (wz ffree); C8 (wz fcmp)]).
    cbn [cells_size csize Nat.add]. replace (L + Z.of_nat 56)%Z with (L + 56)%Z by lia. replace (L + 56 + Z.of_nat 24)%Z with (L + 80)%Z by lia. LiaTuning.ctauto.
  Qed.

  Section FH.
    Variables (q lo L S : Z) (str slack : list byte).
    Variables (gp tp s0 s1 s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Hypothesis QQ : (128 <= q)%Z.
    Hypothesis LO0 : (64 <= lo)%Z.
    Hypothesis LO : (lo + 80 <= q)%Z.
    Hypothesis QL : (q <= L)%Z.
    Hypothesis LHI : (L + 96 < 2^63)%Z.
    Hypothesis SLO : (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo)%Z.
    Hypothesis S0 : (0 <= S)%Z.
    Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
    Hypothesis PAD : ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
    Hypothesis LA8 : (L mod 8 = 0)%Z.

    Definition fh_post (hs : list (hdr AI)) (x1 : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
      fun ms' => exists (r : Z) x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x23 t3' t4' t5' t6' m',
        ms' = MS (mkR x1' (wz q) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (wz L) s3 s4 (wz r) (wz S) x23 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz 0x14e00) fc None m' (seg_rom rsegs)
        /\ munch [(q - 80, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo q
        /\ (r = 0 \/ exists h, In h hs /\ r = hA AI h).

    Hypothesis strncasecmp_spec : strncasecmp_stmt.

    #[using="QQ LO QL LHI SLO NONUL PAD LA8 strncasecmp_spec"] Lemma fh_loop : forall (sfx : list (BLK * Z)) (hsf hs : list (hdr AI)) (pv : Z) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 m,
      sfx <> [] -> dlseg m sfx pv (L + 24) -> hdrs_mem m hsf -> map snd sfx = map (hA AI) hsf -> (forall h, In h hsf -> In h hs) ->
      (forall h, In h hsf -> 16 <= hA AI h /\ hA AI h + 88 <= lo /\ 16 <= nA AI h /\ nA AI h + (ncap AI h + 1) <= lo /\ 16 <= vA AI h /\ vA AI h + (vcap AI h + 1) <= lo)%Z ->
      (forall b it, In (b, it) sfx -> 16 <= blk_addr b /\ blk_addr b + 24 <= lo)%Z ->
      (forall h, In h hsf -> hA AI h mod 8 = 0)%Z -> (forall b it, In (b, it) sfx -> blk_addr b mod 8 = 0)%Z ->
      bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) -> stk rsegs m lo q -> mem_inv rsegs m ->
      evt rsegs (fh_post hs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m)
        (MS (mkR x1 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz L) s3 s4 x21 (wz S) (wz (hd_addr sfx (L + 24))) s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x14dc0) fc None m (seg_rom rsegs)).
    Proof.
      induction sfx as [|[b it] sfx IH]; intros until m; intros NNE DL HS ITEMS HSUB HF NF HA8 NA8 STR ST MI; [congruence|].
      destruct hsf as [|h hsf]; [discriminate|]. cbn [map] in ITEMS. injection ITEMS as ITEM ITEMS'.
      cbn [H_obj.dlseg] in DL. destruct DL as (SZ & NZ & NT & ITR & NC & DL'). cbn [H_obj.hd_addr].
      cbn [H_obj.hdrs_mem] in HS. destruct HS as (HM & HP & HS'). unfold hdro_mem in HM. destruct HM as ([pad HC] & VC & VB & NCc & [nbs [NB NN]]).
      unfold hdro_pure in HP. destruct (HF h (or_introl eq_refl)) as (H16 & HHI & N16 & NHI & V16 & VHI). destruct (NF b it (or_introl eq_refl)) as (B16 & BHI).
      pose proof (HA8 h (or_introl eq_refl)) as HAL. pose proof (NA8 b it (or_introl eq_refl)) as NAL.
      pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
      pose proof (munch_refl [(q - 80, q)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
      unfold node_cells in NC. rewrite ITEM in NC.
      ub_align. zstep. ub_null. ub_align. zstep. zstep. zstep.
      destruct (proj1 (rw_cells_app rsegs m (hA AI h) [C8 (wz (nA AI h)); C8 (wz (nlen AI h))] [C4 (wz (hid AI h)); C4 pad]) HC) as [MPC _].
      pose proof (rw_cells_bytes _ _ _ NB) as NBB. cbn [cells_bytes cbytes] in NBB. rewrite app_nil_r in NBB.
      assert (LNB : length nbs = Z.to_nat (ncap AI h + 1)) by (destruct NB as [[W _] _]; cbn in W; LiaTuning.ctauto).
      destruct (stk_split rsegs _ _ (q - 80)%Z _ ST ltac:(lia)) as [STlo SThi].
      eapply evt_cut.
      { eapply (memptr_cmp_nocase_call strncasecmp_spec (hA AI h) (nA AI h) (nlen AI h) S nbs str slack q);
          try eassumption; try reflexivity; rewrite ?LNB; lia. }
      cbv beta. intros ms' Q. unfold memptr_cmp_qpost in Q. destruct_exs Q. destruct Q as (-> & MU1 & WM1 & MI1 & ST1 & RR).
      lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end.
      assert (ST1' : stk rsegs m1 lo q).
      { eapply stk_merge; [| exact ST1| lia]. eapply stk_transport_disjoint; [exact STlo| exact MU1| exact WM1| cbn; lia]. }
      pose proof (bytes_at_transport rsegs _ m m1 _ _ STR MU1 ltac:(cbn [disjoint_from]; rewrite length_app; cbn [length]; lia)) as STR1.
      assert (DL1 : dlseg m1 sfx (blk_addr b) (L + 24)).
      { eapply (dlseg_transport AI); [exact DL'| exact MU1| exact WM1|]. intros b0 it0 H0. destruct (NF b0 it0 (or_intror H0)). cbn. lia. }
      assert (HS1 : hdrs_mem m1 hsf).
      { eapply (hdrs_mem_transport AI); [exact HS'| exact MU1| exact WM1|]. intros h0 A n Hh HA.
        destruct (HF h0 (or_intror Hh)) as (? & ? & ? & ? & ? & ?).
        destruct (hregion_block AI h0 A n HA) as [k Hk]. unfold hblocks in Hk.
        destruct Hk as [E|[E|[E|[]]]]; injection E as <- <-; cbn; lia. }
      pose proof (rw_cells_transport rsegs _ m m1 _ _ NC MU1 WM1 ltac:(cbn; lia)) as NC1.
      replace (ret_pc (Z_to_bv 64 0x14de4)) with (Z_to_bv 64 0x14de4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear MU WM. rename MU1 into MU. rename WM1 into WM.
      zstep. if_cases K0; zify_cond K0.
      -
        apply evt_done. unfold fh_post. exists (hA AI h). repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1'|]. right. exists h. split; [apply HSUB; left; reflexivity| reflexivity].
      -
        zstep. zstep. zstep.
        assert (NXR : (0 <= hd_addr sfx (L + 24) < 2^64)%Z).
        { destruct sfx as [|[b2 it2] ?]; cbn; [lia|]. destruct (NF b2 it2 (or_intror (or_introl eq_refl))). lia. }
        call (ListNext_spec L (blk_addr b) pv (hd_addr sfx (L + 24)) (hA AI h)). all: side (first [exact NC1| exact MI1| reflexivity| assumption| lia]).
        zstep. zstep. if_cases K1; zify_cond K1.
        +
          destruct sfx as [|[b2 it2] sfx2] eqn:ES.
          { exfalso. cbn in K1. rewrite Z.eqb_refl in K1. cbn in K1. lia. }
          pose proof DL1 as DLx. cbn [H_obj.dlseg] in DLx. destruct DLx as (_ & _ & NT2 & _). cbn [H_obj.hd_addr] in *.
          replace (if blk_addr b2 =? L + 24 then 0 else blk_addr b2) with (blk_addr b2) by (destruct (Z.eqb_spec (blk_addr b2) (L + 24)); [contradiction| reflexivity]).
          eapply evt_cut.
          { eapply (IH hsf hs (blk_addr b)); try eassumption; try discriminate.
            - intros h0 Hh. apply HSUB. right. exact Hh.
            - intros h0 Hh. apply HF. right. exact Hh.
            - intros b0 it0 H0. eapply NF. right. exact H0.
            - intros h0 Hh. apply HA8. right. exact Hh.
            - intros b0 it0 H0. eapply NA8. right. exact H0. }
          cbv beta. intros ms' Q. unfold fh_post in Q |- *. destruct_exs Q. destruct Q as (-> & MU2 & WM2 & MI2 & ST2 & RES).
          apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
          split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2| exact RES].
        +
          zstep. apply evt_done. unfold fh_post. exists 0. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1'|]. left. reflexivity.
    Qed.
  End FH.
End W.
