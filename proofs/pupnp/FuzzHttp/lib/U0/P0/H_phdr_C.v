(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_prep H_httpmsg_compare H_httpheader_free H_scanner_get_token H_ListFind H_list_access H_ListAddTail H_freelist H_obj
     H_membuffer_init H_membuffer_destroy H_membuffer_assign H_membuffer_append H_membuffer_append_str H_memptr_cmp H_map_str_to_int
     H_vfmatch_A H_vfmatch_F H_vfmatch_G1 H_match H_phdr_A H_phdr_B.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma table_strings_mono : forall ws ne B B', table_strings ws ne B -> (B <= B')%Z -> table_strings ws ne B'.
Proof.
  intros ws ne B B' TS HB i Hi. destruct (TS i Hi) as (S & str & slack & H1 & H2 & H3 & H4 & H5).
  exists S, str, slack. repeat (split; [assumption|]). lia.
Qed.

Lemma bytes_sub : forall m a bs off k,
  bytes_at rsegs m a bs -> (off + k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m a bs off k H Hk.
  rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma cell8_agree : forall m A cs1 cs2 k (x y : Z),
  rw_cells rsegs m A cs1 -> rw_cells rsegs m A cs2 -> cell_at cs1 k = Some (C8 (wz x)) -> cell_at cs2 k = Some (C8 (wz y)) ->
  (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x = y.
Proof.
  intros m A cs1 cs2 k x y R1 R2 C1 C2 HX HY.
  pose proof (rw_cells_readn rsegs m A cs1 k _ 8 R1 C1 eq_refl) as E1. pose proof (rw_cells_readn rsegs m A cs2 k _ 8 R2 C2 eq_refl) as E2.
  cbn [cbytes] in E1, E2. rewrite E1 in E2.
  apply (f_equal (fun o : option (list byte) => match o with Some l => le_bytes_to_word l | None => Z_to_bv 64 0 end)) in E2.
  cbv beta iota in E2. rewrite !le_bytes_to_word_le8 in E2.
  apply (f_equal bv_unsigned) in E2. rewrite !unsigned_lit in E2 by lia. exact E2.
Qed.

Lemma upd_nth_same : forall (bs : list byte) i b, nth_error bs i = Some b -> upd bs i b = bs.
Proof.
  induction bs as [|x bs IH]; intros [|i] b H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.

Lemma upd_upd : forall {X} (l : list X) i (x y : X), upd (upd l i x) i y = upd l i y.
Proof. induction l as [|a l IH]; intros [|i] x y; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma nth_error_upd_hit : forall {X} (l : list X) i (x : X), (i < length l)%nat -> nth_error (upd l i x) i = Some x.
Proof. induction l as [|a l IH]; intros [|i] x H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma skipn_upd : forall {X} (l : list X) k i (x : X), (k <= i)%nat -> skipn k (upd l i x) = upd (skipn k l) (i - k) x.
Proof.
  induction l as [|a l IH]; intros [|k] [|i] x H; cbn; try reflexivity; try lia.
  rewrite IH by lia. f_equal.
Qed.

Lemma In_upd_hit : forall {X} (l : list X) i (x : X), (i < length l)%nat -> In x (upd l i x).
Proof. induction l as [|a l IH]; intros [|i] x H; cbn in *; try lia; [left; reflexivity|]. right. apply IH. lia. Qed.

Lemma round_up8_mono : forall x y, (x <= y)%Z -> (round_up8 x <= round_up8 y)%Z.
Proof. intros x y H. unfold round_up8. Z.div_mod_to_equations. lia. Qed.
Lemma round_up8_ge : forall x, (x + (- x) mod 8 = round_up8 x)%Z.
Proof. intros x. unfold round_up8. Z.div_mod_to_equations. lia. Qed.

Definition qmod8 (x : Z) : Prop := (x mod 8 = 0)%Z.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis strncasecmp_spec : strncasecmp_stmt.

  Hypothesis IMGW1 : In (0x10000, 0x2a000)%Z (al_img L_).
  Hypothesis IMGW2 : In (0x2a000, 0x5d000)%Z (al_img L_).

  Variables (P q lo B : Z) (ws : list word).
  Variables (isreq maj min : Z) (cur0 X0 len : Z).
  Notation S := (P + 480)%Z.
  Notation L := (P + 288)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 368 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis QP : (q + 240 <= P)%Z.
  Hypothesis PB : (P + 504 <= B)%Z.
  Hypothesis BHI : (B < 2^63)%Z.
  Hypothesis P8 : (P mod 8 = 0)%Z.
  Hypothesis Q8 : qmod8 q.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, (0 <= i < 33)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
  Hypothesis TS : table_strings ws 33 lo.
  Hypothesis CUR0 : (0 <= cur0 <= len)%Z.
  Hypothesis X00 : (0 <= X0)%Z.

  Definition mwin (okm : option K) (A cap : Z) : list ivl := match okm with Some _ => [(A, A + (cap + 1))%Z] | None => [] end.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5 s6 s7 (wz 4) s9 (wz (-1)) (wz (-104)) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  Definition phFY (m : mem) : Prop :=
    (exists j0, rw_cells rsegs m q [CB 12 j0]) /\ (exists ty, rw_cells rsegs m (q + 12) [C4 ty])
    /\ (exists a b, rw_cells rsegs m (q + 32) [C8 a; C8 b])
    /\ (exists ja id, rw_cells rsegs m (q + 48) [CB 16 ja; C4 id]) /\ (exists j68, rw_cells rsegs m (q + 68) [CB 68 j68]).

  #[using="cur0 len CUR0"] Lemma phFX_Y : forall m, phFX q m <-> (phFY m /\ exists a b, rw_cells rsegs m (q + 16) [C8 a; C8 b]).
  Proof. intros m. unfold phFX, phFY. LiaTuning.ctauto. Qed.

  #[using="LOK P q lo ws QLO CEIL QP PB WSL"] Lemma seg_hp : forall s LB LBh m0 m m' W,
    RHEAP rsegs AI s LB m0 -> bsub AI LBh LB -> munch W m m' -> wmono rsegs m m' ->
    Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= B)
                      \/ (exists b, In b LB /\ (forall b', In b' LBh -> b' <> b) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))%Z W ->
    heap_pres AI LBh B m m'.
  Proof.
    intros s LB LBh m0 m m' W HR SUB MU WM FA. pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU| exact WM|].
    unfold seg_ok. eapply Forall_impl; [| exact FA]. cbn. intros [lo' hi'] [H|(b & Hb & Hne & H1 & H2)]; [left; exact H| right]. cbn in *.
    intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact Hb| | lia| lia].
    intros b0 Hb0. split; [apply SUB; exact Hb0| apply Hne; exact Hb0].
  Qed.

  #[using="ws WSL"] Lemma p_hlist_pres : forall m m' W (LBh : list BLK) SPx ns hs X,
    p_hlist AI m P ns hs X -> munch W m m' -> wmono rsegs m m' -> disjoint_from W (P + 288) 96 ->
    heap_pres AI LBh SPx m m' -> bsub AI (hl_blocks AI ns hs) LBh -> p_hlist AI m' P ns hs X.
  Proof.
    intros m m' W LBh SPx ns hs X (LC & FLC & FF & DL & HS & IT & HB & NB & X0') MU WM DJ HP SUB.
    unfold hl_blocks in SUB. apply (bsub_app AI) in SUB. destruct SUB as [S1 S2].
    split. { eapply rw_cells_transport; [exact LC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FLC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FF| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply (dlseg_heap_pres AI); [exact DL| exact HP|]. intros b it H. apply S1. exact (in_map fst _ _ H). }
    split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HP| exact S2]. }
    auto.
  Qed.

  #[using="q lo ws QLO LO0 QP WSL"] Lemma p_msg_pres : forall m m' W (LBh LB LB' : list BLK) SPx A cap okm bs,
    p_msg AI m LB P A len cap okm bs -> munch W m m' -> wmono rsegs m m' -> disjoint_from W (P + 400) 32 ->
    heap_pres AI LBh SPx m m' -> bsub AI (okb AI okm A cap) LBh -> (forall b, In b (okb AI okm A cap) -> In b LB') ->
    p_msg AI m' LB' P A len cap okm bs.
  Proof.
    intros m m' W LBh LB LB' SPx A cap okm bs (MBC & OWN & HL & HC & NUL) MU WM DJ HP SUB SUB'.
    split. { eapply rw_cells_transport; [exact MBC| exact MU| exact WM|]. exact DJ. }
    split.
    { destruct okm as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [apply SUB'; left; reflexivity|].
      pose proof BLK as BLK'. destruct BLK' as [[W0 _] _].
      eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact BLK|]. eapply client_range_block; [apply SUB; left; reflexivity| cbn; lia|].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. cbn in W0. lia. }
    auto.
  Qed.

  Ltac fa_stack := repeat (apply Forall_cons; [left; cbn; lia|]); apply Forall_nil.
  Ltac by_FY := unfold phFY; split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [do 2 eexists; eassumption|];
                split; [do 2 eexists; eassumption| eexists; eassumption].
  Ltac by_FX := apply phFX_Y; split; [by_FY| do 2 eexists; eassumption].
  Ltac winc := unfold sub_fp; intros xo OX; cbn [outside app] in OX |- *; intuition lia.

  Ltac acc MU WM MUc WMc :=
    lazymatch type of MUc with munch _ _ ?m2 =>
    lazymatch type of MU with munch ?WF ?m0 _ =>
      let MU' := fresh "MU" in let WM' := fresh "WM" in
      assert (MU' : munch WF m0 m2) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUc]; winc]);
      assert (WM' : wmono rsegs m0 m2) by (eapply wmono_trans; [exact WM| exact WMc]);
      clear MU WM; rename MU' into MU; rename WM' into WM
    end end.

  #[using="Type"] Lemma dlseg_node : forall ns m pv TAIL b it,
    dlseg AI m ns pv TAIL -> In (b, it) ns -> exists pv' nx, rw_cells rsegs m (blk_addr b) (node_cells pv' nx it).
  Proof.
    induction ns as [|[b0 it0] ns IH]; intros m pv TAIL b it DL H; [destruct H|]. cbn [dlseg] in DL.
    destruct DL as (SZ & NZ & NT & ITR & NC & DL'). destruct H as [E|H].
    - injection E as -> ->. exists pv, (hd_addr AI ns TAIL). exact NC.
    - eapply IH; [exact DL'| exact H].
  Qed.

  #[using="Type"] Lemma in_items : forall (ns : list (BLK * Z)) (hs : list hdr) (b : BLK) (it : Z), map snd ns = map (hA AI) hs -> In (b, it) ns -> exists h, In h hs /\ it = hA AI h.
  Proof.
    induction ns as [|[b0 it0] ns IH]; intros [|h hs] b it IT H; cbn in IT; try discriminate; [destruct H|].
    injection IT as E IT'. destruct H as [E2|H].
    - injection E2 as -> ->. exists h. split; [left; reflexivity| exact E].
    - destruct (IH hs b it IT' H) as (h' & H1 & H2). exists h'. split; [right; exact H1| exact H2].
  Qed.

  #[using="q lo ws QLO LO0 QP P8 WSL"] Lemma hl_facts : forall s LB m ns hs X LBK,
    RHEAP rsegs AI s LB m -> p_hlist AI m P ns hs X -> bsub AI (hl_blocks AI ns hs ++ LBK) LB ->
    (forall b it, In (b, it) ns -> 16 <= blk_addr b /\ blk_addr b + 24 <= alloc_ceiling /\ blk_size b = 24 /\ it <> 0 /\ 0 <= it < 2^64)%Z
    /\ (forall h, In h hs -> 16 <= hA AI h /\ hA AI h + 88 <= alloc_ceiling /\ hA AI h mod 16 = 0
                          /\ 16 <= nA AI h /\ nA AI h + (ncap AI h + 1) <= alloc_ceiling /\ nA AI h mod 16 = 0
                          /\ 16 <= vA AI h /\ vA AI h + (vcap AI h + 1) <= alloc_ceiling /\ vA AI h mod 16 = 0
                          /\ hdro_pure AI h)%Z.
  Proof.
    intros s LB m ns hs X LBK HR (LC & FLC & FF & DL & HS & IT & HB & NB & X0') BSUB.
    assert (SUBn : forall b it, In (b, it) ns -> In b LB).
    { intros b it H. apply BSUB. apply in_or_app. left. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ H). }
    assert (SUBh : forall h b, In h hs -> In b (hblocks AI h) -> In b LB).
    { intros h b Hh Hb. apply BSUB. apply in_or_app. left. unfold hl_blocks. apply in_or_app. right. eapply (in_hdrs_blocks AI); eauto. }
    assert (HPU : forall h, In h hs -> hdro_pure AI h).
    { clear - HS. induction hs as [|h0 hs IH]; intros h Hh; [destruct Hh|]. cbn in HS. destruct HS as (_ & HP & HS').
      destruct Hh as [<-|Hh]; [exact HP| exact (IH HS' h Hh)]. }
    split.
    - intros b it H. destruct (dlseg_facts AI _ _ _ _ _ _ DL H) as (SZ & NZ & NT & ITR).
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBn b it H)) as (R1 & R2 & R3 & R4 & _). rewrite SZ in R4.
      destruct (in_items ns hs b it IT H) as (h & Hh & ->).
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBh h _ Hh (or_introl eq_refl))) as (S1 & S2 & _). cbn in S1, S2.
      split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact SZ|]. split; lia.
    - intros h Hh. pose proof (HPU h Hh) as HP. unfold hdro_pure in HP.
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBh h _ Hh (or_introl eq_refl))) as (R1 & R2 & R3 & R4 & _). cbn in R1, R2, R3, R4.
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBh h _ Hh (or_intror (or_introl eq_refl)))) as (V1 & V2 & V3 & V4 & _). cbn in V1, V2, V3, V4.
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBh h _ Hh (or_intror (or_intror (or_introl eq_refl))))) as (N1 & N2 & N3 & N4 & _). cbn in N1, N2, N3, N4.
      repeat split; first [lia | Z.div_mod_to_equations; lia].
  Qed.

  #[using="Type"] Lemma hl_node_align : forall s LB m ns hs X LBK,
    RHEAP rsegs AI s LB m -> p_hlist AI m P ns hs X -> bsub AI (hl_blocks AI ns hs ++ LBK) LB ->
    forall b it, In (b, it) ns -> (blk_addr b mod 8 = 0)%Z.
  Proof.
    intros s LB m ns hs X LBK HR HL BSUB b it H.
    assert (INB : In b LB).
    { apply BSUB. apply in_or_app. left. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ H). }
    destruct (ai_block_range rsegs AI _ _ _ _ HR INB) as (_ & R2 & _). clear - R2. Z.div_mod_to_equations. lia.
  Qed.

  #[using="ws QLO CEIL QP WSL"] Lemma hr_at : forall s LB (A cap : Z) (okm : option K) m mx,
    RHEAP rsegs AI s LB m -> (forall k, okm = Some k -> In (k, A, cap + 1) LB) ->
    munch ((lo, q + 240) :: (P + 4, P + 8) :: (P + 448, P + 452) :: (P + 488, P + 496) :: mwin okm A cap)%Z m mx -> wmono rsegs m mx ->
    RHEAP rsegs AI s LB mx.
  Proof.
    intros s LB A cap okm m mx HR HK MU WM. pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM|].
    repeat (apply Forall_cons; [left; cbn; lia|]). destruct okm as [k|]; cbn; [| apply Forall_nil].
    apply Forall_cons; [| apply Forall_nil]. right; right; right. exists (k, A, cap + 1). split; [apply HK; reflexivity|]. cbn. lia.
  Qed.

  #[using="strncasecmp_spec P QLO LO0 QP Q8 WSL TS"] Lemma msi_call : forall (T n : Z) (tok : list byte)
      ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    bytes_at rsegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n < 2^63)%Z ->
    u64arr rsegs m TAB_HDR ws -> stk rsegs m lo q -> (T + Z.of_nat (length tok) <= lo)%Z -> (q < 2^63)%Z -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (r : Z),
        ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(q - 144, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo q
        /\ (r = -1 \/ 0 <= r < 33)%Z)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz T) (wz n) (wz TAB_HDR) (wz 33) (wz 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz map_str_to_int_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros TOK TL N1 TABm ST TLO QHI MI.
    pose proof Q8 as Q8'. unfold qmod8 in Q8'.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    pose proof (u64arr_bound rsegs _ _ _ TABm) as TB.
    destruct (stk_split rsegs _ _ (q - 144)%Z _ ST ltac:(lia)) as [STlo SThi].
    eapply evt_mono.
    { eapply (map_str_to_int_spec strncasecmp_spec T n TAB_HDR 33 0 tok ws _ (Z_to_bv 64 q)); rewrite ?E; try eassumption; try reflexivity; try lia.
      all: try (rewrite WSL; reflexivity). all: try (eapply table_strings_mono; [exact TS| lia]).
      all: match goal with |- ?g => idtac "MSI" g end. }
    intros ms' Q. unfold map_str_to_int_post in Q. rewrite !E in Q. destruct_exs Q. destruct Q as (-> & MU & WM & MI' & ST' & RES).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split; [| exact RES]. eapply stk_merge; [| exact ST'| lia]. eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|]. cbn. lia.
  Qed.

  Definition front_post (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp : word) (F : bvmap 5 word) (fc : bv 32)
      (A cap : Z) (okm : option K) (bs : list byte)
      (cur meth err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X : Z) (LB : list BLK) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      munch ((lo, q + 240) :: (P + 4, P + 8) :: (P + 448, P + 452) :: (P + 488, P + 496) :: mwin okm A cap)%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ u64arr rsegs m' TAB_HDR ws /\ p_msg AI m' LB P A len cap okm bs /\ p_ver m' P isreq maj min
      /\ p_hlist AI m' P ns hs X
      /\ (
           (exists (r cur' meth' pos' : Z),
              ms' = MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0w s1w (wz r) a1 a2 a3 a4 a5 a6 a7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
                       F (ret_pc ra) fc None m' (seg_rom rsegs)
              /\ stk rsegs m' lo (q + 240) /\ p_scan m' P cur' /\ p_meth m' P meth' /\ p_ctl m' P err hack pos' entp clen csz esp
              /\ cur <= cur' <= len /\ (meth' = meth \/ meth' = 11) /\ 0 <= r <= 5 /\ 0 <= pos' <= 4
              /\ (r = 4 -> pos' = POS_ENTITY) /\ (r = 4 -> okm <> None))
        \/
           (exists (h : hdr) (o l cur2 meth' : Z) x1 a0 s6 s7 s9,
              ms' = PRS 0x14e30 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (hA AI h)) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m'
              /\ In h hs /\ stk rsegs m' lo q /\ rw_cells rsegs m' (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) /\ phFY m' /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)]
              /\ p_scan m' P cur2 /\ p_meth m' P meth' /\ p_ctl m' P err hack pos entp clen csz esp
              /\ (meth' = meth \/ meth' = 11) /\ cur + 2 <= cur2 <= len /\ 0 <= l <= cur2 - cur /\ cur <= o /\ o + l <= len /\ okm <> None)
        \/
           (exists (id o l cur2 meth' tl : Z) x1 a0 s6 s7,
              ms' = PRS 0x14e7c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz 0) s6 s7 (wz id) t3 t4 t5 t6 gp tp F fc m'
              /\ stk rsegs m' lo q /\ rw_cells rsegs m' (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) /\ phFY m' /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)]
              /\ rw_cells rsegs m' (q + 32) [C8 (wz (A + cur)); C8 (wz tl)]
              /\ p_scan m' P cur2 /\ p_meth m' P meth' /\ p_ctl m' P err hack pos entp clen csz esp
              /\ (meth' = meth \/ meth' = 11) /\ cur + 2 <= cur2 <= len /\ 0 <= l <= cur2 - cur /\ cur <= o /\ o + l <= len /\ okm <> None
              /\ 1 <= tl /\ cur + tl < len /\ -1 <= id < 64) )%Z.

  Ltac seg_std LBh HR HLSUB SUBh1 SUBh2 HL MSG MUc WMc :=
    let HP := fresh "HP" in
    lazymatch type of MUc with munch _ ?ma ?mb =>
      assert (HP : heap_pres AI LBh B ma mb) by (eapply (seg_hp _ _ LBh); [exact HR| exact HLSUB| exact MUc| exact WMc| fa_stack]);
      let HL' := fresh "HL" in let MSG' := fresh "MSG" in
      pose proof (p_hlist_pres ma mb _ _ B _ _ _ HL MUc WMc ltac:(cbn; lia) HP SUBh1) as HL';
      pose proof (p_msg_pres ma mb _ _ _ _ B _ _ _ _ MSG MUc WMc ltac:(cbn; lia) HP SUBh2 ltac:(intros b Hb; exact (HLSUB b (SUBh2 b Hb)))) as MSG';
      clear HP HL MSG; rename HL' into HL; rename MSG' into MSG;
      transport_after_call rsegs ma mb MUc WMc; try clear MUc WMc
    end.

  Notation WF okm A cap := ((lo, q + 240) :: (P + 4, P + 8) :: (P + 448, P + 452) :: (P + 488, P + 496) :: mwin okm A cap)%Z.

  #[using="LOK B QLO LO0 CEIL QP PB BHI P8 WSL CUR0"] Lemma ph_rexit : forall (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK)
      (cur meth err hack pos entp clen csz esp X : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
      (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp : word) (F : bvmap 5 word) fc
      (r curx : Z) m mx x1' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' x18 x19 x20 s6' s7' s8' s9' s10' s11' (tw1 tw2 tyx idw padw : word) (j0 ja j68 : list byte),
    RHEAP rsegs AI s LB m -> bsub AI (hl_blocks AI ns hs ++ okb AI okm A cap) LB ->
    (0 <= meth <= 11)%Z -> (0 <= isreq <= 1 /\ - 2^31 <= maj < 2^31 /\ - 2^31 <= min < 2^31)%Z ->
    (0 <= err < 2^31 /\ 0 <= hack <= 1 /\ 0 <= pos <= 4 /\ 0 <= entp <= 6 /\ 0 <= clen < 2^32 /\ 0 <= csz < 2^64 /\ 0 <= esp < 2^64)%Z ->
    (cur0 <= cur <= len)%Z -> (cur < 2^64)%Z ->
    (0 <= r <= 5)%Z -> r <> 4 -> (0 <= curx < 2^64)%Z ->
    munch (WF okm A cap) m mx -> wmono rsegs m mx -> mem_inv rsegs mx ->
    stk rsegs mx lo q -> rw_cells rsegs mx (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) ->
    rw_cells rsegs mx q [CB 12 j0] -> rw_cells rsegs mx (q + 12) [C4 tyx] -> (exists a16' b16', rw_cells rsegs mx (q + 16) [C8 a16'; C8 b16']) ->
    rw_cells rsegs mx (q + 32) [C8 tw1; C8 tw2] -> rw_cells rsegs mx (q + 48) [CB 16 ja; C4 idw] -> rw_cells rsegs mx (q + 68) [CB 68 j68] ->
    rw_cells rsegs mx S (SCc S MB curx) -> u64arr rsegs mx TAB_HDR ws -> p_msg AI mx LB P A len cap okm bs ->
    rw_cells rsegs mx P [C4 (wz 1); C4 (wz meth)] -> rw_cells rsegs mx (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 padw] ->
    rw_cells rsegs mx (P + 440) (p_ctl_cells err hack pos entp clen csz esp) -> p_hlist AI mx P ns hs X ->
    evt rsegs (front_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp F fc A cap okm bs cur meth err hack pos entp clen csz esp ns hs X LB m)
      (MS (mkR x1' (wz q) gp tp t0' t1' t2' (wz P) (wz S) (wz r) a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 (wz cur) s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
          F (wz 0x14f38) fc None mx (seg_rom rsegs)).
  Proof.
    intros until j68. intros HR HLSUB METHR VR CR CUR CUR64 R5 R4 CX MUx WMx MIx STx FSx Q0x Q12x (a16' & b16' & Q16x) Q32x Q48x Q68x SCx TABx MSGx MCx VCx CCx HLx.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    unfold phFS in FSx. unfold p_ctl_cells in CCx.
    set (LBh := hl_blocks AI ns hs ++ okb AI okm A cap) in HLSUB.
    assert (SUBh1 : bsub AI (hl_blocks AI ns hs) LBh) by (intros b Hb; apply in_or_app; left; exact Hb).
    assert (SUBh2 : bsub AI (okb AI okm A cap) LBh) by (intros b Hb; apply in_or_app; right; exact Hb).
    eapply evt_cut. { eapply (ph_restore_exit P q lo); try eassumption; try LiaTuning.alia. by_FX. }
    cbv beta. intros ms' (m2 & -> & MU2 & WM2 & MI2 & ST2 & SC2).
    seg_std LBh HR HLSUB SUBh1 SUBh2 HLx MSGx MU2 WM2.
    apply evt_done. unfold front_post. exists m2. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact MUx|]. split; [exact WMx|]. split; [exact MI2|]. split; [exact TABx|]. split; [exact MSGx|].
    split. { split; [eexists; exact VCx| exact VR]. }
    split; [exact HLx|].
    left. exists r, cur, meth, pos. split; [reflexivity|]. split; [exact ST2|]. split; [exact SC2|]. split; [split; [exact MCx| exact METHR]|].
    split; [split; [exact CCx| exact CR]|]. split; [lia|]. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; intros; exfalso; lia.
  Qed.

  #[using="LOK strncasecmp_spec IMGW1 IMGW2 B QLO LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0"] Lemma ph_frontB : forall (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK)
      (cur meth err hack pos entp clen csz esp X : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
      (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp : word) (F : bvmap 5 word) fc
      (tlz ty : Z) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 (idw a16 b16 padw : word) (j0 ja j68 : list byte) m m1,
    (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
    RHEAP rsegs AI s LB m -> munch (WF okm A cap) m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo q ->
    rw_cells rsegs m1 (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) ->
    rw_cells rsegs m1 q [CB 12 j0] -> rw_cells rsegs m1 (q + 12) [C4 (wz ty)] -> rw_cells rsegs m1 (q + 16) [C8 a16; C8 b16] ->
    rw_cells rsegs m1 (q + 32) [C8 (wz (A + cur)); C8 (wz tlz)] -> rw_cells rsegs m1 (q + 48) [CB 16 ja; C4 idw] -> rw_cells rsegs m1 (q + 68) [CB 68 j68] ->
    rw_cells rsegs m1 S (SCc S MB (cur + tlz)) -> (cur0 <= cur)%Z -> (1 <= tlz)%Z -> (cur + tlz <= len)%Z -> (0 <= ty <= 5)%Z ->
    ((ty = TT_IDENTIFIER \/ ty = TT_WHITESPACE) -> cur + tlz < len)%Z ->
    p_msg AI m1 LB P A len cap okm bs -> rw_cells rsegs m1 P [C4 (wz 1); C4 (wz meth)] -> (0 <= meth <= 11)%Z ->
    rw_cells rsegs m1 (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 padw] ->
    (0 <= isreq <= 1 /\ - 2^31 <= maj < 2^31 /\ - 2^31 <= min < 2^31)%Z ->
    rw_cells rsegs m1 (P + 440) (p_ctl_cells err hack pos entp clen csz esp) ->
    (0 <= err < 2^31 /\ 0 <= hack <= 1 /\ 0 <= pos <= 4 /\ 0 <= entp <= 6 /\ 0 <= clen < 2^32 /\ 0 <= csz < 2^64 /\ 0 <= esp < 2^64)%Z ->
    p_hlist AI m1 P ns hs X -> (X <= VMAX)%Z -> bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
    u64arr rsegs m1 TAB_HDR ws ->
    evt rsegs (front_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp F fc A cap okm bs cur meth err hack pos entp clen csz esp ns hs X LB m)
      (PRS 0x14cec x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz cur) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m1).
  Proof.
    intros until m1. intros MSGK HR MU WM MI1 ST1 FSH Q0 TYC1 Q16 TC1 Q48 Q68 SC1 CURA TL1 CLE TY5 STRICT MSG0 MC METHR VC VR CC CR HL0 XV BSUB ND TAB.
    pose proof Q8 as Q8'. unfold qmod8 in Q8'.
    unfold phFS in FSH. unfold p_ctl_cells in CC.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    pose proof (hr_at s LB A cap okm m m1 HR ltac:(intros k Hk; apply BSUB; apply in_or_app; right; exact (MSGK k Hk)) MU WM) as HR1.
    destruct (p_msg_facts AI m1 LB P A len cap okm bs s HR1 MSG0) as (LENR & CAPR & LBS & NONEF & SOMEF).
    assert (AR : (Z.of_nat (length bs) >= len /\ 0 <= cur < 2^64 /\ A + cap + 1 < 2^63 /\ len + 1 <= LMAX /\ LMAX = 2^26 + 16 /\ A + Z.of_nat (length bs) <= lo)%Z).
    { unfold LMAX in *. destruct okm as [k|].
      - destruct (SOMEF ltac:(discriminate)) as (A16 & AHI & _). lia.
      - destruct (NONEF eq_refl) as (-> & -> & ->). cbn in LBS |- *. lia. }
    destruct AR as (LBS2 & CURR & AHI & LENX & LMAXE & BLO).
    set (LBh := hl_blocks AI ns hs ++ okb AI okm A cap).
    assert (HLSUB : bsub AI LBh LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]. { apply BSUB. apply in_or_app. left. exact Hb. }
      pose proof MSG0 as MSGc. destruct MSGc as (_ & OWN & _). destruct okm as [k|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in OWN. exact (proj1 OWN). }
    assert (SUBh1 : bsub AI (hl_blocks AI ns hs) LBh) by (intros b Hb; apply in_or_app; left; exact Hb).
    assert (SUBh2 : bsub AI (okb AI okm A cap) LBh) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (ITEMS : map snd ns = map (hA AI) hs) by (destruct HL0 as (_ & _ & _ & _ & _ & IT & _); exact IT).
    unfold TT_IDENTIFIER, TT_WHITESPACE in STRICT.
    eapply evt_cut. { eapply (ph_core1 P q ws WSL ty); try eassumption; lia. }
    cbv beta. intros ms' [[-> ->]|[TYNZ ->]].
    2:{
      eapply evt_cut. { eapply (ph_notid P q lo) with (ty := ty) (isreq := isreq) (meth := meth) (err := err) (hack := hack) (pos := pos) (entp := entp) (clen := clen) (csz := csz) (esp := esp); try eassumption; try LiaTuning.alia. by_FX. }
      cbv beta. intros ms' (a1' & m2 & -> & MU2 & WM2 & MI2 & ST2 & CC2).
      seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU2 WM2.
      apply evt_done. unfold front_post. exists m2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact TAB|]. split; [exact MSG0|].
      split. { split; [eexists; exact VC| exact VR]. }
      split; [exact HL0|].
      left. exists (notid_r ty isreq meth), (cur + tlz)%Z, meth, (notid_pos ty isreq meth pos). split; [reflexivity|]. split; [exact ST2|]. split; [exact SC1|].
      split; [split; [exact MC| exact METHR]|].
      split. { split; [exact CC2|]. unfold notid_pos. destruct CR as (CR1 & CR2 & CR3). destruct (ty =? 2); [destruct (negb (isreq =? 0) && (meth =? 4))%bool|]; cbn; lia. }
      split; [lia|]. split; [left; reflexivity|].
      unfold notid_r, notid_pos, POS_ENTITY.
      assert (OKNN : okm <> None) by (intros E; destruct (NONEF E); lia).
      destruct (Z.eqb_spec ty 2) as [E2|NE2]; [destruct (negb (isreq =? 0) && (meth =? 4))%bool|]; cbn; (split; [lia|]); (split; [lia|]); (split; [intros; lia|]); intros _; exact OKNN. }

    destruct okm as [km|]; [| exfalso; destruct (NONEF eq_refl); lia].
    assert (MSGB : In (km, A, cap + 1) LB) by (apply BSUB; apply in_or_app; right; apply MSGK; reflexivity).
    assert (MSGB' : forall k, Some km = Some k -> In (k, A, cap + 1) LB) by (intros k E; injection E as <-; exact MSGB).
    destruct (hl_facts s LB m1 ns hs X LBK (hr_at s LB A cap (Some km) m m1 HR MSGB' MU WM) HL0 BSUB) as [NF HF].
    pose proof (hl_node_align s LB m1 ns hs X LBK (hr_at s LB A cap (Some km) m m1 HR MSGB' MU WM) HL0 BSUB) as NA.
    unfold mwin in MU. cbn in LBS.
    destruct (SOMEF ltac:(discriminate)) as (A16 & ACE & AAL). clear NONEF SOMEF.
    assert (MSGWIN : ((A + (cap + 1) <= 0x10000 \/ 0x2a000 <= A) /\ (A + (cap + 1) <= 0x2a000 \/ 0x5d000 <= A))%Z).
    { destruct (ai_block_range rsegs AI _ _ _ _ HR MSGB) as (_ & _ & _ & _ & FA). rewrite Forall_forall in FA.
      pose proof (FA _ IMGW1) as W1. pose proof (FA _ IMGW2) as W2. cbn in W1, W2. lia. }

    pose proof MSG0 as MSGc. destruct MSGc as (MBC1 & OWN1 & _ & _ & _). destruct (p_msg_bytes AI m1 LB P A len cap km bs MSG0) as [BUF1 _].
    assert (MOK : vf_ok (q + -64) lo S MB A len cap (cur + tlz) bs) by (unfold vf_ok; lia).
    eapply evt_cut.
    { eapply (match_hdr q lo S MB A len cap (cur + tlz) bs MOK (q + 16)); try eassumption; unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc; try eassumption; lia. }
    cbv beta. intros ms' Q. unfold mpost in Q. destruct Q as (r2 & cur2 & Q). destruct_exs Q.
    destruct Q as (-> & MU2 & WM2 & MI2 & ST2 & SC2 & MBC2 & BUF2 & R2 & CUR2 & ADV & NADV & XH).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 0x14d04)) with (Z_to_bv 64 0x14d04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold H_vfmatch_A.SCc in SC2. unfold H_vfmatch_A.MBc in MBC2. unfold H_vfmatch_A.BUFc in BUF2. clear MBC1 OWN1 BUF1.
    unfold X_hdr in XH. destruct XH as (pa & pb & Q16b & XOK).
    seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU2 WM2. clear MI1.
    eapply evt_cut. { eapply (ph_m2 P q ws WSL r2 (A + cur) tlz); try eassumption; lia. }
    cbv beta. intros ms' [[-> ->]|[R2NE ->]].
    2:{   rewrite (NADV R2NE) in SC2. eapply (ph_rexit A cap (Some km) bs LBK) with (r := r2) (curx := (cur + tlz)%Z); try eassumption; try LiaTuning.alia. do 2 eexists; eassumption. }
    destruct (XOK eq_refl) as (o & l & -> & -> & O1 & L0 & OL & C21 & OLC). specialize (ADV eq_refl). clear NADV XOK.
    unfold PARSE_OK in *.

    assert (TOKB : bytes_at rsegs m2 (A + cur) (firstn (Z.to_nat tlz) (skipn (Z.to_nat cur) bs))).
    { replace (A + cur)%Z with (A + Z.of_nat (Z.to_nat cur))%Z by lia. apply bytes_sub; [exact BUF2| lia]. }
    eapply evt_cut.
    { eapply (msi_call (A + cur) tlz); try eassumption; try LiaTuning.alia; rewrite length_firstn, length_skipn; lia. }
    cbv beta. intros ms' Q. destruct_exs Q. destruct Q as (-> & MU3 & WM3 & MI3 & ST3 & IDX).
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end. name_r. rename rr into idx.
    replace (ret_pc (Z_to_bv 64 0x14d20)) with (Z_to_bv 64 0x14d20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU3 WM3. clear MI2.

    eapply evt_cut. { eapply (ph_idx P q lo) with (meth := meth); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms' (m4 & [(-> & -> & ->)|(id & meth' & IR & HN & IDR & EM & -> & MU4 & WM4 & MI4 & MC4 & Q48b & TAB4)]).
    -
      idtac.
      pose proof MSG0 as MSGc. destruct MSGc as (MBC3 & [HIN3 BLK3] & _ & _ & NUL3).
      pose proof (u8arr_of_rw_cells rsegs _ _ _ _ BLK3) as ARR3.
      assert (LBS3 : length bs = Z.to_nat (cap + 1)) by (destruct BLK3 as [[W0 _] _]; cbn in W0; lia).
      destruct (nth_error bs (Z.to_nat (cur + tlz))) as [bq|] eqn:HBQ.
      2:{ exfalso. apply nth_error_None in HBQ. lia. }
      eapply evt_cut.
      { eapply (ph_unk1 P q lo) with (A := A) (T := (A + cur)%Z) (tl := tlz) (bs := bs) (b := bq); try eassumption.
        all: try (replace (A + cur + tlz - A)%Z with (cur + tlz)%Z by lia; exact HBQ).
        all: rewrite ?LBS3; lia. }
      cbv beta. intros ms' (m6 & -> & MU6 & WM6 & MI6 & ARR6).
      replace (A + cur + tlz - A)%Z with (cur + tlz)%Z in ARR6 by lia.

      assert (NEQM : forall b', In b' (hl_blocks AI ns hs) -> b' <> (km, A, cap + 1)).
      { intros b' Hb'. eapply (nodup_in_neq AI); [exact ND| exact Hb'| apply MSGK; reflexivity]. }
      assert (HP6 : heap_pres AI (hl_blocks AI ns hs) B m3 m6).
      { eapply (seg_hp s LB); [exact HR| exact (fun b Hb => HLSUB b (SUBh1 b Hb))| exact MU6| exact WM6|].
        apply Forall_cons; [| apply Forall_nil]. right. exists (km, A, cap + 1). split; [exact MSGB|]. split; [exact NEQM|]. cbn. lia. }
      pose proof (p_hlist_pres m3 m6 _ _ B ns hs X HL0 MU6 WM6 ltac:(cbn; lia) HP6 ltac:(intros b Hb; exact Hb)) as HL6.
      clear HP6 HL0 MSG0 BLK3 ARR3. transport_after_call rsegs m3 m6 MU6 WM6. clear MU6 WM6 MI3.

      pose proof HL6 as HLc. destruct HLc as (LC & FLC & FF & DL & HS & _ & _ & NB6 & _).
      pose proof (proj2 (llist_split m6 L (hd_addr AI ns (L + 24)) (last_addr AI ns L) (zlength ns) 0 0 H_httpheader_free.httpheader_free_entry H_httpmsg_compare.httpmsg_compare_entry)) as LLC.
      replace (L + 24)%Z with (P + 312)%Z in LLC by lia. replace (L + 56)%Z with (P + 344)%Z in LLC by lia. replace (L + 80)%Z with (P + 368)%Z in LLC by lia.
      specialize (LLC (conj LC (conj FLC FF))).
      assert (FIRSTR : (0 <= hd_addr AI ns (P + 312) < 2^64)%Z /\ (ns <> [] -> hd_addr AI ns (P + 312) <> 0)).
      { destruct ns as [|[b0 it0] ns']; cbn; [split; [lia| intros X1; exfalso; apply X1; reflexivity]|].
        destruct (NF b0 it0 (or_introl eq_refl)) as (? & ? & _). split; [lia| intros _; lia]. }
      destruct FIRSTR as [FIRSTR FIRSTNZ].
      eapply evt_cut. { eapply (ListHead_spec L); try eassumption; try reflexivity; unfold zlength, VMAX in *; lia. }
      cbv beta. intros ms' Q. unfold ListHead_post in Q. destruct_exs Q. destruct Q as (-> & _ & _ & _).
      replace (ret_pc (Z_to_bv 64 0x14db8)) with (Z_to_bv 64 0x14db8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear LLC LC FLC FF.
      set (hd := if (zlength ns =? 0)%Z then 0%Z else hd_addr AI ns (P + 312)).
      assert (HDR6 : (0 <= hd < 2^64)%Z) by (subst hd; destruct (zlength ns =? 0); lia).
      eapply evt_cut. { eapply (ph_unk2 P q ws WSL hd); lia. }

      pose proof (proj1 ARR6) as STR6.
      destruct (block_slack_bytes AI s LB m6 (km, A, cap + 1) (upd bs (Z.to_nat (cur + tlz)) (Z_to_bv 8 0))
                  (hr_at s LB A cap (Some km) m m6 HR MSGB' MU WM) MSGB STR6 ltac:(cbn; rewrite upd_length, LBS3; lia)) as (sl & STR6' & SLL).
      cbn [blk_addr blk_size fst snd] in STR6', SLL.
      rewrite <- (firstn_skipn (Z.to_nat cur) (upd bs (Z.to_nat (cur + tlz)) (Z_to_bv 8 0))) in STR6'. rewrite <- app_assoc in STR6'.
      apply bytes_at_app in STR6'. destruct STR6' as [_ STR6']. rewrite firstn_length, upd_length in STR6'.
      replace (A + Z.of_nat (Nat.min (Z.to_nat cur) (length bs)))%Z with (A + cur)%Z in STR6' by lia.
      rewrite (skipn_upd bs (Z.to_nat cur) (Z.to_nat (cur + tlz))) in STR6' by lia.
      set (full := upd (skipn (Z.to_nat cur) bs) (Z.to_nat (cur + tlz) - Z.to_nat cur) (Z_to_bv 8 0) ++ sl) in STR6'.
      assert (INZ : In (Z_to_bv 8 0) full).
      { subst full. apply in_or_app. left. apply In_upd_hit. rewrite length_skipn. lia. }
      destruct (first_nul full (Z_to_bv 8 0) INZ) as (str & rest & EF & NONUL).
      assert (SLEN : (Z.of_nat (length str) <= tlz)%Z).
      { destruct (Nat.le_gt_cases (length str) (Z.to_nat tlz)) as [|G]; [lia| exfalso]. apply NONUL.
        assert (EN : nth_error full (Z.to_nat (cur + tlz) - Z.to_nat cur) = Some (Z_to_bv 8 0)).
        { subst full. rewrite nth_error_app1 by (rewrite upd_length, length_skipn; lia). apply nth_error_upd_hit. rewrite length_skipn. lia. }
        rewrite EF in EN. rewrite nth_error_app1 in EN by lia. eapply nth_error_In. exact EN. }
      assert (FL : (Z.of_nat (length full) = cap + 1 - cur + Z.of_nat (length sl))%Z) by (subst full; rewrite app_length, upd_length, length_skipn; lia).
      rewrite EF in STR6'. pose proof (f_equal (@length byte) EF) as EL. rewrite app_length in EL. cbn [length] in EL.

      assert (TAIL3 : forall (hv : Z) mx x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' t3' t4' t5' t6',
        (hv = 0 \/ exists h, In h hs /\ hv = hA AI h)%Z -> (0 <= hv < 2^64)%Z ->
        munch ((lo, q + 240) :: (P + 4, P + 8) :: (P + 448, P + 452) :: (P + 488, P + 496) :: [(A, A + (cap + 1))])%Z m mx -> wmono rsegs m mx -> mem_inv rsegs mx ->
        stk rsegs mx lo q -> rw_cells rsegs mx (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) ->
        rw_cells rsegs mx q [CB 12 j0] -> rw_cells rsegs mx (q + 12) [C4 (wz 0)] -> rw_cells rsegs mx (q + 16) [C8 (wz (A + o)); C8 (wz l)] ->
        rw_cells rsegs mx (q + 32) [C8 (wz (A + cur)); C8 (wz tlz)] -> rw_cells rsegs mx (q + 48) [CB 16 ja; C4 idw] -> rw_cells rsegs mx (q + 68) [CB 68 j68] ->
        rw_cells rsegs mx S (SCc S MB cur2) -> u64arr rsegs mx TAB_HDR ws -> rw_cells rsegs mx MB (mbuf_cells A len cap) ->
        u8arr rsegs mx A (upd bs (Z.to_nat (cur + tlz)) (Z_to_bv 8 0)) ->
        rw_cells rsegs mx P [C4 (wz 1); C4 (wz meth)] -> rw_cells rsegs mx (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 padw] ->
        rw_cells rsegs mx (P + 440) (p_ctl_cells err hack pos entp clen csz esp) -> p_hlist AI mx P ns hs X ->
        evt rsegs (front_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp F fc A cap (Some km) bs cur meth err hack pos entp clen csz esp ns hs X LB m)
          (PRS 0x14e00 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (wz hv) s6' s7' (wz (bv_unsigned bq)) t3' t4' t5' t6' gp tp F fc mx)).
      { intros until t6'. intros HV HVR MUx WMx MIx STx FSx Q0x Q12x Q16x Q32x Q48x Q68x SCx TABx MBCx ARRx MCx VCx CCx HLx.
        unfold phFS in FSx. unfold p_ctl_cells in CCx. unfold mbuf_cells in MBCx.
        eapply evt_cut.
        { eapply (ph_unk3 P q lo) with (A := A) (T := (A + cur)%Z) (tl := tlz) (h := hv) (b := bq); try eassumption; try LiaTuning.alia.
          all: rewrite upd_length, LBS3; lia. }
        cbv beta. intros ms' (m8 & -> & MU8 & WM8 & MI8 & ARR8).
        replace (Z.to_nat (A + cur + tlz - A)) with (Z.to_nat (cur + tlz)) in ARR8 by lia. rewrite upd_upd in ARR8.
        rewrite (upd_nth_same bs _ _ HBQ) in ARR8.
        assert (HP8 : heap_pres AI (hl_blocks AI ns hs) B mx m8).
        { eapply (seg_hp s LB); [exact HR| exact (fun b Hb => HLSUB b (SUBh1 b Hb))| exact MU8| exact WM8|].
          apply Forall_cons; [| apply Forall_nil]. right. exists (km, A, cap + 1). split; [exact MSGB|]. split; [exact NEQM|]. cbn. lia. }
        pose proof (p_hlist_pres mx m8 _ _ B ns hs X HLx MU8 WM8 ltac:(cbn; lia) HP8 ltac:(intros b Hb; exact Hb)) as HL8.
        clear HP8 HLx ARRx. transport_after_call rsegs mx m8 MU8 WM8. clear MU8 WM8 MIx.
        pose proof (rw_cells_of_u8arr rsegs _ _ _ ARR8) as BLK8. rewrite LBS3 in BLK8.
        assert (MSG8 : p_msg AI m8 LB P A len cap (Some km) bs).
        { split; [exact MBCx|]. split; [cbn; split; [exact MSGB| exact BLK8]|]. split; [lia|]. split; [lia|]. exact NUL3. }
        destruct HV as [->|(h & Hh & ->)].
        - cbn [Z.eqb]. apply evt_done. unfold front_post. exists m8. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [exact MUx|]. split; [exact WMx|]. split; [exact MI8|]. split; [exact TABx|]. split; [exact MSG8|].
          split. { split; [eexists; exact VCx| exact VR]. }
          split; [exact HL8|].
          right; right. exists (-1), o, l, cur2, meth, tlz. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [reflexivity|]. split; [exact STx|]. split; [exact FSx|]. split; [by_FY|]. split; [exact Q16x|]. split; [exact Q32x|]. split; [exact SCx|]. split; [split; [exact MCx| lia]|].
          split; [split; [exact CCx| exact CR]|]. repeat split; try lia. discriminate.
        - destruct (HF h Hh) as (H16 & _). replace (hA AI h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          apply evt_done. unfold front_post. exists m8. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [exact MUx|]. split; [exact WMx|]. split; [exact MI8|]. split; [exact TABx|]. split; [exact MSG8|].
          split. { split; [eexists; exact VCx| exact VR]. }
          split; [exact HL8|].
          right; left. exists h, o, l, cur2, meth. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [reflexivity|]. split; [exact Hh|]. split; [exact STx|]. split; [exact FSx|]. split; [by_FY|]. split; [exact Q16x|]. split; [exact SCx|]. split; [split; [exact MCx| lia]|].
          split; [split; [exact CCx| exact CR]|]. repeat split; try lia. discriminate. }
      cbv beta. intros ms' [[HD0 ->]|[HDNZ ->]].
      +
        rewrite HD0. eapply (TAIL3 0); try eassumption; try LiaTuning.alia; try (left; reflexivity).
      +
        assert (NSNE : ns <> []) by (intros ->; apply HDNZ; subst hd; cbn; reflexivity).
        assert (EHD : hd = hd_addr AI ns (L + 24)).
        { subst hd. replace (L + 24)%Z with (P + 312)%Z by lia. destruct ns as [|n0 ns']; [exfalso; apply NSNE; reflexivity|].
          unfold zlength. cbn [length]. destruct (Z.eqb_spec (Z.of_nat (Datatypes.S (length ns'))) 0); [lia| reflexivity]. }
        rewrite EHD.
        pose proof HL6 as HLc. destruct HLc as (_ & _ & _ & DL6 & HS6 & _).
        eapply evt_cut.
        { eapply (fh_loop AI q lo L (A + cur) str rest gp tp _ _ _ _ _ _ _ _ F fc) with (sfx := ns) (hsf := hs) (hs := hs) (pv := L); try eassumption; try LiaTuning.alia.
          all: try (intros h Hh; exact Hh).
          all: try (replace (L + 24)%Z with (P + 312)%Z by lia; exact DL6).
          all: try (intros h Hh; destruct (HF h Hh) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); lia).
          all: try (intros b it Hb; destruct (NF b it Hb) as (? & ? & _); lia).
          all: try (intros h Hh; destruct (HF h Hh) as (? & ? & ? & _); Z.div_mod_to_equations; lia).
          all: try (intros b it Hb; exact (NA b it Hb)).
          all: pose proof (round_up8_ge (A + cur + Z.of_nat (length str) + 1)) as RG;
               pose proof (round_up8_mono (A + cur + Z.of_nat (length str) + 1) (A + (cap + 1)) ltac:(lia)) as RM;
               unfold round_up8 in *; Z.div_mod_to_equations; lia. }
        cbv beta. intros ms' Q. unfold fh_post in Q. destruct Q as (r5 & Q). destruct_exs Q. destruct Q as (-> & MU7 & WM7 & MI7 & ST7 & FND).
        lazymatch type of MI7 with mem_inv _ ?mm => rename mm into m7 end.
        assert (HP7 : heap_pres AI LBh B m6 m7).
        { eapply (seg_hp s LB); [exact HR| exact HLSUB| exact MU7| exact WM7| fa_stack]. }
        pose proof (p_hlist_pres m6 m7 _ _ B ns hs X HL6 MU7 WM7 ltac:(cbn; lia) HP7 SUBh1) as HL7.
        clear HP7. transport_after_call rsegs m6 m7 MU7 WM7. clear MU7 WM7.
        assert (R5R : (0 <= r5 < 2^64)%Z).
        { destruct FND as [->|(h & Hh & ->)]; [lia|]. destruct (HF h Hh) as (? & ? & _). lia. }
        eapply (TAIL3 r5); try eassumption; try LiaTuning.alia.
    -
      lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4' end.
      seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU4 WM4. clear MI3.
      assert (METHR' : (0 <= meth' <= 11)%Z /\ (meth' = meth \/ meth' = 11)) by (rewrite EM; destruct (id =? 19); lia).
      pose proof HL0 as HLc. destruct HLc as (LC & FLC & FF & DL & HS & _ & _ & _ & _).
      pose proof (proj2 (llist_split m4' L (hd_addr AI ns (L + 24)) (last_addr AI ns L) (zlength ns) 0 0 H_httpheader_free.httpheader_free_entry H_httpmsg_compare.httpmsg_compare_entry)) as LLC.
      replace (L + 24)%Z with (P + 312)%Z in LLC by lia. replace (L + 56)%Z with (P + 344)%Z in LLC by lia. replace (L + 80)%Z with (P + 368)%Z in LLC by lia.
      specialize (LLC (conj LC (conj FLC FF))).
      assert (LSG : lseg m4' (lf_nodes AI ns hs) (hd_addr AI ns (P + 312)) L (L + 24)).
      { replace (L + 24)%Z with (P + 312)%Z by lia. eapply (lf_lseg AI); [exact DL| exact HS| exact ITEMS|]. intros b it H. exact (proj1 (proj2 (proj2 (proj2 (NF b it H))))). }
      eapply evt_cut.
      { eapply (ListFind_call q lo L (q + 48) id); try eassumption; try reflexivity; try lia.
        all: intros N it id0 H; destruct (lf_nodes_in2 AI ns hs N it id0 ITEMS H) as (b & h & Hb & Hh & -> & -> & ->);
             pose proof (NA b _ Hb); destruct (NF b _ Hb) as (? & ? & _); destruct (HF h Hh) as (? & ? & ? & _);
             first [lia | split; Z.div_mod_to_equations; lia]. }
      cbv beta. intros ms' Q. destruct_exs Q. destruct Q as (-> & MU5 & WM5 & MI5 & ST5 & FND).
      lazymatch type of MI5 with mem_inv _ ?mm => rename mm into m5 end. name_r. rename rr into nd.
      replace (ret_pc (Z_to_bv 64 0x14d68)) with (Z_to_bv 64 0x14d68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear LLC LSG LC FLC FF DL HS.
      seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU5 WM5. clear MI4.
      assert (NDR : (0 <= nd < 2^64)%Z /\ (nd = 0 \/ exists b h, In (b, hA AI h) ns /\ In h hs /\ nd = blk_addr b /\ id = hid AI h)).
      { destruct FND as [->|(it & H)]; [split; [lia| left; reflexivity]|].
        destruct (lf_nodes_in2 AI ns hs nd it id ITEMS H) as (b & h & Hb & Hh & -> & -> & ->).
        destruct (NF b _ Hb) as (? & ? & _). split; [lia|]. right. exists b, h. auto. }
      destruct NDR as [NDR FND2]. clear FND.
      assert (NDA : (nd mod 8 = 0)%Z) by (destruct FND2 as [->|(b & h & Hb & Hh & -> & ->)]; [reflexivity| exact (NA b _ Hb)]).
      eapply evt_cut.
      { eapply (ph_lf2 P q ws WSL nd); try eassumption; try LiaTuning.alia.
        destruct FND2 as [->|(b & h & Hb & Hh & -> & ->)]; [left; reflexivity| right].
        pose proof HL0 as HLc. destruct HLc as (_ & _ & _ & DL & _).
        destruct (dlseg_node ns m5 L (P + 312) b (hA AI h) DL Hb) as (pv' & nx & NC). exists pv', nx, (hA AI h).
        destruct (NF b _ Hb) as (? & ? & ? & ? & ?). split; [exact NC|]. split; [assumption| assumption]. }
      cbv beta. intros ms' [[-> ->]|(pv' & nx & it & NDNZ & NC & ITNZ & ITR & ->)].
      +
        apply evt_done. unfold front_post. exists m5. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [exact MU|]. split; [exact WM|]. split; [exact MI5|]. split; [exact TAB4|]. split; [exact MSG0|].
        split. { split; [eexists; exact VC| exact VR]. }
        split; [exact HL0|].
        right; right. exists id, o, l, cur2, meth', tlz. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact ST5|]. split; [exact FSH|]. split; [by_FY|]. split; [exact Q16b|]. split; [exact TC1|]. split; [exact SC2|]. split; [split; [exact MC4| lia]|].
        split; [split; [exact CC| exact CR]|]. repeat split; try lia. discriminate.
      +
        destruct FND2 as [E0|(b & h & Hb & Hh & -> & ->)]; [exfalso; lia|].
        pose proof HL0 as HLc. destruct HLc as (_ & _ & _ & DL & _).
        destruct (dlseg_node ns m5 L (P + 312) b (hA AI h) DL Hb) as (pv2 & nx2 & NC2).
        assert (it = hA AI h).
        { unfold node_cells in NC, NC2. destruct (NF b _ Hb) as (? & ? & ? & ? & ?).
          eapply (cell8_agree m5 (blk_addr b) _ _ 16%nat); [exact NC| exact NC2| reflexivity| reflexivity| lia| lia]. }
        subst it.
        apply evt_done. unfold front_post. exists m5. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [exact MU|]. split; [exact WM|]. split; [exact MI5|]. split; [exact TAB4|]. split; [exact MSG0|].
        split. { split; [eexists; exact VC| exact VR]. }
        split; [exact HL0|].
        right; left. exists h, o, l, cur2, meth'. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact Hh|]. split; [exact ST5|]. split; [exact FSH|]. split; [by_FY|]. split; [exact Q16b|]. split; [exact SC2|]. split; [split; [exact MC4| lia]|].
        split; [split; [exact CC| exact CR]|]. repeat split; try lia. discriminate.
  Qed.
  #[using="LOK strncasecmp_spec IMGW1 IMGW2 B QLO LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0"] Lemma ph_front : forall (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK)
      (cur meth err hack pos entp clen csz esp X : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
      (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp : word) (F : bvmap 5 word) fc
      x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 m,
    (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
    RHEAP rsegs AI s LB m -> mem_inv rsegs m -> stk rsegs m lo q ->
    rw_cells rsegs m (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) -> phFX q m ->
    p_scan m P cur -> (cur0 <= cur <= len)%Z ->
    p_msg AI m LB P A len cap okm bs -> p_meth m P meth -> p_ver m P isreq maj min -> p_ctl m P err hack pos entp clen csz esp ->
    p_hlist AI m P ns hs X -> (X <= VMAX)%Z -> bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
    u64arr rsegs m TAB_HDR ws ->
    evt rsegs (front_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp F fc A cap okm bs cur meth err hack pos entp clen csz esp ns hs X LB m)
      (PRS 0x14cd4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MSGK HR MI ST FSH FX SCN CUR MSG METH VER CTL HL XV BSUB ND TAB. unfold phFS in FSH.
    pose proof Q8 as Q8'. unfold qmod8 in Q8'.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (p_msg_facts AI m LB P A len cap okm bs s HR MSG) as (LENR & CAPR & LBS & NONEF & SOMEF).
    pose proof MSG as MSG0. destruct MSG as (MBC & OWN & _ & _ & NULT).
    destruct METH as [MC METHR]. unfold p_scan in SCN.
    assert (BUF : bytes_at rsegs m A bs /\ (0 < A \/ (A = 0 /\ len = 0))%Z /\ (A + Z.of_nat (length bs) <= lo)%Z).
    { destruct okm as [k|].
      - destruct (p_msg_bytes AI m LB P A len cap k bs MSG0) as [B1 B2]. destruct (SOMEF ltac:(discriminate)) as (A16 & AHI & _).
        split; [exact B1|]. split; [left; lia| lia].
      - destruct (NONEF eq_refl) as (-> & -> & ->). cbn in LBS. destruct bs; [| cbn in LBS; lia].
        split; [apply bytes_at_nil; lia|]. split; [right; lia| cbn; lia]. }
    destruct BUF as (BUF & ANZ & BLO).
    apply phFX_Y in FX. destruct FX as [FY (a16 & b16 & Q16)].
    destruct FY as ([j0 Q0] & [tyw Q12] & (a32 & b32 & Q32) & (ja & idw & Q48) & [j68 Q68]).
    assert (AR : (Z.of_nat (length bs) >= len /\ 0 <= cur < 2^64 /\ A + cap + 1 < 2^63 /\ len + 1 <= LMAX /\ LMAX = 2^26 + 16)%Z).
    { unfold LMAX in *. destruct okm as [k|].
      - destruct (SOMEF ltac:(discriminate)) as (A16 & AHI & _). lia.
      - destruct (NONEF eq_refl) as (-> & -> & ->). cbn in LBS |- *. lia. }
    destruct AR as (LBS2 & CURR & AHI & LENX & LMAXE).

    eapply evt_cut. { eapply ph_head; try eassumption; lia. }
    cbv beta. intros ms' ->.
    eapply evt_cut.
    { eapply (sgt_call q lo S (q + 32) (q + 12) MB A cur len cap bs); try eassumption; try reflexivity; unfold mbuf_cells; try lia. }
    cbv beta. intros ms' Q. unfold sgt_qpost in Q. destruct_exs Q.
    destruct Q as (-> & MU1 & WM1 & MI1 & ST1 & SC1 & TC1 & TYC1 & CUR1 & RES).
    lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end. name_r.
    replace (ret_pc (Z_to_bv 64 0x14ce8)) with (Z_to_bv 64 0x14ce8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct VER as [(padw & VC) VR]. destruct CTL as [CC CR]. unfold p_ctl_cells in CC.
    pose proof HL as HL0. destruct HL as (LC & FLC & FF & DL & HS & ITEMS & HB & NB & XR0).
    pose proof (munch_refl (WF okm A cap) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    set (LBh := hl_blocks AI ns hs ++ okb AI okm A cap).
    assert (HLSUB : bsub AI LBh LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]. { apply BSUB. apply in_or_app. left. exact Hb. }
      destruct okm as [k|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in OWN. exact (proj1 OWN). }
    assert (SUBh1 : bsub AI (hl_blocks AI ns hs) LBh) by (intros b Hb; apply in_or_app; left; exact Hb).
    assert (SUBh2 : bsub AI (okb AI okm A cap) LBh) by (intros b Hb; apply in_or_app; right; exact Hb).
    seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU1 WM1. clear MI. try clear LC; try clear FLC; try clear FF; try clear DL; try clear HS.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & -> & -> & -> & -> & TL1 & -> & CLE & TY5 & STRICT & CRB & CRL)|(HRR & -> & ->)].
    2:{
      eapply evt_cut. { eapply (ph_h2 P q rr); lia. }
      cbv beta. intros ms' ->. replace (rr =? 4) with false by (symmetry; apply Z.eqb_neq; lia).
      eapply (ph_rexit A cap okm bs LBK) with (r := rr) (curx := cur); try eassumption; try LiaTuning.alia. do 2 eexists; eassumption. }

    eapply evt_cut. { eapply (ph_h2 P q 4); lia. }
    cbv beta. intros ms' ->. cbn [Z.eqb Pos.eqb].
    eapply (ph_frontB A cap okm bs LBK); try eassumption; try LiaTuning.alia.
  Qed.

  #[using="LOK strncasecmp_spec IMGW1 IMGW2 B QLO LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0"] Lemma ph_frontE : forall (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK)
      (cur meth err hack pos entp clen csz esp X : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
      (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp : word) (F : bvmap 5 word) fc
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
    (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
    RHEAP rsegs AI s LB m -> mem_inv rsegs m -> stk rsegs m lo (q + 240) ->
    p_scan m P cur -> (cur0 <= cur <= len)%Z ->
    p_msg AI m LB P A len cap okm bs -> p_meth m P meth -> p_ver m P isreq maj min -> p_ctl m P err hack pos entp clen csz esp ->
    p_hlist AI m P ns hs X -> (X <= VMAX)%Z -> bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
    u64arr rsegs m TAB_HDR ws ->
    evt rsegs (front_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp tp F fc A cap okm bs cur meth err hack pos entp clen csz esp ns hs X LB m)
      (MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0w s1w (wz P) a1 a2 a3 a4 a5 a6 a7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
          F (wz parse_headers_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MSGK HR MI ST SCN CUR MSG METH VER CTL HL XV BSUB ND TAB.
    pose proof Q8 as Q8'. unfold qmod8 in Q8'.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (p_msg_facts AI m LB P A len cap okm bs s HR MSG) as (LENR & CAPR & LBS & NONEF & SOMEF).
    pose proof MSG as MSG0. destruct MSG as (MBC & OWN & _ & _ & NULT).
    destruct METH as [MC METHR]. unfold p_scan in SCN.
    assert (BUF : bytes_at rsegs m A bs /\ (0 < A \/ (A = 0 /\ len = 0))%Z /\ (A + Z.of_nat (length bs) <= lo)%Z).
    { destruct okm as [k|].
      - destruct (p_msg_bytes AI m LB P A len cap k bs MSG0) as [B1 B2]. destruct (SOMEF ltac:(discriminate)) as (A16 & AHI & _).
        split; [exact B1|]. split; [left; lia| lia].
      - destruct (NONEF eq_refl) as (-> & -> & ->). cbn in LBS. destruct bs; [| cbn in LBS; lia].
        split; [apply bytes_at_nil; lia|]. split; [right; lia| cbn; lia]. }
    destruct BUF as (BUF & ANZ & BLO).
    assert (AR : (Z.of_nat (length bs) >= len /\ 0 <= cur < 2^64 /\ A + cap + 1 < 2^63 /\ len + 1 <= LMAX /\ LMAX = 2^26 + 16)%Z).
    { unfold LMAX in *. destruct okm as [k|].
      - destruct (SOMEF ltac:(discriminate)) as (A16 & AHI & _). lia.
      - destruct (NONEF eq_refl) as (-> & -> & ->). cbn in LBS |- *. lia. }
    destruct AR as (LBS2 & CURR & AHI & LENX & LMAXE).
    destruct VER as [(padw & VC) VR]. destruct CTL as [CC CR]. unfold p_ctl_cells in CC.
    pose proof HL as HL0. destruct HL as (LC & FLC & FF & DL & HS & ITEMS & HB & NB & XR0).
    pose proof (munch_refl (WF okm A cap) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    set (LBh := hl_blocks AI ns hs ++ okb AI okm A cap).
    assert (HLSUB : bsub AI LBh LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]. { apply BSUB. apply in_or_app. left. exact Hb. }
      destruct okm as [k|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in OWN. exact (proj1 OWN). }
    assert (SUBh1 : bsub AI (hl_blocks AI ns hs) LBh) by (intros b Hb; apply in_or_app; left; exact Hb).
    assert (SUBh2 : bsub AI (okb AI okm A cap) LBh) by (intros b Hb; apply in_or_app; right; exact Hb).

    eapply evt_cut. { eapply (ph_entry P q lo); try eassumption; lia. }
    cbv beta. intros ms' (m0' & j0 & j68 & -> & MUe & WMe & MIe & STe & Q0 & [tyw Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & idw & Q48) & Q68 & FSH & SCe).
    unfold phFS in FSH.
    seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MUe WMe. clear MI. try clear LC; try clear FLC; try clear FF; try clear DL; try clear HS.
    eapply evt_cut.
    { eapply (sgt_call q lo S (q + 32) (q + 12) MB A cur len cap bs); try eassumption; try reflexivity; unfold mbuf_cells; try lia.
      all: destruct MSG0 as (MBC0 & _); exact MBC0. }
    cbv beta. intros ms' Q. unfold sgt_qpost in Q. destruct_exs Q.
    destruct Q as (-> & MU1 & WM1 & MI1 & ST1 & SC1 & TC1 & TYC1 & CUR1 & RES).
    lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end. name_r.
    replace (ret_pc (Z_to_bv 64 0x14cac)) with (Z_to_bv 64 0x14cac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    seg_std LBh HR HLSUB SUBh1 SUBh2 HL0 MSG0 MU1 WM1. clear MIe.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    eapply evt_cut. { eapply (ph_e2 P q rr). destruct RES as [(tlz & ty & -> & R)|(HRR & R)]; lia. }
    cbv beta. intros ms' [[-> ->]|[RNE ->]].
    - destruct RES as [(tlz & ty & _ & -> & -> & -> & TL1 & -> & CLE & TY5 & STRICT & CRB & CRL)|(HRR & -> & ->)]; [| exfalso; lia].
      eapply (ph_frontB A cap okm bs LBK); try eassumption; try LiaTuning.alia.
    - destruct RES as [(tlz & ty & E4 & R)|(HRR & -> & ->)]; [exfalso; lia|].
      eapply (ph_rexit A cap okm bs LBK) with (r := rr) (curx := cur); try eassumption; try LiaTuning.alia. do 2 eexists; eassumption.
  Qed.
End W.
