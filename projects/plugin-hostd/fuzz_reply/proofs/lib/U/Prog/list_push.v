From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Arr Bytes.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c list_push_run KindB ListFrame list_push_c
  ListPushTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lp_split : forall segs m a (bs junk : list byte) (n2 : nat),
  rw_cells segs m a [CB (length bs + n2) (bs ++ junk)] -> exists junk', rw_cells segs m a [CB (length bs) bs; CB n2 junk'].
Proof.
  intros segs m a bs junk n2 H.
  apply (rw_cells_split_CB segs m a [] _ _ [] [length bs; n2]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H. rewrite firstn_app, Nat.sub_diag, firstn_all in H. cbn [firstn] in H.
  rewrite app_nil_r in H. eexists. exact H.
Qed.

Lemma lp_cb : forall m a bs, bytes_at rsegs m a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> present m (a + i)) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs HB HP. pose proof (bytes_at_bound rsegs m a bs HB) as BB.
  split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (HP i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

Lemma lp_mid_in : forall {T} (b1 b2 : list T) x y, In x (b1 ++ y :: b2) -> x <> y -> In x (b1 ++ b2).
Proof.
  intros T b1 b2 x y H N. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma lp_nodup_fst : forall {X Y : Type} (l : list (X * Y)) x a b,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l. induction l as [|[x0 y0] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Hn ND'].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - rewrite Ea in Eb. injection Eb as E. exact E.
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Hb).
  - exfalso. apply Hn. replace x0 with x by congruence. exact (in_map fst _ _ Ha).
  - exact (IH x a b ND' Ha Hb).
Qed.

Lemma lp_xr : forall R R' r v, Regs6ss.xregs_eqv R R' -> is_x0 r = false -> reg_get R r = v -> reg_get R' r = v.
Proof. intros R R' r v X H E. rewrite <- (X r H). exact E. Qed.

Ltac xr X F := refine (lp_xr _ _ _ _ X _ F); reflexivity.

Section LPH.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable Fr : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis MALLOC_PC : ms_malloc Bm = 0x1608c.
Hypothesis ERRNO_LOW : errno_addr Bm + 4 <= YM05.alloc_ceiling.
Hypothesis NDB : blocks_nodup Bm API.

Lemma lp_blk : forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) ->
  4096 <= q /\ q + k <= YM05.alloc_ceiling.
Proof.
  intros L A mem md q k HM H. destruct (lf_blocks_in L A q k H) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Lemma lp_direct : malloc_contract_rt Bm API Fr -> memcpy_contract ->
  forall L A regs mem md (bnd : rt_R Fr) (l : hlist) (lines : bool) (x : list byte) (LA SRC n S : Z),
  getr regs 10 = Z_to_bv 64 LA -> getr regs 11 = Z_to_bv 64 SRC -> getr regs 12 = Z_to_bv 64 n -> S = spZ regs ->
  0 <= LA < 2 ^ 64 -> 0 <= SRC < 2 ^ 64 -> 0 <= n ->
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) LIST_PUSH_K L A regs mem md ->
  st_init_done A = true ->
  ro_agree rsegs mem ->
  (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr rsegs (Z_to_bv 64 a) = false) ->
  LA mod 8 = 0 ->
  list_at Bm L A mem LA l lines ->
  hl_n l < hl_cap l ->
  n < 2 ^ 64 - 1 ->
  bytes_at rsegs mem SRC x -> Z.of_nat (length x) = n ->
  src_home Bm L A S SRC n (hl_v l) ->
  (SRC + n <= LA \/ LA + 16 <= SRC) ->
  (lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= 6000) ->
  (lines = false -> 1 <= n) ->
  rt_ok Fr A bnd ->
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF Fr qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_PUSH) mem (seg_rom rsegs)) md)
    (lp_post Bm API Fr L A regs mem md bnd LA (hl_n l) (hl_cap l) (hl_v l) n lines x l).
Proof.
  intros MAL MC L A regs mem md bnd l lines x LA SRC n S E10 E11 E12 ES RLA RSRC RN SEG PRE INIT RO LAI AL8 LIST
    LTC NB SRCB LX SH SLA LT LF RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL. destruct AC as [AC _].
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HC & H63 & HWS & HTP & HERR & HAUX).
  rewrite <- ES in HAL, HC, H63, HWS.
  unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in HC, HWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  pose proof LIST as LIST0.
  destruct LIST as (LC0 & NB0 & CASE0 & ND0 & NV0 & TXF0).
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  destruct CASE0 as [(C0 & _) | (CP & INV & FV & LJ & ARR)]; [lia|].
  assert (LAR : 0 <= LA /\ LA + 16 <= 2 ^ 21).
  { pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI LA ltac:(lia))))).
    pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI (LA + 15) ltac:(lia))))). lia. }
  pose proof (lp_blk L A mem md _ _ HMR INV) as VB.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (ULA : bv_unsigned (Z_to_bv 64 LA) = LA) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (R2E : reg_get regs 2 = Z_to_bv 64 S) by (rewrite ES; symmetry; exact (Z_to_bv_bv_unsigned (getr regs 2))).
  assert (R10 : reg_get regs 10 = Z_to_bv 64 LA) by exact E10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 SRC) by exact E11.
  assert (R12 : reg_get regs 12 = Z_to_bv 64 n) by exact E12.
  assert (ST : stk rsegs mem (S - 48) S).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as STn.
  rewrite SEG in LC0, ARR, TXF0.
  pose proof (rw_cells_normalize rsegs mem LA _ RO LC0
                ltac:(intros i Hi; cbn in Hi; exact (proj2 (LAI (LA + i) ltac:(lia))))) as LCn.
  eapply (lift_run regs (Z_to_bv 64 LIST_PUSH) mem md [(S - 48, S)]
    (fun m' => exists j0, rw_cells rsegs m' (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                                                       C8 (getr regs 8); C8 (getr regs 1)])
    (fun R pc' => pc' = Z_to_bv 64 0x1608c /\ reg_get R 1 = Z_to_bv 64 0x148c0 /\ reg_get R 2 = Z_to_bv 64 (S - 48) /\
       reg_get R 3 = getr regs 3 /\ reg_get R 4 = getr regs 4 /\ reg_get R 8 = Z_to_bv 64 LA /\
       reg_get R 9 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (n + 1) /\ reg_get R 18 = Z_to_bv 64 SRC /\
       reg_get R 20 = getr regs 20 /\ reg_get R 21 = getr regs 21 /\ reg_get R 22 = getr regs 22 /\
       reg_get R 23 = getr regs 23 /\ reg_get R 24 = getr regs 24 /\ reg_get R 25 = getr regs 25 /\
       reg_get R 26 = getr regs 26 /\ reg_get R 27 = getr regs 27));
    [exact Hh | exact Hl | exact RO | |].
  { unfold Regs6ss.mkR_of. rewrite R2E, R10, R11, R12.
    eapply evt_mono.
    { eapply lpu_run1 with (lo := S - 48) (V := hl_v l) (N := hl_n l) (CAP := hl_cap l);
        [rewrite US; exact STn | rewrite US; lia | rewrite ULA; exact LCn | rewrite ULA, US; lia | rewrite ULA; exact AL8
        | lia | lia | rewrite UN; lia]. }
    intros ms' (t0 & t1 & t2 & b1 & b2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & j0 & -> & MU & WM & FR).
    rewrite US in MU, FR. rewrite US, UN.
    eexists _, _, m'. split; [reflexivity|].
    split; [repeat split|].
    split; [exact MU|]. split; [exact WM | exists j0; exact FR]. }
  intros R R1 pc' m1 m'' (EPC & F_1 & F_2 & F_3 & F_4 & F_8 & F_9 & F_10 & F_18 & F_20 & F_21 & F_22 & F_23 & F_24
    & F_25 & F_26 & F_27) X MU1 WM1 RO1 REL1 (j0 & FRp).
  subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL1 FRp) as FR1.
  assert (E1_1 : reg_get R1 1 = Z_to_bv 64 0x148c0) by (xr X F_1).
  assert (E1_2 : reg_get R1 2 = Z_to_bv 64 (S - 48)) by (xr X F_2).
  assert (E1_3 : reg_get R1 3 = getr regs 3) by (xr X F_3).
  assert (E1_4 : reg_get R1 4 = getr regs 4) by (xr X F_4).
  assert (E1_8 : reg_get R1 8 = Z_to_bv 64 LA) by (xr X F_8).
  assert (E1_9 : reg_get R1 9 = Z_to_bv 64 n) by (xr X F_9).
  assert (E1_10 : reg_get R1 10 = Z_to_bv 64 (n + 1)) by (xr X F_10).
  assert (E1_18 : reg_get R1 18 = Z_to_bv 64 SRC) by (xr X F_18).
  assert (E1_20 : reg_get R1 20 = getr regs 20) by (xr X F_20).
  assert (E1_21 : reg_get R1 21 = getr regs 21) by (xr X F_21).
  assert (E1_22 : reg_get R1 22 = getr regs 22) by (xr X F_22).
  assert (E1_23 : reg_get R1 23 = getr regs 23) by (xr X F_23).
  assert (E1_24 : reg_get R1 24 = getr regs 24) by (xr X F_24).
  assert (E1_25 : reg_get R1 25 = getr regs 25) by (xr X F_25).
  assert (E1_26 : reg_get R1 26 = getr regs 26) by (xr X F_26).
  assert (E1_27 : reg_get R1 27 = getr regs 27) by (xr X F_27).
  assert (MID1 : lmid Bm API LIST_PUSH_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (lmid_A Bm API SEG AX LIST_PUSH_K S _ L A mem md m1 [(S - 48, S)]);
      [ exact HMR | exact HWF | exact HBD | unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; lia | lia
      | intros a [Ha|Ha];
        [apply HWS; unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in Ha; lia | apply HERR; exact Ha]
      | exact MU1 | rewrite SEG; exact WM1 | | ].
    - intros y Hy O. cbn [outside] in O. left.
      assert (D : S - 48 <= y < S \/ ~ (S - 48 <= y < S)) by lia.
      destruct D as [D|D];
        [unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; lia | exfalso; apply O; split; [exact D | exact I]].
    - intros y Hy _. cbn [outside]. split; [lia | exact I]. }
  assert (LC1 : rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ LC0 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (LCC : length (concat (map text_rec (hl_recs l))) = Z.to_nat (16 * hl_n l))
    by (rewrite lp_concat_len; unfold hl_n; lia).
  assert (ARRb : rw_cells rsegs mem (hl_v l)
                   [CB (length (concat (map text_rec (hl_recs l))) + Z.to_nat (16 * (hl_cap l - hl_n l)))
                       (concat (map text_rec (hl_recs l)) ++ hl_junk l)]).
  { apply (lp_cb_eq _ _ _ _ _ _ _ ARR); [lia | reflexivity]. }
  destruct (lp_split _ _ _ _ _ _ ARRb) as [junk1 ARRs]. rewrite LCC in ARRs.
  assert (ARR1 : rw_cells rsegs m1 (hl_v l) [CB (Z.to_nat (16 * hl_n l)) (concat (map text_rec (hl_recs l)));
                                            CB (Z.to_nat (16 * (hl_cap l - hl_n l))) junk1]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ ARRs MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (TX1 : Forall (fun r => In (fst r, text_len r) (blocks L A) /\
                   rw_cells rsegs m1 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l)).
  { eapply Forall_impl; [|exact TXF0]. intros r (T1 & _ & T3 & _). split; [exact T1|].
    pose proof (lp_blk L A mem md _ _ HMR T1) as Q.
    apply (rw_cells_transport rsegs _ mem m1 _ _ T3 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (SRC1 : bytes_at rsegs m1 SRC x).
  { apply (bytes_at_transport rsegs _ mem m1 _ _ SRCB MU1). cbn [disjoint_from]. rewrite LX. split; [|exact I].
    destruct SH as [(H1 & H2) | [(q & k & Hq & Hqv & H1 & H2) | (H0 & H1 & H2 & H3)]].
    - right. lia.
    - left. pose proof (lp_blk L A mem md q k HMR Hq). lia.
    - left. rewrite SEG in H3.
      pose proof (ro_in_img Bm SEG (SRC + (n - 1)) ltac:(lia) (H3 (n - 1) ltac:(lia))) as Y.
      pose proof (lf_img_low Bm SEG _ Y). lia. }
  assert (SH1 : (S <= SRC /\ SRC + n <= 2 ^ 64) \/
    (exists q k, In (q, k) (blocks L A) /\ (q <> hl_v l \/ k = 0) /\ q <= SRC /\ SRC + n <= q + k) \/
    (0 < n /\ 0 <= SRC /\ SRC + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr (ms_segs Bm) (Z_to_bv 64 (SRC + i)) = true)).
  { destruct SH as [H|[(q & k & H1 & H2 & H3 & H4)|H]];
      [left; exact H | right; left; exists q, k; split; [exact H1|]; split; [left; exact H2|]; split; [exact H3 | exact H4]
      | right; right; exact H]. }
  assert (B1 : forall q m, In (q, m) (blocks L A) ->
                 (In (q, m) (blocks L A) /\ (0 < m -> ~ (hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l))) \/ q = hl_v l).
  { intros q m Hq. left. split; [exact Hq | intros _ (Y & _); lia]. }
  assert (B2 : forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L A))
    by (intros q m Hq _; exact Hq).
  assert (B3 : forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks l) -> q <> hl_v l).
  { intros q m _ _ NI Eq. apply NI. unfold list_blocks. apply in_or_app. left.
    destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; symmetry; exact Eq]. }
  assert (NE : (hl_n l =? hl_cap l) = false) by (apply Z.eqb_neq; lia).
  assert (EG : hl_cap l = grow_cap (hl_n l) (hl_cap l)) by (unfold grow_cap; rewrite NE; reflexivity).
  assert (LQ0 : length (@nil sptr) = nretF (list_grow_tr (sh_of (known_at L A) l)))
    by (rewrite lp_grow_tr, NE; reflexivity).
  assert (RES1 : rt_ok Fr A (runF Fr [] bnd (list_grow_tr (sh_of (known_at L A) l))))
    by (rewrite lp_grow_tr, NE; exact RES).
  exact (lp_tail Bm API Fr AX CTX MALLOC_PC ERRNO_LOW NDB MAL MC L A regs mem md bnd l lines x L A R1 m1 md (hl_v l)
    (hl_cap l) j0 junk1 (fun _ => False) (fun _ => False) LA SRC n S [] SEG PRE ES LAI LIST0 (fun Y => ltac:(lia)) NB LX
    RSRC SLA LT LF MID1 (fun a Y => match Y with end) (fun q Y => match Y with end) E1_1 E1_2 E1_4 E1_8 E1_9 E1_10 E1_18
    E1_3 E1_20 E1_21 E1_22 E1_23 E1_24 E1_25 E1_26 E1_27 FR1 LC1 EG INV FV ARR1 (fun _ => eq_refl) TX1 NV0 SRC1 SH1
    B1 B2 B3 INIT LQ0 RES1 ROOM (fun Y => ltac:(exfalso; lia)) RO1).
Qed.

Lemma lp_cpk : forall K L A regs mem md (E E' : Z -> Prop) L' A' regs' mem' md',
  call_post_k Bm (aa_MR API) K L A regs mem md E L' A' regs' mem' md' -> (forall a, E a -> E' a) ->
  call_post_k Bm (aa_MR API) K L A regs mem md E' L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E E' L' A' regs' mem' md' (M & W & B & LY & PA & RP & MD & FR & BK & SC) HE.
  split; [exact M|]. split; [exact W|]. split; [exact B|]. split; [exact LY|]. split; [exact PA|].
  split; [exact RP|]. split; [exact MD|].
  split; [intros a Ha N1 N2 NS NE; apply FR; [exact Ha | exact N1 | exact N2 | exact NS | intro Y; exact (NE (HE a Y))]|].
  split; [exact BK | exact SC].
Qed.

Definition lp_rl (L : layout) (A : astate) (R1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model)
    (b : rt_R Fr) (N CAP V G : Z) (gt : trF) (old : list byte) (c' : config) : Prop :=
  exists L2 A2 R2 m2 md2 res,
    c' = mkCfg (YK11.mkst R2 (getr R1 1) m2 (seg_rom rsegs)) md2 /\
    call_post_k Bm (aa_MR API) REALLOC_STACK L A R1 m1 md1 (fun a => 0 < CAP /\ V <= a < V + 16 * CAP)
      L2 A2 R2 m2 md2 /\
    getr R2 10 = Z_to_bv 64 res /\ res <> 0 /\ fresh_block Bm res (16 * G) /\
    (exists b1 b2 c1 c2, blocks L2 A2 = c1 ++ (res, 16 * G) :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
       ((CAP = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAP /\ blocks L A = b1 ++ (V, 16 * CAP) :: b2))) /\
    (forall q k, In (q, k) (user_blocks A) -> 0 < k -> ~ (0 < CAP /\ ptr_addr L q = V) -> In (q, k) (user_blocks A2)) /\
    (forall q, In (q, 0) (user_blocks A) -> In (q, 0) (user_blocks A2)) /\
    ro_agree rsegs m2 /\ bytes_at rsegs m2 res old /\
    st_init_done A2 = true /\ (length (st_regions A) <= length (st_regions A2))%nat /\
    exists q, In (q, 16 * G) (user_blocks A2) /\ ptr_addr L2 q = res /\ rt_ok Fr A2 (runF Fr [q] b gt).

Lemma lp_rl_ra : realloc_contract_rt Bm API Fr 0x178f8 -> ms_segs Bm = rsegs ->
  forall L A R1 m1 md1 b (N CAP V G : Z) old,
  call_pre_k Bm (aa_MR API) REALLOC_STACK L A R1 m1 md1 -> ro_agree rsegs m1 ->
  0 < CAP -> In (V, 16 * CAP) (blocks L A) -> getr R1 10 = Z_to_bv 64 V -> getr R1 11 = Z_to_bv 64 (16 * G) ->
  G = 2 * CAP -> N = CAP -> bytes_at rsegs m1 V old -> Z.of_nat (length old) = 16 * CAP ->
  rt_ok Fr A b -> rt_room Fr b (32 * CAP) ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x178f8) m1 (seg_rom rsegs)) md1)
    (lp_rl L A R1 m1 md1 b N CAP V G [RRealloc (16 * CAP) (32 * CAP) (Known (sptr_of L A V))] old).
Proof.
  intros RA SEG L A R1 m1 md1 b N CAP V G old PRE RO1 CP IN E10 E11 EG EN OB LOLD RES ROOM.
  pose proof PRE as (HM1 & HW1 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (bytes_at_bound rsegs m1 _ _ OB) as BOB.
  destruct (lp_spec Bm API NDB L A m1 md1 HM1 V (16 * CAP) IN) as (Hp & Ep).
  set (p := sptr_of L A V) in *.
  assert (A10 : getr R1 10 = Z_to_bv 64 (ptr_addr L p)) by (rewrite Ep; exact E10).
  assert (AOLD : forall i, 0 <= i < 16 * CAP -> mbyte rsegs m1 (ptr_addr L p + i) = nth_error old (Z.to_nat i)).
  { intros i Hi. rewrite Ep. pose proof (mbyte_of_bytes_at rsegs m1 _ _ (Z.to_nat i) OB ltac:(lia)) as Y.
    rewrite Z2Nat.id in Y by lia. exact Y. }
  assert (ROOM' : rt_room Fr b (16 * G)) by (replace (16 * G) with (32 * CAP) by lia; exact ROOM).
  pose proof RA as R. unfold realloc_contract_rt in R. rewrite SEG in R.
  eapply SR_mono; [exact (R L A R1 m1 md1 p (16 * CAP) (16 * G) old b PRE RO1 Hp A10 E11 AOLD LOLD RES ROOM')|].
  intros c' (L2 & A2 & R2 & m2 & md2 & res & -> & CP' & A0 & NZ & AL & FR & BLK & KEPT & RO2 & GK & SURV & CPY
             & INI2 & LN & (qr & Hqr & Eqr & RES2)).
  pose proof FR as (F1 & F2 & _).
  exists L2, A2, R2, m2, md2, res. split; [reflexivity|].
  split.
  { apply (lp_cpk _ _ _ _ _ _ _ _ _ _ _ _ _ CP'). intros a Ha. cbv beta in Ha |- *. rewrite Ep in Ha.
    split; [exact CP | exact Ha]. }
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split.
  { destruct BLK as (b1 & b2 & c1 & c2 & E1 & E2 & E3). rewrite Ep in E1.
    exists b1, b2, c1, c2. split; [exact E2|]. split; [exact E3|]. right. split; [exact CP | exact E1]. }
  split; [intros q k Hq _ NQ; apply SURV; [exact Hq|]; intros ->; apply NQ; split; [exact CP | exact Ep]|].
  split.
  { intros q Hq. apply SURV; [exact Hq|]. intros ->.
    pose proof (lp_nodup_fst _ p 0 (16 * CAP) (YO10.user_block_ptrs_NoDup A HW1) Hq Hp). lia. }
  split; [exact RO2|].
  split.
  { apply bytes_at_of_mbyte; [lia | lia |].
    intros i Hi. rewrite (CPY (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity. }
  split; [exact INI2|]. split; [exact LN|].
  exists qr. split; [exact Hqr|]. split; [exact Eqr|].
  replace (32 * CAP) with (16 * G) by lia. exact RES2.
Qed.

Lemma lp_rl_rn : realloc_null_contract_rt Bm API Fr 0x178f8 -> ms_segs Bm = rsegs ->
  forall L A R1 m1 md1 b (N CAP V G : Z),
  call_pre_k Bm (aa_MR API) REALLOC_STACK L A R1 m1 md1 -> ro_agree rsegs m1 ->
  CAP = 0 -> V = 0 -> N = CAP -> getr R1 10 = Z_to_bv 64 V -> getr R1 11 = Z_to_bv 64 (16 * G) -> G = 8 ->
  rt_ok Fr A b -> rt_room Fr b 128 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x178f8) m1 (seg_rom rsegs)) md1) (lp_rl L A R1 m1 md1 b N CAP V G [RMalloc 128] []).
Proof.
  intros RN SEG L A R1 m1 md1 b N CAP V G PRE RO1 C0 V0 EN E10 E11 EG RES ROOM.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (A10 : getr R1 10 = Z_to_bv 64 0) by (rewrite E10, V0; reflexivity).
  assert (ROOM' : rt_room Fr b (16 * G)) by (rewrite EG; exact ROOM).
  pose proof RN as R. unfold realloc_null_contract_rt, malloc_ret_rt in R. rewrite SEG in R.
  eapply SR_mono; [exact (R L A R1 m1 md1 (16 * G) b PRE RO1 A10 E11 RES ROOM')|].
  intros c' (L2 & A2 & R2 & m2 & md2 & res & -> & CP' & A0 & NZ & AL & FR & (b1 & b2 & E1 & E2) & KEPT & RO2
             & GK & SURV & INI2 & LN & RES2).
  pose proof FR as (F1 & F2 & _).
  exists L2, A2, R2, m2, md2, res. split; [reflexivity|].
  split; [apply (lp_cpk _ _ _ _ _ _ _ _ _ _ _ _ _ CP'); intros a Ha; destruct Ha|].
  split; [exact A0|]. split; [exact NZ|]. split; [exact FR|].
  split; [exists b1, b2, b1, b2; split; [exact E1|]; split; [reflexivity|]; left; split; [exact C0 | exact E2]|].
  split; [intros q k Hq _ _; exact (SURV q k Hq)|].
  split; [intros q Hq; exact (SURV q 0 Hq)|].
  split; [exact RO2|].
  split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
  split; [exact INI2|]. split; [exact LN|].
  pose proof CP' as (M2' & _).
  destruct (lp_spec Bm API NDB L2 A2 m2 md2 M2' res (16 * G)) as (Hq' & Eq');
    [rewrite E1; apply in_or_app; right; left; reflexivity|].
  exists (sptr_of L2 A2 res). split; [exact Hq'|]. split; [exact Eq'|].
  rewrite EG in RES2. exact RES2.
Qed.

Lemma lp_after : malloc_contract_rt Bm API Fr -> memcpy_contract ->
  forall L A regs mem md (bnd : rt_R Fr) (l : hlist) (lines : bool) (x : list byte) (LA SRC n S : Z)
    R1 m1 j0 G old cf,
  S = spZ regs -> 0 <= SRC < 2 ^ 64 -> 0 <= n ->
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) LIST_PUSH_K L A regs mem md ->
  (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr rsegs (Z_to_bv 64 a) = false) ->
  list_at Bm L A mem LA l lines ->
  hl_n l = hl_cap l -> hl_cap l < 2 ^ 29 -> n < 2 ^ 64 - 1 -> Z.of_nat (length x) = n ->
  (SRC + n <= LA \/ LA + 16 <= SRC) ->
  (lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= 6000) ->
  (lines = false -> 1 <= n) ->
  lmid Bm API LIST_PUSH_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md ->
  reg_get R1 1 = Z_to_bv 64 0x148ac -> reg_get R1 2 = Z_to_bv 64 (S - 48) -> reg_get R1 3 = getr regs 3 ->
  reg_get R1 4 = getr regs 4 -> reg_get R1 8 = Z_to_bv 64 LA -> reg_get R1 9 = Z_to_bv 64 n ->
  reg_get R1 18 = Z_to_bv 64 SRC -> reg_get R1 19 = Z_to_bv 64 G ->
  reg_get R1 20 = getr regs 20 -> reg_get R1 21 = getr regs 21 -> reg_get R1 22 = getr regs 22 ->
  reg_get R1 23 = getr regs 23 -> reg_get R1 24 = getr regs 24 -> reg_get R1 25 = getr regs 25 ->
  reg_get R1 26 = getr regs 26 -> reg_get R1 27 = getr regs 27 ->
  rw_cells rsegs m1 (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
                              C8 (getr regs 1)] ->
  rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))] ->
  G = grow_cap (hl_n l) (hl_cap l) ->
  old = concat (map text_rec (hl_recs l)) ->
  Forall (fun r => In (fst r, text_len r) (blocks L A) /\
                   rw_cells rsegs m1 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l) ->
  bytes_at rsegs m1 SRC x ->
  src_home Bm L A S SRC n (hl_v l) ->
  ro_agree rsegs m1 ->
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF Fr qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  lp_rl L A R1 m1 md bnd (hl_n l) (hl_cap l) (hl_v l) G (list_grow_tr (sh_of (known_at L A) l)) old cf ->
  SR rsegs cf (lp_post Bm API Fr L A regs mem md bnd LA (hl_n l) (hl_cap l) (hl_v l) n lines x l).
Proof.
  intros MAL MC L A regs mem md bnd l lines x LA SRC n S R1 m1 j0 G old cf ES RSRC RN SEG PRE LAI LIST EQ NCAP NB LX
    SLA LT LF MID1 F1_1 F1_2 F1_3 F1_4 F1_8 F1_9 F1_18 F1_19 F1_20 F1_21 F1_22 F1_23 F1_24 F1_25 F1_26 F1_27 FR1 LC1
    EG EO TX1 SRC1 SH RO1 ROOM RL.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL. destruct AC as [AC _].
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HC & H63 & HWS & HTP & HERR & HAUX).
  rewrite <- ES in HAL, HC, H63, HWS.
  unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in HC.
  assert (KVAL : LIST_PUSH_K = 8304) by reflexivity.
  pose proof MID1 as (M1 & W1 & BD1 & LY1 & LN1 & SV1 & Z1 & OW1 & MD1 & FRM1 & BK1 & SC1).
  pose proof LIST as LIST0.
  destruct LIST as (LC0 & NB0 & CASE0 & ND0 & NV0 & TXF0).
  rewrite SEG in TXF0.
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (LAR : 0 <= LA /\ LA + 16 <= 2 ^ 21).
  { pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI LA ltac:(lia))))).
    pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI (LA + 15) ltac:(lia))))). lia. }
  destruct (lp_grow (hl_n l) (hl_cap l) ltac:(lia)) as (GB1 & _). rewrite <- EG in GB1.
  assert (GV : 0 < G <= 2 ^ 30).
  { rewrite EG. unfold grow_cap. destruct (Z.eqb_spec (hl_n l) (hl_cap l)); [|lia].
    destruct (Z.eqb_spec (hl_cap l) 0); lia. }
  assert (LOLD : Z.of_nat (length old) = 16 * hl_n l) by (rewrite EO, lp_concat_len; unfold hl_n; lia).
  assert (SP1 : spZ R1 = S - 48).
  { unfold spZ. change (getr R1 2) with (reg_get R1 2). rewrite F1_2. apply unsigned_lit. lia. }
  assert (NE1 : forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) ->
                  ~ (0 < hl_cap l /\ hl_v l <= a < hl_v l + 16 * hl_cap l)).
  { intros a Ha (Y1 & Y2). destruct CASE0 as [(C0 & _) | (_ & INV & (_ & _ & FVi) & _)]; [lia|].
    pose proof (lp_blk L A mem md _ _ HMR INV) as Q.
    destruct Ha as [Ha|Ha]; [lia|]. apply (FVi (a - hl_v l)); [lia|].
    replace (hl_v l + (a - hl_v l)) with a by ring. exact Ha. }
  assert (NIV : forall q, ~ In q (list_blocks l) -> hl_cap l = 0 \/ q <> hl_v l).
  { intros q NI. destruct (Z.eq_dec (hl_cap l) 0) as [C0|C0]; [left; exact C0|]. right. intro Eq. apply NI.
    unfold list_blocks. apply in_or_app. left. destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; symmetry; exact Eq]. }
  destruct RL as (L2 & A2 & R2 & m2 & md2 & res & -> & CP & A0 & NZ & FRES & BLK & SV & ZV & RO2 & OB2 & INI2 & LN2
    & qg & Hqg & Eqg & RES2).
  destruct BLK as (b1 & b2 & c1 & c2 & BLK1 & BLK2 & BLK3).
  pose proof CP as (M2 & W2 & BD2 & LY2 & PA2 & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ M2) as (Hh2 & Hl2 & Hmat2).
  pose proof FRES as (FR_lo & FR_hi & FR_img).
  assert (CS : forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27)) -> callee_saved r)
    by (intros r Hr; unfold callee_saved; lia).
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (S - 48)) by exact (eq_trans (HPRES 2 (CS 2 ltac:(lia))) F1_2).
  assert (E2_3 : reg_get R2 3 = getr regs 3) by exact (eq_trans (HPRES 3 (CS 3 ltac:(lia))) F1_3).
  assert (E2_4 : reg_get R2 4 = getr regs 4) by exact (eq_trans (HPRES 4 (CS 4 ltac:(lia))) F1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 LA) by exact (eq_trans (HPRES 8 (CS 8 ltac:(lia))) F1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 n) by exact (eq_trans (HPRES 9 (CS 9 ltac:(lia))) F1_9).
  assert (E2_18 : reg_get R2 18 = Z_to_bv 64 SRC) by exact (eq_trans (HPRES 18 (CS 18 ltac:(lia))) F1_18).
  assert (E2_19 : reg_get R2 19 = Z_to_bv 64 G) by exact (eq_trans (HPRES 19 (CS 19 ltac:(lia))) F1_19).
  assert (E2_20 : reg_get R2 20 = getr regs 20) by exact (eq_trans (HPRES 20 (CS 20 ltac:(lia))) F1_20).
  assert (E2_21 : reg_get R2 21 = getr regs 21) by exact (eq_trans (HPRES 21 (CS 21 ltac:(lia))) F1_21).
  assert (E2_22 : reg_get R2 22 = getr regs 22) by exact (eq_trans (HPRES 22 (CS 22 ltac:(lia))) F1_22).
  assert (E2_23 : reg_get R2 23 = getr regs 23) by exact (eq_trans (HPRES 23 (CS 23 ltac:(lia))) F1_23).
  assert (E2_24 : reg_get R2 24 = getr regs 24) by exact (eq_trans (HPRES 24 (CS 24 ltac:(lia))) F1_24).
  assert (E2_25 : reg_get R2 25 = getr regs 25) by exact (eq_trans (HPRES 25 (CS 25 ltac:(lia))) F1_25).
  assert (E2_26 : reg_get R2 26 = getr regs 26) by exact (eq_trans (HPRES 26 (CS 26 ltac:(lia))) F1_26).
  assert (E2_27 : reg_get R2 27 = getr regs 27) by exact (eq_trans (HPRES 27 (CS 27 ltac:(lia))) F1_27).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 res) by exact A0.
  assert (MID2 : lmid Bm API LIST_PUSH_K S (fun _ => False) (fun q => hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l)
                   L A m1 md L2 A2 m2 md2).
  { apply (lmid_call Bm API AX CTX LIST_PUSH_K S REALLOC_STACK L A R1 m1 md
             (fun a => 0 < hl_cap l /\ hl_v l <= a < hl_v l + 16 * hl_cap l) L2 A2 R2 m2 md2 _ M1 CP);
      [ exact NE1 | rewrite SP1; unfold LIST_PUSH_K, LIST_PUSH_FRAME; lia | rewrite SP1; lia | rewrite KVAL; lia | lia
      | exact SC1 | | exact ZV | exact LN2 ].
    intros p k Hp Hk NF. apply SV; [exact Hp | exact Hk |]. intros (Y1 & Y2). apply NF.
    split; [exact EQ|]. split; [exact Y1 | exact Y2]. }
  assert (FR2 : rw_cells rsegs m2 (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                                            C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API REALLOC_STACK L A R1 m1 md _ L2 A2 R2 m2 md2 _ _ CP);
      [|rewrite SEG; exact FR1].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    assert (HA : YM05.alloc_ceiling <= S - 48 + i < 2 ^ 64) by lia.
    split; [left; exact HA|].
    split; [intro Y; pose proof (owned_low Bm _ LAWS _ _ _ _ _ M1 Y); lia|].
    split; [intro Y; pose proof (owned_low Bm _ LAWS _ _ _ _ _ M2 Y); lia|].
    split; [unfold scratch_k; rewrite SP1; lia | exact (NE1 _ (or_introl HA))]. }
  assert (LC2 : rw_cells rsegs m2 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API REALLOC_STACK L A R1 m1 md _ L2 A2 R2 m2 md2 _ _ CP);
      [|rewrite SEG; exact LC1].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    destruct (LAI (LA + i) ltac:(lia)) as [IP NR]. pose proof IP as (II & _ & _ & IE).
    split; [right; exact II|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M1 IP)|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M2 IP)|].
    split; [unfold scratch_k; rewrite SP1; intros [Y|Y]; [unfold REALLOC_STACK, ALLOC_STACK in Y; lia | exact (IE Y)]
           | exact (NE1 _ (or_intror II))]. }
  assert (OLD : forall q k, In (q, k) (blocks L A) -> (hl_cap l = 0 \/ q <> hl_v l) -> In (q, k) (c1 ++ c2)).
  { intros q k Hq Hc. rewrite BLK2. destruct BLK3 as [(C0 & EB) | (CP0 & EB)]; rewrite EB in Hq; [exact Hq|].
    apply (lp_mid_in _ _ _ _ Hq). intros Y. injection Y as Y1 Y2. destruct Hc as [Hc|Hc]; [lia | exact (Hc Y1)]. }
  assert (NEW : forall q k, In (q, k) (c1 ++ c2) -> In (q, k) (blocks L2 A2)).
  { intros q k H. rewrite BLK1. apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left; exact H | right; right; exact H]. }
  assert (DJ : forall q k, In (q, k) (c1 ++ c2) -> q + k <= res \/ res + 16 * G <= q).
  { intros q k H. exact (blocks_mid_disjoint Bm _ LAWS _ _ _ _ _ _ _ _ _ _ M2 BLK1 H). }
  assert (BOLD : forall q k, In (q, k) (c1 ++ c2) -> In (q, k) (blocks L A) /\ (0 < k -> 0 < hl_cap l -> q <> hl_v l)).
  { intros q k H. rewrite BLK2 in H. destruct BLK3 as [(C0 & EB) | (CP0 & EB)]; rewrite EB.
    - split; [exact H | intros _ Y; lia].
    - split; [apply in_or_app; apply in_app_or in H; destruct H as [H|H]; [left; exact H | right; right; exact H]|].
      intros Hk _ Eq. subst q. pose proof (blocks_mid_disjoint Bm _ LAWS _ _ _ _ _ _ _ _ _ _ HMR EB H). lia. }
  pose proof (rw_cells_normalize rsegs m2 LA _ RO2 LC2
                ltac:(intros i Hi; cbn in Hi; exact (proj2 (LAI (LA + i) ltac:(lia))))) as LCn.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  change (getr R1 1) with (reg_get R1 1). rewrite F1_1.
  eapply (lift_run R2 (Z_to_bv 64 0x148ac) m2 md2 [(LA, LA + 16)]
    (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 res); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 G)])
    (fun R pc' => pc' = Z_to_bv 64 0x1608c /\ reg_get R 1 = Z_to_bv 64 0x148c0 /\ reg_get R 2 = Z_to_bv 64 (S - 48) /\
       reg_get R 3 = getr regs 3 /\ reg_get R 4 = getr regs 4 /\ reg_get R 8 = Z_to_bv 64 LA /\
       reg_get R 9 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (n + 1) /\ reg_get R 18 = Z_to_bv 64 SRC /\
       reg_get R 20 = getr regs 20 /\ reg_get R 21 = getr regs 21 /\ reg_get R 22 = getr regs 22 /\
       reg_get R 23 = getr regs 23 /\ reg_get R 24 = getr regs 24 /\ reg_get R 25 = getr regs 25 /\
       reg_get R 26 = getr regs 26 /\ reg_get R 27 = getr regs 27));
    [exact Hh2 | exact Hl2 | exact RO2 | |].
  { unfold Regs6ss.mkR_of. rewrite E2_8, E2_9, E2_10, E2_19.
    eapply evt_mono.
    { eapply lpu_run2 with (V0 := hl_v l) (CAP := hl_cap l); [exact LCn | lia | lia | lia | lia | rewrite UN; lia]. }
    intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & LCm).
    rewrite UN.
    eexists _, _, m'. split; [reflexivity|].
    split.
    { split; [reflexivity|]. split; [reflexivity|]. split; [exact E2_2|]. split; [exact E2_3|]. split; [exact E2_4|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact E2_18|].
      split; [exact E2_20|]. split; [exact E2_21|]. split; [exact E2_22|]. split; [exact E2_23|].
      split; [exact E2_24|]. split; [exact E2_25|]. split; [exact E2_26 | exact E2_27]. }
    split; [exact MU|]. split; [exact WM | exact LCm]. }
  intros R R3 pc' m3 m'' (EPC & G_1 & G_2 & G_3 & G_4 & G_8 & G_9 & G_10 & G_18 & G_20 & G_21 & G_22 & G_23 & G_24
    & G_25 & G_26 & G_27) X3 MU3 WM3 RO3 REL3 LC3p.
  subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 LC3p) as LC3.
  assert (E3_1 : reg_get R3 1 = Z_to_bv 64 0x148c0) by (xr X3 G_1).
  assert (E3_2 : reg_get R3 2 = Z_to_bv 64 (S - 48)) by (xr X3 G_2).
  assert (E3_3 : reg_get R3 3 = getr regs 3) by (xr X3 G_3).
  assert (E3_4 : reg_get R3 4 = getr regs 4) by (xr X3 G_4).
  assert (E3_8 : reg_get R3 8 = Z_to_bv 64 LA) by (xr X3 G_8).
  assert (E3_9 : reg_get R3 9 = Z_to_bv 64 n) by (xr X3 G_9).
  assert (E3_10 : reg_get R3 10 = Z_to_bv 64 (n + 1)) by (xr X3 G_10).
  assert (E3_18 : reg_get R3 18 = Z_to_bv 64 SRC) by (xr X3 G_18).
  assert (E3_20 : reg_get R3 20 = getr regs 20) by (xr X3 G_20).
  assert (E3_21 : reg_get R3 21 = getr regs 21) by (xr X3 G_21).
  assert (E3_22 : reg_get R3 22 = getr regs 22) by (xr X3 G_22).
  assert (E3_23 : reg_get R3 23 = getr regs 23) by (xr X3 G_23).
  assert (E3_24 : reg_get R3 24 = getr regs 24) by (xr X3 G_24).
  assert (E3_25 : reg_get R3 25 = getr regs 25) by (xr X3 G_25).
  assert (E3_26 : reg_get R3 26 = getr regs 26) by (xr X3 G_26).
  assert (E3_27 : reg_get R3 27 = getr regs 27) by (xr X3 G_27).
  pose proof (lmid_trans Bm API LIST_PUSH_K S _ _ _ _ L A mem md L A m1 md L2 A2 m2 md2 HWF MID1 MID2) as MID12.
  pose proof MID12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC12).
  assert (MID3 : lmid Bm API LIST_PUSH_K S (fun a => LA <= a < LA + 16) (fun _ => False) L2 A2 m2 md2 L2 A2 m3 md2).
  { apply (lmid_A Bm API SEG AX LIST_PUSH_K S _ L2 A2 m2 md2 m3 [(LA, LA + 16)]);
      [exact M2 | exact W2 | exact BD2 | rewrite KVAL; lia | lia | exact SC12 | exact MU3 | rewrite SEG; exact WM3 | |].
    - intros y Hy O. cbn [outside] in O. right.
      assert (D : LA <= y < LA + 16 \/ ~ (LA <= y < LA + 16)) by lia.
      destruct D as [D|D]; [exact D | exfalso; apply O; split; [exact D | exact I]].
    - intros y Hy Ho. cbn [outside]. split; [|exact I].
      intro Y. exact (lf_img_not_owned Bm API AX L2 A2 m2 md2 y M2 (proj1 (LAI y Y)) Ho). }
  pose proof (lmid_trans Bm API LIST_PUSH_K S _ _ _ _ L A mem md L2 A2 m2 md2 L2 A2 m3 md2 HWF MID12 MID3) as MIDf.
  assert (HE : forall a, (False \/ False) \/ LA <= a < LA + 16 -> LA <= a < LA + 16)
    by (intros a [[Y|Y]|Y]; [destruct Y | destruct Y | exact Y]).
  assert (HF : forall q, (False \/ (hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l)) \/ False ->
                 hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l)
    by (intros q [[Y|Y]|Y]; [destruct Y | exact Y | destruct Y]).
  assert (FR3 : rw_cells rsegs m3 (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                                            C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (INB : In (res, 16 * G) (blocks L2 A2)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (PR : forall i, 0 <= i < Z.of_nat (length old) -> present m2 (res + i))
    by (intros i Hi; exact (proj1 (block_facts Bm _ LAWS _ _ _ _ _ _ i M2 INB ltac:(lia)))).
  pose proof (lp_cb m2 res old OB2 PR) as OC.
  destruct (lf_block_present_rw Bm API L2 A2 m2 md2 res (16 * G) (res + 16 * hl_n l) (Z.to_nat (16 * (G - hl_n l)))
              M2 INB ltac:(lia) ltac:(lia)) as [junk1 JR].
  rewrite SEG in JR.
  assert (OC' : rw_cells rsegs m2 res [CB (Z.to_nat (16 * hl_n l)) (concat (map text_rec (hl_recs l)))]).
  { apply (lp_cb_eq _ _ _ _ _ _ _ OC); [lia | exact EO]. }
  pose proof (ls_join rsegs m2 res (res + 16 * hl_n l) _ _ OC' JR ltac:(cbn [cells_size csize]; lia)) as ARR2.
  cbn [app] in ARR2.
  assert (ARR3 : rw_cells rsegs m3 res [CB (Z.to_nat (16 * hl_n l)) (concat (map text_rec (hl_recs l)));
                                       CB (Z.to_nat (16 * (G - hl_n l))) junk1]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ ARR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    split; [|exact I].
    pose proof (lp_disj (in_img Bm) LA 16 res (16 * G) ltac:(lia) ltac:(lia)
      (fun i Hi => proj1 (proj1 (LAI (LA + i) ltac:(lia)))) FR_img) as Y. lia. }
  assert (TX3 : Forall (fun r => In (fst r, text_len r) (blocks L2 A2) /\
                   rw_cells rsegs m3 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l)).
  { apply Forall_forall. intros r Ir.
    destruct (proj1 (Forall_forall _ _) TX1 r Ir) as (U1 & U2).
    destruct (proj1 (Forall_forall _ _) TXF0 r Ir) as (_ & (_ & _ & T3) & _).
    assert (NEr : fst r <> hl_v l) by (intro Y; apply NV0; rewrite <- Y; apply in_map; exact Ir).
    destruct (lf_blocks_in L A _ _ U1) as (p & Hp & Ep).
    assert (Hp2 : In (p, text_len r) (user_blocks A2)).
    { apply SV; [exact Hp | unfold text_len; lia | intros (_ & Y); apply NEr; rewrite <- Ep; exact Y]. }
    split.
    - pose proof (lf_blocks_of L2 A2 p _ Hp2) as Y. rewrite (PA2 p _ Hp Hp2), Ep in Y. exact Y.
    - apply (rw_cells_transport rsegs [(LA, LA + 16)] m2 m3 _ _); [| exact MU3 | exact WM3 |].
      + rewrite <- SEG.
        apply (rw_cp_block Bm API REALLOC_STACK L A R1 m1 md _ L2 A2 R2 m2 md2 p (text_len r) (fst r) _ CP Hp Hp2);
          [rewrite Ep; lia | cbn [cells_size csize]; rewrite Ep; unfold text_len; lia | rewrite SEG; exact U2].
      + cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I].
        pose proof (lp_disj (in_img Bm) LA 16 (fst r) (Z.of_nat (length (snd r)) + 1) ltac:(lia) ltac:(lia)
          (fun i Hi => proj1 (proj1 (LAI (LA + i) ltac:(lia)))) T3) as Y. lia. }
  assert (V1T : ~ In res (map fst (hl_recs l))).
  { intro I. apply in_map_iff in I. destruct I as (r & Er & Ir).
    destruct (proj1 (Forall_forall _ _) TX1 r Ir) as (U1 & _).
    assert (NEr : fst r <> hl_v l) by (intro Y; apply NV0; rewrite <- Y; apply in_map; exact Ir).
    pose proof (DJ _ _ (OLD _ _ U1 (or_intror NEr))) as Y. unfold text_len in Y. lia. }
  assert (SRC2 : bytes_at rsegs m2 SRC x).
  { destruct SH as [(H1 & H2) | [(q & kq & Hq & Hqv & H1 & H2) | (H0 & H1 & H2 & H3)]].
    - rewrite <- SEG. apply (ba_cp_frame Bm API REALLOC_STACK L A R1 m1 md _ L2 A2 R2 m2 md2 SRC x CP);
        [|rewrite SEG; exact SRC1].
      intros i Hi. rewrite LX in Hi.
      assert (HA : YM05.alloc_ceiling <= SRC + i < 2 ^ 64) by lia.
      split; [left; exact HA|].
      split; [intro Y; pose proof (owned_low Bm _ LAWS _ _ _ _ _ M1 Y); lia|].
      split; [intro Y; pose proof (owned_low Bm _ LAWS _ _ _ _ _ M2 Y); lia|].
      split; [unfold scratch_k; rewrite SP1; lia | exact (NE1 _ (or_introl HA))].
    - destruct (lf_blocks_in L A q kq Hq) as (pq & Hpq & Epq).
      assert (Hpq2 : In (pq, kq) (user_blocks A2)).
      { destruct (Z.eq_dec kq 0) as [K0|K0]; [subst kq; exact (ZV pq Hpq)|].
        apply SV; [exact Hpq | lia | intros (_ & Y); apply Hqv; rewrite <- Epq; exact Y]. }
      rewrite <- SEG.
      apply (ba_cp_block Bm API REALLOC_STACK L A R1 m1 md _ L2 A2 R2 m2 md2 pq kq SRC x CP Hpq Hpq2);
        [rewrite Epq; lia | rewrite Epq, LX; lia | rewrite SEG; exact SRC1].
    - rewrite <- SEG. apply (ba_ro Bm m1 m2 SRC x);
        [rewrite SEG; exact RO1 | rewrite SEG; exact RO2 | | rewrite SEG; exact SRC1].
      intros i Hi. rewrite LX in Hi. exact (H3 i Hi). }
  assert (SRC3 : bytes_at rsegs m3 SRC x).
  { apply (bytes_at_transport rsegs _ m2 m3 _ _ SRC2 MU3). cbn [disjoint_from]. rewrite LX. split; [lia | exact I]. }
  assert (SH3 : (S <= SRC /\ SRC + n <= 2 ^ 64) \/
    (exists q k, In (q, k) (blocks L2 A2) /\ (q <> res \/ k = 0) /\ q <= SRC /\ SRC + n <= q + k) \/
    (0 < n /\ 0 <= SRC /\ SRC + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr (ms_segs Bm) (Z_to_bv 64 (SRC + i)) = true)).
  { destruct SH as [H|[(q & k & H1 & H2 & H3 & H4)|H]]; [left; exact H | | right; right; exact H].
    right; left. exists q, k. pose proof (OLD q k H1 (or_intror H2)) as Hc.
    split; [exact (NEW _ _ Hc)|]. split; [|split; [exact H3 | exact H4]].
    destruct (Z.eq_dec k 0) as [K0|K0]; [right; exact K0 | left; pose proof (DJ _ _ Hc); lia]. }
  assert (B1 : forall q m, In (q, m) (blocks L2 A2) ->
    (In (q, m) (blocks L A) /\ (0 < m -> ~ (hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l))) \/ q = res).
  { intros q m Hq. rewrite BLK1 in Hq. apply in_app_or in Hq.
    destruct Hq as [Hq|[Hq|Hq]].
    - destruct (BOLD q m (in_or_app _ _ _ (or_introl Hq))) as [Y1 Y2]. left.
      split; [exact Y1 | intros Hm (_ & Y3 & Y4); exact (Y2 Hm Y3 Y4)].
    - injection Hq as Y1 Y2. right. symmetry. exact Y1.
    - destruct (BOLD q m (in_or_app _ _ _ (or_intror Hq))) as [Y1 Y2]. left.
      split; [exact Y1 | intros Hm (_ & Y3 & Y4); exact (Y2 Hm Y3 Y4)]. }
  assert (B2 : forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L2 A2))
    by (intros q m Hq NI; exact (NEW _ _ (OLD q m Hq (NIV q NI)))).
  assert (B3 : forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks l) -> q <> res).
  { intros q m Hq Hm NI Eq. pose proof (DJ _ _ (OLD q m Hq (NIV q NI))). lia. }
  assert (LQ0 : length [qg] = nretF (list_grow_tr (sh_of (known_at L A) l))).
  { rewrite lp_grow_tr, (proj2 (Z.eqb_eq _ _) EQ). destruct (hl_cap l =? 0); reflexivity. }
  exact (lp_tail Bm API Fr AX CTX MALLOC_PC ERRNO_LOW NDB MAL MC L A regs mem md bnd l lines x L2 A2 R3 m3 md2 res G
    j0 junk1 (fun a => (False \/ False) \/ LA <= a < LA + 16)
    (fun q => (False \/ (hl_n l = hl_cap l /\ 0 < hl_cap l /\ q = hl_v l)) \/ False)
    LA SRC n S [qg] SEG PRE ES LAI LIST0 (fun _ => NCAP) NB LX RSRC SLA LT LF MIDf HE HF E3_1 E3_2 E3_4 E3_8 E3_9 E3_10
    E3_18 E3_3 E3_20 E3_21 E3_22 E3_23 E3_24 E3_25 E3_26 E3_27 FR3 LC3 EG INB FRES ARR3 (fun Y => ltac:(lia)) TX3 V1T
    SRC3 SH3 B1 B2 B3 INI2 LQ0 RES2 ROOM (fun _ => ex_intro _ _ (conj Hqg Eqg)) RO3).
Qed.

Lemma lp_grow_entry : malloc_contract_rt Bm API Fr -> realloc_contract_rt Bm API Fr 0x178f8 ->
  realloc_null_contract_rt Bm API Fr 0x178f8 -> memcpy_contract ->
  forall L A regs mem md (bnd : rt_R Fr) (l : hlist) (lines : bool) (x : list byte) (LA SRC n S : Z),
  getr regs 10 = Z_to_bv 64 LA -> getr regs 11 = Z_to_bv 64 SRC -> getr regs 12 = Z_to_bv 64 n -> S = spZ regs ->
  0 <= LA < 2 ^ 64 -> 0 <= SRC < 2 ^ 64 -> 0 <= n ->
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) LIST_PUSH_K L A regs mem md ->
  st_init_done A = true ->
  ro_agree rsegs mem ->
  (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr rsegs (Z_to_bv 64 a) = false) ->
  LA mod 8 = 0 ->
  list_at Bm L A mem LA l lines ->
  hl_n l = hl_cap l -> hl_cap l < 2 ^ 29 ->
  n < 2 ^ 64 - 1 ->
  bytes_at rsegs mem SRC x -> Z.of_nat (length x) = n ->
  src_home Bm L A S SRC n (hl_v l) ->
  (SRC + n <= LA \/ LA + 16 <= SRC) ->
  (lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= 6000) ->
  (lines = false -> 1 <= n) ->
  rt_ok Fr A bnd ->
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF Fr qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_PUSH) mem (seg_rom rsegs)) md)
    (lp_post Bm API Fr L A regs mem md bnd LA (hl_n l) (hl_cap l) (hl_v l) n lines x l).
Proof.
  intros MAL RA RN MC L A regs mem md bnd l lines x LA SRC n S E10 E11 E12 ES RLA RSRC RN0 SEG PRE INIT RO LAI AL8 LIST
    EQ NCAP NB SRCB LX SH SLA LT LF RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL. destruct AC as [AC _].
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HC & H63 & HWS & HTP & HERR & HAUX).
  rewrite <- ES in HAL, HC, H63, HWS.
  unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in HC, HWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  pose proof LIST as LIST0.
  destruct LIST as (LC0 & NB0 & CASE0 & ND0 & NV0 & TXF0).
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (LAR : 0 <= LA /\ LA + 16 <= 2 ^ 21).
  { pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI LA ltac:(lia))))).
    pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI (LA + 15) ltac:(lia))))). lia. }
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (ULA : bv_unsigned (Z_to_bv 64 LA) = LA) by (apply unsigned_lit; lia).
  assert (R2E : reg_get regs 2 = Z_to_bv 64 S) by (rewrite ES; symmetry; exact (Z_to_bv_bv_unsigned (getr regs 2))).
  assert (R10 : reg_get regs 10 = Z_to_bv 64 LA) by exact E10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 SRC) by exact E11.
  assert (R12 : reg_get regs 12 = Z_to_bv 64 n) by exact E12.
  assert (ST : stk rsegs mem (S - 48) S).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as STn.
  rewrite SEG in LC0, TXF0.
  pose proof LC0 as LC0'. rewrite <- EQ in LC0'.
  pose proof (rw_cells_normalize rsegs mem LA _ RO LC0'
                ltac:(intros i Hi; cbn in Hi; exact (proj2 (LAI (LA + i) ltac:(lia))))) as LCn.
  remember (grow_cap (hl_n l) (hl_cap l)) as G eqn:EG.
  assert (EG1 : G = if hl_n l =? 0 then 8 else 2 * hl_n l).
  { rewrite EG. unfold grow_cap. rewrite EQ, Z.eqb_refl. reflexivity. }
  assert (GV : 0 < G <= 2 ^ 30) by (rewrite EG1; destruct (Z.eqb_spec (hl_n l) 0); lia).
  eapply (lift_run regs (Z_to_bv 64 LIST_PUSH) mem md [(S - 48, S)]
    (fun m' => exists j0, rw_cells rsegs m' (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                                                       C8 (getr regs 8); C8 (getr regs 1)])
    (fun R pc' => pc' = Z_to_bv 64 0x178f8 /\ reg_get R 1 = Z_to_bv 64 0x148ac /\ reg_get R 2 = Z_to_bv 64 (S - 48) /\
       reg_get R 3 = getr regs 3 /\ reg_get R 4 = getr regs 4 /\ reg_get R 8 = Z_to_bv 64 LA /\
       reg_get R 9 = Z_to_bv 64 n /\ reg_get R 10 = Z_to_bv 64 (hl_v l) /\ reg_get R 11 = Z_to_bv 64 (16 * G) /\
       reg_get R 18 = Z_to_bv 64 SRC /\ reg_get R 19 = Z_to_bv 64 G /\
       reg_get R 20 = getr regs 20 /\ reg_get R 21 = getr regs 21 /\ reg_get R 22 = getr regs 22 /\
       reg_get R 23 = getr regs 23 /\ reg_get R 24 = getr regs 24 /\ reg_get R 25 = getr regs 25 /\
       reg_get R 26 = getr regs 26 /\ reg_get R 27 = getr regs 27));
    [exact Hh | exact Hl | exact RO | |].
  { unfold Regs6ss.mkR_of. rewrite R2E, R10, R11, R12.
    eapply evt_mono.
    { eapply lpu_run1g with (lo := S - 48) (V := hl_v l) (N := hl_n l) (G := G);
        [rewrite US; exact STn | rewrite US; lia | rewrite ULA; exact LCn | rewrite ULA, US; lia | rewrite ULA; exact AL8
        | lia | exact EG1]. }
    intros ms' (t0 & t1 & t2 & b2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & j0 & -> & MU & WM & FR).
    rewrite US in MU, FR. rewrite US.
    eexists _, _, m'. split; [reflexivity|].
    split; [repeat split|].
    split; [exact MU|]. split; [exact WM | exists j0; exact FR]. }
  intros R R1 pc' m1 m'' (EPC & F_1 & F_2 & F_3 & F_4 & F_8 & F_9 & F_10 & F_11 & F_18 & F_19 & F_20 & F_21 & F_22
    & F_23 & F_24 & F_25 & F_26 & F_27) X MU1 WM1 RO1 REL1 (j0 & FRp).
  subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL1 FRp) as FR1.
  assert (E1_1 : reg_get R1 1 = Z_to_bv 64 0x148ac) by (xr X F_1).
  assert (E1_2 : reg_get R1 2 = Z_to_bv 64 (S - 48)) by (xr X F_2).
  assert (E1_3 : reg_get R1 3 = getr regs 3) by (xr X F_3).
  assert (E1_4 : reg_get R1 4 = getr regs 4) by (xr X F_4).
  assert (E1_8 : reg_get R1 8 = Z_to_bv 64 LA) by (xr X F_8).
  assert (E1_9 : reg_get R1 9 = Z_to_bv 64 n) by (xr X F_9).
  assert (E1_10 : reg_get R1 10 = Z_to_bv 64 (hl_v l)) by (xr X F_10).
  assert (E1_11 : reg_get R1 11 = Z_to_bv 64 (16 * G)) by (xr X F_11).
  assert (E1_18 : reg_get R1 18 = Z_to_bv 64 SRC) by (xr X F_18).
  assert (E1_19 : reg_get R1 19 = Z_to_bv 64 G) by (xr X F_19).
  assert (E1_20 : reg_get R1 20 = getr regs 20) by (xr X F_20).
  assert (E1_21 : reg_get R1 21 = getr regs 21) by (xr X F_21).
  assert (E1_22 : reg_get R1 22 = getr regs 22) by (xr X F_22).
  assert (E1_23 : reg_get R1 23 = getr regs 23) by (xr X F_23).
  assert (E1_24 : reg_get R1 24 = getr regs 24) by (xr X F_24).
  assert (E1_25 : reg_get R1 25 = getr regs 25) by (xr X F_25).
  assert (E1_26 : reg_get R1 26 = getr regs 26) by (xr X F_26).
  assert (E1_27 : reg_get R1 27 = getr regs 27) by (xr X F_27).
  assert (MID1 : lmid Bm API LIST_PUSH_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (lmid_A Bm API SEG AX LIST_PUSH_K S _ L A mem md m1 [(S - 48, S)]);
      [ exact HMR | exact HWF | exact HBD | unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; lia | lia
      | intros a [Ha|Ha];
        [apply HWS; unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in Ha; lia | apply HERR; exact Ha]
      | exact MU1 | rewrite SEG; exact WM1 | | ].
    - intros y Hy O. cbn [outside] in O. left.
      assert (D : S - 48 <= y < S \/ ~ (S - 48 <= y < S)) by lia.
      destruct D as [D|D];
        [unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; lia | exfalso; apply O; split; [exact D | exact I]].
    - intros y Hy _. cbn [outside]. split; [lia | exact I]. }
  assert (LC1 : rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { apply (rw_cells_transport rsegs _ mem m1 _ _ LC0 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (TX1 : Forall (fun r => In (fst r, text_len r) (blocks L A) /\
                   rw_cells rsegs m1 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l)).
  { eapply Forall_impl; [|exact TXF0]. intros r (T1 & _ & T3 & _). split; [exact T1|].
    pose proof (lp_blk L A mem md _ _ HMR T1) as Q.
    apply (rw_cells_transport rsegs _ mem m1 _ _ T3 MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (SRC1 : bytes_at rsegs m1 SRC x).
  { apply (bytes_at_transport rsegs _ mem m1 _ _ SRCB MU1). cbn [disjoint_from]. rewrite LX. split; [|exact I].
    destruct SH as [(H1 & H2) | [(q & k & Hq & Hqv & H1 & H2) | (H0 & H1 & H2 & H3)]].
    - right. lia.
    - left. pose proof (lp_blk L A mem md q k HMR Hq). lia.
    - left. rewrite SEG in H3.
      pose proof (ro_in_img Bm SEG (SRC + (n - 1)) ltac:(lia) (H3 (n - 1) ltac:(lia))) as Y.
      pose proof (lf_img_low Bm SEG _ Y). lia. }
  assert (SP1 : spZ R1 = S - 48).
  { unfold spZ. change (getr R1 2) with (reg_get R1 2). rewrite E1_2. apply unsigned_lit. lia. }
  assert (PRE1 : call_pre_k Bm (aa_MR API) REALLOC_STACK L A R1 m1 md).
  { apply (lmid_pre Bm API LIST_PUSH_K S _ _ L A regs mem md L A m1 md REALLOC_STACK 48 R1 PRE ES MID1 INIT SP1);
      [ rewrite SP1; replace (S - 48) with (S + (-3) * 16) by ring; rewrite Z.mod_add by lia; exact HAL
      | exact E1_4
      | replace (getr R1 1) with (Z_to_bv 64 0x148ac) by (symmetry; exact E1_1); apply ret_ok_even; vm_compute;
        reflexivity
      | lia
      | unfold LIST_PUSH_K, LIST_PUSH_FRAME; lia ]. }
  destruct (Z.eq_dec (hl_cap l) 0) as [C0|CP].
  - assert (V0 : hl_v l = 0) by (destruct CASE0 as [(_ & V0)|(CP & _)]; [exact V0 | lia]).
    assert (G8 : G = 8) by (rewrite EG1, EQ, C0; reflexivity).
    assert (ROOM0 : rt_room Fr bnd 128).
    { pose proof (lp_room_grow Fr L A l x bnd ROOM EQ) as R0. rewrite (proj2 (Z.eqb_eq _ _) C0) in R0. exact R0. }
    assert (EO : [] = concat (map text_rec (hl_recs l))).
    { destruct (hl_recs l) eqn:Er; [reflexivity|]. unfold hl_n in EQ. rewrite Er in EQ. cbn [length] in EQ. lia. }
    eapply SR_bind.
    { exact (lp_rl_rn RN SEG L A R1 m1 md bnd (hl_n l) (hl_cap l) (hl_v l) G PRE1 RO1 C0 V0 EQ E1_10 E1_11 G8 RES
               ROOM0). }
    intros cf RL.
    assert (GT : list_grow_tr (sh_of (known_at L A) l) = [RMalloc 128])
      by (rewrite lp_grow_tr, (proj2 (Z.eqb_eq _ _) EQ), (proj2 (Z.eqb_eq _ _) C0); reflexivity).
    rewrite <- GT in RL.
    exact (lp_after MAL MC L A regs mem md bnd l lines x LA SRC n S R1 m1 j0 G [] cf ES RSRC RN0 SEG PRE LAI LIST0 EQ
      NCAP NB LX SLA LT LF MID1 E1_1 E1_2 E1_3 E1_4 E1_8 E1_9 E1_18 E1_19 E1_20 E1_21 E1_22 E1_23 E1_24 E1_25 E1_26
      E1_27 FR1 LC1 EG EO TX1 SRC1 SH RO1 ROOM RL).
  - destruct CASE0 as [(C0 & _)|(_ & INV & FV & LJ & ARR)]; [lia|].
    assert (G2 : G = 2 * hl_cap l).
    { rewrite EG1. destruct (Z.eqb_spec (hl_n l) 0); lia. }
    assert (JN : hl_junk l = []) by (apply length_zero_iff_nil; lia).
    assert (LOLD : Z.of_nat (length (concat (map text_rec (hl_recs l)))) = 16 * hl_cap l)
      by (rewrite lp_concat_len; unfold hl_n in EQ; lia).
    rewrite SEG in ARR. destruct ARR as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite JN, !app_nil_r in HB.
    assert (OB1 : bytes_at rsegs m1 (hl_v l) (concat (map text_rec (hl_recs l)))).
    { apply (bytes_at_transport rsegs _ mem m1 _ _ HB MU1). cbn [disjoint_from]. split; [|exact I].
      pose proof (lp_blk L A mem md _ _ HMR INV). rewrite LOLD. lia. }
    assert (ROOM0 : rt_room Fr bnd (32 * hl_cap l)).
    { pose proof (lp_room_grow Fr L A l x bnd ROOM EQ) as R0. rewrite (proj2 (Z.eqb_neq _ _) CP) in R0. exact R0. }
    assert (CP' : 0 < hl_cap l) by lia.
    eapply SR_bind.
    { exact (lp_rl_ra RA SEG L A R1 m1 md bnd (hl_n l) (hl_cap l) (hl_v l) G (concat (map text_rec (hl_recs l)))
               PRE1 RO1 CP' INV E1_10 E1_11 G2 EQ OB1 LOLD RES ROOM0). }
    intros cf RL.
    assert (GT : list_grow_tr (sh_of (known_at L A) l) =
                 [RRealloc (16 * hl_cap l) (32 * hl_cap l) (Known (sptr_of L A (hl_v l)))])
      by (rewrite lp_grow_tr, (proj2 (Z.eqb_eq _ _) EQ), (proj2 (Z.eqb_neq _ _) CP); reflexivity).
    rewrite <- GT in RL.
    exact (lp_after MAL MC L A regs mem md bnd l lines x LA SRC n S R1 m1 j0 G _ cf ES RSRC RN0 SEG PRE LAI LIST0 EQ
      NCAP NB LX SLA LT LF MID1 E1_1 E1_2 E1_3 E1_4 E1_8 E1_9 E1_18 E1_19 E1_20 E1_21 E1_22 E1_23 E1_24 E1_25 E1_26
      E1_27 FR1 LC1 EG eq_refl TX1 SRC1 SH RO1 ROOM RL).
Qed.

Theorem list_push_holds : malloc_contract_rt Bm API Fr -> realloc_contract_rt Bm API Fr 0x178f8 ->
  realloc_null_contract_rt Bm API Fr 0x178f8 -> memcpy_contract -> list_push_contract Bm API Fr.
Proof.
  intros MAL RA RN MC. unfold list_push_contract.
  intros L A regs mem md bnd l lines x. cbv zeta.
  intros SEG PRE INIT RO LAI AL8 LIST NCAP NB SRCB LX SH SLA LT LF RES ROOM.
  assert (GS : forall P, SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_PUSH) mem (seg_rom rsegs)) md) P ->
                 SR (ms_segs Bm) (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_PUSH) mem (seg_rom (ms_segs Bm))) md) P)
    by (rewrite SEG; intros P H; exact H).
  apply GS.
  rewrite SEG in RO, LAI, SRCB.
  pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Q10. change (bv_modulus 64) with (2 ^ 64) in Q10.
  pose proof (bv_unsigned_in_range 64 (getr regs 11)) as Q11. change (bv_modulus 64) with (2 ^ 64) in Q11.
  pose proof (bv_unsigned_in_range 64 (getr regs 12)) as Q12. change (bv_modulus 64) with (2 ^ 64) in Q12.
  assert (NC : hl_n l <= hl_cap l) by (destruct LIST as (_ & NB0 & _); lia).
  destruct (Z_lt_ge_dec (hl_n l) (hl_cap l)) as [LTC|GEC].
  - exact (lp_direct MAL MC L A regs mem md bnd l lines x (bv_unsigned (getr regs 10)) (bv_unsigned (getr regs 11))
      (bv_unsigned (getr regs 12)) (spZ regs) (eq_sym (Z_to_bv_bv_unsigned _)) (eq_sym (Z_to_bv_bv_unsigned _))
      (eq_sym (Z_to_bv_bv_unsigned _)) eq_refl Q10 Q11 (proj1 Q12) SEG PRE INIT RO LAI AL8 LIST LTC NB SRCB LX SH SLA LT
      LF RES ROOM).
  - assert (EQ : hl_n l = hl_cap l) by lia.
    exact (lp_grow_entry MAL RA RN MC L A regs mem md bnd l lines x (bv_unsigned (getr regs 10))
      (bv_unsigned (getr regs 11)) (bv_unsigned (getr regs 12)) (spZ regs) (eq_sym (Z_to_bv_bv_unsigned _))
      (eq_sym (Z_to_bv_bv_unsigned _)) (eq_sym (Z_to_bv_bv_unsigned _)) eq_refl Q10 Q11 (proj1 Q12) SEG PRE INIT RO
      LAI AL8 LIST EQ (NCAP EQ) NB SRCB LX SH SLA LT LF RES ROOM).
Qed.

End LPH.
