(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_quar_P AQuarT F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace AQuarU.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition free_icpt_entry : Z := 0x58614.
Definition FICPT_STACK : Z := 4096.

Definition trace_env (m : mem) : Prop :=
  rw_cells asegs m 0xb523c [C4 (wz 30)] /\ rw_cells asegs m 0xaad20 [C8 (wz 0x146068)] /\ rw_cells asegs m 0x14608a [C1 (Z_to_bv 8 1)].

Lemma skipn_repeat_firstn : forall {T} (x : T) (N k n : nat), (k + n <= N)%nat -> firstn n (skipn k (repeat x N)) = repeat x n.
Proof.
  intros T x N k n H. apply nth_ext with (d := x) (d' := x).
  - rewrite firstn_length, skipn_length, !repeat_length. lia.
  - intros i Hi. rewrite firstn_length, skipn_length, repeat_length in Hi.
    rewrite nth_firstn. destruct (i <? n)%nat eqn:E; [| apply Nat.ltb_ge in E; lia].
    rewrite nth_skipn. rewrite !nth_repeat. reflexivity.
Qed.

Lemma rd64_of_C8 : forall (m : mem) A (w : word), rw_cells asegs m A [C8 w] -> rd64 m A (bv_unsigned w).
Proof.
  intros m A w [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. split.
  - rewrite MState.Z_to_bv_bv_unsigned. exact BY.
  - pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2^64) in R. exact R.
Qed.

Section FICPT.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation D := (al_depot AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
  Hypothesis AO : alayout_ok AL.
  Variables (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - FICPT_STACK.
  Hypothesis QTOP : q + 16 < at_top L.
  Hypothesis Q16 : q mod 16 = 0.

  Variables NM2 NM4 : Z.
  Hypothesis HNM2 : NM2 = 262144.
  Hypothesis HNM4 : NM4 = 262728.

  Definition free_tr (ra : word) (ras : list Z) : list Z := PC0_FREE :: bv_unsigned ra :: ras.

  Definition ftouch (X : pstate) (glob loc : list qbatch) (ch : qchunk) (iv : Z * Z) : Prop :=
    atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) iv
    \/ put_nb_iv AL (fst X) loc iv \/ dstat iv \/ dreg AL iv \/ iastat iv \/ iv = (THR + 3168, THR + 3169).

  Definition ficpt_post (ra s0 s1 s2 s3 s4 s5 : word) (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk)
      (hrest : list (Z * Z)) (hs : list Z) (total : Z) (tr : list Z) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W hs' total',
      let P := fst X in let X1 := (fst (enq_prim P loc), snd X) in
      let todo := put_todo P glob loc ch in let gF := put_glob P glob loc ch in let lF := put_loc P loc ch in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X1 todo (H_enq AL P loc H)
      /\ munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) m m'
      /\ Forall (ftouch X glob loc ch) W
      /\ dr_inv AL E (dorecycle X1 todo) H' m' (gF ++ lF) (flat_map qb_chunks (gF ++ lF)) hrest
      /\ xle X (dorecycle X1 todo)
      /\ stk asegs m' lo q
      /\ qlist_rep AL m' gF 0 /\ rw_cells asegs m' QUAR_GQ (qcells AL gF) /\ qcache_rep AL m' TQ lF
      /\ rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]]
      /\ (need_batch loc = true -> 0 <= snd (enq_prim P loc) /\ 16 * snd (enq_prim P loc) + Q_BBYTES <= FA_OFF)
      /\ (need_batch loc = true -> held_ok (fst (enq_prim P loc)) ((K_BCLASS, snd (enq_prim P loc)) :: prim_of ch ++ hrest)
                                   /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim P loc)) c)))
      /\ RDEPOT D hs' total' m' /\ ia_cells NM2 NM4 true m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)).

  #[using="AO q LOH CLO"] Lemma ficpt_img_dj : forall (q' : Z) (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W A k,
    RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
    (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
    Forall (fun iv => atouch AL lo q' (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) iv
                      \/ put_nb_iv AL (fst X) loc iv \/ dstat iv \/ dreg AL iv) W ->
    QUAR_GQ + 32 <= A -> A + k <= 1598472 ->
    disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) A k.
  Proof.
    intros q' X m glob loc ch W A k RP RS TCH TSI VNG FW HA HK.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    cbn [disjoint_from]. split; [clear - HA; lia|]. split; [clear - HA; lia|]. split; [clear - HA HK T3; lia|].
    induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
    destruct HIV as [AT|[[NB CI]|[DS|DR]]].
    - pose proof (atouch_img_dj AL X m lo q' [(a, b)] _ _ A k AO LOH CLO RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) ltac:(clear - HA; lia) ltac:(clear - HK; lia)) as DD.
      cbn [disjoint_from] in DD. exact (proj1 DD).
    - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
      assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity. change Q_BBYTES with 8192 in V1.
      destruct CI as [CI|CI]; unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI.
      + clear - CI V0 V1 RN1 RN2 RG SP1 HK. lia.
      + assert (BBR : 0 <= region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc)) by (clear - V0 RN1 RG SP1; lia).
        change (8192 / 8) with 1024 in CI. unfold sh, SHADOW_OFF in CI. clear - CI BBR HK. Z.div_mod_to_equations. lia.
    - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HK. lia.
    - unfold dreg in DR. cbn [fst snd] in DR. clear - DR HK N1d S1d. lia.
  Qed.

  #[using="AO LOH CLO LOQ QTOP Q16 HNM2 HNM4"] Theorem free_icpt_spec : forall (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z))
        (total : Z) (hs : list Z) (ras : list Z) (inited : bool),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) (prim_of ch ++ hrest) ->
    held_kind X ch -> qchunk_wf ch -> lchunk_rep AL m ch ->
    (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of (flat_map qb_chunks (glob ++ loc)))) ->
    qlist_rep AL m glob 0 -> rw_cells asegs m QUAR_GQ (qcells AL glob) -> qcache_rep AL m TQ loc ->
    rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] ->
    rw_cells asegs m QUAR_CONST [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)] -> rw_cells asegs m AF_MAXFILL [C4 (wz 0)] ->
    Forall qbatch_wf (glob ++ loc) -> qbytes (glob ++ loc) + Q_MAX + Q_BBYTES < 2^56 ->
    refill_budget K_BCLASS (get_cls (fst X) K_BCLASS) -> 0 <= pr_calloc (fst X) -> 0 <= pr_cmapped (fst X) -> pr_cmapped (fst X) + K_REGION < 2^63 ->
    Z.of_nat (length loc) < 2^32 ->
    thread_env2 AL m -> hooks_env m -> trace_env m -> ia_cells NM2 NM4 inited m -> RDEPOT D hs total m ->

    fpchain m (at_top L) q (bv_unsigned s0) ras -> (length ras <= 28)%nat -> Forall (fun r => r <> PC0_FREE) ras ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> PC0_FREE ->
    Forall (fun x => 0 <= x < 2^64) ras ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length (free_tr ra ras)) + 1) <= SWIN D -> total + Z.of_nat (length (free_tr ra ras)) + 1 < 2^20 ->
    implA H (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (ficpt_post ra s0 s1 s2 s3 s4 s5 X H m glob loc ch hrest hs total (free_tr ra ras))
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz free_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 X H m glob loc ch hrest total hs ras inited
      MC ST INV HK WFC LREP NSC QLG GC QCL MTX CST AFM FWF QB RB CA0 CM0 CM1 LEN32
      TE2 HKE TRE IA RD CH LRAS NPC RA4 RANE RNG ROOM_N ROOM_F ROOM_T.
    unfold free_icpt_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (PS : 272 <= PUT_STACK) by (vm_compute; discriminate).
    assert (LQ1 : lo <= q - 2128 - 512) by (unfold FICPT_STACK in LOQ; clear - LOQ; lia).
    assert (LQ2 : lo <= q - 2128 - DEALLOC_STACK) by (unfold FICPT_STACK in LOQ; assert (PS2 : DEALLOC_STACK = 1824) by (vm_compute; reflexivity); clear - LOQ PS2; lia).
    assert (LQ3 : alloc_ceiling + 4096 <= q) by (unfold FICPT_STACK in LOQ; clear - LOQ CLO; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    set (B := qc_blk AL ch) in *. set (rz := qc_rz ch) in *. set (bs := qc_bsize ch) in *. set (n := qc_n ch) in *.
    assert (EM : qc_hdr AL ch = B + rz - 16) by reflexivity.
    set (M := qc_hdr AL ch) in *.
    assert (RU0 : 0 <= rup8 n /\ rup8 n mod 8 = 0 /\ n <= rup8 n) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    unfold qcells in GC. hide GC. destruct QCL as [TQC QLL]. hide TQC. hide MTX. hide CST. hide AFM.
    pose proof (munch_refl [(q - 2128, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep.
    zstep. carve_frame 2128%nat ST.

    do 7 zstep.
    zstep.
    zstep.
    do 2 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -2128) with (q - 2128) in * by lia.
    assert (DJA : forall A k, A + k <= lo -> disjoint_from [(q - 2128, q)] A k) by (intros A k D1; cbn [disjoint_from]; clear - D1 LQ1; lia).
    assert (IAA : ia_cells NM2 NM4 inited mA).
    { destruct IA as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [eapply rw_cells_transport; [exact FL| exact MU| exact WM| apply DJA; unfold ia_flag; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j0; eapply rw_cells_transport; [exact C0| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j2; split; [| exact Z2]; eapply rw_cells_transport; [exact C2| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - LOH HNM2; lia]|].
      split; [exists j3; eapply rw_cells_transport; [exact C3| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]|].
      split; [exists j4; eapply rw_cells_transport; [exact C4'| exact MU| exact WM| apply DJA; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - LOH HNM4; lia]|].
      exists j1; eapply rw_cells_transport; [exact C1'| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia]. }
    pose proof TE as TEc. te_split TEc.
    eapply (rw_cells_transport asegs _ m mA) in TE_gotpg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ m mA) in TE_pg; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply evt_cut.
    { eapply (ialloc_spec NM2 NM4 HNM2 HNM4 _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 2128) mA lo inited).
      - exact ST.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact IAA.
      - exact TE_gotpg.
      - exact TE_pg.
      - assumption. }
    cbv beta. unfold ialloc_post. intros msI (i1 & i2 & i3 & i4 & i5 & i6 & mI & -> & MUi & WMi & MII & IAI & GPI & PGI & STI).

    replace (ret_pc (Z_to_bv 64 362068)) with (Z_to_bv 64 362068) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (AR : 6328320 <= M + 16 /\ M + 16 < 2^47) by (rewrite EM; clear - GLO GHI RZ16 RZN RU0 ACR; lia).
    zstep.
    replace (Z.shiftr (M + 16) 47) with 0 by (symmetry; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; clear - AR; lia).
    zstep. lit_branch.
    do 3 zstep.
    set (i32 := Z.shiftr (M + 16) 32) in *.
    assert (I32 : 0 <= i32 < 32768) by (unfold i32; rewrite Z.shiftr_div_pow2 by lia; clear - AR; change (2^32) with 4294967296; change (2^47) with 140737488355328 in AR; Z.div_mod_to_equations; lia).
    assert (HRD : ov_read_bytes asegs mI (wa (743240 + 8 * i32)) 8 = Some (le8 (wz 0))).
    { destruct IAI as (_ & _ & (j2 & C2 & Z2) & _). specialize (Z2 eq_refl). subst j2. destruct C2 as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      pose proof (bytes_at_read asegs mI 743240 _ (8 * i32) 8 BY ltac:(clear - I32; lia)
                    ltac:(unfold zeros; rewrite repeat_length; clear - I32 HNM2; lia)) as R.
      rewrite R. f_equal. unfold zeros. rewrite skipn_repeat_firstn by (clear - I32 HNM2; lia). reflexivity. }
    replace (743232 + Z.shiftl i32 3) with (743240 + 8 * i32 + -8) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; clear; lia).
    zstep.

    zstep.
    zstep. lit_branch.

    assert (DJI : forall A k, (q - 2128 <= A \/ A + k <= 741952 \/ (1327052 <= A /\ A + k <= lo)) -> disjoint_from [(q - 2128 - 48, q - 2128); (1327048, 1327048 + 4); (743232, 743232 + 8 + NM2); (1005440, 1271624 + 40)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 HNM2 LOH LQ1; lia).
    eapply (rw_cells_transport asegs _ mA mI) in FR; [| exact MUi| exact WMi| apply DJI; left; clear; lia].
    destruct TRE as (TR1 & TR2 & TR3).
    eapply (rw_cells_transport asegs _ m mA) in TR1; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR1; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mA) in TR2; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR2; [| exact MUi| exact WMi| apply DJI; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ m mA) in TR3; [| exact MU| exact WM| apply DJA; cbn [cells_size csize Nat.add]; clear - LOH; lia].
    eapply (rw_cells_transport asegs _ mA mI) in TR3; [| exact MUi| exact WMi| apply DJI; right; right; cbn [cells_size csize Nat.add]; clear - LOH; lia].

    lazymatch type of FR with rw_cells _ _ _ (CB 2072 ?jj :: ?post) =>
      apply (rw_cells_split_CB asegs mI (q - 2128) [] 2072 jj post [8; 8; 240; 1800; 8; 8]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j1; CB 8 ?j2; CB 240 ?j3; CB 1800 ?j4; CB 8 ?j5; CB 8 ?j6; _; _; _; _; _; _; _] =>
      remember j1 as f1 eqn:Ef1; remember j2 as f2 eqn:Ef2; remember j3 as f3 eqn:Ef3; remember j4 as f4 eqn:Ef4; remember j5 as f5 eqn:Ef5; remember j6 as f6 eqn:Ef6 end.
    clear Ef1 Ef2 Ef3 Ef4 Ef5 Ef6.
    hide MU. hide WM. hide MUi. hide WMi.
    pose proof (munch_refl [(q - 2128, q)] mI) as MUf. pose proof (wmono_refl asegs mI) as WMf.
    do 5 zstep.

    replace (q + -81) with (q - 2128 + 2047) by (clear; lia). replace (q + -2128) with (q - 2128 + 0) by (clear; lia). replace (q + -2112) with (q - 2128 + 16) by (clear; lia).
    sstep.
    zstep.
    sstep.

    zstep.
    do 2 zstep.
    do 2 zstep.
    change (sx32 (Z_to_bv 64 30)) with (Z_to_bv 64 30).
    zstep.
    zstep. lit_branch.
    zstep.
    do 2 zstep.
    do 2 zstep.
    zstep.
    zstep.
    zstep.
    do 2 zstep. do 2 zstep.
    change (sx32 (Z_to_bv 64 30)) with (Z_to_bv 64 30).
    do 4 zstep.
    change (Z.b2z (30 <? 1) + -1) with (-1). change (-1 mod 18446744073709551616) with 18446744073709551615.
    replace (Z.land 18446744073709551615 q) with q
      by (symmetry; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; clear - QH ACR CLO LQ1; lia).
    zstep.
    zstep.
    zstep. lit_branch.
    do 2 zstep.
    do 4 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mU end.
    unhide MU. unhide WM. unhide MUi. unhide WMi.
    assert (TEU : thread_env L mU).
    { assert (TEA : thread_env L mA).
      { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
      assert (TEI : thread_env L mI).
      { eapply thread_env_frame_q; [exact TEA| exact MUi| exact WMi|]. unfold thread_clear_q, img_out_q, iastat.
        repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [| clear - LOH LQ1 CLO T1 T2 T3 T4 HNM2; lia]).
        - right; left. clear - LOH LQ1. lia.
        - right; right; right; right; right. clear. lia.
        - right; right; right; right; left. clear - HNM2. lia.
        - right; right; right; right; left. clear. lia. }
      eapply thread_env_frame; [exact TEI| exact MUf| exact WMf|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }

    destruct (proj1 (rw_cells_app asegs mU (q - 2128) [C8 (wz (q - 2128 + 16))] _) FR) as [F0 FRa]. cbn [cells_size csize Nat.add] in FRa. replace (q - 2128 + Z.of_nat 8) with (q - 2128 + 8) in FRa by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 8) [C8 (wz 0)] _) FRa) as [F8 FRb]. cbn [cells_size csize Nat.add] in FRb. replace (q - 2128 + 8 + Z.of_nat 8) with (q - 2128 + 16) in FRb by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 16) [CB 240 f3] _) FRb) as [F16 FRc]. cbn [cells_size csize Nat.add] in FRc. replace (q - 2128 + 16 + Z.of_nat 240) with (q - 2128 + 256) in FRc by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 256) [CB 1800 f4] _) FRc) as [F256 FRd]. cbn [cells_size csize Nat.add] in FRd. replace (q - 2128 + 256 + Z.of_nat 1800) with (q - 2128 + 2056) in FRd by (clear; lia).
    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 2056) [C8 (wz q)] _) FRd) as [F2056 FRe]. cbn [cells_size csize Nat.add] in FRe. replace (q - 2128 + 2056 + Z.of_nat 8) with (q - 64) in FRe by (clear; lia).
    clear FR FRa FRb FRc FRd.
    apply (rw_cells_C8_C4C4 mU (q - 2128 + 8) [] 0 [] ltac:(lia)) in F8. cbn [app] in F8.
    destruct (u64arr_of_CB mU (q - 2128 + 16) 30 f3 F16) as (ws & LWS & BUF).

    destruct (rw_cells_take3 asegs mU (q - 64) [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0] [C8 ra] FRe) as (_ & GS0 & GRA).
    cbn [cells_size csize Nat.add] in GS0, GRA. replace (q - 64 + Z.of_nat 48) with (q - 16) in GS0, GRA by (clear; lia). replace (q - 16 + Z.of_nat 8) with (q - 8) in GRA by (clear; lia).
    pose proof (rd64_of_C8 mU (q - 8) ra GRA) as RDRA. pose proof (rd64_of_C8 mU (q - 16) s0 GS0) as RDS0.

    assert (CHU : fpchain mU (at_top L) q (bv_unsigned s0) ras).
    { eapply fpchain_frame; [| exact MUf| exact WMf| constructor; [cbn [fst snd]; clear; lia| constructor]].
      eapply fpchain_frame; [| exact MUi| exact WMi| repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LOH LQ1 HNM2; lia].
      eapply fpchain_frame; [exact CH| exact MU| exact WM| constructor; [cbn [fst snd]; clear; lia| constructor]]. }
    replace (q + -2128) with (q - 2128) by (clear; lia).
    eapply evt_cut.
    { eapply (ui_entry L _ gp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ _ F_ fc (q - 2128) (q - 2128) 362328 mU
                ltac:(clear - QTOP; lia) ltac:(clear; lia) TLO lo q (bv_unsigned ra) (bv_unsigned s0) ras ws (wz 0) (wz 0) (wz q)).
      - exact STI.
      - exact CLO.
      - clear - LQ1; lia.
      - exact LQ3.
      - exact TEU.
      - exact F8.
      - exact BUF.
      - exact LWS.
      - exact F2056.
      - clear; lia.
      - clear - QTOP; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear; lia.
      - exact RDRA.
      - exact RA4.
      - exact RANE.
      - exact RDS0.
      - exact CHU.
      - exact NPC.
      - exact LRAS.
      - exact MII. }
    cbv beta. unfold ui_post.
    intros msW (w0 & w1 & w2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & mW & ws' & tgw & -> & MUw & WMw & MIW & STW & TEW & SZW & BUFW & LWS' & TRW & TFW).

    replace (ret_pc (Z_to_bv 64 362420)) with (Z_to_bv 64 362420) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    destruct (proj1 (rw_cells_app asegs mU (q - 2128 + 8) [C4 (wz 0)] [C4 (wz 0)]) F8) as [_ TAG].
    cbn [cells_size csize Nat.add] in TAG. replace (q - 2128 + 8 + Z.of_nat 4) with (q - 2128 + 12) in TAG by (clear; lia).
    assert (DJW : forall A k, ((q - 2128 <= A /\ A + k <= q - 2128 + 8) \/ (q - 2128 + 12 <= A /\ A + k <= q - 2128 + 16) \/ (q - 2128 + 256 <= A /\ A + k <= q - 2128 + 2056) \/ q - 2128 + 2064 <= A) ->
              disjoint_from [(lo, q - 2128); (q - 2128 + 8, q - 2128 + 12); (q - 2128 + 16, q - 2128 + 256); (q - 2128 + 2056, q - 2128 + 2064); (THR + 3168, THR + 3169)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1 T4 CLO LQ1; lia).
    eapply (rw_cells_transport asegs _ mU mW) in F0; [| exact MUw| exact WMw| apply DJW; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in TAG; [| exact MUw| exact WMw| apply DJW; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in F256; [| exact MUw| exact WMw| apply DJW; right; right; left; cbn [cells_size csize Nat.add]; clear; lia].
    eapply (rw_cells_transport asegs _ mU mW) in FRe; [| exact MUw| exact WMw| apply DJW; right; right; right; clear; lia].
    set (tr := free_tr ra ras).
    assert (ETR : [362328; bv_unsigned ra] ++ ras = tr) by reflexivity. rewrite ETR in SZW, TRW.
    destruct (proj1 (rw_cells_app asegs mW (q - 2128 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 tgw]) SZW) as [SZ1 _].
    assert (TAG' : rw_cells asegs mW (q - 2128 + 8 + Z.of_nat (cells_size [C4 (wz (Z.of_nat (length tr)))])) [C4 (wz 0)]).
    { cbn [cells_size csize Nat.add]. replace (q - 2128 + 8 + Z.of_nat 4) with (q - 2128 + 12) by (clear; lia). exact TAG. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2128 + 8) [C4 (wz (Z.of_nat (length tr)))] [C4 (wz 0)]) (conj SZ1 TAG')) as SZ8.
    cbn [app] in SZ8.
    assert (LTR : (1 <= length tr <= 30)%nat) by (unfold tr, free_tr; cbn [length]; clear - LRAS; lia).
    apply (rw_cells_C4C4_C8 mW (q - 2128 + 8) [] (Z.of_nat (length tr)) [] ltac:(clear - LTR; lia)) in SZ8. cbn [app] in SZ8.
    assert (SZ8' : rw_cells asegs mW (q - 2128 + Z.of_nat (cells_size [C8 (wz (q - 2128 + 16))])) [C8 (wz (Z.of_nat (length tr)))]).
    { cbn [cells_size csize Nat.add]. replace (q - 2128 + Z.of_nat 8) with (q - 2128 + 8) by (clear; lia). exact SZ8. }
    pose proof (proj2 (rw_cells_app asegs mW (q - 2128) [C8 (wz (q - 2128 + 16))] [C8 (wz (Z.of_nat (length tr)))]) (conj F0 SZ8')) as SOBJ.
    cbn [app] in SOBJ.

    set (Wtot := [(lo, q); (1327048, 1327048 + 4); (743232, 743232 + 8 + NM2); (1005440, 1271624 + 40); (THR + 3168, THR + 3169)]).
    assert (MUT : munch Wtot m mW).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_trans; [eapply munch_weaken; [| exact MUi]| eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]]];
        unfold Wtot, sub_fp; cbn [outside]; intros xo (O1 & O2 & O3 & O4 & O5 & _); repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
    pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMi (wmono_trans asegs _ _ _ WMf WMw))) as WMT.
    assert (FZ : Forall (izone AL lo) Wtot).
    { unfold Wtot, izone, iastat. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd].
      - left. clear. lia.
      - right; left; right. clear. lia.
      - right; left; left. clear - HNM2. lia.
      - right; left; left. clear. lia.
      - right; right. reflexivity. }
    pose proof (dr_inv_frame_i AL E X H m mW _ _ _ lo Wtot AO LOH CLO INV MUT WMT MIW TEW FZ) as INVW.
    pose proof (lchunk_rep_hull AL X Wtot m mW ch AO RP RS HK LREP WFC MUT (fun A0 n0 HU => hull_izone_dj AL X m lo Wtot ch A0 n0 AO LOH CLO RP RS HK FZ HU)) as LREPW.
    assert (HBP : forall b, In b (glob ++ loc) -> held1 (fst X) (bpair b)).
    { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
    assert (QLGW : qlist_rep AL mW glob 0).
    { eapply (qlist_rep_frame_i AL X m mW lo Wtot glob 0 AO LOH CLO RP RS FZ MUT QLG). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. left. exact Hb. }
    assert (QLLW : qlist_rep AL mW loc 0).
    { eapply (qlist_rep_frame_i AL X m mW lo Wtot loc 0 AO LOH CLO RP RS FZ MUT QLL). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. right. exact Hb. }
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
    assert (DJT : forall A k, A + k <= lo -> (A + k <= 743232 \/ (1271664 <= A /\ (A + k <= 1327048 \/ 1327052 <= A))) -> (A + k <= THR + 3168 \/ THR + 3169 <= A) -> disjoint_from Wtot A k)
      by (intros A k D1 D2 D3; unfold Wtot; cbn [disjoint_from]; clear - D1 D2 D3 HNM2; lia).
    unhide GC. unhide TQC. unhide MTX. unhide CST. unhide AFM.
    eapply (rw_cells_transport asegs _ m mW) in GC; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia].
    eapply (rw_cells_transport asegs _ m mW) in MTX; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia].
    eapply (rw_cells_transport asegs _ m mW) in CST; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia].
    eapply (rw_cells_transport asegs _ m mW) in AFM; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia].
    eapply (rw_cells_transport asegs _ m mW) in TQC; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH CLO T3 T4; lia].
    assert (TE2W : thread_env2 AL mW).
    { eapply (thread_env2_frame_m AL Wtot m mW TE2 MUT); apply DJT; clear - LOH CLO T1 T2 T3 T4 T5; lia. }
    assert (HKW : hooks_env mW).
    { unfold hooks_env in *. eapply rw_cells_transport; [exact HKE| exact MUT| exact WMT|]. cbn [cells_size csize Nat.add]. apply DJT; clear - LOH T3; lia. }
    assert (RDW : RDEPOT D hs total mW).
    { eapply (RDEPOT_frame_m AL hs total Wtot m mW DLO SWB RD MUT); apply DJT; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia. }

    do 2 zstep.
    replace (q + -2128) with (q - 2128) by (clear; lia).
    do 2 zstep.
    zstep.
    lz_here.

    rewrite <- (ebind_ret_r (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (dealloc_spec AL E AO gp s10 s11 F_ fc (q - 2128) lo LOH CLO LQ2 ltac:(clear - QH; lia) ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X H mW glob loc ch hrest (q - 2128) (q - 2128 + 16) total hs ws' tr);
        [ assumption | exact STW | exact INVW | exact HK | exact WFC | exact LREPW | exact NSC | exact QLGW | unfold qcells; exact GC | split; [exact TQC| exact QLLW]
        | exact MTX | exact CST | exact AFM | exact FWF | exact QB | exact RB | exact CA0 | exact CM0 | exact CM1 | exact LEN32
        | exact TE2W | exact HKW | exact RDW | exact SOBJ | clear; lia | clear - QH; lia | exact BUFW | exact TRW | rewrite LWS'; clear - LTR; lia | exact LTR
        | unfold tr, free_tr; constructor; [clear; lia| constructor; [pose proof (bv_unsigned_in_range 64 ra) as RR; change (bv_modulus 64) with (2^64) in RR; exact RR| exact RNG]]
        | clear; lia | rewrite LWS'; clear - QH; lia | exact ROOM_N | exact ROOM_F | exact ROOM_T ]. }
    intros u2' H2 ms2 [PO MC2]. unfold qchunk_post in PO. cbv zeta in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & W2 & hs' & total' & -> & -> & MU2 & FW2 & INV2 & XL2 & ST2 & QL2 & GC2 & QC2 & MTX2 & VNG & NBX & RD2 & RES2).
    clean_ms_mem MC2.

    pose proof INVW as (RPW & _ & RSW & _).
    assert (TCHall : Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch)).
    { destruct HOK as [_ FH]. unfold tc_of. rewrite <- app_assoc. rewrite !app_assoc in FH. apply Forall_app in FH as [FH _]. rewrite <- !app_assoc in FH. exact FH. }
    assert (TSIall : incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X))).
    { destruct (dr_inv_tc AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) [] (prim_of ch ++ hrest) ltac:(rewrite app_nil_r; exact INV)) as [_ TSI].
      apply incl_app; [exact TSI|]. destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
    assert (DJ2 : forall A k, q - 2128 <= A -> disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W2) A k)
      by (intros A k HA0; exact (qchunk_W_above AL AO (q - 2128) lo LOH CLO LQ2 X mW glob loc ch W2 A k RPW RSW TCHall TSIall VNG FW2 HA0)).
    eapply (rw_cells_transport_m _ mW m2) in SOBJ; [| exact MU2| apply DJ2; clear; lia].
    eapply (u64arr_transport_m _ mW m2) in BUFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in F256; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in TFW; [| exact MU2| apply DJ2; clear; lia].
    eapply (rw_cells_transport_m _ mW m2) in FRe; [| exact MU2| apply DJ2; clear; lia].
    pose proof (CB_of_u64arr m2 (q - 2128 + 16) ws' BUFW) as CBW. rewrite LWS' in CBW. change (8 * 30)%nat with 240%nat in CBW.
    assert (J4 : rw_cells asegs m2 (q - 2128 + 2056) ([C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 2056) [C8 (wz q)] _)). split; [exact TFW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 2056 + Z.of_nat 8) with (q - 64) by (clear; lia). exact FRe. }
    assert (J3 : rw_cells asegs m2 (q - 2128 + 256) ([CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 256) [CB 1800 f4] _)). split; [exact F256|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 256 + Z.of_nat 1800) with (q - 2128 + 2056) by (clear; lia). exact J4. }
    assert (J2 : rw_cells asegs m2 (q - 2128 + 16) ([CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128 + 16) [CB 240 (u64s ws')] _)). split; [exact CBW|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + 16 + Z.of_nat 240) with (q - 2128 + 256) by (clear; lia). exact J3. }
    assert (FRJ : rw_cells asegs m2 (q - 2128) ([C8 (wz (q - 2128 + 16)); C8 (wz (Z.of_nat (length tr)))] ++ [CB 240 (u64s ws')] ++ [CB 1800 f4] ++ [C8 (wz q)] ++ [CB 8 f6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app asegs m2 (q - 2128) [C8 (wz (q - 2128 + 16)); C8 (wz (Z.of_nat (length tr)))] _)). split; [exact SOBJ|].
      cbn [cells_size csize Nat.add]. replace (q - 2128 + Z.of_nat 16) with (q - 2128 + 16) by (clear; lia). exact J2. }
    cbn [app] in FRJ. clear J2 J3 J4 SOBJ F256 TFW FRe CBW.
    lz_go.
    replace (ret_pc (Z_to_bv 64 362440)) with (Z_to_bv 64 362440) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    do 7 zstep.
    zstep. replace (q - 2128 + 2128) with q by (clear; lia). zstep.

    release_frame FRJ ST2 q.

    unhide MUi. unhide WMi.
    assert (IA2 : ia_cells NM2 NM4 true m2).
    { assert (MUIW : munch [(lo, q); (THR + 3168, THR + 3169)] mI mW).
      { eapply munch_trans; [eapply munch_weaken; [| exact MUf]| eapply munch_weaken; [| exact MUw]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _);
          repeat match goal with |- _ /\ _ => split end; try exact I; try assumption; clear - O1 LQ1; lia. }
      assert (DJC : forall A k, 743232 <= A -> A + k <= 1327052 -> disjoint_from [(lo, q); (THR + 3168, THR + 3169)] A k /\
                                disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W2) A k).
      { intros A k H1 H2. split; [cbn [disjoint_from]; clear - H1 H2 LOH T3; lia|].
        exact (ficpt_img_dj (q - 2128) X mW glob loc ch W2 A k RPW RSW TCHall TSIall VNG FW2 ltac:(clear - H1; lia) ltac:(clear - H2; lia)). }
      assert (TRC : forall A cs, rw_cells asegs mI A cs -> 743232 <= A -> A + Z.of_nat (cells_size cs) <= 1327052 -> rw_cells asegs m2 A cs).
      { intros A cs C H1 H2. destruct (DJC A _ H1 H2) as [D1 D2].
        eapply rw_cells_transport_m; [| exact MU2| exact D2]. eapply rw_cells_transport_m; [exact C| exact MUIW| exact D1]. }
      destruct IAI as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM2; lia); clear - HNM2; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - HNM4; lia); clear - HNM4; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    lz_ret. apply evt_done. unfold ficpt_post. cbv zeta.
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m2, (Wtot ++ W2), hs', total'.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUT]| eapply munch_weaken; [| exact MU2]]; apply sub_fp_incl.
      - intros iv Hiv. right; right; right. apply in_or_app. left. exact Hiv.
      - intros iv [<-|[<-|[<-|Hiv]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity|]. right; right; right. apply in_or_app. right. exact Hiv. }
    split.
    { apply Forall_app. split.
      - unfold Wtot, ftouch, iastat. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd].
        + left. left. unfold sub_iv. cbn [fst snd]. clear - LQ1. lia.
        + right; right; right; right; left. right. clear. lia.
        + right; right; right; right; left. left. clear - HNM2. lia.
        + right; right; right; right; left. left. clear. lia.
        + right; right; right; right; right. reflexivity.
      - eapply Forall_impl; [| exact FW2]. intros iv [AT|[NB|[DS|DR]]]; unfold ftouch.
        + left. eapply (atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 2128) (fst X) (snd X) _ _); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact AT].
        + right; left; exact NB.
        + right; right; left; exact DS.
        + right; right; right; left; exact DR. }
    split; [exact INV2|]. split; [exact XL2|]. split; [exact ST2|]. split; [exact QL2|]. split; [exact GC2|]. split; [exact QC2|]. split; [exact MTX2|].
    split; [exact VNG|]. split; [exact NBX|]. split; [exact RD2|]. split; [exact IA2| exact RES2].
  Qed.

End FICPT.

