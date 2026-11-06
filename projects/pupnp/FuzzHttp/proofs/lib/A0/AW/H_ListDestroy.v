(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA HObjK H_freelist H_ListAddTail H_httpheader_free H_ListDestroy_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation lbrm k LB := (lb_remove (am_K_eqb FI AI) k LB).
Local Notation bsub := (bsub FI AI).
Local Notation dlseg := (dlseg FI AI).
Local Notation flseg := (flseg FI AI).
Local Notation hd_addr := (hd_addr FI AI).
Local Notation last_addr := (last_addr FI AI).
Local Notation hdrs_mem := (hdrs_mem FI AI).
Local Notation hdrs_blocks := (hdrs_blocks FI AI).
Local Notation hblocks := (hblocks FI AI).
Local Notation bkeep := (bkeep FI AI).

Definition ListDestroy_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB LBK : BL) (L fcmp lo : Z) (m : mem) (OWNED : BL) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(L, L + 80)] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB' /\ (forall b, In b LB' -> In b LB)
    /\ (forall b, In b OWNED -> ~ In b LB')
    /\ rw_cells asegs m' L (lhead_cells (L + 24) L 0) /\ rw_cells asegs m' (L + 56) (fl_cells 0 0)
    /\ FFc m' L httpheader_free_entryA fcmp /\ shw m' L 96
    /\ am_nsec FI AI s' = ns0.

Definition ListDestroy_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB LBK : BL) (st : fsstate FI)
         (ns : list (BLK * Z)) (hs : list (hdr FI AI)) (L fcmp lo : Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 96 - 48 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) ->
  rw_cells asegs m (L + 56) (fl_cells 0 0) -> FFc m L httpheader_free_entryA fcmp ->
  dlseg m ns L (L + 24) -> hdrs_mem m hs -> map snd ns = map (hA FI AI) hs ->
  mlocNB FI AI q st L 96 -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  zlength ns < 2^40 -> 0 <= fcmp < 2^64 ->
  bsub (map fst ns ++ hdrs_blocks hs ++ LBK) LB -> NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ LBK)) ->
  a0 = wz L -> a1 = wz 1 ->
  AJ FI AI J (ListDestroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK L fcmp lo m (map fst ns ++ hdrs_blocks hs))
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListDestroy_entryA) fc None m (seg_rom asegs))
    s LB.

Section LOOP.
  Variables (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (st : fsstate FI) (ns0 : Z) (LB0 LBK : BL) (L fcmp lo : Z) (m0 : mem) (pad : list byte).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LO : lo <= q - 96 - 48 - 4096.
  Hypothesis QAL : q mod 16 = 0.
  Hypothesis QTOP : q + 16 <= am_stack_top FI AI.
  Hypothesis LL : mlocNB FI AI q st L 96.
  Hypothesis LHI : L + 96 <= alloc_ceiling.
  Hypothesis LAL : L mod 8 = 0.
  Hypothesis LLO : 0x609000 <= L.
  Hypothesis FCMP : 0 <= fcmp < 2^64.
  Notation q' := (q + -96).
  Variable OWNED : BL.
  Notation POST := (ListDestroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st ns0 LB0 LBK L fcmp lo m0 OWNED).

  #[using="Type"] Lemma gone_hblocks : forall (h : hdr FI AI) (LBx : BL) b0, In b0 (hblocks h) -> ~ In b0 (lbrm (hk FI AI h) (lbrm (vk FI AI h) (lbrm (nk FI AI h) LBx))).
  Proof.
    intros h LBx b0 [<-|[<-|[<-|[]]]] IN.
    - exact (lb_remove_neq FI AI _ _ _ IN eq_refl).
    - apply (lb_remove_sub FI AI) in IN. exact (lb_remove_neq FI AI _ _ _ IN eq_refl).
    - apply (lb_remove_sub FI AI) in IN. apply (lb_remove_sub FI AI) in IN. exact (lb_remove_neq FI AI _ _ _ IN eq_refl).
  Qed.

  #[using="AC ASL AMS CLO LO QAL QTOP LL LHI LAL LLO FCMP"] Lemma ld_exit : forall (FB : BL) (flh fk size : Z) (s : aps FI AI) (LB : BL) (m : mem)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 t3 t4 t5 t6 x1 : word),
    rw_cells asegs m L (lhead_cells (L + 24) L size) ->
    rw_cells asegs m (L + 56) (fl_cells flh fk) -> flseg m FB flh ->
    FFc m L httpheader_free_entryA fcmp ->
    bsub (FB ++ LBK) LB -> NoDup (map blk_id (FB ++ LBK)) -> (forall b, In b LB -> In b LB0) ->
    (forall b0, In b0 OWNED -> In b0 FB \/ ~ In b0 LB) ->
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m -> stk asegs m lo q' -> mem_inv asegs m -> shw m L 96 ->
    DFRA m q' pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
    apx FI AI [(L, L + 80)] LBK q m0 m -> am_nsec FI AI s = ns0 ->
    AJ FI AI J POST
      (XSTA L x1 q' gp (wz A0_TP) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 F fc 0x8b814 m) s LB.
  Proof.
    intros FB flh fk size s LB m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 t3 t4 t5 t6 x1.
    intros LC FLC FLS FF ASUB ND SUB0 GONE HR RF AE ST MI SHWL FR HP0 NS0.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    assert (QC : alloc_ceiling <= q) by lia.
    apply (bsub_app FI AI) in ASUB. destruct ASUB as [FSUB KSUB].
    eapply (aj_evt FI AI J). { eapply (dsegE L (L + 24) L size); try eassumption. }
    intros ms' (m1 & a0' & -> & -> & MU1 & WM1 & MI1 & LC1).
    destruct (cw_frames FI AI s LB st m m1 _ HR RF AE MU1 WM1) as (HR1 & RF1 & AE1).
    { constructor; [| constructor]. eapply (cw_iv_mlocNB FI AI LB q st L 96); [exact LL| exact QC| lia| lia| lia]. }
    pose proof (rw_cells_transport asegs _ m m1 _ _ FLC MU1 WM1 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ FF MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FF1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ FR MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR1.
    assert (ST1 : stk asegs m1 lo q') by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia]).
    assert (SHWL1 : shw m1 L 96) by (eapply (shw_frame _ m m1 L 96 SHWL MU1); app_ivs_tac).
    assert (FLS1 : flseg m1 FB flh).
    { eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb.
      pose proof (mlocNB_apart FI AI s LB m st q L 96 b HR RF LL (FSUB b Hb) QC ltac:(lia)) as D.
      destruct (flseg_shape FI AI FB m flh b FLS Hb) as [Eb _]. rewrite Eb in D |- *. cbn [blk_addr blk_size fst snd] in *. cbn. lia. }
    assert (HP1 : apx FI AI [(L, L + 80)] LBK q m0 m1).
    { eapply (apx_trans FI AI); [exact HP0|]. eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1).
      constructor; [right; right; cbn; lia| constructor]. }
    clear MU1 WM1 HR RF AE FLC FF FR ST FLS HP0 LC MI SHWL.
    assert (FLL : mlocNB FI AI q' st (L + 56) 24).
    { eapply (mlocNB_weaken FI AI); [eapply (mlocNB_sub FI AI); [exact LL| lia| lia]| lia| auto]. }
    eapply (aj_bind FI AI J).
    { eapply (FreeListDestroy_spec_A FI AI J AC ASL AMS) with (lo := lo) (FL := L + 56) (flh := flh) (fk := fk) (FB := FB) (LBK := LBK) (st := st).
      - exact HR1.
      - exact RF1.
      - exact AE1.
      - exact ST1.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO. lia.
      - clear - QAL. Z.div_mod_to_equations. lia.
      - clear - QTOP. lia.
      - exact MI1.
      - exact FLC1.
      - exact FLL.
      - clear - LHI. lia.
      - clear - LAL. Z.div_mod_to_equations. lia.
      - eapply shw_sub; [exact SHWL1| lia| lia| lia].
      - exact FLS1.
      - exact FSUB.
      - exact KSUB.
      - exact ND.
      - reflexivity. }
    intros s2' LB2 ms2 P. unfold FreeListDestroy_post_A in P.
    destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & AE2 & RF2 & HP2 & HR2 & KSUB2 & INCL2 & GONE2 & FLC2 & NS2).
    replace (ret_pc (Z_to_bv 64 0x8b830)) with (Z_to_bv 64 0x8b830) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LM : forall X n, L <= X -> X + n <= L + 96 -> aclient_range FI AI LBK q' X n).
    { intros X n H1 H2. eapply (mblocA_client FI AI _ q' st m1); [exact RF1|]. apply (mlocNB_mblocA FI AI).
      eapply (mlocNB_weaken FI AI); [eapply (mlocNB_sub FI AI); [exact LL| exact H1| exact H2]| lia| auto]. }
    pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply aclient_range_above; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
    pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 LC1 ltac:(apply LM; unfold lhead_cells; cbn; lia) ltac:(unfold lhead_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as LC2.
    pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 FF1 ltac:(apply LM; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FF2.
    assert (SHWL2 : shw m2 L 96).
    { eapply (mlocNB_shw_apx FI AI AMS _ LBK q' st m1 m2 L 96); [| exact SHWL1| exact HP2| app_ivs_tac| exact RF1| lia].
      eapply (mlocNB_weaken FI AI); [exact LL| lia| auto]. }
    assert (HP02 : apx FI AI [(L, L + 80)] LBK q m0 m2).
    { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_weaken FI AI); [exact HP2| | lia| auto]. unfold sub_fp. cbn. intros y [Hy _]. lia. }
    eapply (aj_evt FI AI J). { eapply (dsegF lo pad ra q); try eassumption; lia. }
    intros ms' [-> ST3]. apply (aj_ret FI AI J). unfold ListDestroy_post_A.
    do 14 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST3|]. split; [exact AE2|]. split; [exact RF2|]. split; [exact HP02|].
    split; [exact HR2|]. split; [exact KSUB2|]. split; [intros b Hb; apply SUB0; apply INCL2; exact Hb|].
    split. { intros b0 Hb0 IN2. destruct (GONE b0 Hb0) as [INF|NI]; [exact (GONE2 b0 INF IN2)| exact (NI (INCL2 b0 IN2))]. }
    split; [exact LC2|]. split; [exact FLC2|]. split; [exact FF2|]. split; [exact SHWL2| rewrite NS2; exact NS0].
  Qed.

  #[using="IC AC ASL AMS CLO LO QAL QTOP LL LHI LAL LLO FCMP"] Lemma ld_loop : forall (ns : list (BLK * Z)) (hs : list (hdr FI AI)) (FB : BL) (flh fk : Z) (s : aps FI AI) (LB : BL) (m : mem)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 x1 : word),
    ns <> [] -> dlseg m ns L (L + 24) -> hdrs_mem m hs -> map snd ns = map (hA FI AI) hs ->
    rw_cells asegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) -> zlength ns < 2^40 ->
    rw_cells asegs m (L + 56) (fl_cells flh fk) -> flseg m FB flh -> fk = zlength FB -> fk <= 99 ->
    FFc m L httpheader_free_entryA fcmp ->
    bsub (map fst ns ++ hdrs_blocks hs ++ FB ++ LBK) LB -> NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ FB ++ LBK)) ->
    (forall b, In b LB -> In b LB0) ->
    (forall b0, In b0 OWNED -> In b0 (map fst ns ++ hdrs_blocks hs ++ FB) \/ ~ In b0 LB) ->
    RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m -> stk asegs m lo q' -> mem_inv asegs m -> shw m L 96 ->
    DFRA m q' pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
    apx FI AI [(L, L + 80)] LBK q m0 m -> am_nsec FI AI s = ns0 ->
    AJ FI AI J POST
      (LSTA L (hd_addr ns (L + 24)) x1 q' gp (wz A0_TP) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 F fc 0x8b6c4 m) s LB.
  Proof.
    induction ns as [|[bN it] ns IH]; intros hs FB flh fk s LB m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 x1;
      intros NNE DL HS ITEMS LC LEN FLC FLS FK FK99 FF ASUB ND SUB0 GONE HR RF AE ST MI SHWL FR HP0 NS0; [congruence|].
    destruct hs as [|h hs]; [discriminate|]. cbn [map] in ITEMS. injection ITEMS as ITEM ITEMS'.
    unfold zlength in *. change (length ((bN, it) :: ns)) with (S (length ns)) in *. rewrite !Nat2Z.inj_succ in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    assert (QC : alloc_ceiling <= q) by lia. assert (QC' : alloc_ceiling <= q') by lia.
    cbn [HObjA.dlseg] in DL. destruct DL as (SZ & NZ & NT & ITR & NC & DL').
    pose proof HS as HS0. cbn [HObjA.hdrs_mem] in HS. destruct HS as (HM & HPU & HS').
    set (N := blk_addr bN) in *.

    change (map fst ((bN, it) :: ns)) with ([bN] ++ map fst ns) in ASUB, ND.
    change (hdrs_blocks (h :: hs)) with (hblocks h ++ hdrs_blocks hs) in ASUB, ND.
    rewrite <- !app_assoc in ND. rewrite <- !app_assoc in ASUB.
    apply (bsub_app FI AI) in ASUB. destruct ASUB as [NSUBb REST]. apply (bsub_app FI AI) in REST. destruct REST as [NSUB REST].
    apply (bsub_app FI AI) in REST. destruct REST as [HhSUB REST]. apply (bsub_app FI AI) in REST. destruct REST as [HsSUB REST].
    apply (bsub_app FI AI) in REST. destruct REST as [FSUB KSUB].
    pose proof (NSUBb bN (or_introl eq_refl)) as NIN.
    apply nd_app in ND. destruct ND as (_ & J0 & ND). apply nd_app in ND. destruct ND as (NDn & J1 & ND).
    apply nd_app in ND. destruct ND as (NDHh & J2 & ND). apply nd_app in ND. destruct ND as (NDhs & J3 & ND).
    apply nd_app in ND. destruct ND as (NDF & J4 & NDK).
    apply idj_app_r in J0. destruct J0 as [J0n J0]. apply idj_app_r in J0. destruct J0 as [J0Hh J0]. apply idj_app_r in J0. destruct J0 as [J0hs J0].
    apply idj_app_r in J0. destruct J0 as [J0F J0K].
    apply idj_app_r in J1. destruct J1 as [J1Hh J1]. apply idj_app_r in J1. destruct J1 as [J1hs J1]. apply idj_app_r in J1. destruct J1 as [J1F J1K].
    apply idj_app_r in J2. destruct J2 as [J2hs J2]. apply idj_app_r in J2. destruct J2 as [J2F J2K].
    apply idj_app_r in J3. destruct J3 as [J3F J3K].

    assert (BR : forall b, In b LB -> 0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling
                                      /\ 0x609000 <= blk_addr b /\ (L + 96 <= blk_addr b \/ blk_addr b + blk_size b <= L)).
    { intros b Hb. destruct (am_block_range FI AI _ _ _ _ HR Hb) as (R1 & R2 & R3 & R4 & R5 & _).
      pose proof (mlocNB_apart FI AI s LB m st q L 96 b HR RF LL Hb QC ltac:(lia)) as D. repeat (split; [assumption|]). exact D. }
    destruct (BR bN NIN) as (N0 & NAL & _ & NHI & NLO & NDJL). fold N in N0, NAL, NHI, NLO, NDJL. rewrite SZ in NHI, NDJL.
    assert (NK : bN = (blk_id bN, N, 24)) by (destruct bN as [[kk aa] zz]; cbn in SZ |- *; subst; reflexivity).
    cbn [HObjA.hd_addr] in LC |- *. fold N in LC |- *.
    assert (NODES : forall b0 it0, In (b0, it0) ns -> In b0 LB /\ blk_size b0 = 24 /\ 0x609000 <= blk_addr b0 /\ blk_addr b0 + 24 + 16 <= alloc_ceiling
                                                    /\ blk_addr b0 mod 8 = 0 /\ (N + 24 <= blk_addr b0 \/ blk_addr b0 + 24 <= N)
                                                    /\ (L + 96 <= blk_addr b0 \/ blk_addr b0 + 24 <= L)).
    { intros b0 it0 H0. destruct (dlseg_facts FI AI _ _ _ _ _ _ DL' H0) as (SZ0 & _). pose proof (in_map fst _ _ H0) as H0'. cbn [fst] in H0'.
      pose proof (NSUB _ H0') as B0IN. destruct (BR b0 B0IN) as (B0P & B0AL & _ & B0HI & B0LO & B0DJ). rewrite SZ0 in B0HI, B0DJ.
      pose proof (idj_neq _ _ _ _ J0n (or_introl eq_refl) H0') as NE.
      pose proof (am_blocks_disjoint FI AI _ _ _ _ _ HR NIN B0IN NE) as D. fold N in D. rewrite ?SZ, ?SZ0 in D.
      split; [exact B0IN|]. split; [exact SZ0|]. split; [exact B0LO|]. split; [exact B0HI|]. split; [clear - B0AL; Z.div_mod_to_equations; lia|]. split; [lia| exact B0DJ]. }
    assert (FBF : forall b, In b FB -> In b LB /\ blk_size b = 24 /\ 0x609000 <= blk_addr b /\ blk_addr b + 24 + 16 <= alloc_ceiling
                                       /\ (L + 96 <= blk_addr b \/ blk_addr b + 24 <= L)).
    { intros b Hb. destruct (flseg_shape FI AI _ _ _ _ FLS Hb) as [Eb _]. pose proof (FSUB b Hb) as HbL.
      destruct (BR b HbL) as (Q1 & Q2 & _ & Q4 & Q5 & Q6). assert (SZb : blk_size b = 24) by (rewrite Eb; reflexivity). rewrite SZb in Q4, Q6.
      split; [exact HbL|]. split; [exact SZb|]. split; [exact Q5|]. split; [exact Q4| exact Q6]. }
    assert (HREG : forall h0 A n, In h0 (h :: hs) -> In (A, n) (hregions FI AI h0) ->
              exists k, In (k, A, n) LB /\ In (k, A, n) (hblocks h ++ hdrs_blocks hs) /\ 0x609000 <= A /\ A + n + 16 <= alloc_ceiling /\ 0 <= n
                        /\ (L + 96 <= A \/ A + n <= L)).
    { intros h0 A n Hh HA. destruct (hregion_block FI AI h0 A n HA) as [k Hk]. exists k.
      pose proof (in_hdrs_blocks FI AI _ _ _ Hh Hk) as HB. change (In (k, A, n) (hblocks h ++ hdrs_blocks hs)) in HB.
      assert (HbL : In (k, A, n) LB) by (apply in_app_or in HB; destruct HB as [HB|HB]; [apply HhSUB| apply HsSUB]; exact HB).
      destruct (BR _ HbL) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn in Q1, Q2, Q3, Q4, Q5, Q6.
      split; [exact HbL|]. split; [exact HB|]. split; [exact Q5|]. split; [exact Q4|]. split; [exact Q3| exact Q6]. }
    assert (LASTR : 0 <= last_addr ns N < 2^64).
    { assert (G : forall nsx pv, 0 <= pv < 2^64 -> (forall b it, In (b, it) nsx -> In (b, it) ns) -> 0 <= last_addr nsx pv < 2^64).
      { induction nsx as [|[b0 it0] nsx IHx]; intros pv Hpv Hsub; cbn; [exact Hpv|]. apply IHx.
        - destruct (NODES b0 it0 (Hsub _ _ (or_introl eq_refl))) as (_ & _ & ? & ? & _). lia.
        - intros b1 it1 H1. apply Hsub. right. exact H1. }
      apply G; [lia| auto]. }

    assert (CONT : forall m1 (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      dlseg m1 ns L (L + 24) -> hdrs_mem m1 (h :: hs) ->
      rw_cells asegs m1 L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (Z.succ (Z.of_nat (length ns)))) ->
      rw_cells asegs m1 (L + 56) (fl_cells flh fk) -> flseg m1 FB flh -> FFc m1 L httpheader_free_entryA fcmp ->
      RHEAP_A FI AI s LB m1 -> RFAKE FI st m1 -> asan_env asegs m1 -> stk asegs m1 lo q' -> mem_inv asegs m1 -> shw m1 L 96 ->
      DFRA m1 q' pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra -> rw_cells asegs m1 N (node_cells L (hd_addr ns (L + 24)) it) ->
      apx FI AI [(L, L + 80)] LBK q m0 m1 ->
      AJ FI AI J POST
        (MS (mkR (wz 0x8b748) (wz q') gp (wz A0_TP) t0' t1' t2' (wz L) (wz (L + 48)) (wz (L + 56)) (wz N) a2' a3' a4' a5' a6' a7'
                 (wz (L + 56)) (wz (hd_addr ns (L + 24))) (wz (L + 80)) (wz it) (wz 0x7fff8000) (wz (L + 24))
                 (wz (Z.shiftr (L + 48) 3 + 2147450880)) (wz (Z.shiftr (L + 80) 3 + 2147450880)) s10 s11 t3' t4' t5' t6')
            F (wz FreeListFree_entryA) fc None m1 (seg_rom asegs)) s LB).
    { intros m1 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DL1 HS1 LC1 FLC1 FLS1 FF1 HR1 RF1 AE1 ST1 MI1 SHWL1 FR1 NC1 HP1.
      set (k := blk_id bN) in *.

      assert (OURS : forall b0, In b0 (map fst ns ++ (hblocks h ++ hdrs_blocks hs) ++ FB) -> In b0 (lbrm k LB)).
      { intros b0 H0. apply (in_lb_remove FI AI).
        - rewrite !in_app_iff in H0. destruct H0 as [H0|[[H0|H0]|H0]]; [apply NSUB| apply HhSUB| apply HsSUB| apply FSUB]; exact H0.
        - apply not_eq_sym. unfold k. rewrite !in_app_iff in H0.
          destruct H0 as [H0|[[H0|H0]|H0]]; [eapply J0n| eapply J0Hh| eapply J0hs| eapply J0F]; try (left; reflexivity); exact H0. }
      assert (KEEPk : forall b0, In b0 LBK -> In b0 (lbrm k LB)).
      { intros b0 H0. apply (in_lb_remove FI AI); [apply KSUB; exact H0|]. apply not_eq_sym. eapply J0K; [left; reflexivity| exact H0]. }
      assert (OURSL : forall b0, In b0 (map fst ns ++ (hblocks h ++ hdrs_blocks hs) ++ FB) -> L + 96 <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= L).
      { intros b0 H0. pose proof (OURS b0 H0) as HbL. apply (lb_remove_sub FI AI) in HbL. destruct (BR b0 HbL) as (_ & _ & _ & _ & _ & D). exact D. }
      assert (FLL : mlocNB FI AI q' st (L + 56) 24).
      { eapply (mlocNB_weaken FI AI); [eapply (mlocNB_sub FI AI); [exact LL| lia| lia]| lia| auto]. }

      eapply (aj_bind FI AI J).
      { rewrite NK in NIN. unfold node_cells in NC1.
        eapply (FreeListFree_spec_A FI AI J AC ASL) with (lo := lo) (FL := L + 56) (N := N) (flh := flh) (fk := fk) (FB := FB) (k := k) (st := st).
        - exact HR1.
        - exact RF1.
        - exact AE1.
        - exact ST1.
        - exact CLO.
        - unfold A0_RT_STACK. clear - LO. lia.
        - clear - QAL. Z.div_mod_to_equations. lia.
        - clear - QTOP. lia.
        - exact MI1.
        - unfold valid_frame. rewrite unsigned_lit by (clear - LLO LHI ACR; lia). clear - LHI CLO LO. lia.
        - exact FLC1.
        - exact FLL.
        - clear - LHI. lia.
        - clear - LAL. Z.div_mod_to_equations. lia.
        - eapply shw_sub; [exact SHWL1| lia| lia| lia].
        - exact FLS1.
        - exact FK.
        - exact FK99.
        - exact FSUB.
        - exact NIN.
        - exact NC1.
        - apply nd_cons. split; [| exact NDF]. eapply idj_sub_l; [exact J0F|]. intros x [<-|[]]. rewrite <- NK. left. reflexivity.
        - reflexivity.
        - reflexivity. }
      intros s2' LB2 ms2 P. unfold FreeListFree_post_A in P.
      destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & flh2 & fk2 & FB2 & -> & MI2 & ST2 & AE2 & RF2 & HP2 & HR2 & SUB2 & FLC2 & FLS2 & FK2 & FK2' & FSUB2 & NDF2 & CASES2 & NS2).
      replace (ret_pc (Z_to_bv 64 0x8b748)) with (Z_to_bv 64 0x8b748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      assert (FB2F : forall b, In b FB2 -> b = (k, N, 24) \/ In b FB).
      { intros b Hb. destruct CASES2 as [[-> ->]|[-> ->]]; [destruct Hb as [<-|Hb]; [left; reflexivity| right; exact Hb]| right; exact Hb]. }
      assert (INCL2 : forall b, In b LB2 -> In b LB).
      { intros b Hb. destruct CASES2 as [[-> _]|[-> _]]; [exact Hb| eapply (lb_remove_sub FI AI); exact Hb]. }
      assert (JF2K : idj FB2 LBK).
      { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0K; [left; reflexivity| exact Hb]| exact (J4 a b Ha' Hb)]. }
      assert (JF2n : idj FB2 (map fst ns)).
      { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0n; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J1F a b Ha' Hb)]. }
      assert (JF2Hh : idj FB2 (hblocks h)).
      { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0Hh; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J2F a b Ha' Hb)]. }
      assert (JF2hs : idj FB2 (hdrs_blocks hs)).
      { intros a b Ha Hb. destruct (FB2F a Ha) as [->|Ha']; [cbn; unfold k; eapply J0hs; [left; reflexivity| exact Hb]| exact (idj_sym _ _ J3F a b Ha' Hb)]. }
      assert (FB2B : forall b, In b FB2 -> In b LB2 /\ blk_size b = 24 /\ (L + 96 <= blk_addr b \/ blk_addr b + 24 <= L)).
      { intros b Hb. split; [apply FSUB2; exact Hb|]. destruct (FB2F b Hb) as [->|Hb']; [cbn; split; [reflexivity| exact NDJL]|].
        destruct (FBF b Hb') as (_ & ? & _ & _ & ?). auto. }

      assert (BK2 : bkeep (map fst ns ++ (hblocks h ++ hdrs_blocks hs) ++ FB) m1 m2).
      { eapply (bkeep_of_apx FI AI); [exact HP2| exact OURS|]. intros b0 H0. pose proof (OURSL b0 H0) as D. cbn [disjoint_from]. lia. }
      assert (DL2 : dlseg m2 ns L (L + 24)).
      { eapply (dlseg_bkeep FI AI); [exact DL1| exact BK2|]. intros b0 it0 H0. apply in_or_app. left. exact (in_map fst _ _ H0). }
      assert (HS2 : hdrs_mem m2 (h :: hs)).
      { eapply (hdrs_mem_bkeep FI AI); [exact HS1| exact BK2|]. intros b0 H0. apply in_or_app. right. apply in_or_app. left. exact H0. }
      assert (LM : forall (LBx : BL) mx X n, RFAKE FI st mx -> L <= X -> X + n <= L + 96 -> aclient_range FI AI LBx q' X n).
      { intros LBx mx X n RFx H1 H2. eapply (mblocA_client FI AI _ q' st mx); [exact RFx|]. apply (mlocNB_mblocA FI AI).
        eapply (mlocNB_weaken FI AI); [eapply (mlocNB_sub FI AI); [exact LL| exact H1| exact H2]| lia| auto]. }
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 LC1 ltac:(apply (LM _ m1); [exact RF1| unfold lhead_cells; cbn; lia| unfold lhead_cells; cbn; lia]) ltac:(unfold lhead_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as LC2.
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 FF1 ltac:(apply (LM _ m1); [exact RF1| cbn; lia| cbn; lia]) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FF2.
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP2 FR1 ltac:(apply aclient_range_above; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
      assert (SHWL2 : shw m2 L 96).
      { eapply (mlocNB_shw_apx FI AI AMS _ _ q' st m1 m2 L 96); [| exact SHWL1| exact HP2| app_ivs_tac| exact RF1| lia].
        eapply (mlocNB_weaken FI AI); [exact LL| lia| auto]. }
      assert (HP02 : apx FI AI [(L, L + 80)] LBK q m0 m2).
      { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_weaken FI AI); [exact HP2| | lia| exact KEEPk]. unfold sub_fp. cbn. intros y [Hy _]. lia. }
      clear HP2 HP1 LC1 FF1 FR1 DL1 HS1 BK2 NC1 AE1 RF1 HR1 ST1 MI1 FLS1 FLC1 SHWL1.

      eapply (aj_evt FI AI J).
      { eapply (dsegC L (hd_addr ns (L + 24)) (hd_addr ns (L + 24)) (last_addr ns L) (Z.succ (Z.of_nat (length ns))) fcmp it q');
          try eassumption; try lia. }
      intros ms' (m3 & a2x & -> & MU3 & WM3 & MI3 & LC3 & FF3).
      replace (Z.succ (Z.of_nat (length ns)) - 1) with (Z.of_nat (length ns)) in LC3 by lia.
      destruct (cw_frames FI AI s2' LB2 st m2 m3 _ HR2 RF2 AE2 MU3 WM3) as (HR3 & RF3 & AE3).
      { constructor; [| constructor]. eapply (cw_iv_mlocNB FI AI LB2 q st L 96); [exact LL| exact QC| lia| lia| lia]. }
      pose proof (rw_cells_transport asegs _ m2 m3 _ _ FLC2 MU3 WM3 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC3.
      pose proof (rw_cells_transport asegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR3.
      assert (ST3 : stk asegs m3 lo q') by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
      assert (SHWL3 : shw m3 L 96) by (eapply (shw_frame _ m2 m3 L 96 SHWL2 MU3); app_ivs_tac).
      assert (DL3 : dlseg m3 ns L (L + 24)).
      { eapply (dlseg_transport FI AI); [exact DL2| exact MU3| exact WM3|]. intros b0 it0 H0. destruct (NODES b0 it0 H0) as (_ & _ & _ & _ & _ & _ & D). cbn. lia. }
      assert (HS3 : hdrs_mem m3 (h :: hs)).
      { eapply (hdrs_mem_transport FI AI); [exact HS2| exact MU3| exact WM3|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & _ & _ & _ & _ & ? & D). cbn. lia. }
      assert (FLS3 : flseg m3 FB2 flh2).
      { eapply (flseg_transport FI AI); [exact FLS2| exact MU3| exact WM3|]. intros b Hb. destruct (FB2B b Hb) as (_ & _ & D). cbn. lia. }
      assert (HP03 : apx FI AI [(L, L + 80)] LBK q m0 m3).
      { eapply (apx_trans FI AI); [exact HP02|]. eapply (apx_seg FI AI ASL s2' LB2 _ q _ _ m2 m2 m3 HR2 (fun b Hb => SUB2 b (KEEPk b Hb)) MU3 WM3).
        constructor; [right; right; cbn; lia| constructor]. }
      clear MU3 WM3 HR2 RF2 AE2 FLC2 FR2 ST2 DL2 HS2 FLS2 HP02 LC2 FF2 MI2 SHWL2.

      set (LBK' := map fst ns ++ hdrs_blocks hs ++ FB2 ++ LBK).
      assert (K'SUB : bsub LBK' LB2).
      { intros b0 H0. unfold LBK' in H0. rewrite !in_app_iff in H0. destruct H0 as [H0|[H0|[H0|H0]]].
        - apply SUB2. apply OURS. apply in_or_app. left. exact H0.
        - apply SUB2. apply OURS. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact H0.
        - apply FSUB2. exact H0.
        - apply SUB2. apply KEEPk. exact H0. }
      assert (NDK' : NoDup (map blk_id LBK')).
      { unfold LBK'. apply nd_app. split; [exact NDn|]. split.
        { apply idj_app_r. split; [exact J1hs|]. apply idj_app_r. split; [apply idj_sym; exact JF2n| exact J1K]. }
        apply nd_app. split; [exact NDhs|]. split.
        { apply idj_app_r. split; [apply idj_sym; exact JF2hs| exact J3K]. }
        apply nd_app. split; [exact NDF2|]. split; [exact JF2K| exact NDK]. }
      assert (JHK' : idj (hblocks h) LBK').
      { unfold LBK'. apply idj_app_r. split; [apply idj_sym; exact J1Hh|]. apply idj_app_r. split; [exact J2hs|].
        apply idj_app_r. split; [apply idj_sym; exact JF2Hh| exact J2K]. }
      cbn [HObjA.hdrs_mem] in HS3. destruct HS3 as (HM3 & _ & HS3').
      eapply (aj_bind FI AI J).
      { eapply (httpheader_free_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (LBK := LBK') (h := h) (st := st).
        - exact HR3.
        - exact RF3.
        - exact AE3.
        - exact ST3.
        - exact CLO.
        - unfold A0_RT_STACK. clear - LO. lia.
        - clear - QAL. Z.div_mod_to_equations. lia.
        - clear - QTOP. lia.
        - exact MI3.
        - unfold valid_frame. rewrite unsigned_lit by (clear - LLO LHI ACR; lia). clear - LHI CLO LO. lia.
        - split; [exact HM3|]. split; [exact HPU|]. intros b0 H0. apply SUB2. apply OURS. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact H0.
        - exact K'SUB.
        - apply nd_app. split; [exact NDHh|]. split; [exact JHK'| exact NDK'].
        - reflexivity.
        - rewrite ITEM. reflexivity. }
      intros s4' LB4 ms4 P. unfold httpheader_free_post_A in P.
      destruct P as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MI4 & ST4 & AE4 & RF4 & HP4 & HR4 & K'SUB4 & ELB4 & NS4).
      replace (ret_pc (Z_to_bv 64 httpheader_free_raA)) with (Z_to_bv 64 0x8b774) by (symmetry; apply ret_pc_even; [unfold httpheader_free_raA; lia| reflexivity]).
      assert (INCL4 : forall b, In b LB4 -> In b LB0).
      { intros b Hb. apply SUB0. apply INCL2. rewrite ELB4 in Hb.
        apply (lb_remove_sub FI AI) in Hb. apply (lb_remove_sub FI AI) in Hb. apply (lb_remove_sub FI AI) in Hb. exact Hb. }
      assert (GONE4 : forall b0, In b0 OWNED -> In b0 (map fst ns ++ hdrs_blocks hs ++ FB2) \/ ~ In b0 LB4).
      { intros b0 Hb0. assert (S42 : forall b, In b LB4 -> In b LB2).
        { intros b Hb. rewrite ELB4 in Hb. apply (lb_remove_sub FI AI) in Hb. apply (lb_remove_sub FI AI) in Hb. apply (lb_remove_sub FI AI) in Hb. exact Hb. }
        destruct (GONE b0 Hb0) as [IN|NI]; [| right; intros IN4; exact (NI (INCL2 b0 (S42 b0 IN4)))].
        cbn [map fst] in IN. change (hdrs_blocks (h :: hs)) with (hblocks h ++ hdrs_blocks hs) in IN.
        destruct IN as [<-|IN].
        { destruct CASES2 as [[_ ->]|[-> _]].
          - left. apply in_or_app. right. apply in_or_app. right. left. rewrite NK. reflexivity.
          - right. intros IN4. exact (lb_remove_neq FI AI _ _ _ (S42 _ IN4) eq_refl). }
        apply in_app_or in IN. destruct IN as [IN|IN]; [left; apply in_or_app; left; exact IN|].
        apply in_app_or in IN. destruct IN as [IN|IN].
        { apply in_app_or in IN. destruct IN as [IN|IN]; [| left; apply in_or_app; right; apply in_or_app; left; exact IN].
          right. rewrite ELB4. exact (gone_hblocks h LB2 b0 IN). }
        left. apply in_or_app. right. apply in_or_app. right. destruct CASES2 as [[_ ->]|[_ ->]]; [right; exact IN| exact IN]. }
      assert (BK4 : bkeep LBK' m3 m4).
      { eapply (bkeep_of_apx FI AI); [exact HP4| intros b Hb; exact Hb|]. intros b0 H0. exact I. }
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP4 LC3 ltac:(apply (LM _ m3); [exact RF3| unfold lhead_cells; cbn; lia| unfold lhead_cells; cbn; lia]) ltac:(exact I)) as LC4.
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP4 FF3 ltac:(apply (LM _ m3); [exact RF3| cbn; lia| cbn; lia]) ltac:(exact I)) as FF4.
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP4 FLC3 ltac:(apply (LM _ m3); [exact RF3| unfold fl_cells; cbn; lia| unfold fl_cells; cbn; lia]) ltac:(exact I)) as FLC4.
      pose proof (apx_rw_cells FI AI _ _ _ _ _ _ _ HP4 FR3 ltac:(apply aclient_range_above; cbn; lia) ltac:(exact I)) as FR4.
      assert (SHWL4 : shw m4 L 96).
      { eapply (mlocNB_shw_apx FI AI AMS _ _ q' st m3 m4 L 96); [| exact SHWL3| exact HP4| apply Forall_nil| exact RF3| lia].
        eapply (mlocNB_weaken FI AI); [exact LL| lia| auto]. }
      assert (DL4 : dlseg m4 ns L (L + 24)).
      { eapply (dlseg_bkeep FI AI); [exact DL3| exact BK4|]. intros b0 it0 H0. unfold LBK'. apply in_or_app. left. exact (in_map fst _ _ H0). }
      assert (HS4 : hdrs_mem m4 hs).
      { eapply (hdrs_mem_bkeep FI AI); [exact HS3'| exact BK4|]. intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. left. exact H0. }
      assert (FLS4 : flseg m4 FB2 flh2).
      { eapply (flseg_bkeep FI AI); [exact FLS3| exact BK4|]. intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H0. }
      assert (HP04 : apx FI AI [(L, L + 80)] LBK q m0 m4).
      { eapply (apx_trans FI AI); [exact HP03|]. eapply (apx_weaken FI AI); [exact HP4| intros y Hy; cbn; exact I| lia|].
        intros b0 H0. unfold LBK'. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H0. }
      clear HP4 BK4 LC3 FF3 FR3 FLC3 DL3 HS3' FLS3 HP03 HR3 RF3 AE3 ST3 MI3 HM3 SHWL3.

      assert (CURR : 0 <= hd_addr ns (L + 24) < 2^64).
      { destruct ns as [|[bx itx] nsx]; cbn; [lia|]. destruct (NODES bx itx (or_introl eq_refl)) as (_ & _ & ? & ? & _). lia. }
      eapply (aj_evt FI AI J). { eapply (dsegD L (hd_addr ns (L + 24)) q'); lia. }
      intros ms' ->.
      destruct ns as [|[bx itx] nsx].
      -
        cbn [HObjA.hd_addr HObjA.last_addr] in LC4 |- *. rewrite Z.eqb_refl.
        destruct hs as [|h' hs']; [| discriminate].
        eapply (ld_exit FB2 flh2 fk2 0 s4' LB4 m4); try eassumption; try lia.
      -
        destruct hs as [|h' hs']; [discriminate|].
        pose proof DL4 as DLx. cbn [HObjA.dlseg] in DLx. destruct DLx as (_ & _ & NTx & _).
        cbn [HObjA.hd_addr]. replace (blk_addr bx =? L + 24) with false by (symmetry; apply Z.eqb_neq; exact NTx).
        eapply (IH (h' :: hs') FB2 flh2 fk2 s4' LB4 m4); try eassumption; try lia.
        discriminate. }

    pose proof (block_shw FI AI s LB m bN N 24 HR NIN ltac:(lia) ltac:(rewrite SZ; fold N; lia) ltac:(lia)) as SHWN.
    assert (NAL8 : N mod 8 = 0) by (clear - NAL; Z.div_mod_to_equations; lia).
    destruct ns as [|[b2 it2] ns2] eqn:ENS.
    - cbn [HObjA.last_addr HObjA.hd_addr] in LC, CONT |- *.
      eapply (aj_evt FI AI J).
      { eapply (dsegB L N (L + 24) it N (Z.succ (Z.of_nat (length ([] : list (BLK * Z))))) None q'); try eassumption; try (cbn; lia); try lia; try reflexivity. }
      intros ms' P. unfold unlink_postA in P. destruct P as (m1 & a2x & a3x & -> & MU1 & WM1 & MI1 & LC1 & NC1 & _). cbn [app] in MU1.
      destruct (cw_frames FI AI s LB st m m1 _ HR RF AE MU1 WM1) as (HR1 & RF1 & AE1).
      { constructor; [| constructor]. eapply (cw_iv_mlocNB FI AI LB q st L 96); [exact LL| exact QC| lia| lia| lia]. }
      eapply CONT.
      + exact I.
      + eapply (hdrs_mem_transport FI AI); [exact HS0| exact MU1| exact WM1|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & _ & _ & _ & _ & ? & D). cbn. lia.
      + exact LC1.
      + eapply rw_cells_transport; [exact FLC| exact MU1| exact WM1| unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
      + eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBF b Hb) as (_ & _ & _ & _ & D). cbn. lia.
      + eapply rw_cells_transport; [exact FF| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia].
      + exact HR1.
      + exact RF1.
      + exact AE1.
      + eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia].
      + exact MI1.
      + eapply (shw_frame _ m m1 L 96 SHWL MU1). app_ivs_tac.
      + eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia].
      + exact NC1.
      + eapply (apx_trans FI AI); [exact HP0|]. eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1).
        constructor; [right; right; cbn; lia| constructor].
    - pose proof DL' as DLn. cbn [HObjA.dlseg] in DLn. destruct DLn as (SZ2 & NZ2 & NT2 & ITR2 & NC2 & DL2).
      destruct (NODES b2 it2 ltac:(left; reflexivity)) as (B2IN & _ & B2LO & B2HI & B2AL & DJ2 & DJL2).
      cbn [HObjA.last_addr HObjA.hd_addr] in LC, LASTR, CONT |- *.
      pose proof (block_shw FI AI s LB m b2 (blk_addr b2) 24 HR B2IN ltac:(lia) ltac:(rewrite SZ2; lia) ltac:(lia)) as SHWX.
      eapply (aj_evt FI AI J).
      { eapply (dsegB L N (blk_addr b2) it (last_addr ns2 (blk_addr b2)) (Z.succ (Z.of_nat (length ((b2, it2) :: ns2)))) (Some (hd_addr ns2 (L + 24), it2)) q');
          try eassumption; try lia.
        split; [exact NC2|]. split; [lia|]. split; [lia|]. split; [exact B2AL|]. split; [exact SHWX|]. split; [lia|]. split; [lia|]. split; [| lia].
        destruct ns2 as [|[b3 it3] ?]; cbn; [lia|]. destruct (NODES b3 it3 ltac:(right; left; reflexivity)) as (_ & _ & ? & ? & _). lia. }
      intros ms' P. unfold unlink_postA in P. destruct P as (m1 & a2x & a3x & -> & MU1 & WM1 & MI1 & LC1 & NC1 & NXC1). cbn [app] in MU1.
      assert (B2NE : forall b0, In b0 LB -> b0 <> b2 -> blk_addr b2 + 24 <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= blk_addr b2).
      { intros b0 H0 NE. destruct (am_blocks_disjoint FI AI _ _ _ _ _ HR B2IN H0 ltac:(congruence)) as [D|D]; rewrite ?SZ2 in D; lia. }

      pose proof NDn as NDn2. cbn [map] in NDn2. apply nd_cons in NDn2. destruct NDn2 as [J2r NDn2'].
      assert (ND2x : forall b0, In b0 (map fst ns2 ++ (hblocks h ++ hdrs_blocks hs) ++ FB ++ LBK) -> b0 <> b2).
      { intros b0 H0. apply not_eq_sym. rewrite !in_app_iff in H0. destruct H0 as [H0|[[H0|H0]|[H0|H0]]].
        - eapply (idj_neq _ _ _ _ J2r); [left; reflexivity| exact H0].
        - eapply (idj_neq _ _ _ _ J1Hh); [left; reflexivity| exact H0].
        - eapply (idj_neq _ _ _ _ J1hs); [left; reflexivity| exact H0].
        - eapply (idj_neq _ _ _ _ J1F); [left; reflexivity| exact H0].
        - eapply (idj_neq _ _ _ _ J1K); [left; reflexivity| exact H0]. }
      destruct (cw_frames FI AI s LB st m m1 _ HR RF AE MU1 WM1) as (HR1 & RF1 & AE1).
      { constructor; [| constructor; [| constructor]].
        - eapply (cw_iv_mlocNB FI AI LB q st L 96); [exact LL| exact QC| lia| lia| lia].
        - eapply (cw_iv_blk FI AI LB st b2); [exact B2IN| lia| lia| rewrite SZ2; lia]. }
      eapply CONT.
      + cbn [HObjA.dlseg]. split; [exact SZ2|]. split; [exact NZ2|]. split; [exact NT2|]. split; [exact ITR2|]. split; [exact NXC1|].
        eapply (dlseg_transport FI AI); [exact DL2| exact MU1| exact WM1|]. intros b0 it0 H0.
        destruct (NODES b0 it0 ltac:(right; exact H0)) as (B0IN & B0SZ & _ & _ & _ & _ & D0).
        pose proof (B2NE b0 B0IN ltac:(apply ND2x; apply in_or_app; left; exact (in_map fst _ _ H0))) as D. rewrite B0SZ in D. cbn. lia.
      + eapply (hdrs_mem_transport FI AI); [exact HS0| exact MU1| exact WM1|]. intros h0 A n Hh HA. destruct (HREG h0 A n Hh HA) as (kk & KIN & KH & _ & _ & ? & D0).
        pose proof (B2NE _ KIN ltac:(apply ND2x; apply in_or_app; right; apply in_or_app; left; exact KH)) as D. cbn in D. cbn. lia.
      + exact LC1.
      + eapply rw_cells_transport; [exact FLC| exact MU1| exact WM1| unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia].
      + eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBF b Hb) as (BIN & BSZ & _ & _ & D0).
        pose proof (B2NE _ BIN ltac:(apply ND2x; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as D. rewrite BSZ in D. cbn. lia.
      + eapply rw_cells_transport; [exact FF| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia].
      + exact HR1.
      + exact RF1.
      + exact AE1.
      + eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia].
      + exact MI1.
      + eapply (shw_frame _ m m1 L 96 SHWL MU1). app_ivs_tac.
      + eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia].
      + exact NC1.
      + eapply (apx_trans FI AI); [exact HP0|]. eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1).
        constructor. { right; right. cbn. lia. } constructor; [| constructor].
        right; left. cbn [fst snd]. intros a Ha. eapply (fresh_block_not_aclient FI AI ASL s LB LBK b2 q m a HR B2IN); [| exact QC| rewrite SZ2; lia].
        intros b0 Hb0. split; [apply KSUB; exact Hb0|]. apply ND2x. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right. exact Hb0.
  Qed.
End LOOP.

#[using="IC AC ASL AMS"] Theorem ListDestroy_spec_A : ListDestroy_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB LBK st ns hs L fcmp lo.
  intros HR RF AE ST CLO LO QAL QTOP MI LC FLC FF DL HS ITEMS LL LHI LAL SHWL LEN FCMP ASUB ND -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 96 - 48 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  assert (QC : alloc_ceiling <= q) by lia.
  pose proof (mlocNB_mblocA FI AI LB q st L 96 LL) as LM.
  destruct (mblocA_range FI AI s LB _ q st m L 96 HR (fun b H => H) RF LM QC ltac:(lia)) as (LLO & _ & _).
  pose proof ASUB as ASUB0. apply (bsub_app FI AI) in ASUB. destruct ASUB as [NSUB REST]. apply (bsub_app FI AI) in REST. destruct REST as [HSUB KSUB].
  assert (NODES : forall b0 it0, In (b0, it0) ns -> 0x609000 <= blk_addr b0 /\ blk_addr b0 + 24 <= alloc_ceiling).
  { intros b0 it0 H0. destruct (dlseg_facts FI AI _ _ _ _ _ _ DL H0) as (SZ0 & _).
    pose proof (in_map fst _ _ H0) as H0'. cbn [fst] in H0'.
    destruct (am_block_range FI AI _ _ _ _ HR (NSUB _ H0')) as (R1 & R2 & _ & R4 & R5 & _). rewrite SZ0 in R4. lia. }
  assert (FIRSTR : 0 <= hd_addr ns (L + 24) < 2^64).
  { destruct ns as [|[b it] ns']; cbn; [lia|]. destruct (NODES b it (or_introl eq_refl)). lia. }
  eapply (aj_evt FI AI J). { eapply (dsegA lo L (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)); try eassumption; lia. }
  intros ms' (m1 & pad & MU1 & WM1 & MI1 & ST1 & FR1 & LC1 & CASE).
  destruct (cw_frames FI AI s LB st m m1 _ HR RF AE MU1 WM1) as (HR1 & RF1 & AE1).
  { constructor; [| constructor]. apply (cw_iv_stack FI AI); lia. }
  pose proof (rw_cells_transport asegs _ m m1 _ _ FLC MU1 WM1 ltac:(unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as FLC1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ FF MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FF1.
  assert (SHWL1 : shw m1 L 96) by (eapply (shw_frame _ m m1 L 96 SHWL MU1); app_ivs_tac).
  assert (DL1 : dlseg m1 ns L (L + 24)).
  { eapply (dlseg_transport FI AI); [exact DL| exact MU1| exact WM1|]. intros b it H. destruct (NODES b it H). cbn. lia. }
  assert (HS1 : hdrs_mem m1 hs).
  { eapply (hdrs_mem_transport FI AI); [exact HS| exact MU1| exact WM1|]. intros h0 A n Hh HA.
    destruct (hregion_block FI AI h0 A n HA) as [k Hk]. pose proof (HSUB _ (in_hdrs_blocks FI AI _ _ _ Hh Hk)) as HbL.
    destruct (am_block_range FI AI _ _ _ _ HR HbL) as (R1 & _ & R3 & R4 & _). cbn in R1, R3, R4. cbn. lia. }
  assert (HP1 : apx FI AI [(L, L + 80)] LBK q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  destruct CASE as [(E & a0' & a1' & a2' & ->)|(NE & a0' & a1' & a2' & ->)].
  -
    destruct ns as [|[b it] ns']. 2:{ exfalso. cbn in E. pose proof DL as DLx. cbn [HObjA.dlseg] in DLx. destruct DLx as (_ & _ & NT & _). exact (NT E). }
    destruct hs as [|h hs']; [| discriminate]. cbn [HObjA.hd_addr HObjA.last_addr zlength length Z.of_nat] in LC1 |- *.
    eapply (ld_exit ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK L fcmp lo m pad CLO LO' QAL QTOP LL LHI LAL LLO FCMP [] [] 0 0 0);
      try eassumption; try (cbn; lia).
    intros b Hb; exact Hb.
  - eapply (ld_loop ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK L fcmp lo m pad CLO LO' QAL QTOP LL LHI LAL LLO FCMP (map fst ns ++ hdrs_blocks hs) ns hs [] 0 0);
      try eassumption; try (cbn; lia).
    + destruct ns; [cbn in NE; congruence| discriminate].
    + reflexivity.
    + intros b Hb; exact Hb.
    + intros b0 Hb0. left. rewrite app_nil_r. exact Hb0.
Qed.

End W.
