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
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_quar_P AQuarT F_gct F_depot F_depot_C.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition qchunk_entry : Z := 0x377d4.
Definition QCH_STACK : Z := PUT_STACK.

Section QCH.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation D := (al_depot AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
  Hypothesis AO : alayout_ok AL.
  Variables (gp s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - QCH_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition qchunk_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk)
      (hrest : list (Z * Z)) (hs : list Z) (total : Z) (tr : list Z) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W hs' total',
      let P := fst X in let X1 := (fst (enq_prim P loc), snd X) in
      let todo := put_todo P glob loc ch in let gF := put_glob P glob loc ch in let lF := put_loc P loc ch in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X1 todo (H_enq AL P loc H)
      /\ munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) m m'
      /\ Forall (fun iv => atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) iv
                           \/ put_nb_iv AL P loc iv \/ dstat iv \/ dreg AL iv) W
      /\ dr_inv AL E (dorecycle X1 todo) H' m' (gF ++ lF) (flat_map qb_chunks (gF ++ lF)) hrest
      /\ xle X (dorecycle X1 todo)
      /\ stk asegs m' lo q
      /\ qlist_rep AL m' gF 0 /\ rw_cells asegs m' QUAR_GQ (qcells AL gF) /\ qcache_rep AL m' TQ lF
      /\ rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]]
      /\ (need_batch loc = true -> 0 <= snd (enq_prim P loc) /\ 16 * snd (enq_prim P loc) + Q_BBYTES <= FA_OFF)
      /\ (need_batch loc = true -> held_ok (fst (enq_prim P loc)) ((K_BCLASS, snd (enq_prim P loc)) :: prim_of ch ++ hrest)
                                   /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim P loc)) c)))
      /\ RDEPOT D hs' total' m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)).

  #[using="AO LOH CLO LOQ QH Q16"] Theorem qchunk_spec : forall (ra t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z))
        (STK TR total : Z) (hs : list Z) (ws : list word) (tr : list Z),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) (prim_of ch ++ hrest) ->
    held_kind X ch -> qchunk_wf ch -> pchunk_rep AL m ch ->
    (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of (flat_map qb_chunks (glob ++ loc)))) ->
    qlist_rep AL m glob 0 -> rw_cells asegs m QUAR_GQ (qcells AL glob) -> qcache_rep AL m TQ loc ->
    rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] ->
    rw_cells asegs m QUAR_CONST [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)] -> rw_cells asegs m AF_MAXFILL [C4 (wz 0)] ->
    Forall qbatch_wf (glob ++ loc) -> qbytes (glob ++ loc) + Q_MAX + Q_BBYTES < 2^56 ->
    refill_budget K_BCLASS (get_cls (fst X) K_BCLASS) -> 0 <= pr_calloc (fst X) -> 0 <= pr_cmapped (fst X) -> pr_cmapped (fst X) + K_REGION < 2^63 ->
    Z.of_nat (length loc) < 2^32 ->

    thread_env2 AL m -> RDEPOT D hs total m ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> q <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->
    implA H (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (qchunk_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m glob loc ch hrest hs total tr)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (qc_hdr AL ch)) a2 (wz STK) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz qchunk_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m glob loc ch hrest STK TR total hs ws tr
      MC ST INV HK WFC PREP NSC QLG GC QCL MTX CST AFM FWF QB RB CA0 CM0 CM1 LEN32
      TE2 RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.
    unfold qchunk_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (PS : 272 <= PUT_STACK) by (vm_compute; discriminate).
    assert (LQ1 : lo <= q - 48 - 224) by (unfold QCH_STACK in LOQ; clear - LOQ PS; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    set (B := qc_blk AL ch) in *. set (rz := qc_rz ch) in *. set (bs := qc_bsize ch) in *. set (n := qc_n ch) in *.
    assert (EM : qc_hdr AL ch = B + rz - 16) by reflexivity.
    set (M := qc_hdr AL ch) in *.
    unfold qcells in GC. hide GC. destruct QCL as [TQC QLL]. hide TQC.
    pose proof MTX as MTX0. hide MTX0. pose proof CST as CST0. hide CST0. pose proof AFM as AFM0. hide AFM0.
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.
    zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -48) with (q - 48) in * by lia.
    assert (RU0 : 0 <= rup8 n /\ rup8 n mod 8 = 0 /\ n <= rup8 n) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    pose proof PREP as ((bits & actx & HD) & _). fold M n in HD.
    eapply (rw_cells_transport asegs _ m mA) in HD; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from]; clear - EM RZ16 RZN RU0 GHI CLO LQ1; lia].
    assert (HS : rw_cells asegs mA M [C1 (Z_to_bv 8 3); C1 bits; C2 (wz 0); C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HD| cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app].
      repeat first [ reflexivity | apply (f_equal2 cons); [try reflexivity; apply bv_eq; vm_compute; reflexivity|] ]. }
    clear HD.
    remember M as M0 eqn:HM0 in HS |- *.
    zstep.

    replace (sxb (Z_to_bv 8 3)) with (Z_to_bv 64 3) by (apply bv_eq; vm_compute; reflexivity).
    zstep.
    zstep. if_cases KS; zify_cond KS. { exfalso. clear - KS. lia. } clear KS.
    do 2 zstep.
    zstep.
    assert (TEA : thread_env L mA).
    { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd].
      clear - LOH LQ1 CLO T2 T4. lia. }
    eapply evt_cut.
    { eapply (gct_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 48) mA lo).
      - exact ST.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact TEA.
      - exact TLO.
      - assumption. }
    cbv beta. unfold gct_post. intros msG (g1 & mG & -> & MUg & WMg & MIG & STG & TEG).

    assert (MU1 : munch [(q - 64, q)] m mG).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUg]]; unfold sub_fp; cbn [outside]; intros xo (O1 & _); (split; [clear - O1; lia| exact I]). }
    pose proof (wmono_trans asegs _ _ _ WM WMg) as WM1.
    assert (DJ1 : forall A k, (q <= A \/ A + k <= lo) -> disjoint_from [(q - 64, q)] A k) by (intros A k HA; cbn [disjoint_from]; clear - HA LQ1; lia).
    eapply (rw_cells_transport asegs _ mA mG) in FR; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add disjoint_from]; clear; lia].
    eapply (rw_cells_transport asegs _ mA mG) in SOBJ; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add disjoint_from]; clear - QSTK; lia].
    destruct TE2 as (THC & tidw & TIDC).
    eapply (rw_cells_transport asegs _ m mG) in THC; [| exact MU1| exact WM1| apply DJ1; right; cbn [cells_size csize Nat.add]; clear - T4 CLO; lia].
    eapply (rw_cells_transport asegs _ m mG) in TIDC; [| exact MU1| exact WM1| apply DJ1; right; cbn [cells_size csize Nat.add]; clear - T2 CLO; lia].
    eapply (u64arr_transport asegs _ mA mG) in BUF; [| exact MUg| exact WMg| cbn [disjoint_from]; clear - QTR; lia].
    assert (RDG : RDEPOT D hs total mG).
    { eapply RDEPOT_frame; [exact RD| exact MU1| exact WM1|]. unfold depot_apart. constructor; [| constructor]. cbn [fst snd].
      unfold dl_ok in DLO. clear - DLO LOH CLO LQ1. lia. }
    replace (ret_pc (Z_to_bv 64 227340)) with (Z_to_bv 64 227340) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT T3. lia. } clear KT.
    zstep.
    do 2 zstep.
    zstep.
    do 2 zstep.
    zstep.

    eapply evt_cut.
    { eapply (put_spec D _ gp (wz A0_TP) _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 48) TR total mG hs ws tr DLO RDG BUF TRW LENW LTR RNG).
      - clear - QTR; lia.
      - exact TRH.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - exact ROOM_N.
      - exact ROOM_F.
      - exact ROOM_T.
      - exact MIG.
      - exact STG.
      - exact CLO.
      - clear - LQ1; lia. }
    cbv beta. unfold put_post.
    intros msD (d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & d8 & mD & rid & hs' & total' & -> & MUd & WMd & MID & STD & RDD & BUFD & RES).

    lazymatch type of MUd with munch ?w _ _ => set (Wd := w) in * end.
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    pose proof (bkt_range (depot_hash tr)) as BR.
    assert (T0 : 0 <= total) by (destruct RD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & _); exact T0).
    assert (FZ : Forall (dtouch AL lo q) ((q - 64, q) :: Wd)).
    { unfold Wd. unfold zlen in *. repeat (apply Forall_cons || apply Forall_nil); unfold dtouch, sub_iv, dstat, dreg; cbn [fst snd].
      - left. clear - LQ1. lia.
      - left. clear - LQ1. lia.
      - right; left. clear - BR. lia.
      - right; left. clear. lia.
      - right; right; left. clear - ROOM_N. lia.
      - right; left. clear. lia.
      - right; left. clear. lia.
      - right; right; right. clear - ROOM_F SWB T0. lia. }
    assert (MU2 : munch ((q - 64, q) :: Wd) m mD).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MUd]]; unfold sub_fp; intros xo O.
      - destruct O as [O1 _]. split; [exact O1| exact I].
      - exact (proj2 O). }
    pose proof (wmono_trans asegs _ _ _ WM1 WMd) as WM2.
    assert (FZz : Forall (dzone AL lo) ((q - 64, q) :: Wd)) by (eapply Forall_impl; [| exact FZ]; intros iv; apply dtouch_dzone).
    pose proof (dr_inv_frame_d AL E X H m mD _ _ _ lo _ AO LOH CLO INV MU2 WM2 MID FZz) as INVD.
    pose proof (pchunk_rep_frame_d AL X m mD lo _ ch AO LOH CLO RP RS HK WFC FZz PREP MU2) as PREPD.
    assert (DJF : forall A k, q - 48 <= A -> disjoint_from Wd A k).
    { intros A k HA. unfold Wd. cbn [disjoint_from]. unfold zlen in *. clear - HA BR N2d S2d ROOM_N ROOM_F SWB T0 LOH CLO LQ1. lia. }
    eapply (rw_cells_transport asegs _ mG mD) in FR; [| exact MUd| exact WMd| apply DJF; clear; lia].
    eapply (rw_cells_transport asegs _ mG mD) in SOBJ; [| exact MUd| exact WMd| apply DJF; clear - QSTK; lia].
    pose proof PREPD as ((bits' & actx' & HD) & _ & (uj & UJ) & _). fold M B rz bs n in HD, UJ.
    assert (HS2 : rw_cells asegs mD M [CB 2 [Z_to_bv 8 3; bits']; C2 (wz 0); C4 (wz n); C8 actx']).
    { eapply rw_cells_rebytes; [exact HD| clear; cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app].
      repeat first [ reflexivity | apply (f_equal2 cons); [try reflexivity; apply bv_eq; vm_compute; reflexivity|] ]. }
    clear HD HS.
    assert (BS8 : 8 <= bs - rz) by (clear - RZN RU0 N1; Z.div_mod_to_equations; lia).
    set (k8 := (Z.to_nat (bs - rz) - 8)%nat).
    assert (K8 : Z.of_nat k8 = bs - rz - 8) by (unfold k8; clear - BS8; lia).
    apply (rw_cells_split_CB asegs mD (M + 16) [] _ uj [] [8%nat; k8]) in UJ; [| cbn [sum_nat]; unfold k8; clear - BS8; lia].
    cbn [mk_CB_cells app] in UJ.
    rewrite <- HM0 in HS2, UJ.
    pose proof (munch_refl [(q - 48, q); (M0 + 16, M0 + 24)] mD) as MUx. pose proof (wmono_refl asegs mD) as WMx.
    replace (ret_pc (Z_to_bv 64 227372)) with (Z_to_bv 64 227372) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    do 4 zstep.

    hide MU2. hide MUd. hide WM2. hide WMd.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
    zstep.
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - N1; lia); rewrite Z.mod_small by (clear - N1; lia); reflexivity).
    do 2 zstep.
    do 2 zstep.
    rewrite Z.lor_0_l.
    do 2 zstep.
    do 6 zstep.
    zstep. replace (q - 48 + 48) with q by lia. zstep.

    release_frame FR STD q.
    subst M0.
    unhide MU2. unhide WM2.
    replace (M + 24) with (M + 16 + 8) in MUx by (clear; lia).
    set (WS := ((q - 64, q) :: Wd) ++ [(M + 16, M + 16 + 8)]).
    assert (MUS : munch WS m mS).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MUx]]; unfold WS, sub_fp; intros xo O; apply outside_app in O as [O1 O2].
      - exact O1.
      - destruct O1 as [O1 _]. destruct O2 as [O2 _]. split; [clear - O1; lia|]. split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM2 WMx) as WMS.
    assert (HA : B <= M + 16) by (clear - EM RZ16; lia).
    assert (HN : M + 16 + 8 <= B + bs) by (clear - EM BS8; lia).
    pose proof (dr_inv_blk AL E X H mD mS _ _ hrest ch lo q (q - 48) q (M + 16) 8 AO LOH CLO INVD HK WFC NSC MUx WMx MID
                  ltac:(clear - LQ1; lia) ltac:(clear; lia) HA HN) as INVS.
    assert (SHBG : 2147450880 <= sh B /\ sh B + bs / 8 <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - GLO GHI GS32 ACR; Z.div_mod_to_equations; lia).
    assert (PREPS : pchunk_rep AL mS ch).
    { lazymatch type of UJ with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs mS (M + 16) [] cs [] UJ) as UJ' end. cbn [app cells_size csize cells_bytes cbytes] in UJ'.
      replace (8 + (k8 + 0))%nat with (Z.to_nat (bs - rz)) in UJ' by (clear - K8 BS8; lia).
      eapply (pchunk_ctx_stored AL _ mD mS ch _ PREPD WFC GB8 GS8 MUx UJ'); fold B bs rz.
      - cbn [disjoint_from]. clear - EM GHI CLO LQ1 RZN RU0. lia.
      - cbn [disjoint_from]. assert (S0 : 0 <= bs / 8) by (apply Z.div_pos; [clear - GS32; lia| lia]).
        clear - SHBG S0 LOH LQ1 EM GBAND BS8 RZ16 GLO. lia.
      - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|].
        assert (EBS : B = sc_beg sc + 4096) by (unfold B, qc_blk; rewrite EK; reflexivity).
        assert (SHS : sh B = sh (sc_beg sc) + 512) by (rewrite EBS; unfold sh; clear - GB8 EBS; Z.div_mod_to_equations; lia).
        assert (SHSC : 2147450880 <= sh (sc_beg sc)) by (unfold sh, SHADOW_OFF; clear - EBS GLO; Z.div_mod_to_equations; lia).
        cbn [disjoint_from]. clear - EBS SHS SHSC SHBG EM GHI GBAND GLO CLO LOH LQ1 RZ16 BS8. lia. }
    assert (HBP : forall b, In b (glob ++ loc) -> held1 (fst X) (bpair b) /\ ~ In (bpair b) (prim_of ch)).
    { intros b Hb. destruct HOK as [ND FH]. split; [apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb|].
      intros Hc. apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb|]. apply in_or_app. right. apply in_or_app. left. exact Hc. }
    assert (QLGS : qlist_rep AL mS glob 0).
    { eapply (qlist_rep_frame_dc AL X m mS lo q _ ch (M + 16) 8 glob 0 AO LOH CLO RP RS HK FZz HA HN MUS QLG). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. left. exact Hb. }
    assert (QLLS : qlist_rep AL mS loc 0).
    { eapply (qlist_rep_frame_dc AL X m mS lo q _ ch (M + 16) 8 loc 0 AO LOH CLO RP RS HK FZz HA HN MUS QLL). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. right. exact Hb. }

    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36.
    assert (DJS : forall A k, (A + k <= lo \/ q <= A) -> (A + k <= 1598472 \/ 5858360 <= A) ->
              (A + k <= DN0 D \/ DN0 D + 2^20 <= A) -> (A + k <= SS0 D \/ SS0 D + 2^23 <= A) -> (A + k <= B \/ B + bs <= A) -> disjoint_from WS A k).
    { intros A k H1 H2 H3 H4 H5. unfold WS. apply disjoint_from_app. split; [exact (dtouch_dj AL lo q _ A k FZ H1 H2 H3 H4)|].
      cbn [disjoint_from]. clear - H5 HA HN. lia. }
    unhide GC. unhide TQC. unhide MTX0. unhide CST0. unhide AFM0.
    eapply (rw_cells_transport asegs _ m mS) in GC; [| exact MUS| exact WMS| cbn [cells_size csize Nat.add]; apply DJS; clear - LOH N1d S1d GLO; lia].
    eapply (rw_cells_transport asegs _ m mS) in MTX0; [| exact MUS| exact WMS| cbn [cells_size csize Nat.add]; apply DJS; clear - LOH N1d S1d GLO; lia].
    eapply (rw_cells_transport asegs _ m mS) in CST0; [| exact MUS| exact WMS| cbn [cells_size csize Nat.add]; apply DJS; clear - LOH N1d S1d GLO; lia].
    eapply (rw_cells_transport asegs _ m mS) in AFM0; [| exact MUS| exact WMS| cbn [cells_size csize Nat.add]; apply DJS; clear - LOH N1d S1d GLO; lia].
    pose proof (hull_tq_dj AL X m ch B bs AO RP RS HK ltac:(left; split; reflexivity)) as HTQ. cbn [disjoint_from] in HTQ.
    eapply (rw_cells_transport asegs _ m mS) in TQC; [| exact MUS| exact WMS| cbn [cells_size csize Nat.add]; apply DJS; clear - HTQ T3 T4 CLO A35 A36; lia].

    lz_here.
    eapply implA_mono.
    { eapply (qput_spec AL E AO gp s10 s11 F_ fc q lo (wz STK) LOH CLO LOQ QH Q16 ra _ _ _ s0 s1 _ _ s2 s3 s4 s5 s6 s7 s8 s9 _ _ _ _ X H mS glob loc ch hrest);
        [ assumption | exact STD | exact INVS | exact HK | exact WFC | exact PREPS | exact NSC | exact QLGS | unfold qcells; exact GC | split; [exact TQC| exact QLLS]
        | exact MTX0 | exact CST0 | exact AFM0 | exact FWF | exact QB | exact RB | exact CA0 | exact CM0 | exact CM1 | exact LEN32 ]. }

    intros u H' ms' PO. unfold qput_post in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & W & -> & -> & MUp & FWp & INVp & XLp & STp & QLp & GCp & QCp & MTXp & VNG & NBX).
    unfold qchunk_post. cbv zeta.
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (WS ++ W), hs', total'.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MUp]]; apply sub_fp_incl.
      - intros iv Hiv. right; right; right. apply in_or_app. left. exact Hiv.
      - intros iv [<-|[<-|[<-|Hiv]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity|]. right; right; right. apply in_or_app. right. exact Hiv. }
    assert (ATB : atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) (M + 16, M + 16 + 8)).
    { eapply (atouch_mono AL lo q (fst X) (snd X) _ _ lo q (fst X) (snd X) (prim_of ch) (sec_of ch)); [lia| lia| intros; lia| apply incl_refl| apply incl_appr; apply incl_refl| apply incl_appr; apply incl_refl|].
      exact (held_blk_geo AL X m ch lo q (M + 16) 8 AO RP RS HK HA HN). }
    split.
    { apply Forall_app. split.
      - unfold WS. apply Forall_app. split.
        + eapply Forall_impl; [| exact FZ]. intros iv [DS|[DS|DS]]; [left; left; exact DS| right; right; left; exact DS| right; right; right; exact DS].
        + constructor; [| constructor]. left. exact ATB.
      - eapply Forall_impl; [| exact FWp]. intros iv [AT|NB]; [left; exact AT| right; left; exact NB]. }
    split; [exact INVp|]. split; [exact XLp|]. split; [exact STp|]. split; [exact QLp|]. split; [exact GCp|]. split; [exact QCp|]. split; [exact MTXp|]. split; [exact VNG|]. split; [exact NBX|].
    split.
    2: { destruct RES as [(R1 & R2 & -> & ->)|(R1 & R2 & -> & ->)]; [left| right]; repeat split; try reflexivity; try assumption. rewrite <- R1. exact R2. }

    assert (TCHall : Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch)).
    { destruct HOK as [_ FH]. unfold tc_of. rewrite <- app_assoc. rewrite !app_assoc in FH. apply Forall_app in FH as [FH _]. rewrite <- !app_assoc in FH. exact FH. }
    assert (TSIall : incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X))).
    { destruct (dr_inv_tc AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) [] (prim_of ch ++ hrest) ltac:(rewrite app_nil_r; exact INV)) as [_ TSI].
      apply incl_app; [exact TSI|]. destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 5%nat A05. layout_apart_fact AO 0%nat 6%nat A06.
    assert (DJW : forall A k, (1598472 <= A /\ A + k <= 5858360) \/ (DN0 D <= A /\ A + k <= DN0 D + 2^20) \/ (SS0 D <= A /\ A + k <= SS0 D + 2^23) ->
              disjoint_from ((M + 16, M + 16 + 8) :: W) A k).
    { intros A k HAk.
      assert (DAT : forall a b, atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) (a, b) -> A + k <= a \/ b <= A).
      { intros a b AT. destruct HAk as [[H1 H2]|HR].
        - pose proof (atouch_img_dj AL X m lo q [(a, b)] _ _ A k AO LOH CLO RP RS TCHall TSIall ltac:(constructor; [exact AT| constructor]) ltac:(clear - H1; lia) ltac:(clear - H2; lia)) as DD.
          cbn [disjoint_from] in DD. exact (proj1 DD).
        - pose proof (atouch_dreg_dj AL X m lo q [(a, b)] _ _ A k AO LOH CLO RP RS TCHall TSIall ltac:(constructor; [exact AT| constructor]) HR) as DD.
          cbn [disjoint_from] in DD. exact (proj1 DD). }
      cbn [disjoint_from]. split; [exact (DAT _ _ ATB)|].
      clear - FWp DAT VNG HAk SP1 SP2 SP5 A05 A06 N1d S1d AO. induction FWp as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
      destruct HIV as [AT|[NB CI]]; [exact (DAT a b AT)|]. destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
      assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity.
      change Q_BBYTES with 8192 in V1.
      destruct CI as [CI|CI]; unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI.
      - clear - CI V0 V1 RN1 RN2 RG SP1 SP2 SP5 A05 A06 HAk N1d S1d. lia.
      - assert (BBR : 0 <= region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) /\ region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) + 8192 <= 2^47)
          by (clear - V0 V1 RN1 RN2 RG SP1 SP5; lia).
        change (8192 / 8) with 1024 in CI. unfold sh, SHADOW_OFF in CI.
        clear - CI BBR HAk N1d S1d. Z.div_mod_to_equations. lia. }
    set (W2 := [(q - 48, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)] ++ (M + 16, M + 16 + 8) :: W).
    assert (MUD2 : munch W2 mD m').
    { eapply munch_trans; [eapply munch_weaken; [| exact MUx]| eapply munch_weaken; [| exact MUp]]; apply sub_fp_incl; unfold W2.
      - intros iv [<-|[<-|[]]]; [left; reflexivity| right; right; right; right; left; reflexivity].
      - intros iv [<-|[<-|[<-|Hiv]]]; [right; left; reflexivity| right; right; left; reflexivity| right; right; right; left; reflexivity|]. right; right; right; right; right. exact Hiv. }
    eapply (RDEPOT_frame_m AL hs' total' W2 mD m' DLO SWB RDD MUD2); unfold W2; (apply disjoint_from_app; split; [| apply DJW]).
    - cbn [disjoint_from]. clear - LOH LQ1 T3 T4. lia.
    - left. clear. lia.
    - cbn [disjoint_from]. clear - LOH LQ1 CLO N1d N2d T3 T4 A35. lia.
    - right; left. clear. lia.
    - cbn [disjoint_from]. clear - LOH LQ1 CLO S1d S2d T3 T4 A36. lia.
    - right; right. clear. lia.
  Qed.

  #[using="AO LOH CLO LOQ"] Lemma qchunk_W_above : forall (X : pstate) (m : mem) (glob loc : list qbatch) (ch : qchunk) W A k,
    RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
    Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch) -> incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X)) ->
    (need_batch loc = true -> 0 <= snd (enq_prim (fst X) loc) /\ 16 * snd (enq_prim (fst X) loc) + Q_BBYTES <= FA_OFF) ->
    Forall (fun iv => atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) iv
                      \/ put_nb_iv AL (fst X) loc iv \/ dstat iv \/ dreg AL iv) W ->
    q <= A -> disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) A k.
  Proof.
    intros X m glob loc ch W A k RP RS TCH TSI VNG FW HA.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (PS : 272 <= PUT_STACK) by (vm_compute; discriminate).
    assert (LQ : lo <= q) by (unfold QCH_STACK in LOQ; clear - LOQ PS; lia).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    cbn [disjoint_from]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA T3 T4 CLO LQ; lia|].
    induction FW as [|[a b] W' HIV FW' IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
    destruct HIV as [AT|[[NB CI]|[DS|DR]]].
    - pose proof (atouch_above AL X m lo q [(a, b)] _ _ A k AO LOH CLO LQ RP RS TCH TSI ltac:(constructor; [exact AT| constructor]) HA) as DD.
      cbn [disjoint_from] in DD. exact (proj1 DD).
    - destruct (VNG NB) as [V0 V1]. pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
      assert (RG : region AL K_BCLASS = al_space AL + K_BCLASS * K_REGION) by reflexivity. change Q_BBYTES with 8192 in V1.
      destruct CI as [CI|CI]; unfold chunk_iv, chunk_sh_iv in CI; cbn [fst snd] in CI; change (class_size K_BCLASS) with 8192 in CI.
      + clear - CI V0 V1 RN1 RN2 RG SP1 SP2 SP5 HA CLO LQ. lia.
      + assert (BBR : 0 <= region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) /\ region AL K_BCLASS + 16 * snd (enq_prim (fst X) loc) + 8192 <= 2^47)
          by (clear - V0 V1 RN1 RN2 RG SP1 SP5; lia).
        change (8192 / 8) with 1024 in CI. unfold sh, SHADOW_OFF in CI.
        clear - CI BBR HA LOH LQ. Z.div_mod_to_equations. lia.
    - unfold dstat in DS. cbn [fst snd] in DS. clear - DS HA LOH LQ. lia.
    - unfold dreg in DR. cbn [fst snd] in DR. clear - DR HA N2d S2d CLO LQ. lia.
  Qed.

End QCH.

