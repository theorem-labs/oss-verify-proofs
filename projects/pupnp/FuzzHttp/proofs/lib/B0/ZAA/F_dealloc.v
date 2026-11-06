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
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_quar_P AQuarT F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition asan_free_entry : Z := 0x33304.
Definition deallocate_entry : Z := 0x3332c.
Definition DEALLOC_STACK : Z := QCH_STACK.

Section DEALLOC.
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
  Hypothesis LOQ : lo <= q - DEALLOC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  #[using="q"] Lemma hdr_word_facts2 : forall bu, 0 <= bu < 256 ->
    Z.lor 2 (Z.shiftl bu 8) = 2 + 256 * bu /\ Z.land (2 + 256 * bu) 255 = 2 /\ Z.land (Z.lxor (2 + 256 * bu) 3) 255 = 1
    /\ Z.lxor (2 + 256 * bu) 1 = 3 + 256 * bu /\ Z.lor 3 (Z.shiftl bu 8) = 3 + 256 * bu.
  Proof.
    intros bu Hb.
    pose proof (range_check (fun b => (Z.lor 2 (Z.shiftl b 8) =? 2 + 256 * b) && (Z.land (2 + 256 * b) 255 =? 2) && (Z.land (Z.lxor (2 + 256 * b) 3) 255 =? 1)
                                      && (Z.lxor (2 + 256 * b) 1 =? 3 + 256 * b) && (Z.lor 3 (Z.shiftl b 8) =? 3 + 256 * b))
                  0 256 ltac:(vm_compute; reflexivity) bu ltac:(lia)) as X.
    cbn beta in X. apply andb_true_iff in X as [X X5]. apply andb_true_iff in X as [X X4]. apply andb_true_iff in X as [X X3]. apply andb_true_iff in X as [X1 X2].
    apply Z.eqb_eq in X1, X2, X3, X4, X5. tauto.
  Qed.

  #[using="AO LOH CLO LOQ QH Q16"] Theorem deallocate_spec : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z))
        (STK TR total : Z) (hs : list Z) (ws : list word) (tr : list Z),
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
    thread_env2 AL m -> hooks_env m -> RDEPOT D hs total m ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> q <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->
    implA H (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (qchunk_post AL E gp s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m glob loc ch hrest hs total tr)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (qc_hdr AL ch + 16)) (wz 0) (wz 0) (wz STK) (wz 1) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz deallocate_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m glob loc ch hrest STK TR total hs ws tr
      MC ST INV HK WFC LFULL NSC QLG GC QCL MTX CST AFM FWF QB RB CA0 CM0 CM1 LEN32
      TE2 HKE RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.
    unfold deallocate_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (PS : 272 <= PUT_STACK) by (vm_compute; discriminate).
    assert (LQ1 : lo <= q - 64 - 32) by (unfold DEALLOC_STACK, QCH_STACK in LOQ; clear - LOQ PS; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    set (B := qc_blk AL ch) in *. set (rz := qc_rz ch) in *. set (bs := qc_bsize ch) in *. set (n := qc_n ch) in *.
    assert (EM : qc_hdr AL ch = B + rz - 16) by reflexivity.
    set (M := qc_hdr AL ch) in *.
    assert (RU0 : 0 <= rup8 n /\ rup8 n mod 8 = 0 /\ n <= rup8 n) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    unfold qcells in GC. hide GC. destruct QCL as [TQC QLL]. hide TQC.
    pose proof MTX as MTX0. hide MTX0. pose proof CST as CST0. hide CST0. pose proof AFM as AFM0. hide AFM0.
    pose proof SOBJ as SOBJ0. hide SOBJ0. pose proof BUF as BUF0. hide BUF0.
    pose proof (munch_refl [(q - 64, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 64%nat ST.
    do 8 zstep.

    zstep. if_cases KP; zify_cond KP. { exfalso. clear - KP EM RZ16 GLO. lia. } clear KP.
    do 6 zstep.
    zstep.
    replace (M + 16 + -16) with M by (clear; lia).
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -64) with (q - 64) in * by lia.
    assert (HKA : hooks_env mA).
    { unfold hooks_env in *. eapply rw_cells_transport; [exact HKE| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from]. clear - LOH LQ1. lia. }
    eapply evt_cut.
    { eapply (free_hooks_spec _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 64) mA lo).
      - exact ST.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact HKA.
      - assumption. }
    cbv beta. unfold free_hooks_post. intros msG (g1 & g2 & mG & -> & MUg & WMg & MIG & STG).
    replace (ret_pc (Z_to_bv 64 209784)) with (Z_to_bv 64 209784) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. if_cases KH; zify_cond KH; [| exfalso; revert KH; clear; intros KH; rewrite ?unsigned_lit in KH by lia; lia]. clear KH.

    assert (MU1 : munch [(q - 96, q)] m mG).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUg]]; unfold sub_fp; cbn [outside]; intros xo (O1 & _); (split; [clear - O1; lia| exact I]). }
    pose proof (wmono_trans asegs _ _ _ WM WMg) as WM1.
    pose proof LFULL as ((bits & actx & BITS & HD) & _). fold M n in HD.
    eapply (rw_cells_transport asegs _ m mG) in HD; [| exact MU1| exact WM1| cbn [cells_size csize Nat.add disjoint_from]; clear - EM RZ16 RZN RU0 GHI CLO LQ1; lia].
    eapply (rw_cells_transport asegs _ mA mG) in FR; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add disjoint_from]; clear; lia].
    set (bu := bv_unsigned bits) in *. assert (BU : 0 <= bu < 256) by (unfold bu; apply byte_lt256).
    destruct (hdr_word_facts2 bu BU) as (HW1 & HW2 & HW3 & HW4 & HW5).
    assert (HW : rw_cells asegs mG M [C4 (wz (2 + 256 * bu)); C4 (wz n); C8 actx]).
    { pose proof (rw_cells_CB_C4 asegs mG M [] _ _ HD) as XW. cbn [app] in XW.
      replace (le_bytes_to_word [Z_to_bv 8 2; bits; Z_to_bv 8 0; Z_to_bv 8 0]) with (wz (2 + 256 * bu)) in XW; [exact XW|].
      unfold le_bytes_to_word. cbn [bytes_le_to_Z]. fold bu. f_equal. change (bv_unsigned (Z_to_bv 8 2)) with 2. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      change (Z.shiftl 0 8) with 0. change (Z.lor 0 0) with 0. change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r. symmetry. exact HW1. }
    clear HD.
    hide MU. hide WM. hide MUg. hide WMg. hide MU1. hide WM1. hide FR.
    pose proof (munch_refl [(M, M + 4)] mG) as MUc. pose proof (wmono_refl asegs mG) as WMc.
    remember M as M0 eqn:HM0 in HW, MUc |- *.
    assert (M8 : M0 mod 8 = 0) by (rewrite HM0, EM; clear - GB8 RZM; Z.div_mod_to_equations; lia).
    assert (MR : 6328320 <= M0 /\ M0 + 24 <= alloc_ceiling) by (rewrite HM0, EM; clear - GLO GHI RZ16 RZN RU0 N1; Z.div_mod_to_equations; lia).
    do 5 zstep.
    assert (LA4 : Z.land M0 18446744073709551612 = M0).
    { assert (EU : exists u, M0 = Z.shiftl u 2 /\ 0 <= u < 2^62).
      { exists (M0 / 4). rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. clear - M8 MR ACR. change (2^62) with 4611686018427387904. Z.div_mod_to_equations. lia. }
      destruct EU as (u & -> & Hu). change 18446744073709551612 with (Z.shiftl (Z.ones 62) 2).
      rewrite <- Z.shiftl_land, Z.land_ones by lia. rewrite Z.mod_small by exact Hu. reflexivity. }
    rewrite LA4. clear LA4.
    assert (EMT : exists mt, M0 = 8 * mt) by (exists (M0 / 8); clear - M8; Z.div_mod_to_equations; lia).
    destruct EMT as (mt & EMT).
    assert (SH0 : (64 * mt) mod 32 = 0) by (clear; Z.div_mod_to_equations; lia).
    replace (Z.shiftl M0 3) with (64 * mt) by (rewrite EMT, Z.shiftl_mul_pow2 by lia; change (2^3) with 8; lia).
    zstep.
    rewrite SH0. change (Z.shiftl 255 0) with 255. change (bv_swrap 32 255) with 255.
    zstep.
    rewrite SH0. change (Z.shiftl 2 0) with 2. change (bv_swrap 32 2) with 2.
    zstep.
    rewrite SH0. change (Z.shiftl 3 0) with 3. change (bv_swrap 32 3) with 3.
    assert (AMOM : amo_aligned AW (Z_to_bv 64 M0) = true) by (apply amo_aligned_intro_w; [clear - MR ACR; lia| rewrite EMT; clear; Z.div_mod_to_equations; lia]).
    amo_step_h AMOM.
    rewrite (sx32_lit (2 + 256 * bu)) by (clear - BU; lia).
    zstep.
    rewrite HW2.
    zstep. lit_branch.
    zstep.
    zstep.
    rewrite HW3.
    zstep.
    rewrite HW4.
    amo_step_h AMOM.
    zstep. lit_branch.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.

    unhide MU1. unhide WM1.
    assert (MU2 : munch [(q - 96, q); (M, M + 4)] m mC).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| rewrite HM0 in MUc; exact MUc]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [exact O1| exact I].
      - split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM1 WMc) as WM2.
    assert (DJ2 : forall A k, (A + k <= M \/ M + 4 <= A) -> A + k <= lo -> disjoint_from [(q - 96, q); (M, M + 4)] A k)
      by (intros A k D1 D2; cbn [disjoint_from]; clear - D1 D2 LQ1; lia).
    unhide FR.
    eapply (rw_cells_transport asegs _ mG mC) in FR; [| exact MUc| exact WMc| cbn [cells_size csize Nat.add disjoint_from]; clear - MR ACR CLO LQ1; lia].
    pose proof LFULL as (_ & _ & (ub & UB) & (sj & SLACK) & _). fold M n bs rz in SLACK, UB.
    eapply (rw_cells_transport asegs _ m mC) in UB; [| exact MU2| exact WM2| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - N1; lia); apply DJ2; clear - EM GHI CLO RZN RU0 N1; lia].
    eapply (rw_cells_transport asegs _ m mC) in SLACK; [| exact MU2| exact WM2| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN RU0; lia); apply DJ2; clear - EM GHI CLO RZN RU0 N1; lia].
    assert (BS8 : 8 <= bs - rz) by (clear - RZN RU0 N1; Z.div_mod_to_equations; lia).
    pose proof (cb_join mC (M + 16) _ _ _ _ UB ltac:(rewrite Z2Nat.id by (clear - N1; lia); exact SLACK)) as UJ.
    replace (Z.to_nat n + Z.to_nat (bs - rz - n))%nat with (Z.to_nat (bs - rz)) in UJ by (clear - N1 RZN RU0; lia).
    clear UB SLACK.
    set (k8 := (Z.to_nat (bs - rz) - 8)%nat).
    assert (K8 : Z.of_nat k8 = bs - rz - 8) by (unfold k8; clear - BS8; lia).
    apply (rw_cells_split_CB asegs mC (M + 16) [] _ _ [] [8%nat; k8]) in UJ; [| cbn [sum_nat]; unfold k8; clear - BS8; lia].
    cbn [mk_CB_cells app] in UJ.
    rewrite <- HM0 in UJ.

    assert (HS : rw_cells asegs mC M0 [C1 (Z_to_bv 8 3); C1 bits; C2 (wz 0); C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HW| clear; cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app]. f_equal.
      assert (EW : wz (3 + 256 * bu) = le_bytes_to_word [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]).
      { unfold le_bytes_to_word. cbn [bytes_le_to_Z]. fold bu. f_equal. change (bv_unsigned (Z_to_bv 8 3)) with 3. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        change (Z.shiftl 0 8) with 0. change (Z.lor 0 0) with 0. change (Z.shiftl 0 8) with 0. rewrite Z.lor_0_r. symmetry. exact HW5. }
      rewrite EW, le4_of_bytes by reflexivity. reflexivity. }
    clear HW.
    hide MU2. hide WM2. hide MUc. hide WMc. hide MU1. hide WM1. hide FR.
    pose proof (munch_refl [(M0 + 16, M0 + 24)] mC) as MUs. pose proof (wmono_refl asegs mC) as WMs.
    do 2 zstep.
    sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
    unhide FR.
    eapply (rw_cells_transport asegs _ mC mS) in FR; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add disjoint_from]; clear - MR ACR CLO LQ1; lia].
    zstep.
    zstep.

    fold bu. rewrite BITS.
    zstep. lit_branch.
    do 2 zstep.
    zstep. lit_branch.
    zstep.

    subst M0.
    unhide MU2. unhide WM2.
    assert (MU3 : munch [(q - 96, q); (M, M + 24)] m mS).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MUs]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [exact O1|]. split; [clear - O2; lia| exact I].
      - split; [clear - O2; lia| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM2 WMs) as WM3.
    assert (HA : B <= M) by (clear - EM RZ16; lia).
    assert (HN : M + 24 <= B + bs) by (clear - EM BS8; lia).
    assert (MIS : mem_inv asegs mS) by assumption.
    pose proof (dr_inv_blk AL E X H m mS _ _ hrest ch lo q (q - 96) q M 24 AO LOH CLO INV HK WFC NSC MU3 WM3 MIS
                  ltac:(clear - LQ1; lia) ltac:(clear; lia) HA HN) as INVS.
    pose proof INVS as (RPS & _ & RSS & _ & _ & TES & _).
    eapply evt_cut.
    { eapply (gcts_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q - 64) mS lo).
      - exact STG.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact TES.
      - exact TLO.
      - exact MIS. }
    cbv beta. unfold gcts_post. intros msT (h1 & mH & -> & MUh & WMh & MIH & STH & TEH).

    replace (ret_pc (Z_to_bv 64 210276)) with (Z_to_bv 64 210276) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (DJH : forall A k, (A + k <= q - 96 \/ q - 64 <= A) -> disjoint_from [(q - 64 - 32, q - 64)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mS mH) in FR; [| exact MUh| exact WMh| cbn [cells_size csize Nat.add]; apply DJH; clear; lia].
    eapply (rw_cells_transport asegs _ mS mH) in HS; [| exact MUh| exact WMh| cbn [cells_size csize Nat.add]; apply DJH; clear - EM GHI CLO LQ1 RZN RU0; lia].
    pose proof RPS as (_ & _ & _ & _ & (ts & TS)).
    eapply (rw_cells_transport asegs _ mS mH) in TS; [| exact MUh| exact WMh| cbn [cells_size csize Nat.add]; apply DJH; clear - T4 CLO LQ1; lia].
    pose proof (rw_cells_split_CB asegs mH (THR + 2800) [] _ ts [] [24%nat; 8%nat; 8%nat; 328%nat] TS ltac:(reflexivity)) as TSS.
    cbn [mk_CB_cells app] in TSS. clear TS.
    remember (firstn 24 ts) as tsa eqn:Etsa. remember (skipn 24 ts) as ts1 eqn:Ets1. clear Etsa Ets1.
    remember (firstn 8 ts1) as tb1 eqn:E1. remember (skipn 8 ts1) as ts2 eqn:E2. clear E1 E2.
    remember (firstn 8 ts2) as tb2 eqn:E1. remember (skipn 8 ts2) as ts3 eqn:E2. clear E1 E2.
    remember (firstn 328 ts3) as tsb eqn:E1. clear E1.
    apply (rw_cells_CB_C8 asegs mH (THR + 2800) [CB 24 tsa] tb1) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs mH (THR + 2800) [CB 24 tsa; C8 (le_bytes_to_word tb1)] tb2) in TSS. cbn [app] in TSS.
    remember M as M0 eqn:HM0 in HS |- *.
    replace (M0 + 16 + -14) with (M0 + 2) by (clear; lia). replace (M0 + 16 + -12) with (M0 + 4) by (clear; lia).
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - N1; lia); rewrite Z.mod_small by (clear - N1; lia); reflexivity).
    do 2 zstep.
    do 4 zstep.
    hide MU3. hide WM3. hide MUh. hide WMh. hide MUs. hide WMs. hide MU2. hide WM2. hide HS.
    pose proof (munch_refl [(THR + 2800, THR + 3168)] mH) as MUt. pose proof (wmono_refl asegs mH) as WMt.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.

    do 4 zstep.
    do 8 zstep.
    zstep. replace (q - 64 + 64) with q by lia. zstep.
    release_frame FR STH q.
    subst M0.

    unhide MUh. unhide WMh. unhide MU3. unhide WM3.
    assert (MU4 : munch [(q - 96, q - 64); (THR + 2800, THR + 3168)] mS mT).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUh]| eapply munch_weaken; [| exact MUt]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [clear - O1; lia| exact I].
      - split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WMh WMt) as WM4.
    assert (MIT : mem_inv asegs mT) by assumption.
    assert (TS' : exists ts', rw_cells asegs mT (THR + TSTATS_OFF) [CB 368 ts']) by (destruct (rw_cells_forget _ _ _ _ TSS) as [ts' X0]; exists ts'; exact X0).
    pose proof (dr_inv_tstats AL E X H mS mT _ _ _ lo q (q - 96) (q - 64) AO LOH CLO ltac:(clear - LQ1; lia) ltac:(clear; lia) ltac:(clear; lia) INVS MU4 WM4 MIT TS') as INVT.

    set (WT := [(q - 96, q); (M, M + 24); (THR + 2800, THR + 3168)]).
    assert (MUT : munch WT m mT).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]; unfold WT, sub_fp; cbn [outside]; intros xo (O1 & O2 & O3 & _).
      - split; [exact O1|]. split; [exact O2| exact I].
      - split; [clear - O1; lia|]. split; [exact O3| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WMT.
    assert (FWT : Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) WT).
    { unfold WT. constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ1; lia|].
      constructor; [exact (held_blk_geo AL X m ch lo q M 24 AO RP RS HK HA ltac:(clear - HN; lia))|].
      constructor; [| constructor]. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia. }

    assert (HUT : forall A k, qc_hull AL ch A k -> disjoint_from [(THR + 2800, THR + 3168)] A k).
    { intros A k HU. eapply (hull_atouch_dj AL X m lo q [(THR + 2800, THR + 3168)] [] [] ch A k AO LOH CLO RP RS); [constructor| intros d []| | exact HK| intros cv _ []| intros sc _ []| exact HU].
      constructor; [| constructor]. right; right; left. unfold sub_iv. cbn [fst snd]. clear. lia. }
    pose proof (HUT B bs ltac:(left; split; reflexivity)) as HTB. cbn [disjoint_from] in HTB.
    assert (SHBG : 2147450880 <= sh B /\ sh B + bs / 8 <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - GLO GHI GS32 ACR; Z.div_mod_to_equations; lia).
    unhide HS.
    eapply (rw_cells_transport asegs _ mH mT) in HS; [| exact MUt| exact WMt| cbn [cells_size csize Nat.add disjoint_from]; clear - HTB EM RZ16 RZN RU0; lia].
    eapply (rw_cells_transport asegs _ mS mT) in UJ; [| exact MU4| exact WM4|].
    2: { cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_add, K8. cbn [disjoint_from]. clear - HTB EM RZ16 RZN RU0 BS8 GHI CLO LQ1. lia. }
    assert (HDT : rw_cells asegs mT M [CB 4 [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HS| clear; cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app].
      repeat first [ reflexivity | apply (f_equal2 cons); [try reflexivity; apply bv_eq; vm_compute; reflexivity|] ]. }
    assert (UJT : exists j', rw_cells asegs mT (M + 16) [CB (Z.to_nat (bs - rz)) j']).
    { lazymatch type of UJ with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs mT (M + 16) [] cs [] UJ) as UJ' end.
      cbn [app cells_size csize] in UJ'. replace (8 + (k8 + 0))%nat with (Z.to_nat (bs - rz)) in UJ' by (clear - K8 BS8; lia). eexists. exact UJ'. }
    destruct UJT as [j' UJT].
    assert (PREPT : pchunk_rep AL mT ch).
    { eapply (lchunk_freed AL WT m mT ch bits actx _ LFULL WFC GB8 GS8 MUT HDT UJT); fold B bs rz.
      - unfold WT. cbn [disjoint_from]. clear - HTB EM GHI CLO LQ1 RZ16 RZN RU0. lia.
      - unfold WT. cbn [disjoint_from]. assert (S0 : 0 <= bs / 8) by (apply Z.div_pos; [clear - GS32; lia| lia]).
        clear - SHBG S0 LOH LQ1 EM GBAND BS8 RZ16 GLO T3. lia.
      - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|].
        assert (EBS : B = sc_beg sc + 4096) by (unfold B, qc_blk; rewrite EK; reflexivity).
        assert (SHS : sh B = sh (sc_beg sc) + 512) by (rewrite EBS; unfold sh; clear - GB8 EBS; Z.div_mod_to_equations; lia).
        assert (SHSC : 2147450880 <= sh (sc_beg sc)) by (unfold sh, SHADOW_OFF; clear - EBS GLO; Z.div_mod_to_equations; lia).
        pose proof (HUT (sc_beg sc + 32) 4064 ltac:(right; right; rewrite EK; left; split; reflexivity)) as HT3. cbn [disjoint_from] in HT3.
        unfold WT. cbn [disjoint_from]. clear - HT3 EBS SHS SHSC SHBG EM GHI GBAND GLO CLO LOH LQ1 RZ16 BS8 T3. lia. }

    assert (HBP : forall b, In b (glob ++ loc) -> held1 (fst X) (bpair b) /\ ~ In (bpair b) (prim_of ch)).
    { intros b Hb. destruct HOK as [ND FH]. split; [apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb|].
      intros Hc. apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb|]. apply in_or_app. right. apply in_or_app. left. exact Hc. }
    assert (TCHc : Forall (held1 (fst X)) (prim_of ch)).
    { destruct ch as [[c v|sc] rz0 n0]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HK| constructor]. }
    assert (TSIc : incl (sec_of ch) (se_chunks (snd X))).
    { destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
    assert (QLGT : qlist_rep AL mT glob 0).
    { eapply (qlist_rep_other AL X m mT lo q WT _ _ glob 0 AO LOH CLO RP RS TCHc TSIc MUT FWT QLG). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. left. exact Hb. }
    assert (QLLT : qlist_rep AL mT loc 0).
    { eapply (qlist_rep_other AL X m mT lo q WT _ _ loc 0 AO LOH CLO RP RS TCHc TSIc MUT FWT QLL). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. right. exact Hb. }

    unhide GC. unhide TQC. unhide MTX0. unhide CST0. unhide AFM0. unhide SOBJ0. unhide BUF0.
    assert (DJI : forall A k, GSTATS_A + 16 <= A -> A + k <= 6328320 -> disjoint_from WT A k)
      by (intros A k H1 H2; exact (atouch_img_dj AL X m lo q WT _ _ A k AO LOH CLO RP RS TCHc TSIc FWT H1 H2)).
    eapply (rw_cells_transport asegs _ m mT) in GC; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJI; clear; lia].
    eapply (rw_cells_transport asegs _ m mT) in MTX0; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJI; clear; lia].
    eapply (rw_cells_transport asegs _ m mT) in CST0; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJI; clear; lia].
    eapply (rw_cells_transport asegs _ m mT) in AFM0; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add]; apply DJI; clear; lia].
    eapply (rw_cells_transport asegs _ m mT) in TQC; [| exact MUT| exact WMT| cbn [cells_size csize Nat.add];
      exact (atouch_tq_dj AL X m lo q WT _ _ TQ 32 AO LOH CLO RP RS TCHc TSIc FWT ltac:(clear; lia) ltac:(clear; lia))].
    assert (DJQ : forall A k, q <= A -> disjoint_from WT A k).
    { intros A k HA0. unfold WT. cbn [disjoint_from]. clear - HA0 HN GHI CLO LQ1 T4. lia. }
    eapply (rw_cells_transport asegs _ m mT) in SOBJ0; [| exact MUT| exact WMT| apply DJQ; exact QSTK].
    eapply (u64arr_transport asegs _ m mT) in BUF0; [| exact MUT| exact WMT| apply DJQ; exact QTR].
    assert (TE2T : thread_env2 AL mT).
    { eapply (thread_env2_frame_m AL WT m mT TE2 MUT).
      - exact (atouch_thr_dj AL X m lo q WT _ _ THR 8 AO LOH CLO RP RS TCHc TSIc FWT ltac:(left; clear; lia)).
      - exact (atouch_thr_dj AL X m lo q WT _ _ (at_ctx L + 8) 4 AO LOH CLO RP RS TCHc TSIc FWT ltac:(right; clear; lia)). }
    assert (RDT : RDEPOT D hs total mT).
    { eapply (RDEPOT_frame_m AL hs total WT m mT DLO SWB RD MUT).
      - apply DJI; clear; lia.
      - exact (atouch_dreg_dj AL X m lo q WT _ _ (DN0 D) (2^20) AO LOH CLO RP RS TCHc TSIc FWT ltac:(left; clear; lia)).
      - exact (atouch_dreg_dj AL X m lo q WT _ _ (SS0 D) (2^23) AO LOH CLO RP RS TCHc TSIc FWT ltac:(right; clear; lia)). }

    lz_here.
    eapply implA_mono.
    { eapply (qchunk_spec AL E AO gp s10 s11 F_ fc q lo LOH CLO LOQ QH Q16 ra _ _ _ s0 s1 _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 _ _ _ _ X H mT glob loc ch hrest STK TR total hs ws tr);
        [ assumption | exact STH | exact INVT | exact HK | exact WFC | exact PREPT | exact NSC | exact QLGT | unfold qcells; exact GC | split; [exact TQC| exact QLLT]
        | exact MTX0 | exact CST0 | exact AFM0 | exact FWF | exact QB | exact RB | exact CA0 | exact CM0 | exact CM1 | exact LEN32
        | exact TE2T | exact RDT | exact SOBJ0 | exact QSTK | exact STKH | exact BUF0 | exact TRW | exact LENW | exact LTR | exact RNG | exact QTR | exact TRH
        | exact ROOM_N | exact ROOM_F | exact ROOM_T ]. }

    intros u H' ms' PO. unfold qchunk_post in PO |- *. cbv zeta in PO |- *.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & W & hs' & total' & -> & -> & MUp & FWp & REST).
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (WT ++ W), hs', total'.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUT]| eapply munch_weaken; [| exact MUp]]; apply sub_fp_incl.
      - intros iv Hiv. right; right; right. apply in_or_app. left. exact Hiv.
      - intros iv [<-|[<-|[<-|Hiv]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity|]. right; right; right. apply in_or_app. right. exact Hiv. }
    split; [| exact REST].
    apply Forall_app. split; [| exact FWp].
    eapply Forall_impl; [| exact FWT]. intros iv AT. left.
    eapply (atouch_mono AL lo q (fst X) (snd X) _ _ lo q (fst X) (snd X) (prim_of ch) (sec_of ch)); [lia| lia| intros; lia| apply incl_refl| apply incl_appr; apply incl_refl| apply incl_appr; apply incl_refl| exact AT].
  Qed.

  #[using="AO LOH CLO LOQ QH Q16"] Theorem dealloc_spec : forall (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z))
        (STK TR total : Z) (hs : list Z) (ws : list word) (tr : list Z),
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
    thread_env2 AL m -> hooks_env m -> RDEPOT D hs total m ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> q <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->
    implA H (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (qchunk_post AL E gp s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m glob loc ch hrest hs total tr)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) (wz STK) (wz 1) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_free_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m glob loc ch hrest STK TR total hs ws tr
      MC ST INV HK WFC LFULL NSC QLG GC QCL MTX CST AFM FWF QB RB CA0 CM0 CM1 LEN32
      TE2 HKE RD SOBJ QSTK STKH BUF TRW LENW LTR RNG QTR TRH ROOM_N ROOM_F ROOM_T.
    unfold asan_free_entry.
    lz_go.
    do 2 zstep.
    do 2 zstep.
    do 5 zstep.
    zstep.
    lz_here.
    eapply (deallocate_spec ra _ _ _ s0 s1 _ _ s2 s3 s4 s5 s6 s7 s8 s9 _ _ _ _ X H m glob loc ch hrest STK TR total hs ws tr); eassumption.
  Qed.

End DEALLOC.

