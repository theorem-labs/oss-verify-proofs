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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition qput_entry : Z := 0x37964.
Definition PUT_STACK : Z := 80 + ENQ_STACK + DRAIN_STACK.

Section PUT.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
  Hypothesis AO : alayout_ok AL.
  Variables (gp s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z) (stackw : word).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - PUT_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition put_nb_iv (P : prim) (loc : list qbatch) (iv : Z * Z) : Prop :=
    need_batch loc = true /\ (chunk_iv AL K_BCLASS (snd (enq_prim P loc)) iv \/ chunk_sh_iv AL K_BCLASS (snd (enq_prim P loc)) iv).

  Definition put_loc' (P : prim) (loc : list qbatch) (ch : qchunk) : list qbatch := q_enq loc ch (snd (enq_prim P loc)).
  Definition pq_drains (P : prim) (loc : list qbatch) (ch : qchunk) : bool := Q_CACHE <? qbytes (put_loc' P loc ch).
  Definition put_todo (P : prim) (glob loc : list qbatch) (ch : qchunk) : list qbatch :=
    if pq_drains P loc ch then drain_todo (glob ++ put_loc' P loc ch) else [].
  Definition put_glob (P : prim) (glob loc : list qbatch) (ch : qchunk) : list qbatch :=
    if pq_drains P loc ch then drain_rest (glob ++ put_loc' P loc ch) else glob.
  Definition put_loc (P : prim) (loc : list qbatch) (ch : qchunk) : list qbatch :=
    if pq_drains P loc ch then [] else put_loc' P loc ch.

  Definition qput_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk)
      (hrest : list (Z * Z)) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W,
      let P := fst X in let X1 := (fst (enq_prim P loc), snd X) in
      let todo := put_todo P glob loc ch in let gF := put_glob P glob loc ch in let lF := put_loc P loc ch in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X1 todo (H_enq AL P loc H)
      /\ munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) m m'
      /\ Forall (fun iv => atouch AL lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch) iv \/ put_nb_iv P loc iv) W
      /\ dr_inv AL E (dorecycle X1 todo) H' m' (gF ++ lF) (flat_map qb_chunks (gF ++ lF)) hrest
      /\ xle X (dorecycle X1 todo)
      /\ stk asegs m' lo q
      /\ qlist_rep AL m' gF 0 /\ rw_cells asegs m' QUAR_GQ (qcells AL gF) /\ qcache_rep AL m' TQ lF
      /\ rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]]
      /\ (need_batch loc = true -> 0 <= snd (enq_prim P loc) /\ 16 * snd (enq_prim P loc) + Q_BBYTES <= FA_OFF)
      /\ (need_batch loc = true -> held_ok (fst (enq_prim P loc)) ((K_BCLASS, snd (enq_prim P loc)) :: prim_of ch ++ hrest)
                                   /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim P loc)) c))).

  #[using="AO LOH CLO LOQ QH Q16"] Theorem qput_spec : forall (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (ch : qchunk) (hrest : list (Z * Z)),
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
    implA H (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (qput_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m glob loc ch hrest)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz QUAR) (wz TQ) (wz CACHE) stackw (wz (qc_hdr AL ch)) (wz (qc_n ch)) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz qput_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m glob loc ch hrest
      MC ST INV HK WFC PREP NSC QLG GC QCL MTX CST AFM FWF QB RB CA0 CM0 CM1 LEN32.
    unfold qput_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ1 : lo <= q - 80 - ENQ_STACK) by (unfold PUT_STACK, DRAIN_STACK, QREC_STACK, DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    assert (LQ2 : lo <= q - 80 - DRAIN_STACK) by (unfold PUT_STACK, ENQ_STACK, REFILL_STACK, POP_STACK, MF_STACK in LOQ; lia).
    assert (LQ3 : lo <= q - 80 - 64) by (unfold ENQ_STACK, REFILL_STACK, POP_STACK, MF_STACK in LQ1; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof PE as PEc. pe_split PEc.
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL X m ch AO RP RS HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    unfold qcells in GC. hide GC.
    pose proof (munch_refl [(q - 80, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 80%nat ST.
    do 8 zstep.
    zstep.
    do 2 zstep.
    zstep.
    zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. lia. } clear K0.
    zstep.
    zstep. if_cases KM; zify_cond KM; [| exfalso; clear - KM N1; lia]. clear KM.
    do 3 zstep.
    do 2 zstep.
    zstep.

    zstep. if_cases KF; zify_cond KF; [| exfalso; revert KF; clear; intros KF; rewrite ?unsigned_lit in KF by lia; cbn in KF; lia]. clear KF.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -80) with (q - 80) in * by lia.
    pose proof PREP as ((bits & actx & HD) & _).
    set (B := qc_blk AL ch) in *. set (rz := qc_rz ch) in *. set (bs := qc_bsize ch) in *. set (n := qc_n ch) in *.
    assert (EM : qc_hdr AL ch = B + rz - 16) by reflexivity.
    set (M := qc_hdr AL ch) in *.
    assert (RU0 : 0 <= rup8 n /\ rup8 n mod 8 = 0 /\ n <= rup8 n) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    eapply (rw_cells_transport asegs _ m mA) in HD; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from]; clear - EM RZ16 RZN RU0 GHI CLO LQ3; lia].
    assert (HS : rw_cells asegs mA M [CB 2 [Z_to_bv 8 3; bits]; C2 (wz 0); C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HD| cbn; tauto| | reflexivity]. cbn [cells_bytes cbytes app].
      repeat first [ reflexivity | apply (f_equal2 cons); [try reflexivity; apply bv_eq; vm_compute; reflexivity|] ]. }
    remember M as M0 eqn:HM0 in HS |- *.
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - N1; lia); rewrite Z.mod_small by (clear - N1; lia); reflexivity).
    do 3 zstep.
    rewrite Z.lor_0_l.
    do 2 zstep.
    replace (Z.land (n + 7) 18446744073709551608) with (rup8 n).
    2: { rewrite land_m8 by (clear - N1; lia). unfold rup8. clear. Z.div_mod_to_equations. lia. }
    do 2 zstep.
    zstep.
    subst M0.

    assert (M8 : (M + 16) mod 8 = 0) by (rewrite EM; clear - GB8 RZM; Z.div_mod_to_equations; lia).
    destruct RU0 as (RU0 & RU8 & RUN).
    assert (PEA : poison_env E mA).
    { eapply poison_env_frame; [exact PE| exact MU| exact WM|]. unfold above_img. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ3. lia. }
    pose proof PREP as (_ & _ & _ & _ & (sj & SHU) & _). fold M n in SHU.
    assert (SHG : 2147450880 <= sh (M + 16) /\ sh (M + 16) + rup8 n / 8 <= 17594333495296)
      by (unfold sh, SHADOW_OFF; rewrite EM; clear - GLO GHI RZ16 RZN RU0 ACR; Z.div_mod_to_equations; lia).
    eapply (rw_cells_transport asegs _ m mA) in SHU; [| exact MU| exact WM| cbn [cells_size csize disjoint_from]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia); clear - SHG LOH LQ3; lia].
    eapply evt_cut.
    { eapply (poison_shadow_spec_all E _ gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F_ fc (q - 80) lo (M + 16) (rup8 n) 253 mA).
      - assumption.
      - clear - LOH LQ3 QH; lia.
      - split; [exact M8|]. split; [exact RU8|]. split; [exact RU0|]. split; [| lia].
        unfold poison_range. rewrite EM. clear - GLO GHI GBAND RZ16 RZN RU0 RUN N1 ACR. lia.
      - exact PEA.
      - exact ST.
      - exact SHU. }
    cbv beta. unfold poison_post.
    intros msP (p5 & p6 & p7 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & mP & -> & MUp & WMp & MIP & STP & PEP & SHP).

    set (WP := [(q - 144, q); (sh (M + 16), sh (M + 16) + rup8 n / 8)]).
    assert (MU2 : munch WP m mP).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUp]]; unfold WP, sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [clear - O1; lia| exact I].
      - split; [clear - O1; lia|]. split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM WMp) as WM2.
    assert (EBM : M + 16 = B + rz) by (rewrite EM; lia).
    assert (SHA : sh (M + 16) = sh B + rz / 8) by (rewrite EBM; apply sh_add8; [exact GB8| clear - RZM; Z.div_mod_to_equations; lia]).
    assert (SHE : sh (M + 16 + rup8 n) = sh (M + 16) + rup8 n / 8) by (apply sh_add8; [exact M8| exact RU8]).
    assert (SHBG : 2147450880 <= sh B /\ sh B + bs / 8 <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - GLO GHI GS32 ACR; Z.div_mod_to_equations; lia).
    assert (SHT : sh (M + 16) + rup8 n / 8 <= sh B + bs / 8).
    { rewrite SHA. clear - RZN RZM RU8 GS8 RU0 RZ16. Z.div_mod_to_equations. lia. }
    assert (R8 : 0 <= rup8 n / 8) by (apply Z.div_pos; lia).
    assert (QREP : qchunk_rep AL mP ch).
    { eapply (pchunk_poisoned AL WP m mP ch PREP MU2 WM2); fold M n B rz bs.
      - exact SHP.
      - exact RZ16.
      - clear - RZN RU0; lia.
      - exact RU0.
      - apply Z.div_pos; [clear - RZN; lia| lia].
      - unfold WP. cbn [disjoint_from]. clear - GHI GBAND SHG CLO LQ3. lia.
      - unfold WP. cbn [disjoint_from]. clear - SHA SHG R8 LOH LQ3. lia.
      - unfold WP. cbn [disjoint_from]. rewrite SHE. assert (T8 : 0 <= (bs - rz - rup8 n) / 8) by (apply Z.div_pos; [clear - RZN; lia| lia]).
        assert (TE8 : sh (M + 16) + rup8 n / 8 + (bs - rz - rup8 n) / 8 <= sh B + bs / 8) by (rewrite SHA; clear - RZN RZM RU8 GS8 RU0 RZ16; Z.div_mod_to_equations; lia).
        clear - T8 TE8 SHBG LOH LQ3. lia.
      - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|].
        assert (EBS : B = sc_beg sc + 4096) by (unfold B, qc_blk; rewrite EK; reflexivity).
        assert (SHS : sh B = sh (sc_beg sc) + 512) by (rewrite EBS; unfold sh; clear - GB8 EBS; Z.div_mod_to_equations; lia).
        assert (RZ8 : 0 <= rz / 8) by (apply Z.div_pos; lia).
        unfold WP. cbn [disjoint_from]. clear - EBS SHS SHA SHG RZ8 R8 GHI GBAND GLO CLO LOH LQ3 GS32. lia. }
    assert (INVP : dr_inv AL E X H mP (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) (prim_of ch ++ hrest)).
    { eapply (dr_inv_poison AL E X H m mP _ _ hrest ch lo q (q - 144) q (sh (M + 16)) (rup8 n / 8) AO LOH CLO INV HK WFC NSC MU2 WM2 MIP); fold B bs.
      - clear - LQ3; lia.
      - lia.
      - rewrite SHA. clear - RZ16. Z.div_mod_to_equations. lia.
      - exact SHT. }

    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    assert (DJP : forall A k, (q - 80 <= A \/ (A + k <= 2147450880 /\ 0 <= A)) -> disjoint_from [(q - 80 - 64, q - 80); (sh (M + 16), sh (M + 16) + rup8 n / 8)] A k)
      by (intros A k HA; cbn [disjoint_from]; clear - HA SHG LOH LQ3; lia).
    eapply (rw_cells_transport asegs _ mA mP) in FR; [| exact MUp| exact WMp| apply DJP; left; lia].
    eapply (rw_cells_transport asegs _ mA mP) in MTX; [| exact MUp| exact WMp| apply DJP; right; cbn [cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport asegs _ mA mP) in CST; [| exact MUp| exact WMp| apply DJP; right; cbn [cells_size csize Nat.add]; lia].
    unhide GC.
    eapply (rw_cells_transport asegs _ m mP) in GC; [| exact MU2| exact WM2| unfold WP; cbn [cells_size csize Nat.add disjoint_from]; clear - SHG LOH LQ3; lia].
    destruct QCL as [TQC QLL]. unfold qcells in TQC.
    eapply (rw_cells_transport asegs _ m mP) in TQC; [| exact MU2| exact WM2| unfold WP; cbn [cells_size csize Nat.add disjoint_from]; clear - SHG LOH LQ3 T3 T4 CLO; lia].
    destruct (held_sh_geo AL X m ch AO RP RS HK WFC) as (_ & _ & SGC). fold B bs in SGC.
    assert (FWP : Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) WP).
    { unfold WP. constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ3; lia|]. constructor; [| constructor].
      apply SGC; [rewrite SHA; clear - RZ16; Z.div_mod_to_equations; lia| exact SHT]. }
    assert (TCHc : Forall (held1 (fst X)) (prim_of ch)).
    { destruct ch as [[c v|sc] rz0 n0]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HK| constructor]. }
    assert (TSIc : incl (sec_of ch) (se_chunks (snd X))).
    { destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
    assert (HBP : forall b, In b (glob ++ loc) -> held1 (fst X) (bpair b) /\ ~ In (bpair b) (prim_of ch)).
    { intros b Hb. destruct HOK as [ND FH]. split; [apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb|].
      intros Hc. apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb|]. apply in_or_app. right. apply in_or_app. left. exact Hc. }
    assert (QLGP : qlist_rep AL mP glob 0).
    { eapply (qlist_rep_other AL X m mP lo q WP _ _ glob 0 AO LOH CLO RP RS TCHc TSIc MU2 FWP QLG). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. left. exact Hb. }
    assert (QLLP : qlist_rep AL mP loc 0).
    { eapply (qlist_rep_other AL X m mP lo q WP _ _ loc 0 AO LOH CLO RP RS TCHc TSIc MU2 FWP QLL). apply Forall_forall. intros b Hb. apply HBP. apply in_or_app. right. exact Hb. }
    replace (ret_pc (Z_to_bv 64 228080)) with (Z_to_bv 64 228080) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    do 5 zstep.
    zstep.

    pose proof INVP as (RPP & POKP & RSP & _ & PEP' & TEP & SVP & _ & _ & _ & HOKP & _).
    set (hs := map bpair (glob ++ loc) ++ flat_map prim_of (flat_map qb_chunks (glob ++ loc)) ++ prim_of ch ++ hrest) in *.
    assert (Q16' : (q - 80) mod 16 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
    assert (INCL : incl (map (fun b => (K_BCLASS, qb_v b)) loc) hs).
    { intros cv Hcv. unfold hs. apply in_or_app. left. rewrite map_app. apply in_or_app. right. exact Hcv. }
    assert (NDVL : List.NoDup (map qb_v loc)).
    { destruct HOKP as [ND _]. apply NoDup_app_remove_r in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
      unfold bpair in ND. rewrite <- (map_map qb_v (fun v => (K_BCLASS, v))) in ND. apply NoDup_map_inv in ND. exact ND. }
    assert (CNTL : Forall (fun b => 1 <= qb_count b <= Q_BATCH) loc).
    { apply Forall_app in FWF as [_ FWL]. eapply Forall_impl; [| exact FWL]. intros b (_ & _ & W3 & _). exact W3. }
    lz_here.
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (enqueue_spec AL E (refill_spec AL E) (RPRIM_pop AL AO) (RPRIM_frame AL AO) (wz 228104) gp (wz QUAR) (wz TQ) (wz n) stackw (wz CACHE) (wz M) (wz Q_CACHE) s7 s8 s9 s10 s11
                F_ fc (q - 80) lo mP H (fst X) loc ch hs);
        [ exact AO | exact MIP | assumption | exact SVP | exact PEP' | exact TEP | exact STP | exact LOH | exact CLO | exact LQ1 | clear - QH; lia | exact Q16'
        | exact RPP | exact POKP | exact RB | exact CA0 | exact CM0 | exact CM1 | exact HOKP | exact INCL | exact NDVL | exact CNTL | exact LEN32
        | exact (conj TQC QLLP) | exact WFC ]. }
    intros u H1 ms1 [PO MC1]. unfold enqueue_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & -> & MU3 & WM3 & MI1 & ST1 & PE1 & TE1 & SV1 & RPN & POKN & HOKN & QC1 & WFK).
    clean_ms_mem MC1.

    set (P := fst X) in *. set (PN := fst (enq_prim P loc)) in *. set (VN := snd (enq_prim P loc)) in *. set (loc' := q_enq loc ch VN) in *.
    assert (LQ80 : lo <= q - 80) by (clear - LQ3; lia).
    destruct (dr_inv_enqueue AL E X H _ mP m1 glob loc ch hrest lo (q - 80) AO LOH CLO LQ80 INVP HK WFC QREP NSC QLGP MU3 WM3 MI1 PE1 TE1 SV1 RPN POKN HOKN QC1 WFK) as [INV1 QLG1].
    fold P PN VN loc' in INV1.

    assert (HBLL : forall b, In b loc -> held1 (fst X) (bpair b)) by (intros b Hb; apply HBP; apply in_or_app; right; exact Hb).
    pose proof (enq_W_class AL X mP loc lo (q - 80) AO LQ80 RPP RSP HBLL WFK) as FWE.
    assert (NBH : need_batch loc = true -> held1 PN (K_BCLASS, snd (enq_prim (fst X) loc)) /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls PN c))).
    { intros NB. rewrite NB in HOKN. destruct HOKN as [_ FHN]. split; [exact (Forall_inv FHN)|].
      destruct RPN as (_ & _ & CLSN & _). intros c Hc. exact (proj1 (CLSN c Hc)). }
    assert (DJE : forall A k, (GSTATS_A + 16 <= A /\ A + k <= 6328320) \/ q - 80 <= A -> disjoint_from (enq_W AL (q - 80) lo (fst X) loc) A k)
      by (intros A k HA; exact (enq_class_dj AL X mP loc lo (q - 80) _ PN A k AO LOH CLO LQ80 RPP RSP HBLL NBH FWE HA)).
    eapply (rw_cells_transport asegs _ mP m1) in FR; [| exact MU3| exact WM3| apply DJE; right; lia].
    eapply (rw_cells_transport asegs _ mP m1) in MTX; [| exact MU3| exact WM3| apply DJE; left; cbn [cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport asegs _ mP m1) in CST; [| exact MU3| exact WM3| apply DJE; left; cbn [cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport asegs _ mP m1) in GC; [| exact MU3| exact WM3| apply DJE; left; cbn [cells_size csize Nat.add]; lia].
    pose proof QC1 as [TQC1 QLL1]. fold P VN loc' in TQC1, QLL1. unfold qcells in TQC1.
    lz_go.
    replace (ret_pc (Z_to_bv 64 228104)) with (Z_to_bv 64 228104) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    zstep. if_cases KDR; zify_cond KDR.

    2: {
      assert (QBL : 0 <= qbytes loc' < 2^56).
      { unfold loc'. rewrite q_enq_bytes. apply Forall_app in FWF as [FWG FWL].
        assert (QG0 : 0 <= qbytes glob) by (apply qbytes_nonneg; eapply Forall_impl; [| exact FWG]; intros b (_ & _ & _ & W4 & W5); rewrite W4;
          assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun c acc => qc_n c + acc) 0 l) by (induction 1 as [|c l (_ & _ & N1' & _) _ IHl]; cbn [fold_right]; lia);
          pose proof (S0 _ W5); lia).
        assert (QL0 : 0 <= qbytes loc) by (apply qbytes_nonneg; eapply Forall_impl; [| exact FWL]; intros b (_ & _ & _ & W4 & W5); rewrite W4;
          assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun c acc => qc_n c + acc) 0 l) by (induction 1 as [|c l (_ & _ & N1' & _) _ IHl]; cbn [fold_right]; lia);
          pose proof (S0 _ W5); lia).
        rewrite qbytes_app in QB. fold n. destruct (need_batch loc); clear - QB QG0 QL0 N1; lia. }
      rewrite Z.mod_small in KDR by (clear - QBL; lia).
      assert (PD : pq_drains P loc ch = false) by (unfold pq_drains, put_loc'; fold VN loc'; apply Z.ltb_ge; clear - KDR; lia).
      zstep.
      do 8 zstep.
      zstep. replace (q - 80 + 80) with q by lia. zstep.
      release_frame FR ST1 q.
      unfold put_todo. rewrite PD. cbn [t_dorecycle].
      lz_ret. apply evt_done. unfold qput_post. cbv zeta. fold P. unfold put_todo, put_glob, put_loc. rewrite PD. cbn [H_dorecycle dorecycle]. fold PN.
      destruct (enq_W_parts AL X mP loc lo (q - 80) AO LQ80 RPP RSP HBLL WFK) as [FW1 FWN]. fold P in FW1, FWN.
      do 15 eexists. exists m1, (WP ++ enq_W1 AL lo (q - 80) P loc ++ qlast_iv AL loc ++ enq_NBI AL P loc).
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; apply sub_fp_incl.
        - intros iv Hiv. right; right; right. apply in_or_app. left. exact Hiv.
        - rewrite (enq_W_eq AL lo (q - 80) P loc). intros iv Hiv.
          apply in_app_or in Hiv as [Hiv|Hiv]; [right; right; right; apply in_or_app; right; apply in_or_app; left; exact Hiv|].
          apply in_app_or in Hiv as [[<-|[]]|Hiv]; [right; right; left; reflexivity|].
          right; right; right. apply in_or_app. right. apply in_or_app. right. exact Hiv. }
      split.
      { apply Forall_app. split.
        - eapply Forall_impl; [intros iv A; left; exact A|].
          eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo q (fst X) (snd X) _ _ WP); [lia| lia| intros; lia| apply incl_refl| apply incl_appr; apply incl_refl| apply incl_appr; apply incl_refl| exact FWP].
        - rewrite app_assoc. apply Forall_app. split.
          + eapply Forall_impl; [intros iv A; left; exact A|].
            eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 80) (fst X) (snd X) (map bpair loc) [] _); [lia| lia| intros; lia| apply incl_refl| | intros d []| exact FW1].
            intros cv Hcv. apply in_or_app. left. unfold tc_of. apply in_or_app. left. rewrite map_app. apply in_or_app. right. exact Hcv.
          + eapply Forall_impl; [| exact FWN]. intros iv [NB CI]. right. split; [exact NB| left; exact CI]. }
      split; [exact INV1|].
      split.
      { split; [| apply incl_refl]. intros c Hc. cbn [fst]. pose proof RPP as (LENP & _). destruct (clear_ctx AL X mP RPP RSP) as (WF0P & _).
        exact (enq_prim_au P loc c LENP WF0P Hc WFK). }
      split; [exact ST1|]. split; [exact QLG1|]. split; [unfold qcells; exact GC|]. split; [exact QC1|]. split; [exact MTX|]. split.
        { intros NB. destruct (NBH NB) as [HN WFN]. pose proof (held_geo AL PN AO WFN K_BCLASS _ HN) as GN. cbv zeta in GN. destruct GN as (_ & GN1 & GN2 & GN3 & _).
        change (class_size K_BCLASS) with 8192 in GN2. fold P VN in GN1, GN2 |- *. change Q_BBYTES with 8192. clear - GN1 GN2 GN3. lia. }
        intros NB. pose proof HOKN as HOKc. rewrite NB in HOKc. destruct HOKc as [NDc FHc]. fold P PN VN. split; [split|].
        + apply NoDup_cons_iff in NDc as [NI ND']. constructor; [intros IN; apply NI; apply in_or_app; right; apply in_or_app; right; exact IN|].
          apply NoDup_app_remove_l in ND'. apply NoDup_app_remove_l in ND'. exact ND'.
        + apply Forall_cons_iff in FHc as [F1 F2]. constructor; [exact F1|]. apply Forall_app in F2 as [_ F2]. apply Forall_app in F2 as [_ F2]. exact F2.
        + destruct RPN as (_ & _ & CLSN & _). intros c Hc. exact (proj1 (CLSN c Hc)). }

    assert (QBL : 0 <= qbytes loc' /\ qbytes glob + qbytes loc' < 2^56 /\ 0 <= qbytes glob).
    { unfold loc'. rewrite q_enq_bytes. pose proof FWF as FWFc. apply Forall_app in FWFc as [FWG FWL].
      assert (QG0 : 0 <= qbytes glob) by (apply qbytes_nonneg; eapply Forall_impl; [| exact FWG]; intros b (_ & _ & _ & W4 & W5); rewrite W4;
        assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun c acc => qc_n c + acc) 0 l) by (induction 1 as [|c l (_ & _ & N1' & _) _ IHl]; cbn [fold_right]; lia);
        pose proof (S0 _ W5); lia).
      assert (QL0 : 0 <= qbytes loc) by (apply qbytes_nonneg; eapply Forall_impl; [| exact FWL]; intros b (_ & _ & _ & W4 & W5); rewrite W4;
        assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun c acc => qc_n c + acc) 0 l) by (induction 1 as [|c l (_ & _ & N1' & _) _ IHl]; cbn [fold_right]; lia);
        pose proof (S0 _ W5); lia).
      rewrite qbytes_app in QB. fold n. destruct (need_batch loc); clear - QB QG0 QL0 N1; lia. }
    destruct QBL as (QBL0 & QBL1 & QG0).
    rewrite Z.mod_small in KDR by (clear - QBL0 QBL1 QG0; lia).
    assert (PD : pq_drains P loc ch = true) by (unfold pq_drains, put_loc'; fold VN loc'; apply Z.ltb_lt; exact KDR).
    assert (FWF' : Forall qbatch_wf (glob ++ loc')).
    { pose proof FWF as FWFc. apply Forall_app in FWFc as [FWG FWL]. apply Forall_app. split; [exact FWG|]. unfold loc'. apply q_enq_wf; [exact FWL| exact WFC|].
      intros NB. destruct (NBH NB) as [(_ & V0 & _ & VAL & _) _]. cbn [fst snd] in V0, VAL. change (class_size K_BCLASS) with 8192 in VAL. fold P VN in V0, VAL. split; assumption. }
    do 2 zstep.
    do 2 zstep.
    zstep.
    unfold put_todo. rewrite PD. fold P VN loc'. change (put_loc' P loc ch) with loc'.
    lz_here.
    rewrite <- (ebind_ret_r (t_dorecycle AL (PN, snd X) (drain_todo (glob ++ loc')))).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (drain_spec AL E AO gp s10 s11 F_ fc (q - 80) lo stackw LOH CLO LQ2 ltac:(clear - QH; lia) Q16' (wz 227904) _ _ _ (wz QUAR) (wz TQ) _ _ _ _ (wz n) stackw (wz CACHE) (wz M) (wz Q_CACHE) s7 s8 s9 _ _ _ _
                (PN, snd X) _ m1 glob loc' hrest);
        [ assumption | exact ST1 | exact INV1 | exact QLG1 | unfold qcells; exact GC | exact QLL1 | unfold qcells; exact TQC1 | exact MTX | exact CST | exact FWF'
        | rewrite qbytes_app; exact QBL1 ]. }
    intros u2' H2 ms2 [PO MC2]. unfold drain_post in PO. cbv zeta in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & W2 & -> & -> & MU4 & FW4 & INV2 & XL2 & ST2 & QL2 & GC2 & TC2 & MTX2).
    clean_ms_mem MC2.

    set (gl' := glob ++ loc') in *. set (X1 := (PN, snd X)) in *.
    pose proof INV1 as (RP1 & _ & RS1 & _ & _ & _ & _ & _ & _ & _ & [ND1 FH1] & _).
    assert (TCH1 : Forall (held1 (fst X1)) (tc_of gl')).
    { apply Forall_forall. intros cv Hcv. apply (proj1 (Forall_forall _ _) FH1). unfold tc_of in Hcv.
      apply in_app_or in Hcv as [Hcv|Hcv]; [apply in_or_app; left; exact Hcv| apply in_or_app; right; apply in_or_app; left; exact Hcv]. }
    assert (TSI1 : incl (tsc_of gl') (se_chunks (snd X1))).
    { destruct (dr_inv_tc AL E X1 _ m1 gl' (flat_map qb_chunks gl') [] hrest ltac:(rewrite app_nil_r; exact INV1)) as [_ TSI]. exact TSI. }
    assert (DJ2 : forall A k, q - 80 <= A -> disjoint_from ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W2) A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA LOH LQ80; lia|]. split; [clear - HA LOH LQ80; lia|]. split; [clear - HA T3 T4 CLO LQ80; lia|].
      exact (atouch_above AL X1 m1 lo (q - 80) W2 _ _ A k AO LOH CLO LQ80 RP1 RS1 TCH1 TSI1 FW4 HA). }
    eapply (rw_cells_transport_m _ m1 m2) in FR; [| exact MU4| apply DJ2; lia].
    lz_go.
    replace (ret_pc (Z_to_bv 64 227904)) with (Z_to_bv 64 227904) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    do 8 zstep.
    zstep. replace (q - 80 + 80) with q by lia. zstep.
    release_frame FR ST2 q.
    lz_ret. apply evt_done. unfold qput_post. cbv zeta. fold P. unfold put_todo, put_glob, put_loc. rewrite PD. fold PN VN. change (put_loc' P loc ch) with loc'. fold gl' X1.
    rewrite app_nil_r.
    destruct (enq_W_parts AL X mP loc lo (q - 80) AO LQ80 RPP RSP HBLL WFK) as [FW1 FWN]. fold P in FW1, FWN.
    do 15 eexists. exists m2, ((WP ++ enq_W1 AL lo (q - 80) P loc ++ qlast_iv AL loc ++ enq_NBI AL P loc) ++ W2).
    split; [reflexivity|]. split; [reflexivity|].

    assert (XL1 : xle X X1).
    { split; [| apply incl_refl]. intros c Hc. unfold X1. cbn [fst]. pose proof RPP as (LENP & _). destruct (clear_ctx AL X mP RPP RSP) as (WF0P & _).
      exact (enq_prim_au P loc c LENP WF0P Hc WFK). }
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]]; apply sub_fp_incl.
      - intros iv Hiv. right; right; right. apply in_or_app. left. apply in_or_app. left. exact Hiv.
      - rewrite (enq_W_eq AL lo (q - 80) P loc). intros iv Hiv.
        apply in_app_or in Hiv as [Hiv|Hiv]; [right; right; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hiv|].
        apply in_app_or in Hiv as [[<-|[]]|Hiv]; [right; right; left; reflexivity|].
        right; right; right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hiv.
      - intros iv [<-|[<-|[<-|Hiv]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity|].
        right; right; right. apply in_or_app. right. exact Hiv. }
    split.
    { apply Forall_app. split.
      - apply Forall_app. split.
        + eapply Forall_impl; [intros iv A; left; exact A|].
          eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo q (fst X) (snd X) _ _ WP); [lia| lia| intros; lia| apply incl_refl| apply incl_appr; apply incl_refl| apply incl_appr; apply incl_refl| exact FWP].
        + rewrite app_assoc. apply Forall_app. split.
          * eapply Forall_impl; [intros iv A; left; exact A|].
            eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 80) (fst X) (snd X) (map bpair loc) [] _); [lia| lia| intros; lia| apply incl_refl| | intros d []| exact FW1].
            intros cv Hcv. apply in_or_app. left. unfold tc_of. apply in_or_app. left. rewrite map_app. apply in_or_app. right. exact Hcv.
          * eapply Forall_impl; [| exact FWN]. intros iv [NB CI]. right. split; [exact NB| left; exact CI].
      - eapply Forall_impl; [| exact FW4]. intros iv AT.
        destruct (atouch_split AL (need_batch loc = true) lo q (fst X) (snd X) (tc_of (glob ++ loc) ++ prim_of ch) (tsc_of (glob ++ loc) ++ sec_of ch)
                    lo (q - 80) (fst X1) (snd X1) (tc_of gl') (tsc_of gl') (K_BCLASS, VN) iv ltac:(lia) ltac:(lia) (proj1 XL1) (proj2 XL1)) as [A|[NB A]]; [| | exact AT| left; exact A| right; split; [exact NB| exact A]].
        + intros cv Hcv.
          assert (EBPL : map bpair loc' = map bpair loc ++ (if need_batch loc then [(K_BCLASS, VN)] else [])).
          { unfold bpair. rewrite <- !(map_map qb_v (fun v => (K_BCLASS, v))). unfold loc'. rewrite q_enq_vs, map_app. destruct (need_batch loc); reflexivity. }
          assert (NBC : In cv (if need_batch loc then [(K_BCLASS, VN)] else []) -> need_batch loc = true /\ cv = (K_BCLASS, VN))
            by (destruct (need_batch loc); [intros [<-|[]]; split; reflexivity| intros []]).
          unfold tc_of, gl' in Hcv. rewrite map_app, EBPL in Hcv. unfold loc' in Hcv. rewrite !flat_map_app, q_enq_chunks, flat_map_app in Hcv. cbn [flat_map] in Hcv. rewrite app_nil_r in Hcv.
          unfold tc_of. rewrite !map_app, !flat_map_app. rewrite !in_app_iff in Hcv. rewrite !in_app_iff. clear - Hcv NBC. tauto.
        + intros sc Hsc. unfold tsc_of, gl' in Hsc. unfold loc' in Hsc. rewrite !flat_map_app, q_enq_chunks, flat_map_app in Hsc. cbn [flat_map] in Hsc. rewrite app_nil_r in Hsc.
          unfold tsc_of. rewrite !flat_map_app. rewrite !in_app_iff in Hsc. rewrite !in_app_iff. clear - Hsc. tauto. }
    split; [exact INV2|]. split; [exact (xle_trans _ _ _ XL1 XL2)|]. split; [exact ST2|]. split; [exact QL2|]. split; [exact GC2|].
    split; [split; [exact TC2| exact I]|]. split; [exact MTX2|]. split.
    { intros NB. destruct (NBH NB) as [HN WFN]. pose proof (held_geo AL PN AO WFN K_BCLASS _ HN) as GN. cbv zeta in GN. destruct GN as (_ & GN1 & GN2 & GN3 & _).
    change (class_size K_BCLASS) with 8192 in GN2. fold P VN in GN1, GN2 |- *. change Q_BBYTES with 8192. clear - GN1 GN2 GN3. lia. }
    intros NB. pose proof HOKN as HOKc. rewrite NB in HOKc. destruct HOKc as [NDc FHc]. fold P PN VN. split; [split|].
    + apply NoDup_cons_iff in NDc as [NI ND']. constructor; [intros IN; apply NI; apply in_or_app; right; apply in_or_app; right; exact IN|].
      apply NoDup_app_remove_l in ND'. apply NoDup_app_remove_l in ND'. exact ND'.
    + apply Forall_cons_iff in FHc as [F1 F2]. constructor; [exact F1|]. apply Forall_app in F2 as [_ F2]. apply Forall_app in F2 as [_ F2]. exact F2.
    + destruct RPN as (_ & _ & CLSN & _). intros c Hc. exact (proj1 (CLSN c Hc)).
  Qed.

  #[using="Type"] Lemma drain_sel_todo : forall glob loc1, snd (q_drain_sel (mkAQ loc1 glob)) = drain_todo (glob ++ loc1).
  Proof.
    intros glob loc1. unfold q_drain_sel, drain_todo, q_transfer. cbn [q_glob q_loc].
    destruct (Q_MAX <? qbytes (glob ++ loc1)); [| reflexivity]. destruct (q_recycle_sel (glob ++ loc1)). reflexivity.
  Qed.
  #[using="Type"] Lemma drain_sel_rest : forall glob loc1, fst (q_drain_sel (mkAQ loc1 glob)) = mkAQ [] (drain_rest (glob ++ loc1)).
  Proof.
    intros glob loc1. unfold q_drain_sel, drain_rest, q_transfer. cbn [q_glob q_loc].
    destruct (Q_MAX <? qbytes (glob ++ loc1)); [| reflexivity]. destruct (q_recycle_sel (glob ++ loc1)). reflexivity.
  Qed.
  #[using="Type"] Lemma put_tree_eq : forall X glob loc ch,
    t_put AL X (mkAQ loc glob) ch
    = ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)).
  Proof.
    intros X glob loc ch. unfold t_put, put_todo, pq_drains, put_loc', AQuarM.put_drains, q_put_enq, t_drain. cbn [q_loc q_glob fst snd].
    f_equal. apply functional_extensionality. intros _.
    destruct (Q_CACHE <? qbytes (q_enq loc ch (snd (enq_prim (fst X) loc)))); [rewrite drain_sel_todo; reflexivity| reflexivity].
  Qed.
  #[using="Type"] Lemma put_state_eq : forall X glob loc ch,
    q_put X (mkAQ loc glob) ch
    = (dorecycle (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch), mkAQ (put_loc (fst X) loc ch) (put_glob (fst X) glob loc ch)).
  Proof.
    intros X glob loc ch. unfold q_put, put_todo, put_loc, put_glob, pq_drains, put_loc', AQuarM.put_drains, q_put_enq, q_drain. cbn [q_loc q_glob fst snd].
    destruct (Q_CACHE <? qbytes (q_enq loc ch (snd (enq_prim (fst X) loc)))); [| reflexivity].
    pose proof (drain_sel_todo glob (q_enq loc ch (snd (enq_prim (fst X) loc)))) as ET. pose proof (drain_sel_rest glob (q_enq loc ch (snd (enq_prim (fst X) loc)))) as ER.
    destruct (q_drain_sel (mkAQ (q_enq loc ch (snd (enq_prim (fst X) loc))) glob)) as [Q1 todo]. cbn [fst snd] in ET, ER. subst Q1 todo. reflexivity.
  Qed.
  #[using="Type"] Lemma put_H_eq : forall X glob loc ch H,
    H_put AL X (mkAQ loc glob) ch H = H_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch) (H_enq AL (fst X) loc H).
  Proof.
    intros X glob loc ch H. unfold H_put, put_todo, pq_drains, put_loc', AQuarM.put_drains, q_put_enq, H_drain. cbn [q_loc q_glob fst snd].
    destruct (Q_CACHE <? qbytes (q_enq loc ch (snd (enq_prim (fst X) loc)))); [rewrite drain_sel_todo; reflexivity| reflexivity].
  Qed.
End PUT.

