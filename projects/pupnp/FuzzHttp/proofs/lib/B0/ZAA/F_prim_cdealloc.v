(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame APrimDealloc
                        F_prim_icd F_prim_efa F_prim_rta F_prim_rta2 F_prim_drain ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma ebind_none {Ev} : forall (t : itree Ev (exc unit)), ebind t (fun _ => Ret (Ok tt)) = t.
Proof. intros t. rewrite <- (ebind_ret_r t) at 2. f_equal. apply functional_extensionality. intros []. reflexivity. Qed.

Lemma set_nth_twice : forall {A} (l : list A) i x y, set_nth i x (set_nth i y l) = set_nth i x l.
Proof. induction l as [|h0 t IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Section CDP.
  Context {HC : HasCeiling}.
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q CB : Z) (m0 : mem).

  #[using="Type"] Lemma cd_push : forall lo c cnt csz calloc spacebeg v (maxc : word) (ws : list word)
      (x1 t0 t1 t2 x8 x9 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0o s1o s2o s3o s4o : word),
    mem_inv asegs m0 -> 1 <= c <= 31 -> 0 <= cnt < 16 -> 0 <= csz < 2^32 ->
    0 <= spacebeg -> spacebeg + 2^37 <= 2^47 -> 0 <= v -> 16 * v < 2^32 ->
    CB mod 8 = 0 -> 0 < CB -> (CB + 2592 <= 0x10000 \/ 0x609000 <= CB) -> CB + 2592 <= lo -> alloc_ceiling <= lo -> lo <= q - 48 -> q <= 2^47 ->
    rw_cells asegs m0 (CB + 80 * c) [C4 (wz cnt); C4 maxc; C8 (wz csz)] ->
    u32arr asegs m0 (CB + 80 * c + 16) ws -> length ws = 16%nat ->
    rw_cells asegs m0 (CB + 2576) [C8 (wz calloc)] ->
    rw_cells asegs m0 724728 [C8 (wz spacebeg)] ->
    rw_cells asegs m0 (q - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] -> stk asegs m0 lo (q - 48) ->
    evt asegs (fun ms' => exists a0' a1' a2' a3' a4' m',
        ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0o s1o a0' a1' a2' a3' a4' a5 a6 a7
                      s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(CB + 80 * c, CB + 80 * c + 4); (CB + 80 * c + 16 + 4 * cnt, CB + 80 * c + 16 + 4 * cnt + 4); (CB + 2576, CB + 2584)] m0 m'
        /\ wmono asegs m0 m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (CB + 80 * c) [C4 (wz (cnt + 1)); C4 maxc; C8 (wz csz)]
        /\ u32arr asegs m' (CB + 80 * c + 16) (upd ws (Z.to_nat cnt) (wz v))
        /\ rw_cells asegs m' (CB + 2576) [C8 (wz (calloc - csz))]
        /\ stk asegs m' lo q)
      (MS (mkR x1 (wz (q - 48)) gp tp t0 t1 t2 (wz (CB + 80 * c)) x9 (wz CB) (wz INSTANCE) (wz c) (wz (spacebeg + c * 4294967296 + 16 * v)) (wz cnt) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35ce0) fc None m0 (seg_rom asegs)).
  Proof.
    intros until s4o. intros MI Hc Hcnt Hcsz SB0 SB1 V0 V1 CB8 CBL CBI CBH CLO LO QH PC CH LEN STC SBC FR ST.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    demod CB8.
    pose proof (munch_refl [(CB + 80 * c, CB + 80 * c + 4); (CB + 80 * c + 16 + 4 * cnt, CB + 80 * c + 16 + 4 * cnt + 4); (CB + 2576, CB + 2584)] m0) as MU.
    pose proof (wmono_refl asegs m0) as WM.
    set (pcl := CB + 80 * c) in *. assert (Hpcl : pcl = CB + 80 * c) by reflexivity. clearbody pcl.
    zstep.
    zstep. zstep.
    zstep. zstep.
    zstep.
    zstep.
    zstep. zstep. zstep.
    zstep. zstep.
    assert (E3 : Z.shiftr (((spacebeg + c * 4294967296 + 16 * v - Z.shiftl c 32 mod 18446744073709551616) mod 18446744073709551616 - spacebeg) mod 18446744073709551616) 4 = v).
    { rewrite Z.shiftl_mul_pow2 by lia. change (2^32) with 4294967296. rewrite (Z.mod_small (c * 4294967296)) by lia.
      replace (spacebeg + c * 4294967296 + 16 * v - c * 4294967296) with (spacebeg + 16 * v) by lia.
      rewrite (Z.mod_small (spacebeg + 16 * v)) by lia. replace (spacebeg + 16 * v - spacebeg) with (16 * v) by lia.
      rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. rewrite Z.mul_comm. apply Z.div_mul. lia. }
    assert (E4 : Z.shiftr (Z.shiftl cnt 32 mod 18446744073709551616) 30 = 4 * cnt).
    { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
      replace (cnt * 2 ^ 32) with ((4 * cnt) * 2 ^ 30) by lia. apply Z.div_mul. lia. }
    rewrite E3, E4. clear E3 E4.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u32arr_store_ok asegs mx (pcl + 16) ws cnt (wa (pcl + 4 * cnt + 16)) CH ltac:(lia) ltac:(f_equal; lia)) as SOK end.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u32arr_write asegs mx (pcl + 16) ws cnt (wz v) CH ltac:(lia)) as CH2 end.
    replace (pcl + 16 + 4 * cnt) with (pcl + 4 * cnt + 16) in CH2 by lia.
    clear CH. store_done. rename CH2 into CH.
    zstep.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (CB + 2576)) = true) by (apply amo_aligned_intro_d; [lia| rewrite CB0; clear; Z.div_mod_to_equations; lia]).
    amo_step_h AMO.
    do 6 zstep.
    zstep. replace (q - 48 + 48) with q by lia. zstep.
    release_frame FR ST q.
    subst pcl. cbn [amo_val] in STC. rewrite ?lit_add_lit in STC. replace (calloc + (0 - csz)) with (calloc - csz) in STC by lia.
    apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End CDP.

Section CD2.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).

  #[using="Type"] Lemma cd_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
        (m : mem) (H H1 : word -> bool) (q lo c v : Z) (P P1 : prim) (m1 : mem)
        (x1 t0 t1 t2 x9 a5 a6 a7 xs2 xs3 xs4 t3 t4 t5 t6 : word),
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 48 -> q <= 2^47 -> 1 <= c <= 31 ->
    cache_dealloc P c v = push_prim P1 c v ->
    H1 = (if p_cnt (get_cls P c) =? max_count c then H_efa AL c (get_cls P c) (p_nf (get_cls P c) + max_count c / 2) H else H) ->
    pr_inited P1 = true -> p_cnt (get_cls P1 c) < max_count c ->
    0 <= v -> 16 * v + class_size c <= p_au (get_cls P1 c) -> (16 * v) mod class_size c = 0 ->
    ~ In v (p_fa (get_cls P1 c) ++ p_chunks (get_cls P1 c)) -> free_chunk AL m1 c v ->
    munch (prim_W AL lo q c (get_cls P c) (get_cls P1 c)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    shvis H1 m1 -> poison_env E m1 -> thread_env L m1 -> RPRIM AL P1 m1 ->
    stk asegs m1 lo (q - 48) -> rw_cells asegs m1 (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt asegs (lzk H1 (Ret (Ok tt)) (cache_dealloc_post AL E ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo c v P H m))
      (MS (mkR x1 (wz (q - 48)) gp (wz A0_TP) t0 t1 t2 (wz (CACHE + 80 * c)) x9 (wz CACHE) (wz INSTANCE) (wz c) (wz (region AL c + 16 * v)) (wz (p_cnt (get_cls P1 c))) a5 a6 a7
               xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35ce0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until t6. intros AO LOH CLO LO QH Hc ECD EH1 INI1 CNT1 V0 VAU VAL VNI FCV MU1 WM1 MI1 SV1 PE1 TE1 RP1 ST1 FR1.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.

    destruct (RPRIM_push AL AO P1 m1 c v RP1 INI1 Hc CNT1 V0 VAU VAL VNI FCV) as (CB & PENV & PCL & STATS & (ws & ARR & LWS & CLOSE)).
    set (k1 := get_cls P1 c) in *. set (cnt := p_cnt k1) in *.
    pose proof (class_size_pos c Hc) as CS.
    assert (AUF : p_au k1 <= FA_OFF). { destruct RP1 as (_ & _ & CLS & _). destruct (CLS c Hc) as ((_ & _ & _ & _ & _ & _ & AU & MUF & _) & _). fold k1 in AU, MUF. lia. }
    unfold pcl_addr in PCL, ARR. unfold prim_env in PENV.
    apply (proj1 (rw_cells_app asegs m1 724728 [_] _)) in PENV as [PENV0 _].
    replace (THR + CSTATS_OFF + 16) with (CACHE + 2576) in STATS by lia.
    apply (proj1 (rw_cells_app asegs m1 (CACHE + 2576) [_] [_])) in STATS as [STATS0 STATS1]. cbn [cells_size csize Nat.add] in STATS1.
    pose proof (munch_refl [(CACHE + 80 * c, CACHE + 80 * c + 4); (CACHE + 80 * c + 16 + 4 * cnt, CACHE + 80 * c + 16 + 4 * cnt + 4); (CACHE + 2576, CACHE + 2584)] m1) as MUc.
    pose proof (wmono_refl asegs m1) as WMc.
    assert (CB8 : CACHE mod 8 = 0) by (clear - T7; Z.div_mod_to_equations; lia).
    hide STATS1. hide T1. hide T5. hide T6. hide SPM. hide T7.
    unfold region.
    eapply evt_cut.
    { eapply (cd_push ra gp (wz A0_TP) F_ fc q CACHE m1 lo c cnt (class_size c) (pr_calloc P1) (al_space AL) v (wz (max_count c)) ws
                _ _ _ _ (wz (CACHE + 80 * c)) _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4).
      - assumption.
      - exact Hc.
      - exact CB.
      - clear - CS; lia.
      - clear - SP1; lia.
      - clear - SP5; lia.
      - exact V0.
      - clear - V0 VAU AUF CS; lia.
      - exact CB8.
      - clear - T3; lia.
      - clear - T3; lia.
      - clear - T4 CLO; lia.
      - exact CLO.
      - exact LO.
      - exact QH.
      - exact PCL.
      - exact ARR.
      - exact LWS.
      - exact STATS0.
      - exact PENV0.
      - exact FR1.
      - exact ST1. }
    cbv beta. intros ms2 (b0 & b1 & b2 & b3 & b4 & mF & -> & MUf & WMf & MIF & PCF & ARRF & STF0 & STF).
    unhide STATS1. unhide T1. unhide T5.
    pose proof (rw_cells_transport asegs _ m1 mF _ _ STATS1 MUf WMf ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Hc CB; lia)) as STATS1F.
    assert (STFF : rw_cells asegs mF (THR + CSTATS_OFF + 16) [C8 (wz (pr_calloc P1 - class_size c)); C8 (wz (pr_cmapped P1))]).
    { replace (THR + CSTATS_OFF + 16) with (CACHE + 2576) by lia. apply (proj2 (rw_cells_app asegs mF (CACHE + 2576) [_] [_])). split; [exact STF0| exact STATS1F]. }
    assert (MUp : munch (push_W AL c cnt) m1 mF).
    { refine (munch_weaken _ _ _ _ _ MUf). unfold push_W, pcl_addr. clear. sub_fp_solve. }
    pose proof (CLOSE mF MUp WMf ltac:(unfold pcl_addr; exact PCF) ltac:(unfold pcl_addr; exact ARRF) STFF) as RPF. clear CLOSE.
    pose proof RP1 as (LEN1 & _).
    assert (EKF : get_cls (push_prim P1 c v) c = push_cls k1 v) by (unfold push_prim; apply get_cls_set_same; [exact LEN1| lia]).
    lz_ret. apply evt_done. unfold cache_dealloc_post. cbv zeta. rewrite ECD.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mF.
    split; [reflexivity|]. split; [exact EH1|].
    split.
    { rewrite EKF. change (prim_W AL lo q c (get_cls P c) (push_cls k1 v)) with (prim_W AL lo q c (get_cls P c) k1).
      eapply munch_trans; [exact MU1|]. refine (munch_weaken _ _ _ _ _ MUf).
      unfold sub_fp, prim_W; cbn [outside]. intros xo (_ & _ & _ & _ & _ & _ & O7 & _).
      repeat split; try exact I; intros R; apply O7; clear - R Hc CB; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM1 WMf)|]. split; [exact MIF|]. split; [exact STF|].
    split. { eapply poison_env_frame; [exact PE1| exact MUf| exact WMf|]. clear - T3 T4 Hc CB. env_clear. }
    split. { eapply thread_env_frame; [exact TE1| exact MUf| exact WMf|]. clear - T1 T2 T3 T4 T5 Hc CB. env_clear. }
    split; [eapply shvis_wmono; [exact SV1| exact WMf]|].
    split; [exact RPF|]. unfold prim_ok, push_prim. cbn [pr_inited]. intros X. discriminate.
  Qed.

  #[using="Type"] Theorem cdealloc_spec : cache_dealloc_stmt AL E.
  Proof.
    unfold cache_dealloc_stmt.
    intros ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo c v P
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 Hc RP POK V0 VAU VAL VNI FCV.
    unfold cache_dealloc_entry, CDEALLOC_STACK, MF_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    hide T1. hide T5. hide T6. hide T7. hide SPM. hide Q16.
    pose proof RP as (LEN & PENV & CLS & STAT & (ts & TS)).
    set (k := get_cls P c) in *.
    pose proof (CLS c Hc) as CR. fold k in CR.
    destruct CR as (WF & RIc & (PC1 & PAX) & FAc & TLc & FCHc).
    unfold pcl_addr in PC1.
    pose proof (max_count_range c Hc) as (MR & _).
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.
    zstep. if_false_z.
    zstep.
    zstep. if_cases KB; zify_cond KB. { exfalso. clear - KB Hc. lia. } clear KB.
    do 3 zstep.
    replace (CACHE + c * 80) with (CACHE + 80 * c) by lia.
    assert (PCB : THR + 288 <= CACHE + 80 * c /\ CACHE + 80 * c + 80 <= THR + 2768) by (clear - Hc; lia).
    remember (CACHE + 80 * c) as pcb eqn:Hpcb in *.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.

    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (RPA : RPRIM AL P mA).
    { apply (RPRIM_frame AL AO P _ m mA RP MU WM). unfold prim_clear.
      repeat (apply Forall_cons || apply Forall_nil). left. unfold prim_out. cbn [fst snd]. clear - LO CLO ACR T3 T4 SP2 SHS. repeat split; lia. }
    assert (SVA : shvis H mA) by (eapply shvis_wmono; [exact SV| exact WM]).
    assert (PEA : poison_env E mA) by (eapply poison_env_frame; [exact PE| exact MU| exact WM|]; clear - LO CLO ACR; env_clear).
    assert (TEA : thread_env L mA).
    { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unhide T1. unhide T5. clear - LO CLO ACR T1 T2 T3 T4 T5. env_clear. }
    pose proof (region_range AL c Hc) as [R1 R2].
    pose proof (class_size_pos c Hc) as CS.
    pose proof WF as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & _).
    assert (FCVA : free_chunk AL mA c v).
    { assert (SHV : sh (region AL c + 16 * v) + class_size c / 8 <= 17594333495296).
      { pose proof (sh_le (region AL c + 16 * v + class_size c) (2^47) ltac:(clear - R2 SP5 VAU AU MUF V0; lia)) as X. change (sh (2^47)) with 17594333495296 in X.
        assert (sh (region AL c + 16 * v) + class_size c / 8 <= sh (region AL c + 16 * v + class_size c)) by (unfold sh; clear; Z.div_mod_to_equations; lia). lia. }
      eapply free_chunk_frame; [exact FCV| exact MU| exact WM| exact Hc| |]; cbn [disjoint_from].
      - clear - R2 SP2 VAU AU MUF V0 CLO LO. lia.
      - clear - SHV LOH LO. lia. }
    clear RP SV PE TE FCV RIc PAX FAc TLc FCHc CLS PENV STAT TS.
    replace (q + -48) with (q - 48) in * by lia.
    assert (MUW : forall k', munch (prim_W AL lo q c k k') m mA).
    { intros k'. refine (munch_weaken _ _ _ _ _ MU). unfold sub_fp, prim_W; cbn [outside]. intros xo (O1 & _). split; [intros R; apply O1; clear - R LO; lia| exact I]. }
    destruct (pr_inited P) eqn:INI.
    {
      rewrite (sx32_lit (max_count c)) by (clear - MR; lia).
      zstep. if_false_z.
      zstep.
      rewrite (sx32_lit (p_cnt k)) by (clear - CNT MR; lia).
      assert (EP : mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P) = P) by (destruct P; cbn in INI |- *; rewrite INI; reflexivity).
      zstep. if_cases KEQ; zify_cond KEQ.
      2: {
        assert (NEQ : (p_cnt k =? max_count c) = false) by (apply Z.eqb_neq; exact KEQ).
        unfold t_cdealloc. rewrite NEQ. unfold t_none. subst pcb.
        eapply (cd_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H H q lo c v P P mA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO ltac:(clear - LO; lia) QH Hc).
        - unfold cache_dealloc, push_prim. fold k. rewrite cache_dealloc_cls_eq, NEQ. reflexivity.
        - fold k. rewrite NEQ. reflexivity.
        - exact INI.
        - fold k. clear - KEQ CNT. lia.
        - exact V0.
        - exact VAU.
        - exact VAL.
        - exact VNI.
        - exact FCVA.
        - apply MUW.
        - exact WM.
        - assumption.
        - exact SVA.
        - exact PEA.
        - exact TEA.
        - exact RPA.
        - exact ST.
        - exact FR. }

      assert (EQB : (p_cnt k =? max_count c) = true) by (apply Z.eqb_eq; exact KEQ).
      unfold t_cdealloc. rewrite EQB. unfold t_none. rewrite ebind_none.
      do 7 zstep.
      zstep.
      pose proof RPA as (LENA & PENVA & CLSA & STATA & TSA). rewrite INI in CLSA.
      destruct (CLSA c Hc) as (_ & RIA & PCLA & FAA & _ & _). fold k in RIA, PCLA, FAA. clear CLSA STATA.
      assert (HCNT : max_count c / 2 <= p_cnt k) by (rewrite KEQ; clear - MR; Z.div_mod_to_equations; lia).
      pose proof (drain_cls_wf c k Hc WF HCNT) as WFd.
      set (kd := drain_cls k c) in *.
      pose proof WFd as (_ & Lcntd & _ & _ & MFAd & MFAMd & _).
      assert (MFK : p_mfa k <= p_mfa kd).
      { unfold kd, drain_cls. cbn [p_mfa return_to_allocator ensure_fa]. unfold efa_new.
        destruct (Z.leb_spec (4 * (p_nf k + Z.of_nat (length (skipn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k))))) (p_mfa k)) as [LE|GT]; [lia|].
        pose proof (rup_ge (4 * (p_nf k + Z.of_nat (length (skipn (Z.to_nat (p_cnt k - max_count c / 2)) (p_chunks k))))) K_MAP ltac:(lia)). lia. }
      pose proof (fa_sw_exact AL AO c (p_mfa k) (p_mfa kd) Hc MFAM MFAMd) as (E1 & E2 & E3).
      assert (SHF : 2147450880 <= sh (fa_base AL c + p_mfa k) /\ sh (fa_base AL c + p_mfa kd) <= 17594333495296).
      { split; [pose proof (sh_le 0 (fa_base AL c + p_mfa k) ltac:(unfold fa_base; clear - R1 SP1 MFA; lia)) as X; exact X|].
        pose proof (sh_le (fa_base AL c + p_mfa kd) (2^47) ltac:(unfold fa_base; clear - R2 SP5 MFAd; lia)) as X; exact X. }
      subst pcb. clear PC1.
      hide FR.
      unhide Q16.
      callA0 (drain_spec AL E _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc mA H (q - 48) lo c k AO).
      1: assumption.
      1: assumption.
      1: exact SVA.
      1: exact PEA.
      1: exact TEA.
      1: exact PENVA.
      1: exact ST.
      1: exact LOH.
      1: exact CLO.
      1: unfold DRAIN_STACK, RTA_STACK, MF_STACK; clear - LO; lia.
      1: clear - QH; lia.
      1: clear - Q16; Z.div_mod_to_equations; lia.
      1: exact Hc.
      1: exact WF.
      1: exact HCNT.
      1: exact (drain_budget_wf c k Hc WF).
      1: exact RIA.
      1: exact PCLA.
      1: exact FAA.
      1: exact TSA.

      intros r H' ms' [PO MCx]. destruct r. unfold drain_post in PO. cbv zeta in PO. fold kd in PO.
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & mD & -> & -> & MUd & WMd & MID & STD & PED & TED & PRED & SVD & RID & PCLD & FAD & TSD).
      clean_ms_mem MCx. hide Q16.

      pose proof (drain_close AL AO P mA mD lo (q - 48) c Hc LOH CLO ltac:(clear - LO; lia) INI RPA HCNT MUd WMd PRED RID PCLD FAD TSD) as RPD. fold k in RPD. fold kd in RPD.
      set (Pd := mkPRIM (set_nth (Z.to_nat c) kd (pr_cls P)) true (pr_calloc P) (pr_cmapped P)) in *.
      assert (EKD : get_cls Pd c = kd) by (unfold Pd; apply get_cls_set_same; [exact LENA| clear - Hc; lia]).

      pose proof MUd as MU0. unfold drain_W in MU0. rewrite E1, E2, <- E3 in MU0.
      unhide FR.
      pose proof (rw_cells_transport asegs _ mA mD _ _ FR MU0 WMd ltac:(cbn [disjoint_from cells_size csize Nat.add]; unfold pcl_addr, ri_addr, RIB, fa_base in *; clear - LO CLO LOH SP2 R1 R2 Hc T4 SHF MFAd; lia)) as FRD.
      assert (FCVD : free_chunk AL mD c v).
      { assert (SHV : sh (region AL c) <= sh (region AL c + 16 * v) /\ sh (region AL c + 16 * v) + class_size c / 8 <= sh (fa_base AL c + p_mfa k)).
        { split; [apply sh_le; clear - V0; lia|].
          assert (sh (region AL c + 16 * v) + class_size c / 8 <= sh (region AL c + 16 * v + class_size c)) by (unfold sh; clear; Z.div_mod_to_equations; lia).
          pose proof (sh_le (region AL c + 16 * v + class_size c) (fa_base AL c + p_mfa k) ltac:(unfold fa_base; clear - VAU AU MUF MFA; lia)). lia. }
        assert (SHM : sh (fa_base AL c + p_mfa k) <= sh (fa_base AL c + p_mfa kd)) by (apply sh_le; clear - MFK; lia).
        assert (SHR0 : 2147450880 <= sh (region AL c)) by (pose proof (sh_le 0 (region AL c) ltac:(clear - R1 SP1; lia)) as X; exact X).
        eapply free_chunk_frame; [exact FCVA| exact MU0| exact WMd| exact Hc| |]; cbn [disjoint_from]; unfold pcl_addr, ri_addr, RIB, fa_base in *.
        - clear - R1 R2 SP1 SP2 LP03 T3 T4 VAU AU MUF V0 CS CLO LO Lnf Hc MFA MFAd MFK SHF. lia.
        - clear - SHV SHM SHR0 SHF LOH LO SP1 R1 Lnf T3 T4 Hc. lia. }
      clear FR FCVA RPA RIA PCLA FAA TSA PENVA.
      lz_cont MCx.
      replace (ret_pc (Z_to_bv 64 220748)) with (Z_to_bv 64 220748) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      do 4 zstep.
      destruct PCLD as (PC1D & _). unfold pcl_addr in PC1D.
      remember (CACHE + 80 * c) as pcb eqn:Hpcb in *.
      zstep.
      assert (CNTD : p_cnt kd = p_cnt k - max_count c / 2) by reflexivity.
      assert (CNTDR : 0 <= p_cnt kd < max_count c) by (rewrite CNTD, KEQ; clear - MR; Z.div_mod_to_equations; lia).
      rewrite (sx32_lit (p_cnt kd)) by (clear - CNTDR MR; lia).
      zstep.
      subst pcb. clear PC1D.
      rewrite <- EKD.
      eapply (cd_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H _ q lo c v P Pd mD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO ltac:(clear - LO; lia) QH Hc).
      - unfold cache_dealloc, push_prim. rewrite EKD. unfold Pd. cbn [pr_cls pr_calloc pr_cmapped]. fold k.
        rewrite cache_dealloc_cls_eq, EQB. fold kd. rewrite set_nth_twice. reflexivity.
      - fold k. rewrite EQB. reflexivity.
      - reflexivity.
      - rewrite EKD. exact (proj2 CNTDR).
      - exact V0.
      - rewrite EKD. exact VAU.
      - exact VAL.
      - rewrite EKD. intros IN. apply VNI. apply (drain_cls_free k c v). exact IN.
      - exact FCVD.
      - rewrite EKD. fold k.
        assert (NFK : p_nf k <= p_nf kd) by (unfold kd, drain_cls; cbn [p_nf return_to_allocator]; clear; lia).
        eapply munch_trans; [exact (MUW kd)|]. refine (munch_weaken _ _ _ _ _ MU0).
        unfold sub_fp, prim_W, ri_addr, RIB, fa_base, pcl_addr; cbn [outside]. intros xo (O1 & O2 & O3 & _ & _ & O6 & O7 & O8 & _).
        split; [intros R; apply O1; clear - R; lia|]. split; [exact O2|].
        split; [intros R; apply O3; clear - R NFK; lia|]. split; [exact O6|]. split; [exact O6|]. split; [exact O8|].
        split; [intros R; apply O7; clear - R Hc; lia| exact I].
      - exact (wmono_trans asegs _ _ _ WM WMd).
      - exact MID.
      - exact SVD.
      - exact PED.
      - exact TED.
      - exact RPD.
      - exact STD.
      - exact FRD. }
    {
      change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      zstep. if_true_z.
      pose proof RPA as (LENA & PENVA & CLSA & STATA & (tsA & TSA)). rewrite INI in CLSA.
      assert (FAM0 : forall c', 1 <= c' <= 31 -> pcl_rep AL mA false c' (get_cls P c')) by (intros c' Hc'; exact (proj1 (proj2 (proj2 (CLSA c' Hc'))))).
      assert (THR_OK : 0 < THR /\ THR + 4096 <= 2^47) by (clear - T3 T4 ACR; lia).
      assert (C0 : p_cnt k = 0) by (exact (POK INI c Hc)).
      clear PC1.
      apply (munch_extend _ [(CACHE, CACHE + 2592)]) in MU. cbn [List.app] in MU.
      pose proof (munch_refl [(THR + 292, THR + 2704)] mA) as MUi. pose proof (wmono_refl asegs mA) as WMi.
      call (ic_d_all _ (wz (q - 48)) gp (wz A0_TP) _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc THR THR_OK AL eq_refl mA P _ _ _ _ _ _ _ _ _ _ _ FAM0); [assumption|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mI end.
      match goal with FX : forall c0, 1 <= c0 <= 31 -> pcl_rep AL mI true c0 (get_cls P c0) |- _ => rename FX into FAM1 end.
      destruct (FAM1 c Hc) as (PC1 & _). unfold pcl_addr in PC1. fold k in PC1. rewrite <- Hpcb in PC1. rewrite C0 in PC1.
      zstep.
      rewrite (sx32_lit (max_count c)) by (clear - MR; lia).
      zstep.
      change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
      zstep. if_cases KNE; zify_cond KNE. 2: { exfalso. clear - KNE MR. lia. } clear KNE.
      clear PC1.
      set (Pi := mkPRIM (pr_cls P) true (pr_calloc P) (pr_cmapped P)).
      assert (EKi : forall c', get_cls Pi c' = get_cls P c') by reflexivity.
      assert (NEQ : (p_cnt k =? max_count c) = false) by (apply Z.eqb_neq; rewrite C0; clear - MR; lia).
      assert (AIi : above_img [(THR + 292, THR + 2704)]) by (clear - T3 T4; env_clear).
      unfold t_cdealloc. rewrite NEQ. unfold t_none. subst pcb.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (p_cnt (get_cls Pi c))) by (rewrite EKi; fold k; rewrite C0; reflexivity).
      eapply (cd_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m H H q lo c v P Pi mI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AO LOH CLO ltac:(clear - LO; lia) QH Hc).
      - unfold cache_dealloc, push_prim. rewrite EKi. fold k. rewrite cache_dealloc_cls_eq, NEQ. reflexivity.
      - fold k. rewrite NEQ. reflexivity.
      - reflexivity.
      - rewrite EKi. fold k. rewrite C0. clear - MR. lia.
      - exact V0.
      - rewrite EKi. exact VAU.
      - exact VAL.
      - rewrite EKi. exact VNI.
      -
        assert (SHV : 2147450880 <= sh (region AL c + 16 * v) /\ sh (region AL c + 16 * v) + class_size c / 8 <= 17594333495296).
        { split; [pose proof (sh_le 0 (region AL c + 16 * v) ltac:(clear - R1 SP1 V0; lia)) as X; exact X|].
          pose proof (sh_le (region AL c + 16 * v + class_size c) (2^47) ltac:(clear - R2 SP5 VAU AU MUF V0; lia)) as X. change (sh (2^47)) with 17594333495296 in X.
          assert (sh (region AL c + 16 * v) + class_size c / 8 <= sh (region AL c + 16 * v + class_size c)) by (unfold sh; clear; Z.div_mod_to_equations; lia). lia. }
        eapply free_chunk_frame; [exact FCVA| exact MUi| exact WMi| exact Hc| |]; cbn [disjoint_from].
        + clear - R1 R2 SP1 SP2 LP03 T3 T4 VAU AU MUF V0 CS. lia.
        + clear - SHV T3 T4. lia.
      - rewrite EKi. fold k. refine (munch_weaken _ _ _ _ _ MU). unfold sub_fp, prim_W; cbn [outside].
        intros xo (O1 & _ & _ & _ & _ & _ & O7 & _). split; [intros R; apply O1; clear - R LO; lia|]. split; [exact O7| exact I].
      - exact WM.
      - assumption.
      - eapply shvis_wmono; [exact SVA| exact WMi].
      - eapply poison_env_frame; [exact PEA| exact MUi| exact WMi| exact AIi].
      - eapply thread_env_frame; [exact TEA| exact MUi| exact WMi|]. unhide T1. unhide T5. clear - T1 T2 T3 T4 T5. env_clear.
      -
        split; [exact LENA|].
        split; [eapply prim_env_frame; [exact PENVA| exact MUi| exact WMi| exact AIi]|].
        split.
        { intros c' Hc'. cbn [pr_inited Pi]. rewrite EKi.
          destruct (CLSA c' Hc') as (WFc' & RIc' & _ & FAc' & TLc' & FCHc').
          assert (BM : Forall (cls_miss_body AL c' (get_cls P c')) [(THR + 292, THR + 2704)]).
          { pose proof (region_range AL c' Hc') as [R1' R2'].
            pose proof (sh_le 0 (region AL c') ltac:(lia)) as L1. change (sh 0) with 2147450880 in L1.
            pose proof (sh_le (region AL c' + K_REGION) (2^47) ltac:(lia)) as L2. change (sh (2^47)) with 17594333495296 in L2.
            unfold cls_miss_body, ri_addr, RIB. clear - T3 T4 LP03 SP1 SP2 R1' R2' L1 L2 Hc'.
            repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia| left; lia]). }
          destruct (cls_body_frame AL AO c' (get_cls P c') Hc' WFc' _ mA mI (conj RIc' (conj FAc' (conj TLc' FCHc'))) MUi WMi BM) as (RI' & FA' & TL' & FCH').
          split; [exact WFc'|]. split; [exact RI'|]. split; [exact (FAM1 c' Hc')|]. split; [exact FA'|]. split; [exact TL'| exact FCH']. }
        split; [cbn [pr_calloc pr_cmapped Pi]; exact STATA|]. exists tsA. exact TSA.
      - exact ST.
      - exact FR. }
  Qed.
End CD2.
