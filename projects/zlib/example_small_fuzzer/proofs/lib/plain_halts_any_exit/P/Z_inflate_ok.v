(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Rnd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_irep Z_ikit Z_infl_defs Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_updwin_pure Z_updwin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2 Z_infl_top_pure Z_inflate_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2.

Module Z_inflate_top.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Rnd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_irep Z_ikit Z_infl_defs Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_updwin_pure Z_updwin.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2 Z_infl_top_pure Z_inflate_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_leave2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_pro OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_loop OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_updwin_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_updwin OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2.Z_infl_leave OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_top_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_inflate_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2.Z_inflate_mem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate HarnessSmall RefInflateSafeD RefInflateSafeTY RefInflateEqS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefUpdWin1 RefInflateRel RefInflateEqB InflateFrameIn ZApiInst ZTaintI.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefUpdWin1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateFrameIn OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma iblocks_inv : forall (w w' : option bptr) Aw Aw' (sp_ sp' : bptr) As As',
  Zlib_iface.iblocks w Aw sp_ As = iblk_list w' Aw' sp' As' -> w' = w /\ sp' = sp_ /\ As' = As /\ (w <> None -> Aw' = Aw).
Proof.
  intros w w' Aw Aw' sp_ sp' As As'. unfold Zlib_iface.iblocks, iblk_list, the_zapi. cbn [z_wsize z_isize zinst].
  destruct w as [wp|]; destruct w' as [wp'|]; cbn [app]; intros E; try discriminate E.
  - injection E as E1 E2 E3 E4. subst. repeat split; reflexivity.
  - injection E as E1 E2. subst. repeat split; try reflexivity. intros NE. exfalso. apply NE. reflexivity.
Qed.

Section TOP.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (st : PState) (LB : list block) (S C U cl size : Z) (comprc uc : list Z) (x : istream).
  Variables (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word).
  Variables (s_a : inflate_state) (Awl : Z).

  Notation ti := (zs_total_in (iz_z x)).
  Notation to := (zs_total_out (iz_z x)).
  Notation zc := (zi_zcall comprc x 1 1).
  Notation OW := (iblk_list w Awl sp_ As).
  Notation L := (Z_irep.mkIL S As Awl (C + ti) (U + to)).
  Notation rest0 := (firstn 1 (skipn (Z.to_nat to) (to_bytes uc))).
  Notation hasw := (match w with Some _ => true | None => false end).
  Definition topX : ictx :=
    mkIX L 0 lo (arr_of_list (zc_input zc)) rest0 hasw m sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc.

  Hypothesis ENV : lx_env m st OW LB sp tp B lo errv canary.
  Hypothesis INC : exists b, In b LB /\ blk_addr b = C /\ blk_size b = cl.
  Hypothesis INU : exists b, In b LB /\ blk_addr b = U /\ blk_size b = size.
  Hypothesis LCL : Prelim.zlength comprc = cl.
  Hypothesis LUC : Prelim.zlength uc = size.
  Hypothesis RTI : 0 <= ti < cl.
  Hypothesis RTO : 0 <= to < size.
  Hypothesis SEPCU : U + size <= C \/ C + cl <= U.
  Hypothesis SIF : strm_in_frame sp S B.
  Hypothesis LOSP : lo <= bv_unsigned sp - Z_INFLATE_STACK.
  Hypothesis HWA : w <> None -> Awl = Aw.

  Lemma top_blocks :
    blk_ok As 7176 /\ As + 7176 <= lo
    /\ (forall b, In b LB -> apart As 7176 (blk_addr b) (blk_size b))
    /\ (w <> None -> blk_ok Awl 32768 /\ Awl + 32768 <= lo /\ apart As 7176 Awl 32768 /\ (forall b, In b LB -> apart Awl 32768 (blk_addr b) (blk_size b)))
    /\ (forall b, In b LB -> 0 < blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= lo).
  Proof.
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & _ & _ & _ & _ & _ & _ & _ & _ & LOC & _).
    pose proof alloc_ceiling_range as CR.
    assert (RB : forall b, In b (OW ++ LB) -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ b HP Hb)).
    assert (INS : In (sp_, As, 7176) OW) by (unfold iblk_list; apply in_or_app; right; left; reflexivity).
    pose proof (RB _ (in_or_app _ _ _ (or_introl INS))) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in *.
    split; [unfold blk_ok; repeat split; try assumption; lia|]. split; [lia|].
    split. { intros b Hb. pose proof (heap_sep _ _ _ _ _ b HND HBD HP INS Hb) as X. cbn [blk_addr blk_size fst snd] in X. unfold apart. lia. }
    split.
    { intros NE. destruct w as [wp|] eqn:EW; [|exfalso; apply NE; reflexivity].
      assert (INW : In (wp, Awl, 32768) (iblk_list (Some wp) Awl sp_ As)) by (unfold iblk_list; apply in_or_app; left; left; reflexivity).
      pose proof (RB _ (in_or_app _ _ _ (or_introl INW))) as (Q1 & Q2 & Q3 & Q4 & Q5). cbn [blk_addr blk_size fst snd] in *.
      split; [unfold blk_ok; repeat split; try assumption; lia|]. split; [lia|]. split.
      - pose proof (HND _ _ _ HP) as ND. pose proof (HBD _ _ _ (sp_, As, 7176) (wp, Awl, 32768) HP (in_or_app _ _ _ (or_introl INS)) (in_or_app _ _ _ (or_introl INW))) as X.
        cbn [blk_id blk_addr blk_size fst snd] in X. unfold apart. apply X. intros E. subst wp.
        unfold iblk_list in ND. cbn [app map blk_id fst] in ND. inversion ND as [|? ? NI _]; subst. apply NI. left. reflexivity.
      - intros b Hb. pose proof (heap_sep _ _ _ _ _ b HND HBD HP INW Hb) as X. cbn [blk_addr blk_size fst snd] in X. unfold apart. lia. }
    intros b Hb. pose proof (RB _ (in_or_app _ _ _ (or_intror Hb))) as (Q1 & Q2 & Q3 & Q4 & Q5). lia.
  Qed.

  Lemma top_lens : arr_len (arr_of_list (zc_input zc)) = 1 /\ length rest0 = 1%nat.
  Proof.
    split.
    - rewrite arr_len_of_list. unfold zi_zcall. cbn [zc_input]. unfold zfirstn, zskipn, ZIface.zlength. unfold Prelim.zlength in LCL.
      rewrite length_firstn, length_skipn. lia.
    - unfold Prelim.zlength in LUC. unfold to_bytes. rewrite length_firstn, length_skipn, length_map. lia.
  Qed.

  Lemma top_hasw : ix_hasw topX = true -> w <> None.
  Proof. cbn [ix_hasw topX]. destruct w; [discriminate| intros E; discriminate E]. Qed.

  Lemma top_ix_ok : ix_ok topX.
  Proof.
    destruct top_blocks as (BS & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & SPB & B63 & _ & _ & LOG & _).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATE_STACK, RMALLOC_STACK in LOSP. unfold GLOBALS_TOP in LOG.
    destruct INC as (bc & Hbc & EC1 & EC2). destruct INU as (bu & Hbu & EU1 & EU2).
    pose proof (BLB _ Hbc) as RC. pose proof (BLB _ Hbu) as RU. pose proof (SEPS _ Hbc) as SC. pose proof (SEPS _ Hbu) as SU.
    rewrite EC1, EC2 in *. rewrite EU1, EU2 in *. destruct BS as (BS1 & _). unfold apart in *.
    constructor; cbn [topX ix_L ix_lo ix_sp ix_input ix_rest0 il_S il_As il_Aw il_NI il_NO]; rewrite ?LI, ?LR; change (Z.of_nat 1) with 1; unfold apart.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros HH. destruct (BW (top_hasw HH)) as ((Q1 & _) & Q2 & _). lia.
    - intros HH. destruct (BW (top_hasw HH)) as (_ & _ & _ & Q4). pose proof (Q4 _ Hbc) as Q. rewrite EC1, EC2 in Q. unfold apart in Q. lia.
    - intros HH. destruct (BW (top_hasw HH)) as (_ & _ & _ & Q4). pose proof (Q4 _ Hbu) as Q. rewrite EU1, EU2 in Q. unfold apart in Q. lia.
    - intros HH. destruct (BW (top_hasw HH)) as (_ & _ & Q3 & _). unfold apart in Q3. lia.
  Qed.

  Hypothesis ARMS : arms_ok 0.
  Hypothesis HWb : w = None <-> is_window_blk s_a = None.
  Hypothesis HZQ : izq m L (iz_z x).
  Hypothesis HIST : IST m L s_a.
  Hypothesis HIREL : IREL s_a x.
  Hypothesis HATY : ATY s_a.
  Hypothesis HPQ : PATIq s_a.
  Hypothesis PUB : rw_cells psegs m S (zs_pub (C + ti) 1 ti (U + to) 1 to p1 p2).
  Hypothesis CARR : u8arr psegs m C (to_bytes comprc).
  Hypothesis CBYT : Forall (fun c => 0 <= c < 256) comprc.
  Hypothesis UARR : u8arr psegs m U (to_bytes uc).

  Lemma top_ZC : ZC zc.
  Proof.
    unfold ZC, zi_zcall. cbn [zc_avail_out zc_input]. split; [lia|]. destruct top_lens as (LI & _). rewrite arr_len_of_list in LI. cbn [zc_input zi_zcall] in LI.
    split; [rewrite LI; lia|]. unfold RefZApi.bytes_ok, zfirstn, zskipn.
    apply Forall_forall. intros v Hv. apply (proj1 (Forall_forall _ _) CBYT).
    rewrite <- (firstn_skipn (Z.to_nat ti) comprc). apply in_or_app. right.
    rewrite <- (firstn_skipn (Z.to_nat 1) (skipn (Z.to_nat ti) comprc)). apply in_or_app. left. exact Hv.
  Qed.

  Lemma top_INV : INV s_a.
  Proof. destruct HIREL as (_ & _ & H & _). exact H. Qed.

  Lemma top_W0 : WINV (W0 s_a zc) /\ PHI (W0 s_a zc) < 64 * (ic_avail_in (w_c (W0 s_a zc)) + ic_avail_out (w_c (W0 s_a zc)) + 64)
                 /\ ATY (w_s (W0 s_a zc)) /\ PATI topX (W0 s_a zc).
  Proof.
    destruct (WINV_entry' s_a zc top_INV top_ZC) as [HW HPHI]. split; [exact HW|]. split; [exact HPHI|].
    split; [apply RefInflateSafeTY2.W0_aty; exact HATY|].
    destruct top_lens as (LI & LR). rewrite arr_len_of_list in LI.
    apply W0_PATI; [exact HPQ| reflexivity| rewrite LI; lia| cbn [topX ix_rest0 zc_avail_out zi_zcall]; rewrite LR; reflexivity| cbn [topX ix_rest0]; rewrite LR; lia|].
    cbn [topX ix_hasw]. split.
    - intros NE. destruct w as [wp|] eqn:EW; [reflexivity|]. exfalso. apply NE. apply HWb. reflexivity.
    - intros HH E. destruct w as [wp|] eqn:EW; [|discriminate HH]. apply (proj2 HWb) in E. discriminate E.
  Qed.

  Lemma top_loop : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt psegs (LPOST topX (inf_loop ivar_ref 0 (W0 s_a zc)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_INFLATE) fc None m (seg_rom psegs)).
  Proof.
    intros. destruct top_W0 as (HW & HPHI & HA & HP). destruct top_lens as (LI & LR).
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & SPB & B63 & STK & _ & _ & _ & _ & MI).
    pose proof top_ix_ok as XO. pose proof top_INV as (HCORE & [HB1 HB2] & HMF).
    destruct (iin_of_compr m C comprc ti CARR ltac:(unfold Prelim.zlength in LCL; unfold ZIface.zlength; lia)) as (HIN & LIN1).
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (_ & U1 & UM & U3).
    eapply evt_cut.
    { eapply (inflate_prologue topX s_a zc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m); cbn [topX ix_m0 ix_L ix_lo ix_sp ix_flush ix_rest0 ix_hasw il_NI il_NO].
      - reflexivity.
      - exact XO.
      - eapply izs_of_pub; [| exact HZQ| reflexivity| reflexivity].
        cbn [il_S il_NI il_NO icall_of_zcall ic_next_in ic_avail_in ic_total_in ic_next_out ic_avail_out ic_total_out zc_strm zc_avail_out zi_zcall].
        rewrite !Z.add_0_r. cbn [zc_input zi_zcall] in LIN1. rewrite LIN1. exact PUB.
      - exact HIST.
      - unfold iin. cbn [topX ix_L ix_input il_NI]. exact HIN.
      - unfold iout. cbn [il_NO]. rewrite iout_bytes_0. exact UM.
      - exact STK.
      - exact MI.
      - intros NE. destruct w as [wp|] eqn:EW; [reflexivity|]. exfalso. apply NE. apply HWb. reflexivity.
      - pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM. unfold HEAD, MEM, SYNC in *. lia.
      - lia.
      - split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 HB2)|]. apply Z.pow_le_mono_r; lia.
      - cbn [zc_input zi_zcall] in LIN1 |- *. rewrite LIN1. lia.
      - cbn [zc_avail_out zi_zcall]. lia.
      - lia.
      - destruct XO as [X1 _ X3 _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_NI ix_input] in X1, X3. lia.
      - destruct XO as [X1 _ _ X4 _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_NO ix_rest0] in X1, X4. lia. }
    intros ms1 (x8 & HL).
    exact (inf_loop_of_arms 0 ARMS topX (W0 s_a zc) x8 ms1 eq_refl HL XO HW HA HP HPHI).
  Qed.

  Definition lv_S0 (w' : iw) := s_rest (w_s w') (w_r w').
  Definition lv_C0 (w' : iw) := c_rest (w_c w') (w_r w').
  Definition lv_o (w' : iw) := ir_out (w_r w') - ir_left (w_r w').
  Definition asked (stop : istop) (w' : iw) : bool :=
    match stop with SRet _ => false | SLeave => lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w') && no_window (w_s (lv_w w')) end.
  Definition fin_w (stop : istop) (w' : iw) : iw :=
    match stop with
    | SRet _ => w'
    | SLeave => if lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w')
                then mkW (updw_core (w_s (lv_w w')) (ic_outbuf (w_c w')) (ir_put (w_r w')) (lv_o w')) (w_c (lv_w w')) (w_r w')
                else lv_w w'
    end.
  Definition fin_rc (stop : istop) (w' : iw) : Z :=
    match stop with
    | SRet rc => rc
    | SLeave => ret_model 0 (wrap32 (ir_in (w_r w') - ir_have (w_r w'))) (wrap32 (ir_out (w_r w') - ir_left (w_r w'))) (w_r w')
    end.

  Lemma top_wfacts : forall w', WINV w' -> PATI topX w' ->
    WFACTS (w_s (lv_w w')) /\ 16180 <= is_mode (w_s w') <= 16211 /\ 0 <= is_wsize (w_s w') <= 32768
    /\ 0 <= lv_o w' <= 1 /\ lv_o w' <= ir_put (w_r w') /\ 0 <= ir_put (w_r w') <= 1 /\ 0 <= ir_left (w_r w') <= 1 /\ 0 <= ir_have (w_r w') <= 1
    /\ is_window_blk (w_s (lv_w w')) = is_window_blk (w_s w') /\ is_mode (w_s (lv_w w')) = is_mode (w_s w') /\ is_wsize (w_s (lv_w w')) = is_wsize (w_s w')
    /\ ic_next_out (w_c (lv_w w')) = ir_put (w_r w') /\ ic_outbuf (w_c (lv_w w')) = ic_outbuf (w_c w').
  Proof.
    intros [s c r] HW HP. destruct top_lens as (LI & LR).
    destruct HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
    destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & _ & _ & _).
    destruct HP as (Pw & Pwb & _ & _ & _ & _ & Pin & Pin1 & Pout & Pout1 & _ & (_ & _ & POL & _ & _)). cbn [w_s w_c w_r topX ix_input ix_rest0] in *.
    rewrite Pin, LI in Rnh. rewrite Pout, LR in Rpl. change (Z.of_nat 1) with 1 in Rpl.
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM. unfold HEAD, MEM in RM.
    destruct HCORE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    unfold lv_w, lv_o. cbn [w_s w_c w_r]. rewrite lv_pre_shape. cbv zeta. cbn [fst snd].
    assert (WF0 : WFACTS s).
    { unfold WFACTS, uw_wnext0, uw_whave0. split; [exact Pwb|]. split; [intros NE; rewrite (C3 NE), Pwb; reflexivity|].
      destruct (Z.eqb_spec (is_wsize s) 0) as [E|NE]; [split; [lia|]; split; [lia|]| pose proof (C3 NE) as E3; rewrite Pwb in E3; change (shl32 1 15) with 32768 in E3; pose proof (C7 NE); split; [lia|]; split; [lia|]];
        intros NB; destruct (C2 NB) as [E2 _]; rewrite E2, Pwb; reflexivity. }
    split. { destruct (negb (Z.land (is_wrap (s_rest s r)) 4 =? 0) && negb (wrap32 (ir_out r - ic_avail_out (c_rest c r)) =? 0)); exact WF0. }
    split; [lia|]. split. { destruct WF0 as (_ & W2 & _). destruct (Z.eq_dec (is_wsize s) 0); [lia| rewrite (W2 n); lia]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    destruct (negb (Z.land (is_wrap (s_rest s r)) 4 =? 0) && negb (wrap32 (ir_out r - ic_avail_out (c_rest c r)) =? 0)); repeat split; reflexivity.
  Qed.

  Lemma lv_cond_v : forall s c r, 0 <= ir_out r - ir_left r < 2^32 ->
    lv_cond 0 (s_rest s r) (c_rest c r) r = lv_condv 0 (is_mode s) (is_wsize s) (ir_out r - ir_left r).
  Proof.
    intros s c r H. unfold lv_cond, lv_condv, s_rest, c_rest.
    cbn [is_wsize is_mode iset_bits iset_hold ic_avail_out icset_avail_in icset_next_in icset_avail_out icset_next_out].
    rewrite wrap32_id by lia. reflexivity.
  Qed.

  Lemma top_noask : forall stop w' ms1,
    LPOST topX (stop, w') ms1 -> asked stop w' = false ->
    ir_in (w_r w') = arr_len (ic_input (w_c w')) -> - 2^31 <= ir_ret (w_r w') < 2^31 ->
    evt psegs (fun ms' => exists W, (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) /\ IFIN W topX (fin_rc stop w') (fin_w stop w') ms') ms1.
  Proof.
    intros stop w' ms1 (HST & HW' & HA' & HP') HASK HIN HRR. cbn [fst snd] in *.
    pose proof top_ix_ok as XO. destruct top_lens as (LI & LR).
    destruct stop as [|rc]; cbn [fin_w fin_rc].
    2:{ eapply evt_mono; [exact (epilogue_spec topX rc w' ms1 HST XO)|]. intros ms' H. exists (ix_W topX). split; [left; reflexivity| exact H]. }
    destruct (top_wfacts w' HW' HP') as (WF1 & RM & RWS & RO & ROP & RP & RL & RH & EWB & EMO & EWS & ENO & EOB).
    assert (RIN : 0 <= ir_in (w_r w') <= 1).
    { rewrite HIN. destruct HP' as (_ & _ & _ & _ & _ & _ & Pin & _). rewrite Pin. cbn [topX ix_input]. rewrite LI. lia. }
    eapply evt_cut; [exact (leave_pre topX w' ms1 HST XO HW' HA' HP' HIN)|]. intros ms2 H2.
    eapply evt_cut.
    { eapply (leave_decide (ix_W topX) topX (lv_w w') (is_mode (w_s w')) (is_wsize (w_s w')) (lv_o w') ms2 H2); cbn [lv_w w_r topX ix_flush]; unfold lv_o in *; try lia; reflexivity. }
    intros ms3 (x12 & H3). cbn [topX ix_flush] in H3. fold topX in H3.
    rewrite <- (lv_cond_v (w_s w') (w_c w') (w_r w')) in H3 by (unfold lv_o in RO; lia).
    fold (lv_S0 w') (lv_C0 w') in H3.
    destruct (lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w')) eqn:EC.
    -
      assert (EB' : exists b, is_window_blk (w_s (lv_w w')) = Some b).
      { unfold asked in HASK. rewrite EC in HASK. cbn [andb] in HASK. unfold no_window in HASK.
        destruct (is_window_blk (w_s (lv_w w'))) as [b|]; [exists b; reflexivity| discriminate HASK]. }
      destruct EB' as (b & EB).
      assert (HASW : ix_hasw topX = true).
      { destruct HP' as (_ & _ & _ & _ & _ & Pwin & _). apply Pwin. rewrite <- EWB, EB. discriminate. }
      eapply evt_cut.
      { eapply (leave_call_have topX (lv_w w') b x12 _ (lv_o w') ms3 H3 XO HASW EB WF1); cbn [lv_w w_r w_c]; try lia.
        - exact ENO.
        - cbn [topX ix_rest0]. rewrite LR. lia. }
      intros ms4 (x10' & x12' & x15' & x19' & x25' & H4). cbn [lv_w w_s w_c w_r] in H4.
      eapply evt_mono.
      { eapply (leave_tail (ix_WF topX) topX _ x10' x12' x15' x19' x25' ms4 H4 XO); cbn [w_r topX ix_flush]; unfold lv_o in *; lia. }
      intros ms' H. exists (ix_WF topX). split; [right; split; [reflexivity| exact (top_hasw HASW)]|]. cbn [w_r topX ix_flush] in H. fold topX in H.
      unfold lv_w in EOB. cbn [w_c] in EOB. rewrite EOB in H. exact H.
    - eapply evt_mono.
      { eapply (leave_tail (ix_W topX) topX (lv_w w') _ x12 _ _ _ ms3 H3 XO); cbn [lv_w w_r topX ix_flush]; unfold lv_o in *; lia. }
      intros ms' H. exists (ix_W topX). split; [left; reflexivity|]. cbn [lv_w w_r topX ix_flush] in H. fold topX in H. exact H.
  Qed.

  Lemma top_ask_pre : forall w' ms1,
    LPOST topX (SLeave, w') ms1 -> asked SLeave w' = true ->
    ir_in (w_r w') = arr_len (ic_input (w_c w')) ->
    evt psegs (ILVM (ix_W topX) topX (lv_w w') PC_MALLOC (wz 32768) (fun _ => True)) ms1.
  Proof.
    intros w' ms1 (HST & HW' & HA' & HP') HASK HIN. cbn [fst snd] in *.
    pose proof top_ix_ok as XO. destruct top_lens as (LI & LR).
    destruct (top_wfacts w' HW' HP') as (WF1 & RM & RWS & RO & ROP & RP & RL & RH & EWB & EMO & EWS & ENO & EOB).
    unfold asked in HASK. apply andb_prop in HASK. destruct HASK as [EC ENW].
    assert (EB : is_window_blk (w_s (lv_w w')) = None) by (unfold no_window in ENW; destruct (is_window_blk (w_s (lv_w w'))); [discriminate ENW| reflexivity]).
    eapply evt_cut; [exact (leave_pre topX w' ms1 HST XO HW' HA' HP' HIN)|]. intros ms2 H2.
    eapply evt_cut.
    { eapply (leave_decide (ix_W topX) topX (lv_w w') (is_mode (w_s w')) (is_wsize (w_s w')) (lv_o w') ms2 H2); cbn [lv_w w_r topX ix_flush]; unfold lv_o in *; try lia; reflexivity. }
    intros ms3 (x12 & H3). cbn [topX ix_flush] in H3. fold topX in H3.
    rewrite <- (lv_cond_v (w_s w') (w_c w') (w_r w')) in H3 by (unfold lv_o in RO; lia).
    fold (lv_S0 w') (lv_C0 w') in H3. rewrite EC in H3.
    eapply (leave_call_to_malloc topX (lv_w w') x12 _ ms3 H3 XO EB (proj1 WF1)); cbn [lv_w w_r w_c]; try lia.
    - exact ENO.
    - cbn [topX ix_rest0]. rewrite LR. lia.
  Qed.

  Lemma c_rest_proj : forall c r, ic_outbuf (c_rest c r) = ic_outbuf c /\ ic_next_out (c_rest c r) = ir_put r
    /\ ic_avail_out (c_rest c r) = ir_left r /\ ic_avail_in (c_rest c r) = ir_have r.
  Proof. intros. unfold c_rest. repeat split; reflexivity. Qed.

  Lemma top_model_noask : forall stop w' ans,
    inf_loop ivar_ref 0 (W0 s_a zc) = (stop, w') -> WINV w' -> PATI topX w' -> asked stop w' = false ->
    inflate_p ans s_a zc 0 = ((w_s (fin_w stop w'), zret_of_icall (w_c (fin_w stop w')) (fin_rc stop w')), false).
  Proof.
    intros stop w' ans EL HW' HP' HASK.
    rewrite (inflate_p_shape ans s_a zc 0 (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.INV_check _ top_INV)), EL.
    destruct stop as [|rc]; [|reflexivity]. cbn [fin_w fin_rc].
    destruct (top_wfacts w' HW' HP') as (_ & _ & _ & RO & _ & _ & _ & _ & _ & _ & _ & _ & _).
    destruct (c_rest_proj (w_c w') (w_r w')) as (Q1 & Q2 & Q3 & Q4).
    unfold leave_res. cbv zeta. unfold asked, lv_S0, lv_C0 in HASK. unfold lv_S0, lv_C0. rewrite Q1, Q2, Q3, Q4.
    unfold lv_o in *. rewrite !(wrap32_id (ir_out (w_r w') - ir_left (w_r w'))) by lia.
    unfold lv_w. cbn [w_s w_c].
    destruct (lv_cond 0 (s_rest (w_s w') (w_r w')) (c_rest (w_c w') (w_r w')) (w_r w')) eqn:EC; [|reflexivity].
    cbn [andb w_s w_c] in HASK |- *. unfold uw_pure, no_window. unfold no_window, lv_w in HASK. cbn [w_s] in HASK.
    destruct (is_window_blk (fst (lv_pre (s_rest (w_s w') (w_r w')) (c_rest (w_c w') (w_r w')) (w_r w')))) as [b|]; [reflexivity| discriminate HASK].
  Qed.

  Definition fin_c (stop : istop) (w' : iw) : icall := match stop with SRet _ => w_c w' | SLeave => w_c (lv_w w') end.

  Lemma top_cfacts : forall stop w',
    inf_loop ivar_ref 0 (W0 s_a zc) = (stop, w') -> WINV w' -> PATI topX w' ->
    (match stop with SRet rc => rc = Z_NEED_DICT -> RST w' | SLeave => True end) ->
    let c_f := fin_c stop w' in
    ic_avail_in c_f = 1 - ic_next_in c_f /\ 0 <= ic_next_in c_f <= 1 /\ ic_avail_out c_f = 1 - ic_next_out c_f /\ 0 <= ic_next_out c_f <= 1
    /\ ic_next_out c_f = ir_put (w_r w') /\ ic_total_out c_f = to + ic_next_out c_f
    /\ (fin_rc stop w' = Z_OK -> ic_total_in c_f = ti + ic_next_in c_f)
    /\ ic_outbuf c_f = ic_outbuf (w_c w') /\ ir_in (w_r w') = arr_len (ic_input (w_c w')) /\ - 2^31 <= ir_ret (w_r w') < 2^31.
  Proof.
    intros stop w' EL HW' HP' HRST. cbv zeta.
    destruct top_lens as (LI & LR). destruct top_W0 as (HW0 & HPHI & _ & _).
    pose proof top_ix_ok as XO. destruct XO as [_ _ X3 X4 _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_input ix_rest0 il_NI il_NO] in X3, X4. rewrite LI in X3. rewrite LR in X4.
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & SPB & B63 & _).
    pose proof top_blocks as (_ & _ & _ & _ & BLB). destruct INC as (bc & Hbc & EC1 & EC2). destruct INU as (bu & Hbu & EU1 & EU2).
    pose proof (BLB _ Hbc) as RC. pose proof (BLB _ Hbu) as RU. rewrite EC1, EC2 in RC. rewrite EU1, EU2 in RU.
    assert (RLO : lo < 2^63). { destruct SIF as (SF1 & SF2 & _). unfold Z_INFLATE_STACK, RMALLOC_STACK, ZS_SIZEOF in *. lia. }
    pose proof (inf_loop_fi ti (ZIface.zlength (zc_input zc)) (ZIface.zlength (zc_input zc)) 0 (W0 s_a zc) (W0_FI s_a zc)) as HFI.
    rewrite EL in HFI. cbn [fst snd] in HFI.
    (* zl14infl-r2: a direct return keeps FIR only (DICT moves total_in); the leave keeps FI *)
    assert (EIN : ir_in (w_r w') = arr_len (ic_input (w_c w'))).
    { destruct stop as [|rc]; [destruct HFI as (_ & FI2 & FI3 & _) | destruct HFI as ((FI2 & FI3 & _) & _)]; rewrite FI2, FI3; reflexivity. }
    pose proof HW' as (_ & HREGS & _). destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    destruct HP' as (_ & _ & _ & _ & _ & _ & Pin & _ & Pout & _). cbn [topX ix_input ix_rest0] in Pin, Pout. rewrite Pin, LI in Rnh. rewrite Pout, LR in Rpl. change (Z.of_nat 1) with 1 in Rpl.
    destruct (Z.eq_dec (is_mode s_a) MEM) as [EM|NM].
    -
      rewrite (inf_loop_MEM 0 (W0 s_a zc)) in EL.
      2:{ unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      2:{ cbn [W0 w_c icall_of_zcall ic_avail_in]. unfold ZIface.zlength. lia. }
      2:{ cbn [W0 w_c icall_of_zcall ic_avail_out zc_avail_out zi_zcall]. lia. }
      injection EL as <- <-. cbn [fin_c fin_rc W0 w_c w_r icall_of_zcall ic_avail_in ic_next_in ic_avail_out ic_next_out ic_total_out ic_total_in ic_outbuf ic_input ir_put ir_in ir_ret zc_strm zc_avail_out zi_zcall].
      rewrite arr_len_of_list in LI |- *. cbn [zc_input zi_zcall] in LI. rewrite LI. unfold Z_MEM_ERROR, Z_OK.
      repeat split; try lia; try reflexivity; try (intros E; discriminate E).
    - assert (HBK : BK 1 to (W0 s_a zc)).
      { unfold BK, caseA, W0. cbn [w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out zc_strm zc_avail_out zi_zcall]. unfold arr_make. rewrite arr_len_init.
        pose proof top_INV as (_ & _ & HMF). pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM.
        split; [reflexivity|]. unfold s_entry. destruct (Z.eqb_spec (is_mode s_a) TYPE) as [E|E]; cbn [is_mode iset_mode];
          (split; [unfold TYPEDO, MEM in *; lia|]); (split; [unfold TYPEDO, SYNC, MEM in *; lia|]); left; split; reflexivity. }
      pose proof (inf_loop_bk 0 1 to (W0 s_a zc) HW0 HBK HPHI) as HB. rewrite EL in HB. destruct HB as (_ & HBK' & HRET).
      destruct stop as [|rc]; cbn [fin_c fin_rc].
      + destruct HFI as (FI1 & _ & _ & FI4). cbn [zc_strm zi_zcall] in FI1.
        destruct w' as [s' c' r']. unfold lv_w. cbn [w_s w_c w_r] in *.
        destruct (final_leave_facts s' c' r' ti to 1 (proj1 (proj2 HW')) HBK' FI1 EIN ltac:(lia) ltac:(rewrite Pin, LI; lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
        rewrite F1, F2, F3, F4, F5, F6, F7. repeat split; try lia; try exact EIN.
      + destruct HFI as ((_ & _ & FR3) & _). destruct HRET as [ERC _]. destruct (HRST ERC) as (R1 & R2 & R3 & R4 & R5).
        destruct HBK' as (_ & _ & _ & BC). rewrite R1, R2, R3, R4, R5.
        assert (ETO : ic_total_out (w_c w') = to).
        { destruct BC as [(A1 & _)|(A1 & _)]; [exact A1|]. rewrite A1, R5, Z.add_0_r. apply wrap64_id. lia. }
        rewrite ETO. rewrite ERC. unfold Z_NEED_DICT, Z_OK. repeat split; try lia; try exact EIN; try (intros E; discriminate E).
  Qed.

  Lemma top_data : forall (Xf : ictx) W s_f c_f r_f m' (w_f : option bptr) (Awf : Z) s_c',
    IMEMF W Xf (mkW s_f c_f r_f) m' ->
    ix_L Xf = Z_irep.mkIL S As Awf (C + ti) (U + to) -> ix_rest0 Xf = rest0 ->
    ir_put r_f = ic_next_out c_f -> ic_avail_in c_f = 1 - ic_next_in c_f -> ic_avail_out c_f = 1 - ic_next_out c_f -> 0 <= ic_next_out c_f <= 1 ->
    ic_total_out c_f = to + ic_next_out c_f ->
    u8arr psegs m' U (firstn (Z.to_nat to) (to_bytes uc)) -> u8arr psegs m' (U + to + 1) (skipn (Z.to_nat to + 1) (to_bytes uc)) ->
    IREL s_f (mkIZ s_c' (zstrm_of_icall c_f)) -> ATY s_f -> PATIq s_f -> (w_f = None <-> is_window_blk s_f = None) ->
    (exists p1' p2', rw_cells psegs m' S (zs_pub (C + ti + ic_next_in c_f) (1 - ic_next_in c_f) (ic_total_in c_f) (U + ic_total_out c_f)
                                               (1 - ic_next_out c_f) (ic_total_out c_f) p1' p2'))
    /\ zr_i_def m' S (iblk_list w_f Awf sp_ As) (mkIZ s_c' (zstrm_of_icall c_f))
    /\ u8arr psegs m' U (to_bytes (zstore uc to (arr_slice (ic_outbuf c_f) 0 (ic_next_out c_f)))).
  Proof.
    intros Xf W s_f c_f r_f m' w_f Awf s_c' (STK & [ZS ST] & IN & OUT & MI & MU & WM) EL ER EP E1 E3 RNO ETO U1 U3 HI HA HPq HWf.
    cbn [w_s w_c w_r] in *. rewrite EL, ER in *. rewrite EP in OUT.
    destruct (izs_to_pub _ _ _ ZS) as ((q1 & q2 & PUB') & ZQ). cbn [il_S il_NI il_NO] in PUB'.
    split; [|split].
    - exists q1, q2. rewrite E1, E3 in PUB'. replace (U + ic_total_out c_f) with (U + to + ic_next_out c_f) by lia. exact PUB'.
    - exists s_f, (Z_irep.mkIL S As Awf (C + ti) (U + to)), w_f, sp_. cbn [il_S il_As il_Aw iz_z].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HWf|]. split; [split; [exact ZQ| exact ST]|]. split; [exact HI|]. split; [exact HA| exact HPq].
    - unfold iout in OUT. cbn [il_NO] in OUT.
      apply (uncompr_join m' U uc to c_f (ic_next_out c_f)); [unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia| lia| exact U1| exact OUT| exact U3].
  Qed.

  Lemma lvw_fields : forall w', let s1 := w_s (lv_w w') in let s := w_s w' in
    is_wrap s1 = is_wrap s /\ is_wbits s1 = is_wbits s /\ is_head s1 = is_head s /\ is_flags s1 = is_flags s /\ is_mode s1 = is_mode s
    /\ is_last s1 = is_last s /\ is_havedict s1 = is_havedict s /\ is_window s1 = is_window s /\ is_window_blk s1 = is_window_blk s.
  Proof.
    intros [s c r]. cbv zeta. unfold lv_w. cbn [w_s w_c w_r]. rewrite lv_pre_shape. cbv zeta. cbn [fst].
    destruct (negb (Z.land (is_wrap (s_rest s r)) 4 =? 0) && negb (wrap32 (ir_out r - ic_avail_out (c_rest c r)) =? 0)); repeat split; reflexivity.
  Qed.

  Lemma top_hasw_iff : forall w', PATI topX w' -> (w = None <-> is_window_blk (w_s w') = None).
  Proof.
    intros w' (_ & _ & _ & _ & _ & Pwin & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PHW)). cbn [topX ix_hasw] in Pwin, PHW. split.
    - intros E. destruct (is_window_blk (w_s w')) eqn:EB; [|reflexivity]. exfalso. specialize (Pwin ltac:(discriminate)). rewrite E in Pwin. discriminate Pwin.
    - intros E. destruct w as [wp|] eqn:EW; [|reflexivity]. exfalso. exact (PHW eq_refl E).
  Qed.

  Lemma top_succ_noask : forall stop w', WINV w' -> PATI topX w' -> asked stop w' = false ->
    PATIq (w_s (fin_w stop w')) /\ (w = None <-> is_window_blk (w_s (fin_w stop w')) = None).
  Proof.
    intros stop w' HW' HP' HASK. pose proof (top_hasw_iff w' HP') as HIFF.
    destruct (lvw_fields w') as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). cbv zeta in *.
    pose proof HP' as HP0. destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (POB & POW & _)).
    assert (HIFF1 : w = None <-> is_window_blk (w_s (lv_w w')) = None) by (rewrite F9; exact HIFF).
    assert (HPQ' : forall s_f, is_wrap s_f = is_wrap (w_s w') -> is_wbits s_f = is_wbits (w_s w') -> is_head s_f = is_head (w_s w') -> is_flags s_f = is_flags (w_s w') ->
                    is_mode s_f = is_mode (w_s w') -> is_last s_f = is_last (w_s w') -> is_havedict s_f = is_havedict (w_s w') ->
                    (forall i, 0 <= i < arr_len (is_window s_f) -> 0 <= arr_get (is_window s_f) i < 256) -> PATIq s_f).
    { intros s_f E1 E2 E3 E4 E5 E6 E7 HB. destruct w' as [s' c' r']. exact (PATIq_of_PATI topX s' c' r' s_f HP' E1 E2 E3 E4 (or_introl E5) E6 E7 HB). }
    destruct stop as [|rc]; cbn [fin_w].
    2:{ split; [|exact HIFF]. apply HPQ'; try reflexivity. exact POW. }
    destruct (lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w')) eqn:EC; cbn [w_s].
    2:{ split; [|exact HIFF1]. apply HPQ'; try assumption. rewrite F8. exact POW. }
    destruct (top_wfacts _ HW' HP') as ((Hwb & Hws & Hwn & Hwh & _) & _ & _ & RO & ROP & _).
    rewrite (updw_small _ (ic_outbuf (w_c w')) (ir_put (w_r w')) (lv_o w') Hwb RO Hws Hwn Hwh). unfold uw_set.
    split; [|exact HIFF1].
    apply HPQ'; cbn [is_wrap is_wbits is_head is_flags is_mode is_last is_havedict is_window is_window_blk iset_whave iset_wnext iset_wsize iset_window]; try assumption.
    apply window_blit_bytes; [rewrite F8; exact POW|]. intros j Hj. apply POB. unfold lv_o in *. lia.
  Qed.

  Lemma top_pres_core : forall W m' put_f,
    (forall a, 0 <= a < 2^64 -> outside W a -> (bv_unsigned sp <= a \/ in_block LB a \/ (0x28000 <= a < 0x5b000 /\ ~ ralloc_static a)) ->
               m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    (wview psegs m (wa (U + to)) <> None -> wview psegs m' (wa (U + to)) <> None) ->
    (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) ->
    0 <= put_f <= 1 -> (put_f = 0 -> u8arr psegs m' (U + to) rest0) ->
    lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF); (U + to, U + to + put_f)] m m'.
  Proof.
    intros W m' put_f AG WNO HWc RP HU0 a Ra (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX.
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (_ & _ & UM & _).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    destruct (Z.eq_dec a (U + to)) as [EA|NA].
    - assert (P0 : put_f = 0) by lia. specialize (HU0 P0). split; [|rewrite EA; exact WNO].
      destruct UM as [(_ & _ & B1) _]. destruct HU0 as [(_ & _ & B2) _].
      assert (L0 : (0 < length rest0)%nat) by (rewrite LR; lia).
      pose proof (B1 0%nat L0) as Q1. pose proof (B2 0%nat L0) as Q2. rewrite Z.add_0_r in Q1, Q2. rewrite <- EA in Q1, Q2.
      assert (ROM : seg_rom psegs (wa a) = None).
      { apply RMallocRep.ref_seg_rom_none. destruct INU as (bu & Hbu & EU1 & EU2). pose proof (HBR _ _ _ bu (proj1 ENV) (in_or_app _ _ _ (or_intror Hbu))) as (_ & _ & _ & _ & R5).
        rewrite EU1, EU2 in R5. unfold wa. rewrite unsigned_lit by lia. lia. }
      unfold mrd in Q1, Q2. rewrite ROM in Q1, Q2. destruct (m (wa a)), (m' (wa a)); congruence.
    - assert (OUTW : outside W a).
      { assert (CL : bv_unsigned sp <= a \/ (exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b) \/ 0x28000 <= a < 0x5b000).
        { destruct HC as [H|[H|[H _]]]; [left; exact H| right; left; exact H| right; right; exact H]. }
        assert (OS : a < As \/ As + 7176 <= a).
        { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (SEPS _ Hb) as Q; unfold apart in Q; lia| lia]. }
        assert (OL : a < lo \/ bv_unsigned sp <= a).
        { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (BLB _ Hb); lia| lia]. }
        destruct HWc as [-> |(-> & NEW)]; unfold ix_WF, ix_W; cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_Aw il_NO app outside]; rewrite ?LR; change (Z.of_nat 1) with 1.
        - repeat split; lia.
        - destruct (BW NEW) as ((Q1 & _ & _ & Q4) & Q2 & _ & Q5).
          assert (OWn : a < Awl \/ Awl + 32768 <= a).
          { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (Q5 _ Hb) as Q; unfold apart in Q; lia| lia]. }
          repeat split; lia. }
      exact (AG a Ra OUTW HC).
  Qed.

  Lemma top_pres : forall W m' put_f,
    munch W m m' -> wmono psegs m m' -> (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) ->
    0 <= put_f <= 1 -> (put_f = 0 -> u8arr psegs m' (U + to) rest0) ->
    lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF); (U + to, U + to + put_f)] m m'.
  Proof.
    intros W m' put_f MU WM. apply top_pres_core; [|apply WM].
    intros a Ra OUTW _. split; [apply MU; unfold wa; rewrite unsigned_lit by lia; exact OUTW| apply WM].
  Qed.

  Lemma top_env_gen : forall W mb m' (spb spx : word) (stx : PState) (errx : word),
    lx_env mb stx OW LB spb tp B lo errx canary ->
    munch W mb m' -> wmono psegs mb m' -> mem_inv psegs m' -> stk psegs m' lo (bv_unsigned spx) -> bv_unsigned spx <= bv_unsigned sp ->
    (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) ->
    lx_env m' stx OW LB spx tp B lo errx canary.
  Proof.
    intros W mb m' spb spx stx errx ENVx MU WM MI' STK' SPX HWc.
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ X4 _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S il_NO ix_rest0] in X1, X4. rewrite LR in X4. change (Z.of_nat 1) with 1 in X4.
    pose proof ENVx as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & _).
    destruct SIF as (SF1 & SF2 & _). unfold ZS_SIZEOF in SF2. destruct INU as (bu & Hbu & EU1 & EU2).
    assert (WOK0 : Forall (rclient_write_ok (OW ++ LB)) (ix_W topX)).
    { unfold ix_W. cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_NO]. rewrite LR. change (Z.of_nat 1) with 1.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold rclient_write_ok; cbn [fst snd].
      - left. lia.
      - left. lia.
      - right; right. exists (sp_, As, 7176). split; [apply in_or_app; left; unfold iblk_list; apply in_or_app; right; left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
      - right; right. exists bu. split; [apply in_or_app; right; exact Hbu|]. rewrite EU1, EU2. lia. }
    assert (OUT0 : forall a, B <= a \/ 0x28000 <= a < 0x5b000 -> outside (ix_W topX) a).
    { intros a Ha. unfold ix_W. cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_NO outside]. rewrite LR. change (Z.of_nat 1) with 1.
      pose proof (BLB _ Hbu) as RU. rewrite EU1, EU2 in RU. pose proof (HBR _ _ _ bu (proj1 ENVx) (in_or_app _ _ _ (or_intror Hbu))) as (_ & _ & _ & _ & R5). rewrite EU1, EU2 in R5.
      repeat split; lia. }
    destruct SIF as (SF0 & _). eapply (lx_env_munch W mb m' stx OW LB spb spx tp B lo errx canary HFRAME ENVx MU WM MI' STK'); [pose proof ENV as E9; unfold lx_env in E9; destruct E9 as (_ & _ & _ & _ & _ & _ & SPB9 & _); lia| |].
    - destruct HWc as [-> |(-> & NEW)]; [exact WOK0|]. unfold ix_WF. apply Forall_app. split; [exact WOK0|]. constructor; [|constructor].
      destruct w as [wp|] eqn:EW; [|exfalso; apply NEW; reflexivity]. right; right. exists (wp, Awl, 32768). cbn [topX ix_L il_Aw fst snd blk_addr blk_size].
      split; [apply in_or_app; left; left; reflexivity| lia].
    - intros a Ha. destruct HWc as [-> |(-> & NEW)]; [exact (OUT0 a Ha)|]. unfold ix_WF. apply outside_app || idtac.
      destruct (BW NEW) as ((Q1 & _ & _ & Q4) & Q2 & _). pose proof (OUT0 a Ha) as O0. unfold ix_W in *. cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_Aw il_NO app outside] in *.
      repeat split; lia.
  Qed.
  Lemma top_env : forall W m' (spx : word) (stx : PState) (errx : word),
    lx_env m stx OW LB sp tp B lo errx canary ->
    munch W m m' -> wmono psegs m m' -> mem_inv psegs m' -> stk psegs m' lo (bv_unsigned spx) -> bv_unsigned spx <= bv_unsigned sp ->
    (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) ->
    lx_env m' stx OW LB spx tp B lo errx canary.
  Proof. intros W m' spx stx errx. apply top_env_gen. Qed.

  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.
  Hypothesis FRM0 : frm0 fc.

  Lemma top_noask_post : forall stop w' ms',
    inf_loop ivar_ref 0 (W0 s_a zc) = (stop, w') -> WINV w' -> PATI topX w' -> asked stop w' = false ->
    (match stop with SRet rc => rc = Z_NEED_DICT -> RST w' | SLeave => True end) ->
    (exists W, (W = ix_W topX \/ (W = ix_WF topX /\ w <> None)) /\ IFIN W topX (fin_rc stop w') (fin_w stop w') ms') ->
    i_wants comprc x w = false /\
    inflate_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB S C U comprc uc x w Aw sp_ As lo B canary m None st ms'.
  Proof.
    intros stop w' ms' EL HW' HP' HASK HRST (W & HWc & HFIN).
    pose proof (top_model_noask stop w' (wans_g (gwb []) true) EL HW' HP' HASK) as EM.
    destruct (zi_step s_a x comprc (gwb []) true HIREL HATY top_ZC) as (s_c' & EZI & HIREL' & HATY' & EWW). cbv zeta in EZI, HIREL', HATY', EWW.
    change Z_NO_FLUSH with 0 in EZI, HIREL', HATY', EWW. rewrite EM in EZI, HIREL', HATY', EWW. cbn [fst snd] in EZI, HIREL', HATY', EWW.
    assert (EIW : i_wants comprc x w = false).
    { unfold i_wants, the_zapi. cbn [i_wants_window zinst]. rewrite EWW. reflexivity. }
    split; [exact EIW|].
    destruct (top_cfacts stop w' EL HW' HP' HRST) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10). cbv zeta in *.
    destruct (top_succ_noask stop w' HW' HP' HASK) as (HPQ' & HIFF').
    assert (ECF : w_c (fin_w stop w') = fin_c stop w').
    { destruct stop; cbn [fin_w fin_c]; [|reflexivity]. destruct (lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w')); reflexivity. }
    assert (ERF : w_r (fin_w stop w') = w_r w').
    { destruct stop; cbn [fin_w]; [|reflexivity]. destruct (lv_cond 0 (lv_S0 w') (lv_C0 w') (w_r w')); reflexivity. }
    destruct HFIN as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & HMEMF).
    destruct (fin_w stop w') as [s_f c_f r_f] eqn:EFW. cbn [w_s w_c w_r] in *. subst c_f r_f.
    pose proof HMEMF as (STK' & _ & _ & OUT' & MI' & MU' & WM'). cbn [topX ix_m0 ix_lo ix_sp ix_L ix_rest0 w_c w_r] in STK', OUT', MU', WM'.
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (LR & U1 & UM & U3).
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    destruct INU as (bu & Hbu & EU1 & EU2). pose proof (BLB _ Hbu) as RU. pose proof (SEPS _ Hbu) as SU. rewrite EU1, EU2 in RU, SU. unfold apart in SU.
    assert (LU1 : Z.of_nat (length (firstn (Z.to_nat to) (to_bytes uc))) = to) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_firstn, length_map; lia).
    assert (LU3 : Z.of_nat (length (skipn (Z.to_nat to + 1) (to_bytes uc))) = size - to - 1) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_skipn, length_map; lia).
    assert (DJ : forall A n, U <= A -> A + n <= U + size -> (A + n <= U + to \/ U + to + 1 <= A) -> 0 <= n -> disjoint_from W A n).
    { intros A n H1 H2 H3 H4. destruct HWc as [-> |(-> & NEW)]; unfold ix_WF, ix_W; cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_Aw il_NO app disjoint_from]; rewrite ?LR; change (Z.of_nat 1) with 1.
      - repeat split; lia.
      - destruct (BW NEW) as (_ & _ & _ & Q5). pose proof (Q5 _ Hbu) as Q. rewrite EU1, EU2 in Q. unfold apart in Q. repeat split; lia. }
    apply (u8arr_transport psegs W m m') in U1; [| exact MU'| exact WM'| rewrite LU1; apply DJ; lia].
    apply (u8arr_transport psegs W m m') in U3; [| exact MU'| exact WM'| rewrite LU3; apply DJ; lia].
    destruct (top_data topX W s_f (fin_c stop w') (w_r w') m' w Awl s_c' HMEMF eq_refl eq_refl ltac:(symmetry; exact C5) C1 C3 C4 C6 U1 U3 HIREL' HATY' HPQ' HIFF')
      as ((q1 & q2 & PUB') & ZR' & UARR').
    unfold inflate_post. exists t0, t1, t2, (wz (fin_rc stop w')), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m', q1, q2, Awl, (C + ti + ic_next_in (fin_c stop w')).
    unfold i_ok. rewrite EIW. unfold i_window. rewrite EIW. unfold the_zapi. cbn [i_inflate i_total_in i_total_out zinst].
    rewrite EZI. cbn [zr_strm zr_consumed zr_output zr_rc zret_of_icall iz_z zs_total_in zs_total_out zstrm_of_icall].
    assert (ESL : ZIface.zlength (arr_slice (ic_outbuf (fin_c stop w')) 0 (ic_next_out (fin_c stop w'))) = ic_next_out (fin_c stop w')) by (apply zlength_slice; lia).
    change (Prelim.zlength (arr_slice (ic_outbuf (fin_c stop w')) 0 (ic_next_out (fin_c stop w')))) with (ZIface.zlength (arr_slice (ic_outbuf (fin_c stop w')) 0 (ic_next_out (fin_c stop w')))).
    rewrite ESL. destruct top_lens as (LI & _). rewrite arr_len_of_list in LI. rewrite LI.
    change (Zlib_iface.iblocks w Awl sp_ As) with (iblk_list w Awl sp_ As).
    split; [exact EMS|]. split.
    { unfold lx_post_env. split; [exists errv; exact (top_env W m' sp st errv ENV MU' WM' MI' STK' ltac:(lia) HWc)|]. split; [exact FRM0|].
      split; [|split; reflexivity].
      apply (top_pres W m' (ic_next_out (fin_c stop w')) MU' WM' HWc C4). intros E0. unfold iout in OUT'. cbn [il_NO] in OUT'. rewrite C5 in E0. rewrite E0, iout_bytes_0 in OUT'. exact OUT'. }
    split; [exact HWA|]. split; [unfold wint; apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity|].
    split; [exact PUB'|]. split; [intros E; rewrite (C7 E); lia|]. split; [rewrite ER; exact ZR'| exact UARR'].
  Qed.


  Lemma top_model_ask : forall w' ans,
    inf_loop ivar_ref 0 (W0 s_a zc) = (SLeave, w') -> WINV w' -> PATI topX w' -> asked SLeave w' = true ->
    inflate_p ans s_a zc 0
    = (match ans with
       | None => (iset_mode (w_s (lv_w w')) MEM, zret_of_icall (w_c (lv_w w')) Z_MEM_ERROR)
       | Some (b, g) => (updw_core (iset_window (iset_window_blk (w_s (lv_w w')) (Some b)) (iarr_u8_of g 0 32768)) (ic_outbuf (w_c w')) (ir_put (w_r w')) (lv_o w'),
                         zret_of_icall (w_c (lv_w w')) (fin_rc SLeave w'))
       end, true).
  Proof.
    intros w' ans EL HW' HP' HASK.
    rewrite (inflate_p_shape ans s_a zc 0 (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.INV_check _ top_INV)), EL.
    destruct (top_wfacts w' HW' HP') as ((Hwb & _) & _ & _ & RO & _).
    destruct (c_rest_proj (w_c w') (w_r w')) as (Q1 & Q2 & Q3 & Q4).
    unfold leave_res. cbv zeta. unfold asked, lv_S0, lv_C0 in HASK. rewrite Q1, Q2, Q3, Q4. cbn [fin_rc].
    unfold lv_o in *. rewrite !(wrap32_id (ir_out (w_r w') - ir_left (w_r w'))) by lia.
    apply andb_prop in HASK. destruct HASK as [EC ENW]. rewrite EC.
    unfold lv_w in *. cbn [w_s w_c] in *. unfold uw_pure, lv_mem. rewrite ENW. unfold no_window in ENW.
    destruct (is_window_blk (fst (lv_pre (s_rest (w_s w') (w_r w')) (c_rest (w_c w') (w_r w')) (w_r w')))) as [b|]; [discriminate ENW|].
    rewrite Hwb. change (shl32 1 15) with 32768.
    destruct ans as [[b g]|]; reflexivity.
  Qed.

  Lemma top_iw : forall stop w', inf_loop ivar_ref 0 (W0 s_a zc) = (stop, w') -> WINV w' -> PATI topX w' ->
    i_wants comprc x w = asked stop w'.
  Proof.
    intros stop w' EL HW' HP'.
    destruct (zi_step s_a x comprc (gwb []) true HIREL HATY top_ZC) as (_ & _ & _ & _ & EWW). cbv zeta in EWW. change Z_NO_FLUSH with 0 in EWW.
    unfold i_wants, the_zapi. cbn [i_wants_window zinst]. rewrite EWW.
    destruct (asked stop w') eqn:EA.
    - destruct stop as [|rc]; [|discriminate EA]. rewrite (top_model_ask w' _ EL HW' HP' EA). cbn [snd andb].
      unfold asked in EA. apply andb_prop in EA. destruct EA as [_ ENW]. unfold no_window in ENW.
      destruct (lvw_fields w') as (_ & _ & _ & _ & _ & _ & _ & _ & F9). cbv zeta in F9.
      assert (EB : is_window_blk (w_s (lv_w w')) = None) by (destruct (is_window_blk (w_s (lv_w w'))); [discriminate ENW| reflexivity]).
      rewrite EB in F9. rewrite (proj2 (top_hasw_iff w' HP') (eq_sym F9)). reflexivity.
    - rewrite (top_model_noask stop w' _ EL HW' HP' EA). reflexivity.
  Qed.

  Lemma top_ask_malloc : forall w' ms1 (Q : option bptr -> PState -> machine_state -> Prop),
    ILVM (ix_W topX) topX (lv_w w') PC_MALLOC (wz 32768) (fun _ => True) ms1 ->
    (forall x21 x22 x23 x26 x27 m1 r st' ms2,
        rw_cells psegs m1 (bv_unsigned sp + -272)
          [C8 (wz (ir_out (w_r w') - ir_left (w_r w'))); C8 (wz (ir_left (w_r w'))); C8 (wz (ir_have (w_r w'))); C8 (wz (ir_ret (w_r w')));
           C8 (wz As); C8 (wz PC_LV_BACK)] ->
        iframeL topX (w_r w') m1 -> IREP m1 L (w_s (lv_w w')) (w_c (lv_w w')) -> iin m1 topX -> iout m1 L rest0 (w_c (lv_w w')) (ir_put (w_r w')) ->
        munch (ix_W topX) m m1 -> wmono psegs m m1 ->
        lx_env m1 st OW LB (wz (bv_unsigned sp + -272)) tp B lo errv canary ->
        rmalloc_post (wz PC_UW_RET) (wz (bv_unsigned sp + -272)) gp tp (wz (U + to + ir_put (w_r w'))) (wz (ir_out (w_r w') - ir_left (w_r w')))
                     (wz 1) (wz As) (wz (ir_out (w_r w') - ir_left (w_r w'))) (wz (ir_in (w_r w'))) x21 x22 x23 (wz (ir_out (w_r w'))) x27 x26 F fc st (OW ++ LB) 32768 lo B m1 r st' ms2 ->
        evt psegs (Q r st') ms2) ->
    implM psegs (raw_malloc 32768) st Q ms1.
  Proof.
    intros w' ms1 Q HM K.
    destruct HM as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x21 & x22 & x23 & x26 & x27 & t3 & t4 & t5 & t6 & m1 & -> & FRU & FRI & STK1 & HREP1 & IN1 & OUT1 & MI1 & MU1 & WM1 & _).
    cbn [topX ix_sp ix_gp ix_tp ix_L ix_lo ix_F ix_fc ix_m0 ix_rest0 il_NO il_As lv_w w_r w_s w_c] in *. fold topX in *.
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    assert (E272 : bv_unsigned (wz (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 st OW LB (wz (bv_unsigned sp + -272)) tp B lo errv canary).
    { apply (top_env (ix_W topX) m1 (wz (bv_unsigned sp + -272)) st errv ENV MU1 WM1 MI1); [rewrite E272; exact STK1| rewrite E272; lia| left; reflexivity]. }
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
    eapply implM_post_evt''.
    { eapply (MALLOC (wz PC_UW_RET) (wz (bv_unsigned sp + -272)) gp tp t0 t1 t2 _ _ (wz 32768) a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m1 st (OW ++ LB) 32768 lo B errv);
        [exact HP1| exact AUX1| exact SPB1| exact ST1| exact LOC1| rewrite E272; unfold Z_INFLATE_STACK in LOSP; lia| exact ERR1| exact MI1| exact TP1| reflexivity| lia]. }
    intros r st' ms2 PO. eapply (K x21 x22 x23 x26 x27 m1 r st' ms2); try eassumption.
  Qed.

  Lemma top_ask_rebase : forall w' m1 m2,
    WINV w' -> PATI topX w' -> is_window_blk (w_s (lv_w w')) = None ->
    rheap_pres (OW ++ LB) (bv_unsigned sp + -272) m1 m2 ->
    rw_cells psegs m1 (bv_unsigned sp + -272)
      [C8 (wz (ir_out (w_r w') - ir_left (w_r w'))); C8 (wz (ir_left (w_r w'))); C8 (wz (ir_have (w_r w'))); C8 (wz (ir_ret (w_r w')));
       C8 (wz As); C8 (wz PC_LV_BACK)] ->
    iframeL topX (w_r w') m1 -> IREP m1 L (w_s (lv_w w')) (w_c (lv_w w')) -> iin m1 topX -> iout m1 L rest0 (w_c (lv_w w')) (ir_put (w_r w')) ->
    rw_cells psegs m2 (bv_unsigned sp + -272)
      [C8 (wz (ir_out (w_r w') - ir_left (w_r w'))); C8 (wz (ir_left (w_r w'))); C8 (wz (ir_have (w_r w'))); C8 (wz (ir_ret (w_r w')));
       C8 (wz As); C8 (wz PC_LV_BACK)]
    /\ iframeL topX (w_r w') m2 /\ IREP m2 L (w_s (lv_w w')) (w_c (lv_w w')) /\ iin m2 topX /\ iout m2 L rest0 (w_c (lv_w w')) (ir_put (w_r w')).
  Proof.
    intros w' m1 m2 HW' HP' EB HPR FRU FRI HREP IN1 OUT1.
    destruct (top_wfacts w' HW' HP') as (_ & _ & _ & _ & _ & RP & _).
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    pose proof top_ix_ok as XO. destruct XO as [X1 X2 X3 X4 _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp ix_input ix_rest0 il_S il_As il_NI il_NO] in X1, X2, X3, X4.
    destruct INC as (bc & Hbc & EC1 & EC2). destruct INU as (bu & Hbu & EU1 & EU2).
    pose proof (BLB _ Hbc) as RC. pose proof (BLB _ Hbu) as RU.
    assert (RLO : lo < 2^63). { destruct SIF as (SF1 & SF2 & _). pose proof ENV as E9. unfold lx_env in E9. destruct E9 as (_ & _ & _ & _ & _ & _ & SPB9 & B63 & _). unfold Z_INFLATE_STACK, RMALLOC_STACK in *. lia. }
    split.
    - eapply Z_dview.rw_cells_agree; [exact FRU|]. apply (agree_iv (OW ++ LB) (bv_unsigned sp + -272)); [exact HPR| lia| cbn [cells_size csize Nat.add]; lia|].
      intros a Ha. left. lia.
    - eapply (imem_heap_pres topX _ _ (w_r w') (ir_put (w_r w')) (OW ++ LB) (bv_unsigned sp + -272) m1 m2 (sp_, As, 7176) bc bu HPR);
        cbn [topX ix_L ix_lo ix_sp ix_input ix_rest0 il_S il_As il_NI il_NO blk_addr blk_size fst snd]; rewrite ?LI, ?LR; change (Z.of_nat 1) with 1;
        try eassumption; try lia.
      + apply in_or_app. left. unfold iblk_list. apply in_or_app. right. left. reflexivity.
      + apply in_or_app. right. exact Hbc.
      + apply in_or_app. right. exact Hbu.
  Qed.

  Definition topXm (mb : mem) : ictx :=
    mkIX L 0 lo (arr_of_list (zc_input zc)) rest0 hasw mb sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc.
  Lemma topXm_ok : forall mb, ix_ok (topXm mb).
  Proof. intros mb. destruct top_ix_ok as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]. constructor; assumption. Qed.

  Lemma top_ask_null_evt : forall w' m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6,
    WINV w' -> PATI topX w' -> is_window_blk (w_s (lv_w w')) = None ->
    rw_cells psegs m2 (bv_unsigned sp + -272)
      [C8 (wz (ir_out (w_r w') - ir_left (w_r w'))); C8 (wz (ir_left (w_r w'))); C8 (wz (ir_have (w_r w'))); C8 (wz (ir_ret (w_r w')));
       C8 (wz As); C8 (wz PC_LV_BACK)] ->
    iframeL topX (w_r w') m2 -> IREP m2 L (w_s (lv_w w')) (w_c (lv_w w')) -> iin m2 topX -> iout m2 L rest0 (w_c (lv_w w')) (ir_put (w_r w')) ->
    mem_inv psegs m2 -> stk psegs m2 lo (bv_unsigned sp + -272) ->
    evt psegs (IFIN (ix_W (topXm m2)) (topXm m2) Z_MEM_ERROR (mkW (iset_mode (w_s (lv_w w')) MEM) (w_c (lv_w w')) (w_r w')))
      (MS (mkR (wz PC_UW_RET) (wz (bv_unsigned sp + -272)) gp tp t0 t1 t2 (wz (U + to + ir_put (w_r w'))) (wz (ir_out (w_r w') - ir_left (w_r w'))) (wz 0)
               a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz As) (wz (ir_out (w_r w') - ir_left (w_r w'))) (wz (ir_in (w_r w'))) x21 x22 x23 (wz (ir_out (w_r w'))) x27 x26 t3 t4 t5 t6)
          F (wz PC_UW_RET) fc None m2 (seg_rom psegs)).
  Proof.
    intros w' m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6 HW' HP' EB FRU FRI HREP IN2 OUT2 MI2 STK2.
    destruct (top_wfacts w' HW' HP') as (_ & _ & _ & _ & _ & RP & _). destruct top_lens as (_ & LR).
    eapply (leave_from_malloc_null (topXm m2) (lv_w w') (fun _ => True)); [| exact (topXm_ok m2)| exact EB| cbn [lv_w w_r topXm ix_rest0]; rewrite LR; lia].
    unfold ILVM. cbn [lv_w w_r w_s w_c topXm ix_sp ix_gp ix_tp ix_L ix_lo ix_F ix_fc ix_m0 ix_rest0 il_NO il_As].
    do 20 eexists. split; [reflexivity|]. split; [exact FRU|]. split; [exact FRI|]. split; [exact STK2|]. split; [exact HREP|].
    split; [exact IN2|]. split; [exact OUT2|]. split; [exact MI2|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact I].
  Qed.

  Lemma PATIq_of_PATI_w : forall X w' s_f, PATI X w' ->
    is_wrap s_f = is_wrap (w_s w') -> is_wbits s_f = is_wbits (w_s w') -> is_head s_f = is_head (w_s w') -> is_flags s_f = is_flags (w_s w') ->
    (is_mode s_f = is_mode (w_s w') \/ (is_mode s_f = MEM /\ is_flags (w_s w') = 0)) -> is_last s_f = is_last (w_s w') -> is_havedict s_f = is_havedict (w_s w') ->
    (forall i, 0 <= i < arr_len (is_window s_f) -> 0 <= arr_get (is_window s_f) i < 256) -> PATIq s_f.
  Proof. intros X [s c r] s_f. apply PATIq_of_PATI. Qed.

  Lemma top_ask_null_post : forall w' m1 m2 st' errv2 ms',
    inf_loop ivar_ref 0 (W0 s_a zc) = (SLeave, w') -> WINV w' -> PATI topX w' -> asked SLeave w' = true ->
    munch (ix_W topX) m m1 -> wmono psegs m m1 -> rheap_pres (OW ++ LB) (bv_unsigned sp + -272) m1 m2 ->
    lx_env m2 st' OW LB (wz (bv_unsigned sp + -272)) tp B lo errv2 canary -> ps_so st' = ps_so st -> ps_fa st' = ps_fa st ->
    IFIN (ix_W (topXm m2)) (topXm m2) Z_MEM_ERROR (mkW (iset_mode (w_s (lv_w w')) MEM) (w_c (lv_w w')) (w_r w')) ms' ->
    inflate_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB S C U comprc uc x w Aw sp_ As lo B canary m None st' ms'.
  Proof.
    intros w' m1 m2 st' errv2 ms' EL HW' HP' EA MU1 WM1 HPR ENV2 ESO EFA HFIN.
    pose proof (top_model_ask w' None EL HW' HP' EA) as EM.
    destruct (zi_step s_a x comprc (gwb []) false HIREL HATY top_ZC) as (s_c' & EZI & HIREL' & HATY' & _). cbv zeta in EZI, HIREL', HATY'.
    change Z_NO_FLUSH with 0 in EZI, HIREL', HATY'. change (wans_g (gwb []) false) with (@None (ZProg.blk * (Z -> Z))) in EZI, HIREL', HATY'.
    rewrite EM in EZI, HIREL', HATY'. cbn [fst snd] in EZI, HIREL', HATY'.
    pose proof (top_iw SLeave w' EL HW' HP') as EIW. rewrite EA in EIW.
    destruct (top_cfacts SLeave w' EL HW' HP' I) as (C1 & C2 & C3 & C4 & C5 & C6 & _ & C8 & _). cbv zeta in *. cbn [fin_c] in *.
    destruct (lvw_fields w') as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). cbv zeta in *.
    pose proof (top_hasw_iff w' HP') as HIFF.
    assert (EB : is_window_blk (w_s (lv_w w')) = None).
    { unfold asked in EA. apply andb_prop in EA. destruct EA as [_ ENW]. unfold no_window in ENW. destruct (is_window_blk (w_s (lv_w w'))); [discriminate ENW| reflexivity]. }
    assert (EWN : w = None) by (apply (proj2 HIFF); rewrite <- F9; exact EB).
    assert (Pf0 : is_flags (w_s w') = 0).
    { destruct (top_wfacts w' HW' HP') as (_ & _ & _ & RO & _).
      unfold asked in EA. apply andb_prop in EA. destruct EA as [EC _]. unfold lv_S0, lv_C0 in EC. rewrite lv_cond_v in EC by (unfold lv_o in RO; lia).
      destruct HW' as (HCORE & _). destruct HCORE as (CW1 & _). rewrite F9 in EB. rewrite (CW1 EB) in EC. unfold lv_condv in EC. cbn [Z.eqb negb orb] in EC.
      apply andb_prop in EC. destruct EC as [EC _]. apply andb_prop in EC. destruct EC as [EC _]. apply negb_true_iff in EC. apply Z.eqb_neq in EC.
      destruct HP' as (_ & _ & _ & Pfl & _). destruct Pfl as [Pf|(_ & _ & _ & Pf)]; [exact Pf| exfalso; lia]. }
    assert (HPQ' : PATIq (iset_mode (w_s (lv_w w')) MEM)).
    {
      pose proof HP' as HP0. pose proof HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & POW & _)). cbn [w_s w_c w_r] in POW.
      set (sv := w_s (lv_w w')) in *. clearbody sv.
      apply (PATIq_of_PATI_w topX w' _ HP'); cbn [is_wrap is_wbits is_head is_flags is_mode is_last is_havedict is_window iset_mode]; try assumption.
      - right. split; [reflexivity| exact Pf0].
      - rewrite F8. exact POW. }
    assert (HIFF' : w = None <-> is_window_blk (iset_mode (w_s (lv_w w')) MEM) = None) by (cbn [is_window_blk iset_mode]; rewrite F9; exact HIFF).
    destruct HFIN as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & HMEMF).
    pose proof HMEMF as (STK' & _ & _ & OUT' & MI' & MU' & WM'). cbn [topXm ix_m0 ix_lo ix_sp ix_L ix_rest0 w_c w_r] in STK', OUT', MU', WM'.
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (LR & U1 & UM & U3).
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    destruct INU as (bu & Hbu & EU1 & EU2). pose proof (BLB _ Hbu) as RU. pose proof (SEPS _ Hbu) as SU. rewrite EU1, EU2 in RU, SU. unfold apart in SU.
    assert (LU1 : Z.of_nat (length (firstn (Z.to_nat to) (to_bytes uc))) = to) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_firstn, length_map; lia).
    assert (LU3 : Z.of_nat (length (skipn (Z.to_nat to + 1) (to_bytes uc))) = size - to - 1) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_skipn, length_map; lia).
    assert (DJ : forall A n, U <= A -> A + n <= U + size -> (A + n <= U + to \/ U + to + 1 <= A) -> 0 <= n -> disjoint_from (ix_W topX) A n).
    { intros A n H1 H2 H3 H4. unfold ix_W; cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_NO disjoint_from]; rewrite ?LR; change (Z.of_nat 1) with 1. repeat split; lia. }
    assert (AGU : forall A n, U <= A -> A + n <= U + size -> 0 <= n -> Z_dview.agree_on A (A + n) m1 m2).
    { intros A n H1 H2 H3. apply (agree_iv (OW ++ LB) (bv_unsigned sp + -272)); [exact HPR| lia| lia|]. intros a Ha. right; right.
      apply (in_block_iv _ bu); [apply in_or_app; right; exact Hbu| rewrite EU1, EU2; lia]. }
    apply (u8arr_transport psegs (ix_W topX) m m1) in U1; [| exact MU1| exact WM1| rewrite LU1; apply DJ; lia].
    apply (u8arr_transport psegs (ix_W topX) m m1) in U3; [| exact MU1| exact WM1| rewrite LU3; apply DJ; lia].
    apply (Z_dview.u8arr_agree m1 m2) in U1; [| rewrite LU1; apply AGU; lia]. apply (Z_dview.u8arr_agree m1 m2) in U3; [| rewrite LU3; replace (U + to + 1 + (size - to - 1)) with (U + to + 1 + (size - to - 1)) by lia; apply AGU; lia].
    apply (u8arr_transport psegs (ix_W topX) m2 m') in U1; [| exact MU'| exact WM'| rewrite LU1; apply DJ; lia].
    apply (u8arr_transport psegs (ix_W topX) m2 m') in U3; [| exact MU'| exact WM'| rewrite LU3; apply DJ; lia].
    destruct (top_data (topXm m2) (ix_W (topXm m2)) _ (w_c (lv_w w')) (w_r w') m' w Awl s_c' HMEMF eq_refl eq_refl ltac:(symmetry; exact C5) C1 C3 C4 C6 U1 U3 HIREL' HATY' HPQ' HIFF')
      as ((q1 & q2 & PUB') & ZR' & UARR').
    unfold inflate_post. exists t0, t1, t2, (wz Z_MEM_ERROR), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m', q1, q2, Awl, (C + ti + ic_next_in (w_c (lv_w w'))).
    unfold i_ok. rewrite EIW. unfold i_window. rewrite EIW. unfold the_zapi. cbn [i_inflate i_total_in i_total_out zinst].
    rewrite EZI. cbn [zr_strm zr_consumed zr_output zr_rc zret_of_icall iz_z zs_total_in zs_total_out zstrm_of_icall].
    assert (ESL : ZIface.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w')))) = ic_next_out (w_c (lv_w w'))) by (apply zlength_slice; lia).
    change (Prelim.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w'))))) with (ZIface.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w'))))).
    rewrite ESL. destruct top_lens as (LI & _). rewrite arr_len_of_list in LI. rewrite LI.
    change (Zlib_iface.iblocks None Awl sp_ As) with (iblk_list None Awl sp_ As).
    assert (EUNS : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply unsigned_lit; lia).
    split; [exact EMS|]. split.
    { unfold lx_post_env. split.
      { exists errv2. rewrite <- EWN. exact (top_env_gen (ix_W topX) m2 m' (wz (bv_unsigned sp + -272)) sp st' errv2 ENV2 MU' WM' MI' STK' ltac:(lia) (or_introl eq_refl)). }
      split; [exact FRM0|]. split; [|split; assumption].
      apply (top_pres_core (ix_W topX) m' (ic_next_out (w_c (lv_w w')))); [| | left; reflexivity| exact C4|].
      - intros a Ra OUTW HC.
        assert (CL : rclient_addr (OW ++ LB) (bv_unsigned sp + -272) a).
        { destruct HC as [H|[(b & Hb & Hr)|H]]; [left; lia| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| right; left; exact H]. }
        destruct (HPR a Ra CL) as [E2 W2]. split.
        + rewrite (MU' (wa a)) by (rewrite EUNS by lia; exact OUTW). rewrite E2. apply MU1. rewrite EUNS by lia. exact OUTW.
        + intros H. apply WM'. apply W2. apply WM1. exact H.
      - intros H. apply WM'.
        assert (CL : rclient_addr (OW ++ LB) (bv_unsigned sp + -272) (U + to)).
        { right; right. apply (in_block_iv _ bu); [apply in_or_app; right; exact Hbu| rewrite EU1, EU2; lia]. }
        apply (proj2 (HPR (U + to) ltac:(lia) CL)). apply WM1. exact H.
      - intros E0. unfold iout in OUT'. cbn [il_NO] in OUT'. rewrite C5 in E0. rewrite E0, iout_bytes_0 in OUT'. exact OUT'. }
    split; [exact HWA|]. split; [unfold wint; apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity|].
    split; [exact PUB'|]. split; [intros E; discriminate E|]. split; [rewrite ER; rewrite EWN in ZR'; exact ZR'| exact UARR'].
  Qed.

  Definition topX2 (A : Z) (mb : mem) : ictx :=
    mkIX (il_setw L A) 0 lo (arr_of_list (zc_input zc)) rest0 true mb sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc.

  Lemma top_newblk : forall (p : bptr) A st' m2,
    rblock_range A 32768 -> RHEAP st' ((p, A, 32768) :: OW ++ LB) m2 ->
    blk_ok A 32768 /\ A + 32768 <= lo /\ apart As 7176 A 32768 /\ (forall b, In b LB -> apart A 32768 (blk_addr b) (blk_size b)).
  Proof.
    intros p A st' m2 (R1 & R2 & R3 & R4 & R5) HP2.
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LOC & _).
    pose proof alloc_ceiling_range as CR.
    assert (INS : In (sp_, As, 7176) (OW ++ LB)) by (apply in_or_app; left; unfold iblk_list; apply in_or_app; right; left; reflexivity).
    assert (SEPA : forall b, In b (OW ++ LB) -> apart A 32768 (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (heap_sep st' [(p, A, 32768)] (OW ++ LB) m2 (p, A, 32768) b HND HBD HP2 (or_introl eq_refl) Hb) as X.
      cbn [blk_addr blk_size fst snd] in X. unfold apart. exact X. }
    split; [unfold blk_ok; repeat split; try assumption; lia|]. split; [lia|]. split.
    - pose proof (SEPA _ INS) as X. cbn [blk_addr blk_size fst snd] in X. unfold apart in *. lia.
    - intros b Hb. apply SEPA. apply in_or_app. right. exact Hb.
  Qed.

  Lemma topX2_ok : forall A mb, blk_ok A 32768 -> A + 32768 <= lo -> apart As 7176 A 32768 ->
    (forall b, In b LB -> apart A 32768 (blk_addr b) (blk_size b)) -> ix_ok (topX2 A mb).
  Proof.
    intros A mb (BA1 & _) BAlo SEPS SEPB.
    destruct top_ix_ok as [H1 H2 H3 H4 H5 H6 H7 _ _ _ _]. destruct top_lens as (LI & LR).
    destruct top_blocks as (_ & _ & _ & _ & BLB).
    destruct INC as (bc & Hbc & EC1 & EC2). destruct INU as (bu & Hbu & EU1 & EU2).
    pose proof (SEPB _ Hbc) as SC. pose proof (SEPB _ Hbu) as SU. rewrite EC1, EC2 in SC. rewrite EU1, EU2 in SU.
    constructor; try assumption; cbn [topX2 ix_hasw ix_L ix_lo ix_input ix_rest0 il_setw il_S il_As il_Aw il_NI il_NO]; intros _; rewrite ?LI, ?LR; change (Z.of_nat 1) with 1; unfold apart in *.
    - lia.
    - lia.
    - lia.
    - lia.
  Qed.

  Notation s_blk w' junk := (updw_core (iset_window (iset_window_blk (w_s (lv_w w')) (@Some ZProg.blk 6%N)) (iarr_u8_of (gwb junk) 0 32768)) (ic_outbuf (w_c w')) (ir_put (w_r w')) (lv_o w')) (only parsing).

  Lemma top_ask_block_evt : forall w' A junk m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6,
    WINV w' -> PATI topX w' -> is_window_blk (w_s (lv_w w')) = None ->
    ix_ok (topX2 A m2) -> blk_ok A 32768 ->
    ir_in (w_r w') = arr_len (ic_input (w_c w')) -> - 2^31 <= ir_ret (w_r w') < 2^31 ->
    rw_cells psegs m2 (bv_unsigned sp + -272)
      [C8 (wz (ir_out (w_r w') - ir_left (w_r w'))); C8 (wz (ir_left (w_r w'))); C8 (wz (ir_have (w_r w'))); C8 (wz (ir_ret (w_r w')));
       C8 (wz As); C8 (wz PC_LV_BACK)] ->
    iframeL topX (w_r w') m2 -> IREP m2 L (w_s (lv_w w')) (w_c (lv_w w')) -> iin m2 topX -> iout m2 L rest0 (w_c (lv_w w')) (ir_put (w_r w')) ->
    mem_inv psegs m2 -> stk psegs m2 lo (bv_unsigned sp + -272) -> rw_cells psegs m2 A [CB (Z.to_nat 32768) junk] ->
    evt psegs (IFIN (ix_WF (topX2 A m2)) (topX2 A m2) (fin_rc SLeave w')
                 (mkW (s_blk w' junk) (w_c (lv_w w')) (w_r w')))
      (MS (mkR (wz PC_UW_RET) (wz (bv_unsigned sp + -272)) gp tp t0 t1 t2 (wz (U + to + ir_put (w_r w'))) (wz (ir_out (w_r w') - ir_left (w_r w'))) (wz A)
               a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz As) (wz (ir_out (w_r w') - ir_left (w_r w'))) (wz (ir_in (w_r w'))) x21 x22 x23 (wz (ir_out (w_r w'))) x27 x26 t3 t4 t5 t6)
          F (wz PC_UW_RET) fc None m2 (seg_rom psegs)).
  Proof.
    intros w' A junk m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6 HW' HP' EB XO2 BOK HIN HRR FRU FRI HREP IN2 OUT2 MI2 STK2 WJ.
    destruct (top_wfacts w' HW' HP') as (WF1 & RM & RWS & RO & ROP & RP & RL & RH & EWB & EMO & EWS & ENO & EOB). destruct top_lens as (LI & LR).
    assert (RIN : 0 <= ir_in (w_r w') <= 1).
    { rewrite HIN. destruct HP' as (_ & _ & _ & _ & _ & _ & Pin & _). rewrite Pin. cbn [topX ix_input]. rewrite LI. lia. }
    eapply evt_cut.
    { eapply (leave_from_malloc_block (topX2 A m2) (lv_w w') A 6%N junk); [| exact XO2| reflexivity| reflexivity| exact BOK| exact EB| exact WF1| | |];
        cbn [lv_w w_r topX2 ix_rest0]; rewrite ?LR; unfold lv_o in *; try lia.
      unfold ILVM. cbn [lv_w w_r w_s w_c topX2 ix_sp ix_gp ix_tp ix_L ix_lo ix_F ix_fc ix_m0 ix_rest0 il_setw il_S il_As il_NI il_NO].
      do 20 eexists. split; [reflexivity|]. split; [exact FRU|]. split; [exact FRI|]. split; [exact STK2|].
      split. { destruct HREP as [ZS ST]. split; [exact (izs_setw _ _ _ A ZS)| exact (IST_setw _ _ _ A EB ST)]. }
      split; [exact IN2|]. split; [exact OUT2|]. split; [exact MI2|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact WJ]. }
    intros ms4 (x10' & x12' & x15' & x19' & x25' & H4). cbn [lv_w w_s w_c w_r] in H4.
    eapply evt_mono.
    { eapply (leave_tail (ix_WF (topX2 A m2)) (topX2 A m2) _ x10' x12' x15' x19' x25' ms4 H4 XO2); cbn [w_r topX2 ix_flush]; unfold lv_o in *; lia. }
    intros ms' H. cbn [w_r topX2 ix_flush fin_rc] in H |- *. fold (topX2 A m2) in H.
    unfold lv_w in EOB. cbn [w_c] in EOB. unfold lv_o. rewrite <- EOB. unfold s_fresh in H. exact H.
  Qed.

  Lemma zi_step_eq : forall s_a0 x0 comprc0 gw ok ans s' zr ask,
    IREL s_a0 x0 -> ATY s_a0 -> ZC (zi_zcall comprc0 x0 1 1) -> ans = wans_g gw ok ->
    inflate_p ans s_a0 (zi_zcall comprc0 x0 1 1) 0 = (s', zr, ask) ->
    exists s_c', zi_inflate comprc0 x0 1 1 ok
                 = (mkIZ s_c' (zr_strm zr), ZIface.zlength (zc_input (zi_zcall comprc0 x0 1 1)) - zr_consumed zr, 1 - ZIface.zlength (zr_output zr), zr_output zr, zr_rc zr)
                 /\ IREL s' (mkIZ s_c' (zr_strm zr)) /\ ATY s'.
  Proof.
    intros s_a0 x0 comprc0 gw ok ans s' zr ask HI HA HZ -> E.
    destruct (zi_step s_a0 x0 comprc0 gw ok HI HA HZ) as (s_c' & EZI & HIREL' & HATY' & _). cbv zeta in EZI, HIREL', HATY'.
    change Z_NO_FLUSH with 0 in EZI, HIREL', HATY'. rewrite E in EZI, HIREL', HATY'. cbn [fst snd] in EZI, HIREL', HATY'.
    exists s_c'. split; [exact EZI|]. split; [exact HIREL'| exact HATY'].
  Qed.


  Lemma s_blk_facts : forall s wb junk src e copy, WFACTS s -> 0 <= copy <= 1 ->
    (forall j, e - copy <= j < e -> 0 <= arr_get src j < 256) ->
    let s' := updw_core (iset_window (iset_window_blk s (Some wb)) (iarr_u8_of (gwb junk) 0 32768)) src e copy in
    is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s /\ is_head s' = is_head s /\ is_flags s' = is_flags s
    /\ is_mode s' = is_mode s /\ is_last s' = is_last s /\ is_havedict s' = is_havedict s
    /\ (forall i, 0 <= i < arr_len (is_window s') -> 0 <= arr_get (is_window s') i < 256)
    /\ is_window_blk s' = Some wb.
  Proof.
    intros s wb junk src e copy (Hwb & Hws & Hwn & Hwh & _) RC HS. cbv zeta.
    change (iset_window (iset_window_blk s (Some wb)) (iarr_u8_of (gwb junk) 0 32768)) with (s_fresh s wb junk).
    rewrite (updw_small (s_fresh s wb junk) src e copy Hwb RC Hws Hwn Hwh). unfold uw_set, s_fresh.
    cbn [is_wrap is_wbits is_head is_flags is_mode is_last is_havedict is_window is_window_blk iset_whave iset_wnext iset_wsize iset_window iset_window_blk].
    repeat (split; [reflexivity|]). split; [|reflexivity].
    apply window_blit_bytes; [|intros j Hj; apply HS; lia]. intros i Hi. unfold iarr_u8_of. rewrite arr_get_init. apply junk_bytes.
  Qed.

  Lemma top_pres_blk : forall A mb m' put_f,
    blk_ok A 32768 -> A + 32768 <= lo -> (forall b, In b LB -> apart A 32768 (blk_addr b) (blk_size b)) ->
    (forall a, 0 <= a < 2^64 -> outside (ix_WF (topX2 A mb)) a -> (bv_unsigned sp <= a \/ in_block LB a \/ (0x28000 <= a < 0x5b000 /\ ~ ralloc_static a)) ->
               m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
    (wview psegs m (wa (U + to)) <> None -> wview psegs m' (wa (U + to)) <> None) ->
    0 <= put_f <= 1 -> (put_f = 0 -> u8arr psegs m' (U + to) rest0) ->
    lx_pres LB (bv_unsigned sp) [(S, S + ZS_SIZEOF); (U + to, U + to + put_f)] m m'.
  Proof.
    intros A mb m' put_f (BA1 & _ & _ & BA4) BAlo SEPB AG WNO RP HU0 a Ra (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX.
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (_ & _ & UM & _).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    destruct (Z.eq_dec a (U + to)) as [EA|NA].
    - assert (P0 : put_f = 0) by lia. specialize (HU0 P0). split; [|rewrite EA; exact WNO].
      destruct UM as [(_ & _ & B1) _]. destruct HU0 as [(_ & _ & B2) _].
      assert (L0 : (0 < length rest0)%nat) by (rewrite LR; lia).
      pose proof (B1 0%nat L0) as Q1. pose proof (B2 0%nat L0) as Q2. rewrite Z.add_0_r in Q1, Q2. rewrite <- EA in Q1, Q2.
      assert (ROM : seg_rom psegs (wa a) = None).
      { apply RMallocRep.ref_seg_rom_none. destruct INU as (bu & Hbu & EU1 & EU2). pose proof (HBR _ _ _ bu (proj1 ENV) (in_or_app _ _ _ (or_intror Hbu))) as (_ & _ & _ & _ & R5).
        rewrite EU1, EU2 in R5. unfold wa. rewrite unsigned_lit by lia. lia. }
      unfold mrd in Q1, Q2. rewrite ROM in Q1, Q2. destruct (m (wa a)), (m' (wa a)); congruence.
    - assert (OUTW : outside (ix_WF (topX2 A mb)) a).
      { assert (CL : bv_unsigned sp <= a \/ (exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b) \/ 0x28000 <= a < 0x5b000).
        { destruct HC as [H|[H|[H _]]]; [left; exact H| right; left; exact H| right; right; exact H]. }
        assert (OS : a < As \/ As + 7176 <= a).
        { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (SEPS _ Hb) as Q; unfold apart in Q; lia| lia]. }
        assert (OL : a < lo \/ bv_unsigned sp <= a).
        { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (BLB _ Hb); lia| lia]. }
        assert (OWn : a < A \/ A + 32768 <= a).
        { destruct CL as [H|[(b & Hb & Hr)|H]]; [lia| pose proof (SEPB _ Hb) as Q; unfold apart in Q; lia| lia]. }
        unfold ix_WF, ix_W; cbn [topX2 ix_L ix_lo ix_sp ix_rest0 il_setw il_S il_As il_Aw il_NO app outside]; rewrite ?LR; change (Z.of_nat 1) with 1.
        repeat split; lia. }
      exact (AG a Ra OUTW HC).
  Qed.

  Lemma top_env_blk : forall (p : bptr) A mb m' (spb spx : word) (stx : PState) (errx : word),
    blk_ok A 32768 -> A + 32768 <= lo ->
    lx_env mb stx ((p, A, 32768) :: OW) LB spb tp B lo errx canary ->
    munch (ix_WF (topX2 A mb)) mb m' -> wmono psegs mb m' -> mem_inv psegs m' -> stk psegs m' lo (bv_unsigned spx) -> bv_unsigned spx <= bv_unsigned sp ->
    lx_env m' stx ((p, A, 32768) :: OW) LB spx tp B lo errx canary.
  Proof.
    intros p A mb m' spb spx stx errx (BA1 & _ & _ & BA4) BAlo ENVx MU WM MI' STK' SPX.
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB). destruct top_lens as (LI & LR).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ X4 _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S il_NO ix_rest0] in X1, X4. rewrite LR in X4. change (Z.of_nat 1) with 1 in X4.
    pose proof ENVx as E0. unfold lx_env in E0. destruct E0 as (_ & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & _).
    destruct SIF as (SF1 & SF2 & _). unfold ZS_SIZEOF in SF2. destruct INU as (bu & Hbu & EU1 & EU2).
    pose proof (BLB _ Hbu) as RU. rewrite EU1, EU2 in RU.
    pose proof (HBR _ _ _ bu (proj1 ENV) (in_or_app _ _ _ (or_intror Hbu))) as (_ & _ & _ & _ & R5). rewrite EU1, EU2 in R5.
    eapply (lx_env_munch (ix_WF (topX2 A mb)) mb m' stx ((p, A, 32768) :: OW) LB spb spx tp B lo errx canary HFRAME ENVx MU WM MI' STK');
      [pose proof ENV as E9; unfold lx_env in E9; destruct E9 as (_ & _ & _ & _ & _ & _ & SPB9 & _); lia| |].
    - unfold ix_WF, ix_W. cbn [topX2 ix_L ix_lo ix_sp ix_rest0 il_setw il_S il_As il_Aw il_NO app]. rewrite LR. change (Z.of_nat 1) with 1.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; unfold rclient_write_ok; cbn [fst snd].
      + left. lia.
      + left. lia.
      + right; right. exists (sp_, As, 7176). split; [right; apply in_or_app; left; unfold iblk_list; apply in_or_app; right; left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
      + right; right. exists bu. split; [right; apply in_or_app; right; exact Hbu|]. rewrite EU1, EU2. lia.
      + right; right. exists (p, A, 32768). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
    - intros a Ha. unfold ix_WF, ix_W. cbn [topX2 ix_L ix_lo ix_sp ix_rest0 il_setw il_S il_As il_Aw il_NO app outside]. rewrite LR. change (Z.of_nat 1) with 1.
      repeat split; lia.
  Qed.

  Lemma top_ask_block_post : forall w' m1 m2 st' errv2 (p : bptr) A junk ms',
    inf_loop ivar_ref 0 (W0 s_a zc) = (SLeave, w') -> WINV w' -> PATI topX w' -> asked SLeave w' = true ->
    munch (ix_W topX) m m1 -> wmono psegs m m1 -> rheap_pres (OW ++ LB) (bv_unsigned sp + -272) m1 m2 ->
    lx_env m2 st' ((p, A, 32768) :: OW) LB (wz (bv_unsigned sp + -272)) tp B lo errv2 canary -> ps_so st' = ps_so st -> ps_fa st' = ps_fa st ->
    blk_ok A 32768 -> A + 32768 <= lo -> (forall b, In b LB -> apart A 32768 (blk_addr b) (blk_size b)) ->
    IFIN (ix_WF (topX2 A m2)) (topX2 A m2) (fin_rc SLeave w')
         (mkW (s_blk w' junk) (w_c (lv_w w')) (w_r w')) ms' ->
    inflate_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB S C U comprc uc x w Aw sp_ As lo B canary m (Some p) st' ms'.
  Proof.
    intros w' m1 m2 st' errv2 p A junk ms' EL HW' HP' EA MU1 WM1 HPR ENV2 ESO EFA BOK BAlo SEPB HFIN.
    pose proof (top_model_ask w' (Some (6%N, gwb junk)) EL HW' HP' EA) as EM.
    destruct (zi_step_eq s_a x comprc (gwb junk) true _ _ _ _ HIREL HATY top_ZC eq_refl EM) as (s_c' & EZI & HIREL' & HATY').
    pose proof (top_iw SLeave w' EL HW' HP') as EIW. rewrite EA in EIW.
    destruct (top_cfacts SLeave w' EL HW' HP' I) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _). cbv zeta in *. cbn [fin_c] in *.
    destruct (lvw_fields w') as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). cbv zeta in *.
    pose proof (top_hasw_iff w' HP') as HIFF.
    assert (EB : is_window_blk (w_s (lv_w w')) = None).
    { unfold asked in EA. apply andb_prop in EA. destruct EA as [_ ENW]. unfold no_window in ENW. destruct (is_window_blk (w_s (lv_w w'))); [discriminate ENW| reflexivity]. }
    assert (EWN : w = None) by (apply (proj2 HIFF); rewrite <- F9; exact EB).
    destruct (top_wfacts w' HW' HP') as (WF1 & _ & _ & RO & ROP & _).
    destruct (s_blk_facts (w_s (lv_w w')) 6%N junk (ic_outbuf (w_c w')) (ir_put (w_r w')) (lv_o w') WF1 RO) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    { intros j Hj. destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (POB & _)). apply POB. lia. }
    assert (HPQ' : PATIq (s_blk w' junk)).
    { apply (PATIq_of_PATI_w topX w' _ HP'); [rewrite G1; exact F1| rewrite G2; exact F2| rewrite G3; exact F3| rewrite G4; exact F4| left; rewrite G5; exact F5| rewrite G6; exact F6| rewrite G7; exact F7| exact G8]. }
    assert (HIFF' : Some p = None <-> is_window_blk (s_blk w' junk) = None).
    { rewrite G9. split; intros E; discriminate E. }
    destruct HFIN as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & HMEMF).
    pose proof HMEMF as (STK' & _ & _ & OUT' & MI' & MU' & WM'). cbn [topX2 ix_m0 ix_lo ix_sp ix_L ix_rest0 w_c w_r] in STK', OUT', MU', WM'. fold (topX2 A m2) in MU'.
    destruct (uncompr_split m U uc to UARR ltac:(unfold Prelim.zlength in LUC; unfold ZIface.zlength; lia)) as (LR & U1 & UM & U3).
    destruct top_blocks as ((BS1 & _ & _ & BS4) & BSlo & SEPS & BW & BLB).
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    destruct INU as (bu & Hbu & EU1 & EU2). pose proof (BLB _ Hbu) as RU. pose proof (SEPS _ Hbu) as SU. pose proof (SEPB _ Hbu) as SUA. rewrite EU1, EU2 in RU, SU, SUA. unfold apart in SU, SUA.
    assert (LU1 : Z.of_nat (length (firstn (Z.to_nat to) (to_bytes uc))) = to) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_firstn, length_map; lia).
    assert (LU3 : Z.of_nat (length (skipn (Z.to_nat to + 1) (to_bytes uc))) = size - to - 1) by (unfold Prelim.zlength in LUC; unfold to_bytes; rewrite length_skipn, length_map; lia).
    assert (DJ : forall A0 n, U <= A0 -> A0 + n <= U + size -> (A0 + n <= U + to \/ U + to + 1 <= A0) -> 0 <= n -> disjoint_from (ix_W topX) A0 n).
    { intros A0 n H1 H2 H3 H4. unfold ix_W; cbn [topX ix_L ix_lo ix_sp ix_rest0 il_S il_As il_NO disjoint_from]; rewrite ?LR; change (Z.of_nat 1) with 1. repeat split; lia. }
    assert (DJ2 : forall A0 n, U <= A0 -> A0 + n <= U + size -> (A0 + n <= U + to \/ U + to + 1 <= A0) -> 0 <= n -> disjoint_from (ix_WF (topX2 A m2)) A0 n).
    { intros A0 n H1 H2 H3 H4. unfold ix_WF, ix_W; cbn [topX2 ix_L ix_lo ix_sp ix_rest0 il_setw il_S il_As il_Aw il_NO app disjoint_from]; rewrite ?LR; change (Z.of_nat 1) with 1. repeat split; lia. }
    assert (AGU : forall A0 n, U <= A0 -> A0 + n <= U + size -> 0 <= n -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3. apply (agree_iv (OW ++ LB) (bv_unsigned sp + -272)); [exact HPR| lia| lia|]. intros a Ha. right; right.
      apply (in_block_iv _ bu); [apply in_or_app; right; exact Hbu| rewrite EU1, EU2; lia]. }
    apply (u8arr_transport psegs (ix_W topX) m m1) in U1; [| exact MU1| exact WM1| rewrite LU1; apply DJ; lia].
    apply (u8arr_transport psegs (ix_W topX) m m1) in U3; [| exact MU1| exact WM1| rewrite LU3; apply DJ; lia].
    apply (Z_dview.u8arr_agree m1 m2) in U1; [| rewrite LU1; apply AGU; lia]. apply (Z_dview.u8arr_agree m1 m2) in U3; [| rewrite LU3; apply AGU; lia].
    apply (u8arr_transport psegs (ix_WF (topX2 A m2)) m2 m') in U1; [| exact MU'| exact WM'| rewrite LU1; apply DJ2; lia].
    apply (u8arr_transport psegs (ix_WF (topX2 A m2)) m2 m') in U3; [| exact MU'| exact WM'| rewrite LU3; apply DJ2; lia].
    destruct (top_data (topX2 A m2) (ix_WF (topX2 A m2)) (s_blk w' junk) (w_c (lv_w w')) (w_r w') m' (Some p) A s_c' HMEMF eq_refl eq_refl ltac:(symmetry; exact C5) C1 C3 C4 C6 U1 U3 HIREL' HATY' HPQ' HIFF')
      as ((q1 & q2 & PUB') & ZR' & UARR').
    unfold inflate_post. exists t0, t1, t2, (wz (fin_rc SLeave w')), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, m', q1, q2, A, (C + ti + ic_next_in (w_c (lv_w w'))).
    unfold i_ok. rewrite EIW. unfold i_window. rewrite EIW. unfold the_zapi. cbn [i_inflate i_total_in i_total_out zinst].
    rewrite EZI. cbn [zr_strm zr_consumed zr_output zr_rc zret_of_icall iz_z zs_total_in zs_total_out zstrm_of_icall].
    assert (ESL : ZIface.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w')))) = ic_next_out (w_c (lv_w w'))) by (apply zlength_slice; lia).
    change (Prelim.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w'))))) with (ZIface.zlength (arr_slice (ic_outbuf (w_c (lv_w w'))) 0 (ic_next_out (w_c (lv_w w'))))).
    rewrite ESL. destruct top_lens as (LI & _). rewrite arr_len_of_list in LI. rewrite LI.
    change (Zlib_iface.iblocks (Some p) A sp_ As) with (iblk_list (Some p) A sp_ As).
    assert (EUNS : forall a, 0 <= a < 2^64 -> bv_unsigned (wa a) = a) by (intros a Ha; unfold wa; apply unsigned_lit; lia).
    split; [exact EMS|]. split.
    { unfold lx_post_env. split.
      { exists errv2. pose proof (top_env_blk p A m2 m' (wz (bv_unsigned sp + -272)) sp st' errv2 BOK BAlo ENV2 MU' WM' MI' STK' ltac:(lia)) as E9.
        rewrite EWN in E9. exact E9. }
      split; [exact FRM0|]. split; [|split; assumption].
      apply (top_pres_blk A m2 m' (ic_next_out (w_c (lv_w w'))) BOK BAlo SEPB); [| | exact C4|].
      - intros a Ra OUTW HC.
        assert (OUTW1 : outside (ix_W topX) a).
        { revert OUTW. unfold ix_WF, ix_W. cbn [topX topX2 ix_L ix_lo ix_sp ix_rest0 il_setw il_S il_As il_Aw il_NO app outside]. intros (Q1 & Q2 & Q3 & Q4 & _). repeat split; assumption. }
        assert (CL : rclient_addr (OW ++ LB) (bv_unsigned sp + -272) a).
        { destruct HC as [H|[(b & Hb & Hr)|H]]; [left; lia| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| right; left; exact H]. }
        destruct (HPR a Ra CL) as [E2 W2]. split.
        + rewrite (MU' (wa a)) by (rewrite EUNS by lia; exact OUTW). rewrite E2. apply MU1. rewrite EUNS by lia. exact OUTW1.
        + intros H. apply WM'. apply W2. apply WM1. exact H.
      - intros H. apply WM'.
        assert (CL : rclient_addr (OW ++ LB) (bv_unsigned sp + -272) (U + to)).
        { right; right. apply (in_block_iv _ bu); [apply in_or_app; right; exact Hbu| rewrite EU1, EU2; lia]. }
        apply (proj2 (HPR (U + to) ltac:(lia) CL)). apply WM1. exact H.
      - intros E0. unfold iout in OUT'. cbn [il_setw il_NO] in OUT'. rewrite C5 in E0. rewrite E0, iout_bytes_0 in OUT'. exact OUT'. }
    (split; [intros NE; exfalso; apply NE; exact EWN|]). (split; [unfold wint; apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity|]).
    (split; [exact PUB'|]). (split; [intros E; rewrite (C7 E); lia|]). (split; [rewrite ER; exact ZR'| exact UARR']).
  Qed.

  Lemma TOP_ASK : forall w' ms1,
    inf_loop ivar_ref 0 (W0 s_a zc) = (SLeave, w') -> WINV w' -> ATY (w_s w') -> PATI topX w' -> asked SLeave w' = true ->
    ILVM (ix_W topX) topX (lv_w w') PC_MALLOC (wz 32768) (fun _ => True) ms1 ->
    implM psegs (lib_malloc lops (z_wsize the_zapi)) st
          (inflate_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB S C U comprc uc x w Aw sp_ As lo B canary m) ms1.
  Proof.
    intros w' ms1 EL HW' HA' HP' EA HM.
    change (lib_malloc lops (z_wsize the_zapi)) with (raw_malloc 32768).
    destruct (top_cfacts SLeave w' EL HW' HP' I) as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & C10).
    assert (EB : is_window_blk (w_s (lv_w w')) = None).
    { pose proof EA as EA0. unfold asked in EA0. apply andb_prop in EA0. destruct EA0 as [_ ENW]. unfold no_window in ENW. destruct (is_window_blk (w_s (lv_w w'))); [discriminate ENW| reflexivity]. }
    pose proof top_ix_ok as XO. destruct XO as [X1 _ _ _ _ _ _ _ _ _ _]. cbn [topX ix_L ix_lo ix_sp il_S] in X1.
    assert (E272 : bv_unsigned (wz (bv_unsigned sp + -272)) = bv_unsigned sp + -272) by (apply unsigned_lit; lia).
    apply (top_ask_malloc w' ms1 _ HM).
    intros x21 x22 x23 x26 x27 m1 r st' ms2 FRU FRI HREP1 IN1 OUT1 MU1 WM1 ENV1 PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & errv2 & -> & MI2 & STK2 & ERR2 & AUX2 & HPR & EFA & ESO & HR).
    rewrite E272 in STK2, HPR.
    replace (ret_pc (wz PC_UW_RET)) with (wz PC_UW_RET) by (symmetry; apply ret_pc_even; [unfold PC_UW_RET; lia| reflexivity]).
    destruct (top_ask_rebase w' m1 m2 HW' HP' EB HPR FRU FRI HREP1 IN1 OUT1) as (FRU2 & FRI2 & HREP2 & IN2 & OUT2).
    assert (HPRc : rheap_pres LB (bv_unsigned (wz (bv_unsigned sp + -272))) m1 m2).
    { rewrite E272. eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; apply in_or_app; right; exact Hb]. }
    destruct r as [p|].
    -
      destruct HR as (A & junk & -> & RBR & HP2 & WJ & _).
      destruct (top_newblk p A st' m2 RBR HP2) as (BOK & BAlo & SEPS & SEPB).
      pose proof (topX2_ok A m2 BOK BAlo SEPS SEPB) as XO2.
      assert (ENV2 : lx_env m2 st' ((p, A, 32768) :: OW) LB (wz (bv_unsigned sp + -272)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 st st' OW ((p, A, 32768) :: OW) LB (wz (bv_unsigned sp + -272)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E272; exact STK2| exact ERR2| exact AUX2]. }
      eapply evt_mono; [exact (top_ask_block_evt w' A junk m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6 HW' HP' EB XO2 BOK C9 C10 FRU2 FRI2 HREP2 IN2 OUT2 MI2 STK2 WJ)|].
      intros ms' HFIN.
      exact (top_ask_block_post w' m1 m2 st' errv2 p A junk ms' EL HW' HP' EA MU1 WM1 HPR ENV2 ESO EFA BOK BAlo SEPB HFIN).
    -
      destruct HR as (-> & HP2).
      assert (ENV2 : lx_env m2 st' OW LB (wz (bv_unsigned sp + -272)) tp B lo errv2 canary).
      { apply (lx_env_heap m1 m2 st st' OW OW LB (wz (bv_unsigned sp + -272)) tp B lo errv errv2 canary ENV1 HPRc HP2 MI2); [rewrite E272; exact STK2| exact ERR2| exact AUX2]. }
      eapply evt_mono; [exact (top_ask_null_evt w' m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x26 x27 t3 t4 t5 t6 HW' HP' EB FRU2 FRI2 HREP2 IN2 OUT2 MI2 STK2)|].
      intros ms' HFIN.
      exact (top_ask_null_post w' m1 m2 st' errv2 ms' EL HW' HP' EA MU1 WM1 HPR ENV2 ESO EFA HFIN).
  Qed.

  Lemma top_stmt : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    implM psegs (if i_wants comprc x w then lib_malloc lops (z_wsize the_zapi) else ret lops None) st
          (inflate_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st LB S C U comprc uc x w Aw sp_ As lo B canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz S) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz Z_INFLATE) fc None m (seg_rom psegs)).
  Proof.
    intros. eapply implM_evt; [exact (top_loop t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)|]. intros ms1 HLP.
    destruct (inf_loop ivar_ref 0 (W0 s_a zc)) as [stop w'] eqn:EL.
    pose proof HLP as (HST & HW' & HA' & HP'). cbn [fst snd] in HST, HW', HA', HP'.
    rewrite (top_iw stop w' EL HW' HP').
    assert (HRST : match stop with SRet rc => rc = Z_NEED_DICT -> RST w' | SLeave => True end).
    { destruct stop as [|rc]; [exact I|]. cbn [fst] in HST.
      destruct HST as (x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & mm & _ & _ & H). exact H. }
    destruct (top_cfacts stop w' EL HW' HP' HRST) as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & C10).
    destruct (asked stop w') eqn:EA.
    - destruct stop as [|rc]; [|discriminate EA].
      eapply implM_evt; [exact (top_ask_pre w' ms1 HLP EA C9)|]. intros ms2 H2.
      exact (TOP_ASK w' ms2 EL HW' HA' HP' EA H2).
    - apply implM_ret. eapply evt_mono; [exact (top_noask stop w' ms1 HLP EA C9 C10)|].
      intros ms' H. exact (proj2 (top_noask_post stop w' ms' EL HW' HP' EA HRST H)).
  Qed.
End TOP.
End WithCeiling0.
End Z_inflate_top.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_pro OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_loop OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_updwin_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_updwin OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2.Z_infl_leave OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_top_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_inflate_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_leave2.Z_inflate_mem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_inflate_ok.Z_inflate_top.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate HarnessSmall RefInflateSafeD RefInflateSafeTY RefInflateEqS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefUpdWin1 RefInflateRel RefInflateEqB InflateFrameIn ZApiInst ZTaintI.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqS OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefUpdWin1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateFrameIn OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section OK.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis ARMS : arms_ok 0.
  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflate_ok : inflate_stmt R.
  Proof.
    unfold inflate_stmt. intros until canary. intros ENV PUB ZR INC CARR LCL CBYT INU UARR LUC RTI RTO SEPCU SIF LOSP SP16 FRM0 -> ->.
    rewrite ER in ZR. destruct ZR as (s_a & L0 & w' & sp' & ES & EL & HW & HR & HI & HA & HP).
    destruct (iblocks_inv _ _ _ _ _ _ _ _ EL) as (-> & -> & EAs & EAw).
    rewrite EL in ENV. rewrite EAs in *.
    apply (IREPq_relay m L0 s_a _ (C + i_total_in the_zapi is) (U + i_total_out the_zapi is)) in HR. rewrite ES, EAs in HR. destruct HR as [HZQ HIST].
    unfold the_zapi in *. cbn [i_total_in i_total_out zinst] in *. change ZApi.Z_NO_FLUSH with 0.
    eapply (top_stmt MALLOC HFRAME HBR HND HBD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S C U cl size comprc uc is w Aw sp_ As p1 p2 lo B errv canary s_a (il_Aw L0));
      try eassumption.
  Qed.
End OK.
End WithCeiling0.
