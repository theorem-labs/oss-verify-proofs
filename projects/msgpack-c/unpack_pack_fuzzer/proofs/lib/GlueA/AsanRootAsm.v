(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val ValProofs IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops CtrSys StackInit InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadC ReadPre ReadPost StackSh LowImg StrReg StrRegC RangeC PubC PubImg GshC GshImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AsanOps AsanRun AsanRoot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 InitAsan2.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.
Module R2 := RootAsan2.RootAsan2.
Module I2 := InitAsan2.InitAsan2.

Definition ROOT_OPS (CRED : int) : list opinst :=
  [OpI 1%uint63 (ROOT_HEAP_ARGS CRED); OpI 5%uint63 []; OpI 7%uint63 [VL wzero]; OpI 15%uint63 [VL wzero; VL wzero];
   OpI 10%uint63 []; OpI 11%uint63 []; OpI 12%uint63 []; OpI 13%uint63 []; OpI 14%uint63 [VP 1%uint63 (wlit 24%uint63)];
   OpI 16%uint63 []; OpI 17%uint63 []].

Section Asm.
Context {rc : runConstT}.

Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.
Variables p1 file : list byte.

Hypothesis IMGX_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX (shad a').

Let OPSA : optable := AsanRun.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.

Lemma no_seg_hi : forall a, 0x62f000 <= a -> ~ (exists seg, find_segment asegs a 1 = Some seg).
Proof. intros a Ha [seg H]. rewrite (UnreggPre.no_seg_above a Ha) in H. discriminate H. Qed.

Lemma shad_val : forall x, 0 <= x -> shad x = 2147450880 + x / 8.
Proof. intros x Hx. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma priv_pool_fl : forall a, 6340960 <= a < 6340968 -> in_priv R2.PRIV a.
Proof. intros a Ha. unfold in_priv, R2.PRIV. apply Exists_cons_hd. cbn [fst snd]. change (to_Z 6340960%uint63) with 6340960. change (to_Z 6340968%uint63) with 6340968. exact Ha. Qed.
Lemma priv_pool_hb : forall a, 6340976 <= a < 6341488 -> in_priv R2.PRIV a.
Proof. intros a Ha. unfold in_priv, R2.PRIV. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. change (to_Z 6340976%uint63) with 6340976. change (to_Z 6341488%uint63) with 6341488. exact Ha. Qed.
Lemma priv_stage : forall a, 0x5fc110 <= a < 0x60c110 -> in_priv R2.PRIV a.
Proof.
  intros a Ha. unfold in_priv. apply Exists_exists. exists (6275344%uint63, 6340880%uint63). split.
  - unfold R2.PRIV. cbn [In]. tauto.
  - cbn [fst snd]. change (to_Z 6275344%uint63) with 6275344. change (to_Z 6340880%uint63) with 6340880. lia.
Qed.

Theorem aroot2_st_ok : forall (xb : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (CRED : int)
    (L : alayout) (RNG : footprint) (sta : astate),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp) -> valid_hwcap (in_hwcap inp) ->
  length (in_argv inp) = 2%nat ->
  ME.amain_at en inp ms mo ->

  bv_unsigned (en_sp en) = ATOP + 8388608 ->

  AHEAP AIu2 L RNG sta [] (ms_mem ms) -> ACCT (wbv (wlit CRED)) L RNG sta [] mo -> incl UNIV (al_U L) -> lazy_shape C0 mo ->
  aprist sta ->

  (forall ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws (ms_mem ms)) ->

  (forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX a -> in_priv R2.PRIV a) ->
  exists E : env,
    eb E = eb (InitLib.E0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) xb) /\
    st_ok asegs OPSA E (I2.ROOT_with (ROOT_OPS CRED)) ms mo.
Proof.
  intros xb en inp ms mo CRED L RNG sta Hva Hve Hsp Hfit Hhw Hargc HM USP AH AC HU LZ APR CW0 IMG_APART.
  pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  set (usp := bv_unsigned (en_sp en)) in *.
  assert (USPlo : 0x7fff80000000 <= usp <= 0x800000000000) by lia.
  assert (USP16 : usp mod 16 = 0).
  { rewrite USP. replace (ATOP + 8388608) with (ATOP + 524288 * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (USP8 : usp = 8 * (usp / 8)) by (Z.div_mod_to_equations; lia).
  assert (TOPB : usp + 200 <= 2 ^ 47).
  { pose proof (SI.BSB_top AImg.a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hfit) as TOP.
    pose proof (InitLib.len_BSB AImg.a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as LEN.
    pose proof (InitLib.sstruct_val AImg.a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as SV.
    unfold SI.SP, SI.argcZ, SI.envcZ in *. fold usp in TOP. lia. }

  pose proof HM as (w0 & V0 & m0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & AMO).
  destruct (I2.amain_st_ok_ops xb en inp ms mo Hva Hve Hsp Hfit Hhw Hargc HM)
    as (E & EB & HUL & BH & EV1 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FIN).
  fold usp in BH, EV1, F7, F8.
  exists E. split; [exact EB|].
  change R2.SEGS with asegs in *.
  set (m := ms_mem ms) in *.
  assert (USPE : bv_unsigned (ev E 1%uint63) = ATOP + 8388608) by (rewrite EV1; exact USP).
  assert (DEC : decode (map (den E) (ROOT_HEAP_ARGS CRED)) = Some (0, den E (VL (wlit CRED)), ROOT_WS, []))
    by exact (root_decode E CRED USPE).

  assert (BASED : forall a, in_based E R2.REGS a -> in_ws ROOT_WS a \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')).
  { intros a IB. destruct (BH a IB) as [S|T].
    - left. unfold in_ws, ROOT_WS. apply Exists_cons_hd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
    - right. exists (8 * (a - ASHOFF)). unfold ASHOFF.
      split; [lia|]. symmetry. apply shad_unshad. }
  assert (BASED_HI : forall a, in_based E R2.REGS a -> 0x10006fef8000 <= a).
  { intros a IB. destruct (BH a IB) as [S|T]; lia. }
  apply FIN.
  -
    split; [exact (ME.am_halted _ _ _ _ AMO)| exact LZ].
  -
    unfold ops_hold, ROOT_OPS. repeat (apply Forall_cons); [| | | | | | | | | | | apply Forall_nil]; cbn [op_id op_args].
    +
      apply (proj2 (AsanRun.OPSA_holds1 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file _ m mo)).
      exact (root_heap_holds AIu2 ACCT UNIV Cw E CRED L RNG sta m mo USPE AH AC HU CW0 APR).
    +   exact (ME.am_fds _ _ _ _ AMO).
    +
      change (Pool.Pool.pool_holds FLA asegs [den E (VL wzero)] m mo).
      replace (den E (VL wzero)) with (Z_to_bv 64 0) by (apply bv_eq; rewrite ValP.den_VL; reflexivity).
      apply (Pool.PoolSnd.pool_holds_fresh asegs FLA (fun _ => True) FLA8 FLAB). exact F6.
    +
      change (ReadPost.rstage_holds_v file [den E (VL wzero); den E (VL wzero)] m).
      assert (Z0 : bv_unsigned (den E (VL wzero)) = 0) by (rewrite ValP.den_VL; reflexivity).
      cbn [ReadPost.rstage_holds_v]. rewrite Z0. split; [lia|]. split; [lia|]. intros i Hi. lia.
    +
      change (UnreggPre.shmap_holds m). intros a Ha. apply F1.
      unfold UnreggPre.SH_LO, UnreggPre.SH_HI, UnreggPre.ASH_LO, UnreggPre.ASH_HI, R2.IMGSH_LO, R2.IMGSH_LEN in *. lia.
    +
      change (ReadPre.zsh_holds m). split.
      * intros a Ha. apply F1. unfold ReadPre.ZSH_LO, ReadPre.ZSH_HI, R2.IMGSH_LO, R2.IMGSH_LEN in *. lia.
      * intros a Ha. apply (F3 a). unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI, R2.ZSH_LO, R2.ZSH_HI in *. lia.
    +
      change (StackSh.ssh_holds m). intros a Ha. apply F7.
      assert (A0 : 0 <= ATOP) by (clear - ATR; lia).
      rewrite (shad_val ATOP A0) in Ha. unfold Shadow.KHIGH in Ha.
      replace (usp - 8388608) with ATOP by (clear - USP; lia). clear - Ha. lia.
    +
      change (LowImg.zro_holds m). intros s Hs. apply F2. unfold LowImg.ZRO_LO, LowImg.ZRO_HI, R2.IMGSH_LO, R2.ZRO_LEN in *. lia.
    +
      change (zarg_holds_c [den E (VP 1%uint63 (wlit 24%uint63))] m).
      assert (AZ : bv_unsigned (den E (VP 1%uint63 (wlit 24%uint63))) = usp + 24).
      { rewrite ValP.den_VP, EV1. change (w2Zs (wlit 24%uint63)) with 24. apply Z.mod_small. unfold two64. lia. }
      pose proof (SI.BSB_top AImg.a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hfit) as TOP.
      pose proof (InitLib.len_BSB AImg.a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as LEN.
      unfold SI.SP in TOP. fold usp in TOP.
      cbn [zarg_holds_c]. unfold StrReg.zarg_holds. rewrite AZ. split; [clear - USP; lia|]. split; [clear - TOPB; lia|].
      intros s Hs. apply F8. assert (A0 : 0 <= usp + 24 + 7) by (clear - USPlo; lia).
      rewrite (shad_val (usp + 24 + 7) A0) in Hs. unfold Shadow.KHIGH in Hs. clear - Hs. lia.
    +
      change (PubImg.zpb_holds m). intros s (wv & Hw & Hs). apply F4. unfold PubImg.ZPBW in Hw. cbn [In] in Hw. unfold R2.ZPB_LO, R2.ZPB_HI.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hs; lia.
    +
      change (GshImg.gsh_holds GshC.GshC.GSH_TAB_ASAN m). exact F5.
  -
    unfold ops_apart, ROOT_OPS. repeat (apply Forall_cons); [| | | | | | | | | | | apply Forall_nil]; cbn [op_id op_args]; intros a FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX (map (den E) (ROOT_HEAP_ARGS CRED)))) in FP.
      apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC)) in FP as (RA & NX & NW). split.
      * intros IB. destruct (BASED a IB) as [W|(a' & Ra' & ->)]; [exact (NW W)| exact (NX (IMGX_stksh a' Ra'))].
      * intros SEG. exact (IMG_APART a SEG NX).
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (Pool.Pool.pool_fp FLA [den E (VL wzero)])) in FP.
      unfold Pool.Pool.pool_fp in FP. replace (bv_unsigned (den E (VL wzero))) with 0 in FP by (rewrite ValP.den_VL; reflexivity).
      change (0 =? 3) with false in FP. change (0 <? 3) with true in FP. cbv iota in FP.
      pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. rewrite HBv in FP. change (to_Z FLA) with 6340960 in FP.
      apply Exists_exists in FP as (v & [<-|[<-|[]]] & Ha); cbn [fst snd] in Ha.
      * split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_pool_fl; lia].
      * split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_pool_hb; lia].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(ReadPre.STAGE, ReadPre.STAGE + 65536)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.STAGE in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_stage; lia].
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(ReadPre.ZSC_LO, ReadPre.ZSC_HI)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.ZSC_LO, ReadPre.ZSC_HI in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(LowImg.ZRO_LO, LowImg.ZRO_HI)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.ZRO_LO, LowImg.ZRO_HI in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (zarg_fp [den E (VP 1%uint63 (wlit 24%uint63))])) in FP.
      assert (AZ : bv_unsigned (den E (VP 1%uint63 (wlit 24%uint63))) = usp + 24).
      { rewrite ValP.den_VP, EV1. change (w2Zs (wlit 24%uint63)) with 24. apply Z.mod_small. unfold two64. lia. }
      cbn [zarg_fp] in FP. rewrite AZ in FP. rewrite Z.max_l in FP by lia. rewrite (shad_val (usp + 24 + 7) ltac:(lia)) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold Shadow.KHIGH in Ha.
      split; [| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
      intros IB. destruct (BH a IB) as [S|T]; [lia| Z.div_mod_to_equations; lia].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) PubImg.ZPBW) in FP.
      apply Exists_exists in FP as (v & Hv & Ha). unfold PubImg.ZPBW in Hv. cbn [In] in Hv.
      assert (R : 0x800b9828 <= a < 0x800bdca8) by (destruct Hv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia).
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (GshImg.gsh_fp GshC.GshC.GSH_TAB_ASAN)) in FP.
      pose proof (gsh_hull a FP) as R.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
  -
    intros a [IB|SEG].
    + destruct (BH a IB) as [S|T].
      * left. right. unfold two64. lia.
      * right. unfold insts, ROOT_OPS. cbn [map op_id op_args]. apply Exists_cons_hd. cbn [fst snd].
        apply (proj2 (AsanRun.OPSA_cov1 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file _ a)).
        split; [reflexivity|]. exists 0, (den E (VL (wlit CRED))), ROOT_WS, []. split; [exact DEC|]. right. left.
        exists (8 * (a - ASHOFF)). unfold ASHOFF. split; [Z.div_mod_to_equations; lia|]. symmetry. apply shad_unshad.
    + left. exact (AsanRun.OPSA_cov0_img IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file a SEG).
Qed.
End Asm.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainEntryBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootBoth2 InitBoth2.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CtrSys OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.StackInit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.InitLib.
Import Ledger.TwinB Op.TwinB.
Import AsanOps.TwinB AsanRun.TwinB AsanRoot.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.
Module R2 := RootBoth2.RootBoth2.
Module I2 := InitBoth2.InitBoth2.

Definition ROOT_OPS (CRED : int) : list opinst :=
  [OpI 1%uint63 (ROOT_HEAP_ARGS CRED); OpI 5%uint63 []; OpI 7%uint63 [VL wzero]; OpI 15%uint63 [VL wzero; VL wzero];
   OpI 10%uint63 []; OpI 11%uint63 []; OpI 12%uint63 []; OpI 13%uint63 []; OpI 14%uint63 [VP 1%uint63 (wlit 24%uint63)];
   OpI 16%uint63 []; OpI 17%uint63 []].

Section Asm.
Context {rc : runConstT}.

Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AIu2 IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AIu2 L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AIu2 L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AIu2 L RNG st LB m'.
Variable Cw : client_world.
Variables p1 file : list byte.

Hypothesis IMGX_stksh : forall a', ATOP <= a' < 2 ^ 47 -> in_ivs IMGX (shad a').

Let OPSA : optable := AsanRun.TwinB.OPSA IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file.

Lemma no_seg_hi : forall a, 0x631000 <= a -> ~ (exists seg, find_segment bsegs a 1 = Some seg).
Proof. intros a Ha [seg H]. rewrite (UnreggPre.TwinB.no_seg_above a Ha) in H. discriminate H. Qed.

Lemma shad_val : forall x, 0 <= x -> shad x = 2147450880 + x / 8.
Proof. intros x Hx. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma priv_pool_fl : forall a, 6349600 <= a < 6349608 -> in_priv R2.PRIV a.
Proof. intros a Ha. unfold in_priv, R2.PRIV. apply Exists_cons_hd. cbn [fst snd]. change (to_Z 6349600%uint63) with 6349600. change (to_Z 6349608%uint63) with 6349608. exact Ha. Qed.
Lemma priv_pool_hb : forall a, 6349616 <= a < 6350128 -> in_priv R2.PRIV a.
Proof. intros a Ha. unfold in_priv, R2.PRIV. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. change (to_Z 6349616%uint63) with 6349616. change (to_Z 6350128%uint63) with 6350128. exact Ha. Qed.
Lemma priv_stage : forall a, 0x5fe2d0 <= a < 0x60e2d0 -> in_priv R2.PRIV a.
Proof.
  intros a Ha. unfold in_priv. apply Exists_exists. exists (6283984%uint63, 6349520%uint63). split.
  - unfold R2.PRIV. cbn [In]. tauto.
  - cbn [fst snd]. change (to_Z 6283984%uint63) with 6283984. change (to_Z 6349520%uint63) with 6349520. lia.
Qed.

Theorem aroot2_st_ok : forall (xb : int -> list byte) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) (CRED : int)
    (L : alayout) (RNG : footprint) (sta : astate),
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_sp (en_sp en) ->
  entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp) -> valid_hwcap (in_hwcap inp) ->
  length (in_argv inp) = 2%nat ->
  ME.bmain_at en inp ms mo ->

  bv_unsigned (en_sp en) = ATOP + 8388608 ->

  AHEAP AIu2 L RNG sta [] (ms_mem ms) -> ACCT (wbv (wlit CRED)) L RNG sta [] mo -> incl UNIV (al_U L) -> lazy_shape C0 mo ->
  aprist sta ->

  (forall ws, Forall (fun w => w_kind w = K_STACK) ws -> cw_holds Cw 0 [] [] ws (ms_mem ms)) ->

  (forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> ~ in_ivs IMGX a -> in_priv R2.PRIV a) ->
  exists E : env,
    eb E = eb (InitLib.E0 (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) xb) /\
    st_ok bsegs OPSA E (I2.ROOT_with (ROOT_OPS CRED)) ms mo.
Proof.
  intros xb en inp ms mo CRED L RNG sta Hva Hve Hsp Hfit Hhw Hargc HM USP AH AC HU LZ APR CW0 IMG_APART.
  pose proof atop_range as ATR. pose proof ATOP_al16 as A16.
  set (usp := bv_unsigned (en_sp en)) in *.
  assert (USPlo : 0x7fff80000000 <= usp <= 0x800000000000) by lia.
  assert (USP16 : usp mod 16 = 0).
  { rewrite USP. replace (ATOP + 8388608) with (ATOP + 524288 * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (USP8 : usp = 8 * (usp / 8)) by (Z.div_mod_to_equations; lia).
  assert (TOPB : usp + 200 <= 2 ^ 47).
  { pose proof (SI.BSB_top BImg.b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hfit) as TOP.
    pose proof (InitLib.len_BSB BImg.b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as LEN.
    pose proof (InitLib.sstruct_val BImg.b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as SV.
    unfold SI.SP, SI.argcZ, SI.envcZ in *. fold usp in TOP. lia. }

  pose proof HM as (w0 & V0 & m0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & AMO).
  destruct (I2.amain_st_ok_ops xb en inp ms mo Hva Hve Hsp Hfit Hhw Hargc HM)
    as (E & EB & HUL & BH & EV1 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FIN).
  fold usp in BH, EV1, F7, F8.
  exists E. split; [exact EB|].
  change R2.SEGS with bsegs in *.
  set (m := ms_mem ms) in *.
  assert (USPE : bv_unsigned (ev E 1%uint63) = ATOP + 8388608) by (rewrite EV1; exact USP).
  assert (DEC : decode (map (den E) (ROOT_HEAP_ARGS CRED)) = Some (0, den E (VL (wlit CRED)), ROOT_WS, []))
    by exact (root_decode E CRED USPE).

  assert (BASED : forall a, in_based E R2.REGS a -> in_ws ROOT_WS a \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')).
  { intros a IB. destruct (BH a IB) as [S|T].
    - left. unfold in_ws, ROOT_WS. apply Exists_cons_hd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
    - right. exists (8 * (a - ASHOFF)). unfold ASHOFF.
      split; [lia|]. symmetry. apply shad_unshad. }
  assert (BASED_HI : forall a, in_based E R2.REGS a -> 0x10006fef8000 <= a).
  { intros a IB. destruct (BH a IB) as [S|T]; lia. }
  apply FIN.
  -
    split; [exact (ME.bm_halted _ _ _ _ AMO)| exact LZ].
  -
    unfold ops_hold, ROOT_OPS. repeat (apply Forall_cons); [| | | | | | | | | | | apply Forall_nil]; cbn [op_id op_args].
    +
      apply (proj2 (AsanRun.TwinB.OPSA_holds1 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file _ m mo)).
      exact (root_heap_holds AIu2 ACCT UNIV Cw E CRED L RNG sta m mo USPE AH AC HU CW0 APR).
    +   exact (ME.bm_fds _ _ _ _ AMO).
    +
      change (Pool.Pool.pool_holds FLA bsegs [den E (VL wzero)] m mo).
      replace (den E (VL wzero)) with (Z_to_bv 64 0) by (apply bv_eq; rewrite ValP.den_VL; reflexivity).
      apply (Pool.PoolSnd.pool_holds_fresh bsegs FLA (fun _ => True) FLA8 FLAB). exact F6.
    +
      change (ReadPost.TwinB.rstage_holds_v file [den E (VL wzero); den E (VL wzero)] m).
      assert (Z0 : bv_unsigned (den E (VL wzero)) = 0) by (rewrite ValP.den_VL; reflexivity).
      cbn [ReadPost.TwinB.rstage_holds_v]. rewrite Z0. split; [lia|]. split; [lia|]. intros i Hi. lia.
    +
      change (UnreggPre.TwinB.shmap_holds m). intros a Ha. apply F1.
      unfold UnreggPre.TwinB.SH_LO, UnreggPre.TwinB.SH_HI, UnreggPre.TwinB.ASH_LO, UnreggPre.TwinB.ASH_HI, R2.IMGSH_LO, R2.IMGSH_LEN in *. lia.
    +
      change (ReadPre.TwinB.zsh_holds m). split.
      * intros a Ha. apply F1. unfold ReadPre.TwinB.ZSH_LO, ReadPre.TwinB.ZSH_HI, R2.IMGSH_LO, R2.IMGSH_LEN in *. lia.
      * intros a Ha. apply (F3 a). unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI, R2.ZSH_LO, R2.ZSH_HI in *. lia.
    +
      change (StackSh.TwinB.ssh_holds m). intros a Ha. apply F7.
      assert (A0 : 0 <= ATOP) by (clear - ATR; lia).
      rewrite (shad_val ATOP A0) in Ha. unfold Shadow.KHIGH in Ha.
      replace (usp - 8388608) with ATOP by (clear - USP; lia). clear - Ha. lia.
    +
      change (LowImg.TwinB.zro_holds m). intros s Hs. apply F2. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI, R2.IMGSH_LO, R2.ZRO_LEN in *. lia.
    +
      change (zarg_holds_c [den E (VP 1%uint63 (wlit 24%uint63))] m).
      assert (AZ : bv_unsigned (den E (VP 1%uint63 (wlit 24%uint63))) = usp + 24).
      { rewrite ValP.den_VP, EV1. change (w2Zs (wlit 24%uint63)) with 24. apply Z.mod_small. unfold two64. lia. }
      pose proof (SI.BSB_top BImg.b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) Hfit) as TOP.
      pose proof (InitLib.len_BSB BImg.b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as LEN.
      unfold SI.SP in TOP. fold usp in TOP.
      cbn [zarg_holds_c]. unfold StrReg.TwinB.zarg_holds. rewrite AZ. split; [clear - USP; lia|]. split; [clear - TOPB; lia|].
      intros s Hs. apply F8. assert (A0 : 0 <= usp + 24 + 7) by (clear - USPlo; lia).
      rewrite (shad_val (usp + 24 + 7) A0) in Hs. unfold Shadow.KHIGH in Hs. clear - Hs. lia.
    +
      change (PubImg.TwinB.zpb_holds m). intros s (wv & Hw & Hs). apply F4. unfold PubImg.TwinB.ZPBW in Hw. cbn [In] in Hw. unfold R2.ZPB_LO, R2.ZPB_HI.
      destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hs; lia.
    +
      change (GshImg.TwinB.gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m). exact F5.
  -
    unfold ops_apart, ROOT_OPS. repeat (apply Forall_cons); [| | | | | | | | | | | apply Forall_nil]; cbn [op_id op_args]; intros a FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (heap_fp IMGX (map (den E) (ROOT_HEAP_ARGS CRED)))) in FP.
      apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC)) in FP as (RA & NX & NW). split.
      * intros IB. destruct (BASED a IB) as [W|(a' & Ra' & ->)]; [exact (NW W)| exact (NX (IMGX_stksh a' Ra'))].
      * intros SEG. exact (IMG_APART a SEG NX).
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (Pool.Pool.pool_fp FLA [den E (VL wzero)])) in FP.
      unfold Pool.Pool.pool_fp in FP. replace (bv_unsigned (den E (VL wzero))) with 0 in FP by (rewrite ValP.den_VL; reflexivity).
      change (0 =? 3) with false in FP. change (0 <? 3) with true in FP. cbv iota in FP.
      pose proof (Pool.PoolSnd.HB_val FLA FLAB) as HBv. rewrite HBv in FP. change (to_Z FLA) with 6349600 in FP.
      apply Exists_exists in FP as (v & [<-|[<-|[]]] & Ha); cbn [fst snd] in Ha.
      * split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_pool_fl; lia].
      * split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_pool_hb; lia].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(ReadPre.TwinB.STAGE, ReadPre.TwinB.STAGE + 65536)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.STAGE in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros _; apply priv_stage; lia].
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold ReadPre.TwinB.ZSC_LO, ReadPre.TwinB.ZSC_HI in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +   apply Exists_nil in FP. destruct FP.
    +
      change (Exists (fun iv => fst iv <= a < snd iv) [(LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI)]) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold LowImg.TwinB.ZRO_LO, LowImg.TwinB.ZRO_HI in Ha.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (zarg_fp [den E (VP 1%uint63 (wlit 24%uint63))])) in FP.
      assert (AZ : bv_unsigned (den E (VP 1%uint63 (wlit 24%uint63))) = usp + 24).
      { rewrite ValP.den_VP, EV1. change (w2Zs (wlit 24%uint63)) with 24. apply Z.mod_small. unfold two64. lia. }
      cbn [zarg_fp] in FP. rewrite AZ in FP. rewrite Z.max_l in FP by lia. rewrite (shad_val (usp + 24 + 7) ltac:(lia)) in FP.
      apply Exists_exists in FP as (v & [<-|[]] & Ha). cbn [fst snd] in Ha. unfold Shadow.KHIGH in Ha.
      split; [| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
      intros IB. destruct (BH a IB) as [S|T]; [lia| Z.div_mod_to_equations; lia].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) PubImg.TwinB.ZPBW) in FP.
      apply Exists_exists in FP as (v & Hv & Ha). unfold PubImg.TwinB.ZPBW in Hv. cbn [In] in Hv.
      assert (R : 0x800b9c60 <= a < 0x800be0e0) by (destruct Hv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; lia).
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
    +
      change (Exists (fun iv => fst iv <= a < snd iv) (GshImg.TwinB.gsh_fp GshC.TwinB.GshC.GSH_TAB_ASAN)) in FP.
      pose proof (gsh_hull a FP) as R.
      split; [intros IB; pose proof (BASED_HI a IB); lia| intros SEG; exfalso; exact (no_seg_hi a ltac:(lia) SEG)].
  -
    intros a [IB|SEG].
    + destruct (BH a IB) as [S|T].
      * left. right. unfold two64. lia.
      * right. unfold insts, ROOT_OPS. cbn [map op_id op_args]. apply Exists_cons_hd. cbn [fst snd].
        apply (proj2 (AsanRun.TwinB.OPSA_cov1 IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file _ a)).
        split; [reflexivity|]. exists 0, (den E (VL (wlit CRED))), ROOT_WS, []. split; [exact DEC|]. right. left.
        exists (8 * (a - ASHOFF)). unfold ASHOFF. split; [Z.div_mod_to_equations; lia|]. symmetry. apply shad_unshad.
    + left. exact (AsanRun.TwinB.OPSA_cov0_img IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top Cw p1 file a SEG).
Qed.
End Asm.
End TwinB.
