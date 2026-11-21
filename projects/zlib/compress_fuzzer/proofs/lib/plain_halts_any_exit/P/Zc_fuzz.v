(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RCalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZApiC ZHarnessC ZInstC ZTargetC Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Drv_kit Drv_facts Zlib_iface Zh_kit F_memcpy F_memcmp F_atexit Exit_cb Zc_kit Zc_wkit Zc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Transparent the_zapi the_zapiC.

Lemma norm8_id : forall l, Forall (fun c => 0 <= c < 256) l -> norm8 l = l.
Proof. induction l as [|b l IH]; intros H; [reflexivity|]. inversion H; subst. cbn [norm8 map]. unfold norm8 in IH. rewrite IH by assumption. f_equal. apply Z.mod_small. lia. Qed.

Lemma to_bytes_eq_norm8 : forall l1 l2, to_bytes l1 = to_bytes l2 <-> norm8 l1 = norm8 l2.
Proof.
  unfold to_bytes, norm8.
  induction l1 as [|a l1 IH]; intros [|b l2]; cbn [map]; try (split; intros H; (reflexivity || discriminate)).
  split; intros H.
  - assert (E1 : Z_to_bv 8 a = Z_to_bv 8 b) by congruence. assert (E2 : map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2) by congruence.
    f_equal; [| apply IH; exact E2].
    apply (f_equal bv_unsigned) in E1. rewrite !Z_to_bv_unsigned in E1. unfold bv_wrap in E1. exact E1.
  - assert (E1 : a mod 256 = b mod 256) by congruence. assert (E2 : map (fun b => b mod 256) l1 = map (fun b => b mod 256) l2) by congruence.
    f_equal; [| apply IH; exact E2]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. exact E1.
Qed.

Fixpoint zall_below (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S k => f (Z.of_nat k) && zall_below k f end.
Lemma zall_below_ok : forall n f, zall_below n f = true -> forall x, 0 <= x < Z.of_nat n -> f x = true.
Proof.
  induction n as [|k IH]; intros f H x Hx; [lia|]. cbn [zall_below] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  destruct (Z.eq_dec x (Z.of_nat k)) as [->|NE]; [exact H1|]. apply (IH f H2). lia.
Qed.

Definition mod5_mach (x : Z) : Z :=
  x + - Z.land ((x * 3689348814741910324) ≫ 64) 18446744073709551615
    + - Z.land (Z.land ((x * 3689348814741910324) ≫ 64) 18446744073709551615 ≪ 2) 18446744073709551615.
Lemma mod5_mach_ok : forall x, 0 <= x < 256 -> mod5_mach x = x mod 5.
Proof.
  intros x Hx. pose proof (zall_below_ok 256 (fun x => mod5_mach x =? x mod 5) ltac:(vm_compute; reflexivity) x ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Definition mod10_mach (x : Z) : Z := x - Z.land ((x * 205) ≫ 11 * 10) 18446744073709551615.
Lemma mod10_mach_ok : forall x, 0 <= x < 256 -> mod10_mach x = x mod 10.
Proof.
  intros x Hx. pose proof (zall_below_ok 256 (fun x => mod10_mach x =? x mod 10) ltac:(vm_compute; reflexivity) x ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma size_test_zc : forall n, 0 <= n < 2^30 ->
  (18446744073708503049 <= Z.land (n + -1048577) 18446744073709551615 <-> 10 <= n <= 1048576).
Proof.
  intros n Hn. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.le_gt_cases 1048577 n) as [G|G].
  - rewrite Z.mod_small by lia. lia.
  - replace ((n + -1048577) mod 2^64) with (n + -1048577 + 2^64) by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia.
Qed.

Lemma skipn_repeat_z : forall (a : Z) k m, skipn k (repeat a m) = repeat a (m - k).
Proof. induction k as [|k IH]; intros [|m]; cbn; try reflexivity. apply IH. Qed.

Lemma bufC_store : forall uout n, 0 <= n -> zlength uout <= n -> bufC uout n = zstore (zrepeat 0 n) 0 uout.
Proof.
  intros uout n Hn HL. rewrite zstore0_app by (unfold zrepeat; rewrite repeat_length; unfold zlength in HL; lia).
  unfold bufC, zrepeat. rewrite skipn_repeat_z.
  replace (Z.to_nat (n - zlength uout)) with (Z.to_nat n - length uout)%nat by (unfold zlength; lia).
  rewrite firstn_app, firstn_all2 by (unfold zlength in HL; lia). rewrite firstn_all2 by (rewrite repeat_length; unfold zlength in HL; lia). reflexivity.
Qed.

Lemma list2_of_len : forall (l : list byte), length l = 2%nat -> exists x y, l = [x; y].
Proof. intros [|x [|y [|z l]]] H; cbn in H; try lia. exists x, y. reflexivity. Qed.

Definition hdr0 (cm fl : Z) : Z := znth (zhdr_bytes cm fl) 0.
Definition hdr1 (cm fl : Z) : Z := znth (zhdr_bytes cm fl) 1.
Lemma zhdr_bytes_eq : forall cm fl, zhdr_bytes cm fl = [hdr0 cm fl; hdr1 cm fl].
Proof. intros. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.
Notation zc := the_zapiC.

Lemma magic5_cells : forall m, mem_inv psegs m -> ro_cells psegs m A_MAGIC5 [C8 (Z_to_bv 64 3689348814741910324)].
Proof.
  intros m MI. split; [cbn; split; [reflexivity| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply ro_bytes_at; [exact MI| unfold A_MAGIC5; lia| cbn; unfold A_MAGIC5; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma hdr_steps : forall (Q : machine_state -> Prop) (x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (cm fl : Z),
  mem_inv psegs m -> (cm = 0 \/ cm = 1 \/ cm = 2 \/ cm = 3 \/ cm = 8) -> (fl = 0 \/ fl = 32) ->
  (forall (v10 v11 v12 v20 v21 : word), bv_unsigned v10 mod 256 = hdr0 cm fl -> bv_unsigned v11 mod 256 = hdr1 cm fl ->
     evt psegs Q (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 v10 v11 v12 a3 a4 a5 a6 a7 x18 x19 v20 v21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16050) fc None m (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 cm) (Z_to_bv 64 fl) x22 x23 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16008) fc None m (seg_rom psegs)).
Proof.
  intros until fl. intros MI HCM HFL K.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
  destruct HFL as [-> | ->]; destruct HCM as [-> |[-> |[-> |[-> | ->]]]];
    (do 18 zstep; eapply K; [vm_compute; reflexivity| vm_compute; reflexivity]).
Qed.

Lemma fz_wint_cases : forall rc, - 2^31 <= rc < 2^31 ->
  (0 <= rc /\ bv_unsigned (wint rc) = rc) \/ (rc < 0 /\ bv_unsigned (wint rc) = rc + 2^64).
Proof.
  intros rc Hrc. unfold wint. cbv beta delta [MallocRep.wz]. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
  destruct (Z.lt_ge_cases rc 0) as [Ng|Ng]; [right| left]; (split; [lia|]).
  - symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
  - apply Z.mod_small. lia.
Qed.

(* oss-fuzz #16582 branches: from the branch hypothesis K (after zify_cond) and the cases WC of a return code, the code
   is Z_MEM_ERROR (fz_rc_m4) or it is not (fz_rc_n4). *)
Local Ltac fz_rc_m4 K WC :=
  lazymatch type of K with
  | bv_unsigned (wint ?rc) = ?r =>
      let v := eval vm_compute in r in change r with v in K;
      let WS := fresh "WS" in let WQ := fresh "WQ" in destruct WC as [[WS WQ]|[WS WQ]]; lia
  | ?r = bv_unsigned (wint ?rc) =>
      let v := eval vm_compute in r in change r with v in K;
      let WS := fresh "WS" in let WQ := fresh "WQ" in destruct WC as [[WS WQ]|[WS WQ]]; lia
  end.
Local Ltac fz_rc_n4 K :=
  let CE := fresh "CE" in intros CE; rewrite CE in K; vm_compute in K;
  first [ exact (K eq_refl) | discriminate K | (apply K; reflexivity) ].

Section FZ.
  Variable R : zreps.
  Hypothesis ZOK : zlib_okC R.
  Hypothesis CBND : compressBound_stmt.
  Hypothesis CALLOC : rcalloc_stmt.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis C2 : rcompress2_stmt.
  Hypothesis UNC : runcompress_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Lemma frame_top24 : forall m A (c0 c1 c2 : cell) rest,
    rw_cells psegs m A (c0 :: c1 :: c2 :: rest) -> csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat ->
    rw_cells psegs m A (CB 24 (cells_bytes [c0; c1; c2]) :: rest).
  Proof.
    intros m A c0 c1 c2 rest H E0 E1 E2. pose proof H as [[WF _] _].
    assert (WF3 : cells_wf [c0; c1; c2]) by (cbn [cells_wf] in WF |- *; tauto).
    eapply rw_cells_recast; [exact H| |].
    - cbn [cells_wf cell_wf]. split; [rewrite (cells_bytes_length _ WF3); cbn; lia|]. cbn [cells_wf] in WF. tauto.
    - change (c0 :: c1 :: c2 :: rest) with ([c0; c1; c2] ++ rest). rewrite cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite app_nil_r, <- !app_assoc. reflexivity.
  Qed.

  Lemma fz_ret : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j : list byte) (lo : Z) (Q : machine_state -> Prop),
    rw_cells psegs m (bv_unsigned sp + -96) [CB 24 j; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    stk psegs m lo (bv_unsigned sp + -96) -> lo <= bv_unsigned sp + -96 -> mem_inv psegs m -> bv_unsigned sp < 2^63 -> 96 <= bv_unsigned sp ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6', stk psegs m lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' S0 S1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom psegs))) ->
    evt psegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v S8 S9 S10 S11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x16084) fc None m (seg_rom psegs)).
  Proof.
    intros until Q. intros FR ST LO MI SPH SPL KK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    do 10 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep. apply evt_done. apply KK. exact ST.
  Qed.

  Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
  Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma land32_cases : forall x, 0 <= x < 256 -> Z.land x 32 = 0 \/ Z.land x 32 = 32.
  Proof.
    intros x Hx. pose proof (zall_below_ok 256 (fun x => (Z.land x 32 =? 0) || (Z.land x 32 =? 32)) ltac:(vm_compute; reflexivity) x ltac:(lia)) as H.
    apply orb_true_iff in H. destruct H as [H|H]; apply Z.eqb_eq in H; [left| right]; exact H.
  Qed.
  Lemma zc_bound_mono : forall a b, 0 <= a <= b -> b <= 2^21 -> zc_bound zc a <= zc_bound zc b.
  Proof.
    intros a b Hab Hb. cbn [zc_bound the_zapiC ZApiInstC.zinstC]. unfold Deflate.compressBound_m, Deflate.sat_bound64, ZIface.wrap64.
    rewrite !Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_le_mono a b (2^12) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono a b (2^14) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono a b (2^25) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos a (2^12) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos a (2^14) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos a (2^25) ltac:(lia) ltac:(lia)).
    assert (b / 2^12 <= 2^9) by (apply Z.div_le_upper_bound; lia). assert (b / 2^14 <= 2^7) by (apply Z.div_le_upper_bound; lia). assert (b / 2^25 <= 1) by (apply Z.div_le_upper_bound; lia).
    change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia.
    (* zlib 1.4 (zl14cmp-r1): compressBound saturates; under 2^21 neither sum is below its length *)
    repeat match goal with |- context [if ?x <? ?y then _ else _] => replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) end.
    lia.
  Qed.

  Section World.
    Variables (sp : word) (LB : list block) (D : Z) (d : list Z) (n : Z) (m0 : mem) (s0 : PState) (lo : Z).
    Notation usp := (bv_unsigned sp).
    Notation SP_ := (usp + -96).
    Notation PAYR_ := (forall a, D <= a < D + zlength d -> a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ in_block LB a).
    Notation LBR_ := (forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).

    Definition WLD (m : mem) (ss : PState) : Prop :=
      lx_pres LB usp [LXW_ZH; LXW_STDERR] m0 m /\ ps_so ss = ps_so s0 /\ ps_fa ss = ps_fa s0 /\ payload_ok m LB D d
      /\ zhc_statics m (D + 3) n /\ rw_cells psegs m ZL_MREPL [C4 (Z_to_bv 64 0)]
      /\ stdout_file m (ps_so s0) /\ adp_cells_cb m /\ xcb_cells m.

    Definition wst_addr (a : Z) : Prop :=
      (ZH_STATICS <= a < ZH_STATICS + 16) \/ (ZL_MREPL <= a < ZL_MREPL + 4) \/ stdout_addr a
      \/ (RINIT_FLAG <= a < RINIT_FLAG + 1) \/ (RIN_CB <= a < RIN_CB + 1) \/ (RATX_FIN <= a < RATX_FIN + 1) \/ (RATX_LOCK <= a < RATX_LOCK + 8)
      \/ (RATX_HEAD <= a < RATX_HEAD + 24) \/ (RATX_A0 <= a < RATX_A0 + 8) \/ xcb_addr a.
    Lemma wst_image : forall a, wst_addr a -> 0x29000 <= a < 0x5c000 /\ ~ ralloc_static a /\ ~ stderr_addr a.
    Proof.
      intros a Ha. unfold wst_addr, xcb_addr, stdout_addr, stderr_addr, ZH_STATICS, ZL_MREPL, RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, REXIT_LOCK,
        ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
    Qed.

    Lemma WLD_agree : forall (P : Z -> Prop) m m' ss, WLD m ss -> agree_on P m m' ->
      (forall a, wst_addr a -> P a) -> (forall a, D <= a < D + zlength d -> P a) -> lx_pres LB usp [LXW_ZH; LXW_STDERR] m m' -> WLD m' ss.
    Proof.
      intros P m m' ss (PR & ESO & EFA & POK & ZST & MRP & SOF & ADP & XCB) AG HS HD LXP. unfold WLD.
      split; [eapply lx_pres_trans; [exact PR| exact LXP]|]. split; [exact ESO|]. split; [exact EFA|].
      split; [eapply payload_ok_agree; [exact AG| exact POK| exact HD]|].
      split; [unfold zhc_statics in *; eapply rw_cells_agree; [exact AG| exact ZST| intros a Ha; cbn in Ha; apply HS; unfold wst_addr; lia]|].
      split; [eapply rw_cells_agree; [exact AG| exact MRP| intros a Ha; cbn in Ha; apply HS; unfold wst_addr; lia]|].
      split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HS; unfold wst_addr; tauto| exact SOF]|].
      split.
      - destruct ADP as (A1 & A2 & A3 & A4 & A5 & A6). unfold adp_cells_cb.
        repeat split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; cbn in Ha; apply HS; unfold wst_addr; lia]).
      - destruct XCB as (td0 & td1 & td2 & td3 & t & X1 & Ht & X2). exists td0, td1, td2, td3, t.
        split; [eapply rw_cells_agree; [exact AG| exact X1| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, xcb_addr; lia]|]. split; [exact Ht|].
        eapply rw_cells_agree; [exact AG| exact X2| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, xcb_addr; lia].
    Qed.

    Lemma WLD_heap : forall L m m' ss ss', PAYR_ -> WLD m ss -> rheap_pres L SP_ m m' -> (forall b, In b LB -> In b L) ->
      ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD m' ss'.
    Proof.
      intros L m m' ss ss' PAYR W HPR HL ESO' EFA'.
      assert (W' : WLD m' ss).
      { eapply (WLD_agree _ m m' ss W (agree_of_heap_pres _ _ _ _ HPR)).
        - intros a Ha. destruct (wst_image a Ha) as (I1 & I2 & _). right; left. split; [exact I1| exact I2].
        - intros a Ha. destruct (PAYR a Ha) as (_ & _ & (b & Hb & Hr)). right; right. exists b. split; [apply HL; exact Hb| exact Hr].
        - eapply lx_pres_weaken; [apply (lx_pres_of_heap_pres L _ [LXW_ZH; LXW_STDERR]); exact HPR| lia| exact HL| auto]. }
      destruct W' as (PR & ESO & EFA & REST). split; [exact PR|]. split; [rewrite ESO'; exact ESO|]. split; [rewrite EFA'; exact EFA| exact REST].
    Qed.

    Lemma WLD_lx : forall LB' X (A k : Z) m m' ss ss', PAYR_ -> LBR_ -> alloc_ceiling <= lo -> 0x5c000 <= lo -> lo + 96 <= usp ->
      WLD m ss -> lx_pres LB' SP_ X m m' -> (forall b, In b LB -> In b LB') ->
      (forall a, rin_ivs X a -> (A <= a < A + k) \/ (SP_ <= a < usp)) ->
      (forall b, In b LB -> blk_addr b + blk_size b <= A \/ A + k <= blk_addr b) -> (A + k <= 0x10000 \/ 0x5c000 <= A) -> A + k <= alloc_ceiling ->
      ps_so ss' = ps_so ss -> ps_fa ss' = ps_fa ss -> WLD m' ss'.
    Proof.
      intros LB' X A k m m' ss ss' PAYR LBR LOC LOG LOSP W LXP HL HX SEP AI AC ESO' EFA'.
      assert (NX : forall a, (usp <= a \/ in_block LB a \/ (0x29000 <= a < 0x5c000)) -> ~ rin_ivs X a).
      { intros a Ha Hi. destruct (HX a Hi) as [H1|H1]; destruct Ha as [Ha|[(b & Hb & Hr)|Ha]];
          first [lia | pose proof (SEP b Hb); pose proof (LBR b Hb) as (_ & _ & _ & BC & _); lia]. }
      assert (W' : WLD m' ss).
      { eapply (WLD_agree _ m m' ss W (agree_of_lx_pres _ _ _ _ _ LXP)).
        - intros a Ha. destruct (wst_image a Ha) as (I1 & I2 & _). split; [apply NX; lia| right; right; split; [exact I1| exact I2]].
        - intros a Ha. destruct (PAYR a Ha) as (_ & _ & (b & Hb & Hr)). split; [apply NX; right; left; exists b; auto| right; left; exists b; split; [apply HL; exact Hb| exact Hr]].
        - eapply lx_pres_sub; [exact LXP|]. intros a [HXa Hc]. split.
          + apply NX. destruct Hc as [Hc|[Hc|[Hc _]]]; [left; exact Hc| right; left; exact Hc| right; right; exact Hc].
          + destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left; exists b; split; [apply HL; exact Hb| exact Hr]| right; right; exact Hc]. }
      destruct W' as (PR & ESO & EFA & REST). split; [exact PR|]. split; [rewrite ESO'; exact ESO|]. split; [rewrite EFA'; exact EFA| exact REST].
    Qed.

    Lemma WLD_munch : forall W m m' ss, PAYR_ -> WLD m ss -> munch W m m' -> wmono psegs m m' ->
      (forall a, (usp <= a \/ in_block LB a \/ (0x29000 <= a < 0x5c000 /\ ~ (ZH_STATICS <= a < ZH_STATICS + 16))) -> outside W a) ->
      zhc_statics m' (D + 3) n -> WLD m' ss.
    Proof.
      intros W m m' ss PAYR (PR & ESO & EFA & POK & ZST & MRP & SOF & ADP & XCB) MU WM OUT ZST'.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      assert (HS : forall a, wst_addr a -> ~ (ZH_STATICS <= a < ZH_STATICS + 16) -> outside W a).
      { intros a Ha Hz. destruct (wst_image a Ha) as (I1 & _). apply OUT. right; right. split; [exact I1| exact Hz]. }
      unfold WLD. split.
      { eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HXa Hc]. apply OUT.
        destruct Hc as [Hc|[Hc|[Hc _]]]; [left; exact Hc| right; left; exact Hc| right; right]. split; [exact Hc|].
        intros Hz. apply HXa. cbn [rin_ivs]. left. unfold LXW_ZH. cbn [fst snd]. exact Hz. }
      split; [exact ESO|]. split; [exact EFA|].
      split; [eapply payload_ok_agree; [exact AG| exact POK| intros a Ha; apply OUT; right; left; exact (proj2 (proj2 (PAYR a Ha)))]|].
      split; [exact ZST'|].
      split; [eapply rw_cells_agree; [exact AG| exact MRP| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, ZL_MREPL, ZH_STATICS in *; lia]|].
      split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HS; [unfold wst_addr; tauto| unfold stdout_addr, ZH_STATICS in *; lia]| exact SOF]|].
      split.
      - destruct ADP as (A1 & A2 & A3 & A4 & A5 & A6). unfold adp_cells_cb.
        repeat split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, ZH_STATICS in *; lia]).
      - destruct XCB as (td0 & td1 & td2 & td3 & t & X1 & Ht & X2). exists td0, td1, td2, td3, t.
        split; [eapply rw_cells_agree; [exact AG| exact X1| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, xcb_addr, REXIT_LOCK, ZH_STATICS in *; lia]|]. split; [exact Ht|].
        eapply rw_cells_agree; [exact AG| exact X2| intros a Ha; cbn in Ha; apply HS; unfold wst_addr, xcb_addr, REXIT_LOCK, ZH_STATICS in *; lia].
    Qed.
  End World.

  Lemma frame_join4 : forall m A (j0 : list byte) (c1 c2 : cell) rest,
    rw_cells psegs m A [CB 8 j0] -> rw_cells psegs m (A + 8) [c1] -> rw_cells psegs m (A + 16) [c2] -> rw_cells psegs m (A + 24) rest ->
    csize c1 = 8%nat -> csize c2 = 8%nat ->
    rw_cells psegs m A (CB 24 (cells_bytes [CB 8 j0; c1; c2]) :: rest).
  Proof.
    intros m A j0 c1 c2 rest H0 H1 H2 HR E1 E2. apply frame_top24; [| reflexivity| exact E1| exact E2].
    change (CB 8 j0 :: c1 :: c2 :: rest) with ([CB 8 j0] ++ [c1] ++ [c2] ++ rest).
    apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact H0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [eapply rw_cells_addr_eq; [exact H1| lia]|]. cbn [cells_size Nat.add]. rewrite E1.
    apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [eapply rw_cells_addr_eq; [exact H2| lia]|]. cbn [cells_size Nat.add]. rewrite E2.
    eapply rw_cells_addr_eq; [exact HR| lia].
  Qed.

  Lemma to_bytes_nth : forall (l : list Z) i, 0 <= i < zlength l -> nth_error (to_bytes l) (Z.to_nat i) = Some (Z_to_bv 8 (znth l i)).
  Proof.
    intros l i Hi. unfold to_bytes, znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite nth_error_map. unfold zlength in Hi.
    destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E.
    - cbn. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
    - apply nth_error_None in E. lia.
  Qed.
  Lemma znth_byte : forall (l : list Z) i, Forall (fun c => 0 <= c < 256) l -> 0 <= i < zlength l -> 0 <= znth l i < 256.
  Proof. intros l i HF Hi. apply (proj1 (Forall_forall _ _) HF). apply znth_range. exact Hi. Qed.
  Lemma unsigned8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
  Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

  Notation POSTF ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 := (rfuzz_one_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11).

  Lemma fz_exit : forall (ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (s0 s : PState) (LB LK : list block) (D : Z) (d : list Z) (j : list byte) (lo B : Z) (errv canary : word),
    lx_env m s LK LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv canary ->
    rw_cells psegs m (bv_unsigned sp + -96) [CB 24 j; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m0 m -> ps_so s = ps_so s0 -> ps_fa s = ps_fa s0 -> frm0 fc ->
    (length LK <= 2)%nat -> payload_ok m LB D d ->
    bv_unsigned sp <= B -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    evt psegs (rfuzz_one_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB D d lo B canary m0 0 s)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v S8 S9 S10 S11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16084) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV FR PRES ESO EFA FRM LKL POK SPB LOSP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & B63 & ST & LOC & _ & _ & _ & MI).
    unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in LOSP.
    rewrite unsigned_lit in ST by lia.
    eapply fz_ret; [exact FR| exact ST| lia| exact MI| lia| lia|]. intros. unfold rfuzz_one_post.
    do 15 eexists. exists F, fc, m, LK. split; [reflexivity|].
    split; [| split; [exact LKL| split; [reflexivity| split; [reflexivity| exact POK]]]].
    unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| assumption| exact SPB]|].
    split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
  Qed.

  Lemma frame_split4 : forall m A (j0 : list byte) (c1 c2 : cell) rest,
    rw_cells psegs m A (CB 8 j0 :: c1 :: c2 :: rest) -> csize c1 = 8%nat -> csize c2 = 8%nat ->
    rw_cells psegs m A [CB 8 j0] /\ rw_cells psegs m (A + 8) [c1] /\ rw_cells psegs m (A + 16) [c2] /\ rw_cells psegs m (A + 24) rest.
  Proof.
    intros m A j0 c1 c2 rest H E1 E2.
    change (CB 8 j0 :: c1 :: c2 :: rest) with ([CB 8 j0] ++ [c1] ++ [c2] ++ rest) in H.
    apply (proj1 (rw_cells_app psegs _ _ _ _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add] in H.
    apply (proj1 (rw_cells_app psegs _ _ _ _)) in H. destruct H as [H1 H]. cbn [cells_size Nat.add] in H. rewrite E1 in H.
    apply (proj1 (rw_cells_app psegs _ _ _ _)) in H. destruct H as [H2 H]. cbn [cells_size Nat.add] in H. rewrite E2 in H.
    split; [exact H0|]. split; [eapply rw_cells_addr_eq; [exact H1| lia]|]. split; [eapply rw_cells_addr_eq; [exact H2| lia]| eapply rw_cells_addr_eq; [exact H| lia]].
  Qed.

  Section Tail.
    Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
    Variables (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m0 : mem) (s0 : PState).
    Variables (n cl C U : Z) (cp up : bptr) (junk : list byte).
    Notation usp := (bv_unsigned sp).
    Notation SP_ := (usp + -96).
    Notation LB' := ((up, U, n) :: (cp, C, cl) :: LB).
    Notation RP := (rfuzz_one_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB D d lo B canary m0).
    Hypothesis SZ : 10 <= zlength d <= 1048576.
    Hypothesis EN : n = zlength d - 3.
    Hypothesis CLF : n < cl <= 2097152.
    Hypothesis CLM : cl <= zc_bound zc (1048576 - 3).
    Hypothesis DR : Forall (fun c => 0 <= c < 256) d.
    Hypothesis D0 : 0 < D.
    Hypothesis PAYR : forall a, D <= a < D + zlength d -> a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ in_block LB a.
    Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).
    Hypothesis CR : rblock_range C cl.
    Hypothesis UR : rblock_range U n.
    Hypothesis NEQ : cp <> up.
    Hypothesis SEPC : forall b, In b LB -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b.
    Hypothesis SEPU : forall b, In b ((cp, C, cl) :: LB) -> blk_addr b + blk_size b <= U \/ U + n <= blk_addr b.
    Hypothesis DC : D + zlength d <= C \/ C + cl <= D.
    Hypothesis LOC : alloc_ceiling <= lo.
    Hypothesis LOG : 376832 <= lo.
    Hypothesis LOSP : lo <= usp - LX_FUZZ_STACK.
    Hypothesis SPB : usp <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis TP : tp = wz RATP.
    Hypothesis SP16 : usp mod 16 = 0.

    Lemma tail_facts : 0 <= usp < 2^64 /\ lo <= usp - 12496 /\ bv_unsigned (Z_to_bv 64 SP_) = SP_ /\ SP_ mod 16 = 0.
    Proof.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in LOSP.
      split; [lia|]. split; [lia|]. split; [apply unsigned_lit; lia| clear - SP16 RSP; Z.div_mod_to_equations; lia].
    Qed.

    Lemma fz_frees : forall mm ss errvx (x1 w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 s2v s3v s4v s5v s6v s7v w3 w4 w5 w6 : word) Fx fcx (cu cc : cell),
      lx_env mm ss [] LB' (Z_to_bv 64 SP_) tp B lo errvx canary -> WLD sp LB D d n m0 s0 mm ss -> frm0 fcx ->
      rw_cells psegs mm SP_ [CB 8 (take 8 junk)] -> rw_cells psegs mm (usp + -88) [cu] -> rw_cells psegs mm (usp + -80) [cc] ->
      csize cu = 8%nat -> csize cc = 8%nat ->
      rw_cells psegs mm (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
      implM psegs (mbind (Target.lib_free_opt raw_free (Some cp)) (fun _ => mbind (Target.lib_free_opt raw_free (Some up)) (fun _ => mret 0))) ss RP
        (MS (mkR x1 (Z_to_bv 64 SP_) gp tp w0 w1 w2 (Z_to_bv 64 C) (Z_to_bv 64 U) e0 e1 e2 e3 e4 e5 e6 e7 s2v s3v s4v s5v s6v s7v S8 S9 S10 S11 w3 w4 w5 w6)
            Fx (Z_to_bv 64 0x16074) fcx None mm (seg_rom psegs)).
    Proof.
      intros until cc. intros ENVm WLDm FRMm FJ FU FC EU EC FH.
      pose proof tail_facts as (RSP & LOSP' & E96 & SPM).
      cbn [Target.lib_free_opt].
      pose proof ENVm as (HPm & _ & _ & _ & _ & AUXm & _ & _ & STm & _ & _ & ERRm & _ & MIm). rewrite E96 in STm. cbn [app] in HPm.
      assert (HPm' : RHEAP ss ((cp, C, cl) :: (up, U, n) :: LB) mm) by (eapply RHEAP_perm; [exact HPm| apply perm_swap]).
      assert (ENVm' : lx_env mm ss [(cp, C, cl); (up, U, n)] LB (Z_to_bv 64 SP_) tp B lo errvx canary) by (eapply lx_env_blocks; [exact ENVm| exact HPm']).
      pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl psegs mm) as WM.
      unfold implM. iprefix. zstep. zstep. clear MU WM. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss RP msx) end.
      eapply implM_bind.
      { eapply FREE with (s := ss) (LB := (cp, C, cl) :: (up, U, n) :: LB) (p := cp) (A := C) (n := cl) (lo := lo) (B := B) (errv := errvx);
          rewrite ?E96; unfold RFREE_STACK;
          [ exact HPm' | left; reflexivity | exact AUXm | lia | exact STm | exact LOC | lia | exact ERRm | exact MIm | exact TP | reflexivity ]. }
      cbv beta. intros [] ss' ms' PO.
      destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & mm' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
      replace (ret_pc (Z_to_bv 64 0x1607c)) with (Z_to_bv 64 0x1607c) by (symmetry; rpc).
      rewrite (lb_remove_head cp C cl _ (HND _ _ _ HPm')) in HPR', HP'.
      pose proof HPR' as HPRr. rewrite E96 in HPRr.
      pose proof (WLD_heap sp LB D d n m0 s0 lo _ mm mm' ss ss' PAYR WLDm HPRr ltac:(intros b Hb; right; exact Hb) ESO' EFA') as WLD'.
      assert (ENV' : lx_env mm' ss' [(up, U, n)] LB (Z_to_bv 64 SP_) tp B lo errvx canary).
      { eapply (lx_env_heap mm mm' ss ss'); [exact ENVm'| rewrite E96; eapply rheap_pres_weaken; [exact HPRr| lia| intros b Hb; right; exact Hb]| exact HP'| exact MI'| exact ST'| exact ERR'| exact AUX']. }
      pose proof (agree_of_heap_pres _ _ _ _ HPRr) as AG'.
      assert (FJ' : rw_cells psegs mm' SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG'| exact FJ| intros a Ha; cbn in Ha; left; lia]).
      assert (FU' : rw_cells psegs mm' (usp + -88) [cu]) by (eapply rw_cells_agree; [exact AG'| exact FU| intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite EU in Ha; left; lia]).
      assert (FC' : rw_cells psegs mm' (usp + -80) [cc]) by (eapply rw_cells_agree; [exact AG'| exact FC| intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite EC in Ha; left; lia]).
      assert (FH' : rw_cells psegs mm' (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG'| exact FH| intros a Ha; cbn in Ha; left; lia]).
      rewrite E96 in ST'.
      pose proof (munch_refl ([] : list (Z * Z)) mm') as MU. pose proof (wmono_refl psegs mm') as WM.
      unfold implM. iprefix. zstep. zstep. clear MU WM. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss' RP msx) end.
      eapply implM_bind.
      { eapply FREE with (s := ss') (LB := (up, U, n) :: LB) (p := up) (A := U) (n := n) (lo := lo) (B := B) (errv := errvx);
          rewrite ?E96; unfold RFREE_STACK;
          [ exact HP' | left; reflexivity | exact AUX' | lia | exact ST' | exact LOC | lia | exact ERR' | exact MI' | exact TP | reflexivity ]. }
      cbv beta. intros [] ss'' ms'' PO.
      destruct PO as (o0 & o1 & o2 & l0 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & o3 & o4 & o5 & o6 & mm'' & -> & MI'' & ST'' & ERR'' & AUX'' & HPR'' & EFA'' & ESO'' & HP'').
      replace (ret_pc (Z_to_bv 64 0x16084)) with (Z_to_bv 64 0x16084) by (symmetry; rpc).
      rewrite (lb_remove_head up U n _ (HND _ _ _ HP')) in HPR'', HP''.
      pose proof HPR'' as HPRr2. rewrite E96 in HPRr2.
      pose proof (WLD_heap sp LB D d n m0 s0 lo _ mm' mm'' ss' ss'' PAYR WLD' HPRr2 ltac:(auto) ESO'' EFA'') as WLD''.
      assert (ENV'' : lx_env mm'' ss'' [] LB (Z_to_bv 64 SP_) tp B lo errvx canary).
      { eapply (lx_env_heap mm' mm'' ss' ss''); [exact ENV'| rewrite E96; eapply rheap_pres_weaken; [exact HPRr2| lia| auto]| exact HP''| exact MI''| exact ST''| exact ERR''| exact AUX'']. }
      pose proof (agree_of_heap_pres _ _ _ _ HPRr2) as AG''.
      assert (FJ'' : rw_cells psegs mm'' SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG''| exact FJ'| intros a Ha; cbn in Ha; left; lia]).
      assert (FU'' : rw_cells psegs mm'' (usp + -88) [cu]) by (eapply rw_cells_agree; [exact AG''| exact FU'| intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite EU in Ha; left; lia]).
      assert (FC'' : rw_cells psegs mm'' (usp + -80) [cc]) by (eapply rw_cells_agree; [exact AG''| exact FC'| intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite EC in Ha; left; lia]).
      assert (FH'' : rw_cells psegs mm'' (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG''| exact FH'| intros a Ha; cbn in Ha; left; lia]).
      pose proof (frame_join4 mm'' SP_ _ cu cc _ FJ'' ltac:(eapply rw_cells_addr_eq; [exact FU''| lia]) ltac:(eapply rw_cells_addr_eq; [exact FC''| lia]) ltac:(eapply rw_cells_addr_eq; [exact FH''| lia]) EU EC) as FR24.
      destruct WLD'' as (PRES'' & ESOw & EFAw & POK'' & _).
      apply implM_ret.
      eapply fz_exit; [exact ENV''| exact FR24| exact PRES''| exact ESOw| exact EFAw| exact FRMm| cbn; lia| exact POK''| exact SPB| exact LOSP].
    Qed.

    (** A failed check: the issued binary calls __assert_fail and aborts, and the model has an unreachable leaf
        there ([ZTargetC.check_failM]), so the walk stops at the branch (the model's safety proof,
        [TargetSafeR.fuzz_one_R], shows the leaf is never reached). *)
    Lemma fz_check : forall (k : ckfail) ss (Q : Z -> PState -> machine_state -> Prop) ms,
      implM psegs (check_failM lops (@Target.err_pieces PState) (Target.cb_exit ps_so set_so_ps) k) ss Q ms.
    Proof. intros k ss Q ms. unfold check_failM, lops. cbv zeta. cbn [unreachable Target.ops]. apply implM_unr. Qed.

    Lemma fz_decomp : forall mm ss errvx (x1 w0 w1 w2 e0 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 v7s vu vc : word) Fx fcx (cout : list Z),
      lx_env mm ss [] LB' (Z_to_bv 64 SP_) tp B lo errvx canary -> WLD sp LB D d n m0 s0 mm ss -> frm0 fcx ->
      rw_cells psegs mm SP_ [CB 8 (take 8 junk)] -> rw_cells psegs mm (usp + -88) [C8 vu] -> rw_cells psegs mm (usp + -80) [C8 vc] ->
      rw_cells psegs mm (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
      u8arr psegs mm C (to_bytes (zstore (zrepeat 0 cl) 0 cout)) -> Forall (fun c => 0 <= c < 256) cout -> zlength cout <= cl ->
      implM psegs (mbind (check_decompressM lops zc (zdrop 3 d) n cl (sel_cm d) (sel_flags d))
                        (fun _ => mbind (Target.lib_free_opt raw_free (Some cp)) (fun _ => mbind (Target.lib_free_opt raw_free (Some up)) (fun _ => mret 0)))) ss RP
        (MS (mkR x1 (Z_to_bv 64 SP_) gp tp w0 w1 w2 (Z_to_bv 64 C) (Z_to_bv 64 U) e0 e1 e2 e3 e4 e5 e6 e7
                 (Z_to_bv 64 cl) (Z_to_bv 64 n) (Z_to_bv 64 (sel_cm d)) (Z_to_bv 64 (znth d 2)) (Z_to_bv 64 239648) v7s S8 S9 S10 S11 w3 w4 w5 w6)
            Fx (Z_to_bv 64 0x15fdc) fcx None mm (seg_rom psegs)).
    Proof.
      intros until cout. intros ENVm WLDm FRMm FJ FU FC FH CARR CF LCL.
      pose proof tail_facts as (RSP & LOSP' & E96 & SPM).
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      pose proof (znth_byte d 2 DR ltac:(lia)) as RB2. pose proof (znth_byte d 1 DR ltac:(lia)) as RB1.
      assert (DHI : D + zlength d <= lo) by (destruct (PAYR (D + zlength d - 1) ltac:(lia)) as (X & _); lia).
      assert (LCC : Z.of_nat (length (to_bytes (zstore (zrepeat 0 cl) 0 cout))) = cl) by (rewrite to_bytes_len; pose proof (zstore_length cout (zrepeat 0 cl) 0) as X; unfold zlength in X; unfold zrepeat in *; rewrite repeat_length in X; lia).
      assert (LND : Z.of_nat (length (to_bytes (zdrop 3 d))) = n) by (rewrite to_bytes_len; unfold zdrop; rewrite length_skipn; unfold zlength in *; lia).
      pose proof ENVm as (HPm & _ & _ & _ & _ & AUXm & _ & _ & STm & _ & _ & ERRm & _ & MIm). rewrite E96 in STm. cbn [app] in HPm.
      pose proof (box _ WLDm) as WLDb. destruct WLDm as (PRm & ESOm & EFAm & POKm & ZSTm & MRPm & RESTm). unfold zhc_statics, ZH_STATICS in ZSTm. cbv beta delta [MallocRep.wz] in ZSTm.
      unfold check_decompressM. cbn [bind ret unreachable lib_malloc lib_free lops Target.ops].
      apply implM_bind_assoc.

      apply box in CARR.
      pose proof (munch_refl [(usp + -80, usp + -72)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
      unfold implM. iprefix. zs. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
      assert (ENV1 : lx_env m1 ss [] LB' (Z_to_bv 64 SP_) tp B lo errvx canary).
      { eapply (lx_env_munch [(usp + -80, usp + -72)] mm m1); [exact HFRAME| exact ENVm| exact MU| exact WM| assumption| rewrite E96; assumption| rewrite E96; lia| |].
        - constructor; [left; cbn [fst]; lia| constructor].
        - intros a Ha. cbn [outside]. clear - Ha SPB LOG LOSP' RSP. lia. }
      assert (WLD1 : WLD sp LB D d n m0 s0 m1 ss).
      { eapply (WLD_munch sp LB D d n m0 s0 lo _ mm m1 ss PAYR (unbox _ WLDb) MU WM).
        - intros a Ha. cbn [outside]. split; [| exact I]. destruct Ha as [Ha|[(b & Hb & Hr)|[Ha _]]]; [lia| destruct (LBR b Hb) as (_ & _ & _ & BC & _); lia| lia].
        - unfold zhc_statics, ZH_STATICS. cbv beta delta [MallocRep.wz]. exact ZSTm. }
      assert (CARR1 : u8arr psegs m1 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))) by (eapply u8arr_agree; [exact AG1| exact (unbox _ CARR)| intros a Ha; rewrite LCC in Ha; cbn [outside]; lia]).
      pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & _ & _ & ST1 & _ & _ & ERR1 & _ & MI1). rewrite E96 in ST1. cbn [app] in HP1.
      clear AG1 MU WM CARR.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss RP msx) end.
      eapply implM_bind.
      { eapply MALLOC with (s := ss) (LB := LB') (n := n + 2) (lo := lo) (B := B) (errv := errvx);
          rewrite ?E96; unfold RMALLOC_STACK;
          [ exact HP1 | exact AUX1 | lia | exact ST1 | exact LOC | lia | exact ERR1 | exact MI1 | exact TP | unfold MallocRep.wz; f_equal; lia | lia ]. }
      cbv beta. intros r ss2 ms2 PO. unfold rmalloc_post in PO.
      destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR2 & EFA2 & ESO2 & RES).
      replace (ret_pc (Z_to_bv 64 0x15fec)) with (Z_to_bv 64 0x15fec) by (symmetry; rpc).
      pose proof HPR2 as HPR2r. rewrite E96 in HPR2r.
      pose proof (WLD_heap sp LB D d n m0 s0 lo LB' m1 m2 ss ss2 PAYR WLD1 HPR2r ltac:(intros b Hb; right; right; exact Hb) ESO2 EFA2) as WLD2.
      pose proof (agree_of_heap_pres _ _ _ _ HPR2r) as AG2.
      lazymatch goal with FJ1 : rw_cells psegs m1 SP_ _ |- _ => assert (FJ2 : rw_cells psegs m2 SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG2| exact FJ1| intros a Ha; cbn in Ha; left; lia]) end
        || assert (FJ2 : rw_cells psegs m2 SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG2| exact FJ| intros a Ha; cbn in Ha; left; lia]).
      assert (FU2 : rw_cells psegs m2 (usp + -88) [C8 vu]) by (eapply rw_cells_agree; [exact AG2| exact FU| intros a Ha; cbn in Ha; left; lia]).
      lazymatch goal with FC1 : rw_cells psegs m1 (usp + -80) _ |- _ => assert (FC2 : rw_cells psegs m2 (usp + -80) [C8 (Z_to_bv 64 cl)]) by (eapply rw_cells_agree; [exact AG2| exact FC1| intros a Ha; cbn in Ha; left; lia]) end.
      assert (FH2 : rw_cells psegs m2 (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG2| exact FH| intros a Ha; cbn in Ha; left; lia]).
      assert (CARR2 : u8arr psegs m2 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))).
      { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha. rewrite LCC in Ha. right; right. exists (cp, C, cl). split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
      destruct r as [kp|].
      2:{
        destruct RES as [-> HP2].
        assert (ENV2 : lx_env m2 ss2 [] LB' (Z_to_bv 64 SP_) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
        apply implM_retb.
        pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        unfold implM. iprefix. zstep. if_true. apply evt_done.
        eapply (fz_frees m2 ss2 errv2); [exact ENV2| exact WLD2| exact FRMm| exact FJ2| exact FU2| exact FC2| reflexivity| reflexivity| exact FH2]. }

      destruct RES as (A & junkA & -> & AR & HP2 & KB & _).
      pose proof AR as (A0 & _ & _ & AC & AI).
      assert (ENV2 : lx_env m2 ss2 [(kp, A, n + 2)] LB' (Z_to_bv 64 SP_) tp B lo errv2 canary) by (eapply lx_env_heap; [exact ENV1| exact HPR2| exact HP2| exact MI2| exact ST2| exact ERR2| exact AUX2]).
      assert (SEPA : forall b, In b LB' -> blk_addr b + blk_size b <= A \/ A + (n + 2) <= blk_addr b).
      { intros b Hb. pose proof (heap_sep ss2 [(kp, A, n + 2)] LB' m2 (kp, A, n + 2) b HND HBD HP2 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
      assert (DA : D + zlength d <= A \/ A + (n + 2) <= D).
      { destruct (PAYR D ltac:(lia)) as (_ & _ & (bd & Hbd & Hr)). pose proof (SEPA bd ltac:(right; right; exact Hbd)). pose proof (LBR _ Hbd) as (_ & _ & BS & _).
        destruct (PAYR (D + zlength d - 1) ltac:(lia)) as (_ & _ & (bd' & Hbd' & Hr')). pose proof (SEPA bd' ltac:(right; right; exact Hbd')). lia. }
      assert (NEQK : cp <> kp).
      { pose proof (HND _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. inversion ND as [|? ? NI _]; subst. intros E. apply NI. right. left. exact E. }
      rewrite E96 in ST2.
      pose proof (box _ WLD2) as WLD2b. destruct WLD2 as (PR2 & ESO2' & EFA2' & POK2 & ZST2 & MRP2 & REST2). unfold zhc_statics, ZH_STATICS in ZST2. cbv beta delta [MallocRep.wz] in ZST2.
      pose proof POK2 as (DBY2 & _).
      assert (SRC2 : bytes_at psegs m2 (D + 3) (to_bytes (zdrop 3 d))).
      { unfold zdrop. rewrite to_bytes_skipn. pose proof DBY2 as X. rewrite <- (firstn_skipn 3 (to_bytes d)) in X. apply bytes_at_app in X. destruct X as [_ X].
        rewrite length_firstn, to_bytes_len, Nat.min_l in X by (unfold zlength in *; lia). exact X. }

      apply (rw_cells_split_CB psegs _ _ [] (Z.to_nat (n + 2)) junkA [] [2; Z.to_nat n]%nat) in KB; [| cbn [sum_nat]; lia]. cbn [mk_CB_cells app] in KB.
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in KB. destruct KB as [KB01 KBD]. cbn [cells_size csize Nat.add] in KBD.
      apply implM_bind_assoc.

      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      apply box in CARR2. apply box in SRC2.
      unfold implM. iprefix.
      zstep. if_cases KK; zify_cond KK; rewrite ?unsigned_lit in KK by lia; [exfalso; lia|].
      zstep. zstep. zstep. zstep. zstep. zstep. clear MU WM.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fcx m2 (to_bytes (zdrop 3 d))); rewrite ?unsigned_lit by lia;
          [ exact (unbox _ SRC2) | rewrite to_bytes_len; unfold zdrop; rewrite length_skipn; unfold zlength in *; lia
          | eapply rw_cells_addr_eq; [exact KBD| lia] | lia | exact MI2 ]. }
      cbv beta. intros ms3 (v0 & v1 & v2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & KBD3 & SRC3).
      replace (ret_pc (Z_to_bv 64 0x16008)) with (Z_to_bv 64 0x16008) by (symmetry; rpc).
      rewrite ?unsigned_lit in MU3, KBD3, SRC3 by lia. rewrite ?(unsigned_lit n) in KBD3 by lia. rewrite ?(unsigned_lit n) in MU3 by lia.
      pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
      lazymatch type of MU3 with munch ?W _ _ => assert (OUT3 : forall a, ~ (A + 2 <= a < A + 2 + n) -> outside W a) by (intros a Ha; cbn [outside]; rewrite ?unsigned_lit by lia; lia) end.
      assert (KB013 : rw_cells psegs m3 A [CB 2 (take 2 junkA)]) by (eapply rw_cells_agree; [exact AG3| exact KB01| intros a Ha; cbn in Ha; apply OUT3; lia]).
      assert (ST3 : stk psegs m3 lo SP_) by (eapply stk_agree; [exact AG3| exact ST2| intros a Ha; apply OUT3; lia]).

      pose proof (land32_cases (znth d 2) RB2) as FLC.
      assert (CMC : sel_cm d = 0 \/ sel_cm d = 1 \/ sel_cm d = 2 \/ sel_cm d = 3 \/ sel_cm d = 8).
      { unfold sel_cm. pose proof (Z.mod_pos_bound (znth d 1) 5 ltac:(lia)) as M5. destruct (Z.eqb_spec (znth d 1 mod 5) 4); lia. }
      eapply hdr_steps with (cm := sel_cm d) (fl := Z.land (znth d 2) 32); [exact MI3| exact CMC| exact FLC|].
      intros v10 v11 v12 v20 v21 H10 H11. clear CMC FLC. apply box in H10. apply box in H11.
      assert (FJ3 : rw_cells psegs m3 SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG3| exact FJ2| intros a Ha; cbn in Ha; apply OUT3; lia]).
      assert (FU3 : rw_cells psegs m3 (usp + -88) [C8 vu]) by (eapply rw_cells_agree; [exact AG3| exact FU2| intros a Ha; cbn in Ha; apply OUT3; lia]).
      assert (FC3 : rw_cells psegs m3 (usp + -80) [C8 (Z_to_bv 64 cl)]) by (eapply rw_cells_agree; [exact AG3| exact FC2| intros a Ha; cbn in Ha; apply OUT3; lia]).
      assert (FH3 : rw_cells psegs m3 (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG3| exact FH2| intros a Ha; cbn in Ha; apply OUT3; lia]).
      assert (ZST3 : rw_cells psegs m3 239648 [C8 (Z_to_bv 64 (D + 3)); C8 (Z_to_bv 64 n)]) by (eapply rw_cells_agree; [exact AG3| exact ZST2| intros a Ha; cbn in Ha; apply OUT3; lia]).
      pose proof (SEPA (cp, C, cl) ltac:(right; left; reflexivity)) as SCA. cbn [blk_addr blk_size fst snd] in SCA.
      assert (CARR3 : u8arr psegs m3 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))) by (eapply u8arr_agree; [exact AG3| exact (unbox _ CARR2)| intros a Ha; rewrite LCC in Ha; apply OUT3; lia]).
      apply box in CARR3. apply box in KBD3. clear FJ2 FU2 FC2 FH2 ZST2 CARR2 SRC2 SRC3.

      apply box in MU3. apply box in WM3.
      pose proof (munch_refl [(A, A + 2)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
      pose proof KB013 as [[WFK _] _]. cbn [cells_wf cell_wf] in WFK. destruct WFK as [LK2 _].
      destruct (list2_of_len _ LK2) as (bj0 & bj1 & EJ). rewrite EJ in KB013.
      assert (KC : rw_cells psegs m3 A [C1 bj0; C1 bj1]) by (eapply rw_cells_recast; [exact KB013| cbn; repeat split| reflexivity]).
      clear KB013.
      zstep. change (le1 v10) with [Z_to_bv 8 (bv_unsigned v10)]. mem_after_store.
      zstep. change (le1 v11) with [Z_to_bv 8 (bv_unsigned v11)]. mem_after_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG4.
      assert (KBD4 : rw_cells psegs m4 (A + 2) [CB (Z.to_nat n) (to_bytes (zdrop 3 d))]) by (eapply rw_cells_agree; [exact AG4| exact (unbox _ KBD3)| intros a Ha; cbn [cells_size csize Nat.add] in Ha; cbn [outside]; lia]).
      assert (CARR4 : u8arr psegs m4 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))) by (eapply u8arr_agree; [exact AG4| exact (unbox _ CARR3)| intros a Ha; rewrite LCC in Ha; cbn [outside]; lia]).
      assert (MU24 : munch [(A, A + (n + 2))] m2 m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact (unbox _ MU3)]| eapply munch_weaken; [| exact MU]]; intros a Ha; cbn [outside] in Ha |- *; rewrite ?unsigned_lit by lia; (split; [lia| exact I]). }
      assert (WM24 : wmono psegs m2 m4) by (eapply wmono_trans; [exact (unbox _ WM3)| exact WM]).
      assert (ENV4 : lx_env m4 ss2 [] ((kp, A, n + 2) :: LB') (Z_to_bv 64 SP_) tp B lo errv2 canary).
      { eapply lx_env_blocks with (OW := [(kp, A, n + 2)]) (LB := LB'); [| destruct ENV2 as [HPx _]; eapply HFRAME; [exact HPx| exact MU24| exact WM24|]; constructor; [right; right; exists (kp, A, n + 2); split; [left; reflexivity| cbn; lia]| constructor]].
        eapply (lx_env_munch [(A, A + (n + 2))] m2 m4); [exact HFRAME| exact ENV2| exact MU24| exact WM24| assumption| rewrite E96; assumption| rewrite E96; lia| |].
        - constructor; [right; right; exists (kp, A, n + 2); split; [left; reflexivity| cbn; lia]| constructor].
        - intros a Ha. cbn [outside]. clear - Ha AC AI A0 LOC LOSP' SPB. lia. }
      assert (WLD4 : WLD sp LB D d n m0 s0 m4 ss2).
      { eapply (WLD_munch sp LB D d n m0 s0 lo _ m2 m4 ss2 PAYR (unbox _ WLD2b) MU24 WM24).
        - intros a Ha. cbn [outside]. split; [| exact I]. destruct Ha as [Ha|[(b & Hb & Hr)|[Ha _]]]; [lia| pose proof (SEPA b ltac:(right; right; exact Hb)); lia| lia].
        - unfold zhc_statics, ZH_STATICS. cbv beta delta [MallocRep.wz]. exact ZST3. }
      pose proof (zhdr_bytes_ok (sel_cm d) (Z.land (znth d 2) 32)) as [HDRF HDRL]. pose proof HDRF as HDRF2. rewrite zhdr_bytes_eq in HDRF2.
      pose proof (Forall_inv HDRF2) as R0. pose proof (Forall_inv (Forall_inv_tail HDRF2)) as R1. cbv beta in R0, R1.
      assert (EB0 : Z_to_bv 8 (bv_unsigned v10) = Z_to_bv 8 (hdr0 (sel_cm d) (Z.land (znth d 2) 32))).
      { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (unbox _ H10). symmetry. apply Z.mod_small. exact R0. }
      assert (EB1 : Z_to_bv 8 (bv_unsigned v11) = Z_to_bv 8 (hdr1 (sel_cm d) (Z.land (znth d 2) 32))).
      { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (unbox _ H11). symmetry. apply Z.mod_small. exact R1. }
      rewrite EB0, EB1 in KC.
      assert (KALL : u8arr psegs m4 A (to_bytes (zhdr_bytes (sel_cm d) (Z.land (znth d 2) 32) ++ zdrop 3 d))).
      { rewrite zhdr_bytes_eq, to_bytes_app. cbn [to_bytes map app].
        apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat (n + 2))).
        eapply rw_cells_recast.
        - apply (proj2 (rw_cells_app psegs m4 A [C1 (Z_to_bv 8 (hdr0 (sel_cm d) (Z.land (znth d 2) 32))); C1 (Z_to_bv 8 (hdr1 (sel_cm d) (Z.land (znth d 2) 32)))] [CB (Z.to_nat n) (to_bytes (zdrop 3 d))])).
          split; [exact KC| cbn [cells_size csize Nat.add]; exact KBD4].
        - cbn. split; [| exact I]. cbn [length]. rewrite to_bytes_len. unfold zdrop. rewrite length_skipn. unfold zlength in *. lia.
        - cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. }
      clear AG4 KBD3 KBD4 CARR3 MU WM.

      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl psegs m4) as WM.
      zstep. zstep. zstep. zstep. zstep. clear MU WM.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss2 RP msx) end.
      unfold runcompress_stmt in UNC.
      eapply implM_bind.
      { eapply UNC with (s := ss2) (LB := (kp, A, n + 2) :: LB') (up := cp) (cpS := kp) (U := C) (dlen := cl) (PL := usp + -80) (C := A) (cl := n + 2) (slen := n + 2)
                        (uc := zstore (zrepeat 0 cl) 0 cout) (comprc := zhdr_bytes (sel_cm d) (Z.land (znth d 2) 32) ++ zdrop 3 d) (lo := lo) (B := B) (errv := errv2) (canary := canary);
          rewrite ?E96; unfold ZC_UNC_STACK, ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, ZC_MAX;
          [ nm 1 ltac:(exact ENV4) | nm 2 ltac:(right; right; left; reflexivity) | nm 3 ltac:(exact CARR4)
          | nm 4 ltac:(rewrite zstore_length; unfold zrepeat, zlength; rewrite repeat_length; lia)
          | nm 5 ltac:(exact FC3) | nm 6 ltac:(lia) | nm 7 ltac:(lia) | nm 8 ltac:(clear - SP16 RSP; Z.div_mod_to_equations; lia)
          | nm 9 ltac:(left; reflexivity) | nm 10 ltac:(exact KALL)
          | nm 11 ltac:(rewrite zlength_app', HDRL; unfold zdrop; unfold zlength; rewrite length_skipn; clear - SZ EN; unfold zlength in *; lia)
          | nm 12 ltac:(apply Forall_app; split; [exact HDRF| unfold zdrop; apply Forall_skipn_; exact DR])
          | nm 13 ltac:(lia)
          | nm 14 ltac:(unfold ztake; apply firstn_all2; rewrite zhdr_bytes_eq; cbn [length app]; unfold zdrop; rewrite length_skipn; clear - SZ EN; unfold zlength in *; lia)
          | nm 15 ltac:(exact NEQK)
          | nm 16 ltac:(lia) | nm 17 ltac:(replace (zc_bound zc (1048576 - 3)) with 1048904 by (vm_compute; reflexivity); clear - SZ EN; lia)
          | nm 18 ltac:(lia) | nm 19 ltac:(exact SPM) | nm 20 ltac:(exact FRMm)
          | nm 21 ltac:(reflexivity) | nm 22 ltac:(unfold MallocRep.wz; f_equal; lia) | nm 23 ltac:(reflexivity) | nm 24 ltac:(reflexivity) ]. }
      cbv beta. intros [[ko kt] krc] ss3 ms3' PO. unfold runcompress_post in PO. cbn [fst snd] in PO.
      destruct PO as (z0 & z1 & z2 & g0' & g1' & g2' & g3' & g4' & g5' & g6' & g7' & z3 & z4 & z5 & z6 & F5 & fc5 & m5 & rc5 & -> & ((errv5 & ENV5) & FRM5 & LXP5 & ESO5 & EFA5) & -> & _ & _ & _ & _ & _ & FC5).
      replace (ret_pc (Z_to_bv 64 0x1606c)) with (Z_to_bv 64 0x1606c) by (symmetry; rpc).
      rewrite E96 in LXP5. cbv beta delta [MallocRep.wz] in FC5.
      assert (HLk : forall b, In b LB -> In b ((kp, A, n + 2) :: LB')) by (intros b Hb; right; right; right; exact Hb).
      assert (WLD5 : WLD sp LB D d n m0 s0 m5 ss3).
      { eapply (WLD_lx sp LB D d n m0 s0 lo _ _ C cl m4 m5 ss2 ss3 PAYR LBR LOC LOG ltac:(lia) WLD4 LXP5 HLk);
          [ intros a Ha; cbn [rin_ivs fst snd] in Ha; lia | exact SEPC | exact CI | exact CC | exact ESO5 | exact EFA5 ]. }
      pose proof (agree_of_lx_pres _ _ _ _ _ LXP5) as AG5.
      assert (NX5 : forall a, SP_ <= a -> ~ (usp + -80 <= a < usp + -72) -> lx_client ((kp, A, n + 2) :: LB') SP_ [(C, C + cl); (usp + -80, usp + -80 + 8)] a).
      { intros a Ha Hn. apply stack_client; [exact Ha|]. cbn [rin_ivs fst snd]. lia. }
      assert (FJ5 : rw_cells psegs m5 SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG5| exact FJ3| intros a Ha; cbn in Ha; apply NX5; lia]).
      assert (FU5 : rw_cells psegs m5 (usp + -88) [C8 vu]) by (eapply rw_cells_agree; [exact AG5| exact FU3| intros a Ha; cbn in Ha; apply NX5; lia]).
      assert (FH5 : rw_cells psegs m5 (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG5| exact FH3| intros a Ha; cbn in Ha; apply NX5; lia]).
      pose proof ENV5 as (HP5 & _ & _ & _ & _ & AUX5 & _ & _ & ST5 & _ & _ & ERR5 & _ & MI5). rewrite E96 in ST5. cbn [app] in HP5.
      clear AG5 NX5 FJ3 FU3 FH3 FC3 KALL KC CARR4.

      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl psegs m5) as WM.
      unfold implM. iprefix. zstep. zstep. clear MU WM. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
      eapply implM_bind.
      { eapply FREE with (s := ss3) (LB := (kp, A, n + 2) :: LB') (p := kp) (A := A) (n := n + 2) (lo := lo) (B := B) (errv := errv5);
          rewrite ?E96; unfold RFREE_STACK;
          [ exact HP5 | left; reflexivity | exact AUX5 | lia | exact ST5 | exact LOC | lia | exact ERR5 | exact MI5 | exact TP | reflexivity ]. }
      cbv beta. intros [] ss4 ms4' PO.
      destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR6 & EFA6 & ESO6 & HP6).
      replace (ret_pc (Z_to_bv 64 0x16074)) with (Z_to_bv 64 0x16074) by (symmetry; rpc).
      rewrite (lb_remove_head kp A (n + 2) _ (HND _ _ _ HP5)) in HPR6, HP6.
      pose proof HPR6 as HPR6r. rewrite E96 in HPR6r.
      pose proof (WLD_heap sp LB D d n m0 s0 lo LB' m5 m6 ss3 ss4 PAYR WLD5 HPR6r ltac:(intros b Hb; right; right; exact Hb) ESO6 EFA6) as WLD6.
      assert (ENV5' : lx_env m5 ss3 [(kp, A, n + 2)] LB' (Z_to_bv 64 SP_) tp B lo errv5 canary) by (eapply lx_env_blocks; [exact ENV5| exact HP5]).
      assert (ENV6 : lx_env m6 ss4 [] LB' (Z_to_bv 64 SP_) tp B lo errv5 canary).
      { eapply (lx_env_heap m5 m6 ss3 ss4); [exact ENV5'| exact HPR6| exact HP6| exact MI6| exact ST6| exact ERR6| exact AUX6]. }
      pose proof (agree_of_heap_pres _ _ _ _ HPR6r) as AG6.
      assert (FJ6 : rw_cells psegs m6 SP_ [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG6| exact FJ5| intros a Ha; cbn in Ha; left; lia]).
      assert (FU6 : rw_cells psegs m6 (usp + -88) [C8 vu]) by (eapply rw_cells_agree; [exact AG6| exact FU5| intros a Ha; cbn in Ha; left; lia]).
      assert (FC6 : rw_cells psegs m6 (usp + -80) [C8 (Z_to_bv 64 kt)]) by (eapply rw_cells_agree; [exact AG6| exact FC5| intros a Ha; cbn in Ha; left; lia]).
      assert (FH6 : rw_cells psegs m6 (usp + -72) [C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 ra]) by (eapply rw_cells_agree; [exact AG6| exact FH5| intros a Ha; cbn in Ha; left; lia]).
      rewrite E96 in ST6.

      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl psegs m6) as WM.
      clear MU WM.
      eapply (fz_frees m6 ss4 errv5); [exact ENV6| exact WLD6| exact FRM5| exact FJ6| exact FU6| exact FC6| reflexivity| reflexivity| exact FH6].
    Qed.
  End Tail.

  Theorem fz_main : rfuzz_oneC_stmt.
  Proof.
    unfold rfuzz_oneC_stmt. intros until canary.
    intros HP0 LXS0 ZLS0 SEW0 SSP0 AUX0 SPB B63 ST0 LOC LOG LOSP ERR0 TP MI0 SP16 POK0 SOF0 ADP0 XCB0 FRM -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOSP as LOSP0. unfold LX_FUZZ_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    pose proof POK0 as (DBY0 & DR & D0 & D63 & D30 & PIN0).
    assert (DL0 : 0 <= zlength d) by (unfold zlength; lia).
    assert (ENV0 : lx_env m s [] LB sp tp B lo errv canary).
    { unfold lx_env. cbn [app]. unfold GLOBALS_TOP. repeat (split; [eassumption|]). eassumption. }
    assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP0 Hb)).
    assert (PAYR : forall a, D <= a < D + zlength d -> a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ in_block LB a).
    { intros a Ha. destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in Ha; unfold zlength in Ha; cbn in Ha; lia|].
      pose proof (LBR bd Hbd) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|]. exists bd. split; [exact Hbd| lia]. }
    pose proof ZLS0 as (_ & _ & (v1 & v2 & ZHC) & MRP). unfold ZH_STATICS in ZHC. unfold ZL_MREPL in MRP. cbv beta delta [MallocRep.wz] in MRP.
    unfold fuzz_oneC. cbn [bind ret unreachable lib_malloc lib_free lops Target.ops]. rewrite (norm8_id d DR).
    unfold LX_FUZZ. cbv beta delta [MallocRep.wz].
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (0x3a820, 0x3a820 + 16)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (LD : Z.of_nat (length (to_bytes d)) = zlength d) by (rewrite to_bytes_len; reflexivity).
    set (RP := rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB D d lo B canary m).
    assert (IMG : forall a, 0x29000 <= a < 0x5c000 -> ~ (0x3a820 <= a < 0x3a820 + 16) -> outside [(bv_unsigned sp + -96, bv_unsigned sp); (0x3a820, 0x3a820 + 16)] a) by (intros a Ha Hz; cbn [outside]; lia).

    assert (OWN : forall mm (w1 w2 : word), munch [(bv_unsigned sp + -96, bv_unsigned sp); (0x3a820, 0x3a820 + 16)] m mm -> wmono psegs m mm -> mem_inv psegs mm ->
                    stk psegs mm lo (bv_unsigned sp + -96) -> rw_cells psegs mm 0x3a820 [C8 w1; C8 w2] ->
                    lx_env mm s [] LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv canary
                    /\ lx_pres LB (bv_unsigned sp) [LXW_ZH; LXW_STDERR] m mm /\ payload_ok mm LB D d
                    /\ stdout_file mm (ps_so s) /\ adp_cells_cb mm /\ xcb_cells mm).
    { intros mm w1 w2 MUm WMm MIm STm ZHm. pose proof (agree_on_of_munch _ _ _ MUm WMm) as AGm.
      split; [| split; [| split; [| split; [| split]]]].
      - eapply (lx_env_munch_gen _ m mm); [exact HFRAME| exact ENV0| exact MUm| exact WMm| exact MIm| rewrite unsigned_lit by lia; exact STm| rewrite unsigned_lit by lia; lia| | | | ].
        + constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        + intros a Ha. cbn [outside]. unfold ZH_STATICS, stderr_addr in Ha. lia.
        + eapply stderr_wfile0_agree; [exact AGm| | exact SEW0]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia.
        + exists w1, w2. exact ZHm.
      - eapply lx_pres_of_munch; [exact MUm| exact WMm|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
        + lia.
        + pose proof (LBR b Hb) as (_ & _ & _ & BC & BI). lia.
        + split; [lia|]. split; [| exact I]. intros Hz. apply HX. cbn [rin_ivs]. left. unfold LXW_ZH, ZH_STATICS. cbn [fst snd]. lia.
      - eapply payload_ok_agree; [exact AGm| exact POK0|]. intros a Ha. destruct (PAYR a Ha) as (P1 & P2 & _). cbn [outside]. lia.
      - eapply stdout_file_agree; [exact AGm| | exact SOF0]. intros a Ha. apply IMG; unfold stdout_addr in Ha; lia.
      - destruct ADP0 as (A1 & A2 & A3 & A4 & A5 & A6). unfold adp_cells_cb.
        repeat split; (eapply rw_cells_agree; [exact AGm| eassumption| intros a Ha; cbn in Ha; apply IMG; unfold RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0 in *; lia]).
      - destruct XCB0 as (td0 & td1 & td2 & td3 & t & X1 & Ht & X2). exists td0, td1, td2, td3, t.
        split; [eapply rw_cells_agree; [exact AGm| exact X1| intros a Ha; cbn in Ha; apply IMG; unfold REXIT_LOCK in *; lia]|]. split; [exact Ht|].
        eapply rw_cells_agree; [exact AGm| exact X2| intros a Ha; cbn in Ha; apply IMG; unfold REXIT_LOCK in *; lia]. }
    apply box in DBY0.
    unfold implM. iprefix.
    zstep. carve_frame 96%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 96 junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 9 zstep. do 4 zstep. zstep. if_cases KSZ; zify_cond KSZ.
    {
      assert (OUTR : zlength d < 10 \/ 1048576 < zlength d) by (pose proof (proj2 (size_test_zc (zlength d) ltac:(lia))) as ST'; lia).
      replace ((zlength d <? ZC_MIN) || (ZC_MAX <? zlength d)) with true by (symmetry; apply orb_true_iff; unfold ZC_MIN, ZC_MAX; destruct OUTR; [left; apply Z.ltb_lt| right; apply Z.ltb_lt]; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => destruct (OWN mx v1 v2 MU WM MI0 ST0 ZHC) as (ENV1 & PRES1 & POK1 & _) end.
      lazymatch type of FR with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?rest) => pose proof (frame_top24 mx _ c0 c1 c2 rest FR eq_refl eq_refl eq_refl) as FR24 end.
      cbn [cells_bytes cbytes app] in FR24.
      eapply evt_mono; [eapply fz_exit; [exact ENV1| exact FR24| exact PRES1| reflexivity| reflexivity| exact FRM| cbn; lia| exact POK1| exact SPB| exact LOSP0]|].
      intros ms' H'. apply impl_ret_ok. apply evt_done. exact H'. }
    assert (SZ : 10 <= zlength d <= 1048576) by (apply (proj1 (size_test_zc (zlength d) ltac:(lia))); lia).
    replace ((zlength d <? ZC_MIN) || (ZC_MAX <? zlength d)) with false by (symmetry; apply orb_false_iff; unfold ZC_MIN, ZC_MAX; split; apply Z.ltb_ge; lia).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (BY1 : bytes_at psegs m1 D (to_bytes d)).
    { eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact (unbox _ DBY0)|]. intros a Ha. rewrite LD in Ha. destruct (PAYR a Ha) as (P1 & P2 & _). cbn [outside]. lia. }
    apply box in BY1.
    pose proof (znth_byte d 0 DR ltac:(lia)) as RB0. pose proof (znth_byte d 1 DR ltac:(lia)) as RB1. pose proof (znth_byte d 2 DR ltac:(lia)) as RB2.
    set (c0 := Z_to_bv 8 (znth d 0)). set (c1 := Z_to_bv 8 (znth d 1)). set (c2 := Z_to_bv 8 (znth d 2)).
    assert (E0 : bv_unsigned c0 = znth d 0) by (apply unsigned8; exact RB0). assert (E1 : bv_unsigned c1 = znth d 1) by (apply unsigned8; exact RB1). assert (E2 : bv_unsigned c2 = znth d 2) by (apply unsigned8; exact RB2).
    pose proof (magic5_cells m1 ltac:(assumption)) as RO5. unfold A_MAGIC5 in RO5.

    pose proof (u8ro_read psegs m1 _ _ 1 c1 (wa (D + 1)) (unbox _ BY1) (to_bytes_nth d 1 ltac:(lia)) ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    do 6 zstep.
    fold (mod5_mach (bv_unsigned c1)). rewrite (mod5_mach_ok (bv_unsigned c1)) by lia. rewrite E1.

    lazymatch goal with |- evt _ ?Q _ =>
      assert (JOIN : forall r13' r14' : word,
        evt psegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (zlength d)) (Z_to_bv 64 4) r13' r14' a5 a6 a7
                             s2 s3 (Z_to_bv 64 (sel_cm d)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15f00) fc None m1 (seg_rom psegs)))
    end.
    2:{ zstep. zstep. if_cases KCM; zify_cond KCM; rewrite ?Z.mod_small in KCM by lia.
        - replace (znth d 1 mod 5) with (sel_cm d) by (unfold sel_cm; replace (znth d 1 mod 5 =? 4) with false by (symmetry; apply Z.eqb_neq; exact KCM); reflexivity). apply JOIN.
        - zstep. replace (Z_to_bv 64 8) with (Z_to_bv 64 (sel_cm d)) by (unfold sel_cm; rewrite KCM; reflexivity). apply JOIN. }
    intros r13' r14'.

    pose proof (u8ro_read psegs m1 _ _ 0 c0 (wa (D + 0)) (unbox _ BY1) (to_bytes_nth d 0 ltac:(lia)) ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    pose proof (u8ro_read psegs m1 _ _ 2 c2 (wa (D + 2)) (unbox _ BY1) (to_bytes_nth d 2 ltac:(lia)) ltac:(lia) eq_refl) as R2.
    zstep. clear R2. cbv beta.
    zstep. zstep. zstep. zstep.
    set (n := zlength d - 3) in *.
    replace (zlength d + -3) with n by lia.
    eapply evt_cut.
    { eapply CBND with (n := n); [lia| reflexivity| assumption]. }
    cbv beta. intros ms2 (u0 & u1 & u2 & b0' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & u3 & u4 & u5 & u6 & -> & CBV).
    replace (ret_pc (Z_to_bv 64 0x15f18)) with (Z_to_bv 64 0x15f18) by (symmetry; rpc).
    specialize (CBV ltac:(unfold ZH_MAX; lia)). subst b0'.
    set (cl := zc_bound zc n) in *. change (z_bound za n) with cl.
    pose proof (zo_boundC zc the_zapiC_ok n ltac:(unfold ZC_MAX; lia)) as CLF. fold cl in CLF. unfold ZBC_MAX, ZC_MAX in CLF.

    cbv beta delta [MallocRep.wz].
    do 3 zstep. zs. zs. do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    replace (zlength d + -3) with n in ZHC by lia.
    destruct (OWN m2 _ _ MU WM MI0 ST0 ZHC) as (ENV2 & PRES2 & POK2 & SOF2 & ADP2 & XCB2).
    assert (E96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
    assert (SPM : (bv_unsigned sp + -96) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    pose proof ENV2 as (HP2 & _ & _ & _ & _ & AUX2 & _ & _ & ST2 & _ & _ & ERR2 & _ & MI2). cbn [app] in HP2. rewrite E96 in ST2.
    assert (WLD2 : WLD sp LB D d n m s m2 s).
    { unfold WLD. split; [exact PRES2|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact POK2|].
      split; [unfold zhc_statics, ZH_STATICS; cbv beta delta [MallocRep.wz]; exact ZHC|]. split; [exact MRP|]. split; [exact SOF2|]. split; [exact ADP2| exact XCB2]. }
    clear PRES2 POK2 SOF2 ADP2 XCB2 MU WM.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s RP msx) end.
    eapply implM_bind.
    { eapply CALLOC with (s := s) (LB := LB) (n := cl) (lo := lo) (B := B) (errv := errv);
        rewrite ?E96; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
        [ exact HP2 | exact AUX2 | lia | exact ST2 | exact LOC | lia | exact ERR2 | exact MRP | exact MI2 | exact TP | reflexivity | reflexivity | lia ]. }
    cbv beta. intros r ss3 ms3 PO. unfold rcalloc_post in PO.
    destruct PO as (x0 & x1' & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & EFA3 & ESO3 & RES).
    replace (ret_pc (Z_to_bv 64 0x15f38)) with (Z_to_bv 64 0x15f38) by (symmetry; rpc).
    pose proof HPR3 as HPR3r. rewrite E96 in HPR3r.
    pose proof (WLD_heap sp LB D d n m s lo LB m2 m3 s ss3 PAYR WLD2 HPR3r ltac:(auto) ESO3 EFA3) as WLD3.
    pose proof (agree_of_heap_pres _ _ _ _ HPR3r) as AG3.
    assert (FR3 : rw_cells psegs m3 (bv_unsigned sp + -96) [CB 8 (take 8 junk); CB 8 (take 8 (drop 8 junk)); CB 8 (take 8 (drop 8 (drop 8 junk))); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact AG3| exact FR| intros a Ha; cbn in Ha; left; lia]. }
    clear FR.
    destruct r as [cp|].
    2:{
      destruct RES as [-> HP3].
      assert (ENV3 : lx_env m3 ss3 [] LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv3 canary) by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
      rewrite E96 in ST3.
      apply implM_ret.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
      zstep. zstep. if_true. zstep. zstep. zstep. zstep.
      eapply evt_cut; [eapply rfree_null_spec; reflexivity|]. cbv beta. intros ms4 ->.
      replace (ret_pc (Z_to_bv 64 0x1607c)) with (Z_to_bv 64 0x1607c) by (symmetry; rpc).
      zstep. zstep.
      eapply evt_cut; [eapply rfree_null_spec; reflexivity|]. cbv beta. intros ms5 ->.
      replace (ret_pc (Z_to_bv 64 0x16084)) with (Z_to_bv 64 0x16084) by (symmetry; rpc).
      destruct WLD3 as (PRES3 & ESO3' & EFA3' & POK3 & _).
      pose proof (frame_top24 m3 _ _ _ _ _ FR3 eq_refl eq_refl eq_refl) as FR24.
      eapply fz_exit; [exact ENV3| exact FR24| exact PRES3| exact ESO3'| exact EFA3'| exact FRM| cbn; lia| exact POK3| exact SPB| exact LOSP0]. }

    destruct RES as (C & -> & CR & HP3 & CZ3).
    pose proof CR as (C0 & _ & _ & CC & CI).
    assert (ENV3 : lx_env m3 ss3 [(cp, C, cl)] LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv3 canary) by (eapply lx_env_heap; [exact ENV2| exact HPR3| exact HP3| exact MI3| exact ST3| exact ERR3| exact AUX3]).
    destruct WLD3 as (PRES3 & ESO3' & EFA3' & POK3 & ZST3 & MRP3 & WREST3).
    rewrite E96 in ST3.

    unfold implM. iprefix.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep. zstep. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by lia; [exfalso; lia|]. do 3 zstep.
    clear MU WM.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss3 RP msx) end.
    eapply implM_bind.
    { eapply CALLOC with (s := ss3) (LB := (cp, C, cl) :: LB) (n := n) (lo := lo) (B := B) (errv := errv3);
        rewrite ?E96; unfold RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED;
        [ exact HP3 | exact AUX3 | lia | exact ST3 | exact LOC | lia | exact ERR3 | exact MRP3 | exact MI3 | exact TP | reflexivity | reflexivity | lia ]. }
    cbv beta. intros r ss4 ms4 PO. unfold rcalloc_post in PO.
    destruct PO as (y0 & y1 & y2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & RES).
    replace (ret_pc (Z_to_bv 64 0x15f4c)) with (Z_to_bv 64 0x15f4c) by (symmetry; rpc).
    pose proof HPR4 as HPR4r. rewrite E96 in HPR4r.
    pose proof (WLD_heap sp LB D d n m s lo ((cp, C, cl) :: LB) m3 m4 ss3 ss4 PAYR (conj PRES3 (conj ESO3' (conj EFA3' (conj POK3 (conj ZST3 (conj MRP3 WREST3)))))) HPR4r ltac:(intros b Hb; right; exact Hb) ESO4 EFA4) as WLD4.
    assert (HPR4' : rheap_pres LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) m3 m4) by (rewrite E96; eapply rheap_pres_weaken; [exact HPR4r| lia| intros b Hb; right; exact Hb]).
    pose proof (agree_of_heap_pres _ _ _ _ HPR4r) as AG4.
    lazymatch type of FR3 with rw_cells _ _ _ ?cells => assert (FR4 : rw_cells psegs m4 (bv_unsigned sp + -96) cells) by (eapply rw_cells_agree; [exact AG4| exact FR3| intros a Ha; cbn in Ha; left; lia]) end.
    assert (CZ4 : rw_cells psegs m4 C [CB (Z.to_nat cl) (zeros (Z.to_nat cl))]).
    { eapply rw_cells_agree; [exact AG4| exact CZ3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia.
      right; right. exists (cp, C, cl). split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]. }
    clear FR3 CZ3 AG3 AG4.
    destruct r as [up|].
    2:{
      destruct RES as [-> HP4].
      assert (ENV4 : lx_env m4 ss4 [(cp, C, cl)] LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv4 canary) by (eapply lx_env_heap; [exact ENV3| exact HPR4'| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]).
      rewrite E96 in ST4.
      cbn [Target.lib_free_opt].
      unfold implM. iprefix.
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl psegs m4) as WM.
      zstep. if_true. zstep. zstep. zstep. zstep.
      clear MU WM. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss4 RP msx) end.
      eapply implM_bind.
      { eapply FREE with (s := ss4) (LB := (cp, C, cl) :: LB) (p := cp) (A := C) (n := cl) (lo := lo) (B := B) (errv := errv4);
          rewrite ?E96; unfold RFREE_STACK;
          [ exact HP4 | left; reflexivity | exact AUX4 | lia | exact ST4 | exact LOC | lia | exact ERR4 | exact MI4 | exact TP | reflexivity ]. }
      cbv beta. intros [] ss5 ms5 PO.
      destruct PO as (n0 & n1 & n2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & n3 & n4 & n5 & n6 & m5 & -> & MI5 & ST5 & ERR5 & AUX5 & HPR5 & EFA5 & ESO5 & HP5).
      replace (ret_pc (Z_to_bv 64 0x1607c)) with (Z_to_bv 64 0x1607c) by (symmetry; rpc).
      rewrite (lb_remove_head cp C cl _ (HND _ _ _ HP4)) in HPR5, HP5.
      pose proof HPR5 as HPR5r. rewrite E96 in HPR5r.
      pose proof (WLD_heap sp LB D d n m s lo LB m4 m5 ss4 ss5 PAYR WLD4 HPR5r ltac:(auto) ESO5 EFA5) as WLD5.
      assert (ENV5 : lx_env m5 ss5 [] LB (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv4 canary).
      { eapply (lx_env_heap m4 m5 ss4 ss5); [exact ENV4| exact HPR5| exact HP5| exact MI5| exact ST5| exact ERR5| exact AUX5]. }
      lazymatch type of FR4 with rw_cells _ _ _ ?cells => assert (FR5 : rw_cells psegs m5 (bv_unsigned sp + -96) cells) by (eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HPR5r)| exact FR4| intros a Ha; cbn in Ha; left; lia]) end.
      rewrite E96 in ST5.
      apply implM_ret.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl psegs m5) as WM.
      zstep. zstep.
      eapply evt_cut; [eapply rfree_null_spec; reflexivity|]. cbv beta. intros ms6 ->.
      replace (ret_pc (Z_to_bv 64 0x16084)) with (Z_to_bv 64 0x16084) by (symmetry; rpc).
      destruct WLD5 as (PRES5 & ESO5' & EFA5' & POK5 & _).
      pose proof (frame_top24 m5 _ _ _ _ _ FR5 eq_refl eq_refl eq_refl) as FR24.
      eapply fz_exit; [exact ENV5| exact FR24| exact PRES5| exact ESO5'| exact EFA5'| exact FRM| cbn; lia| exact POK5| exact SPB| exact LOSP0]. }

    destruct RES as (U & -> & UR & HP4 & UZ4).
    pose proof UR as (U0 & _ & _ & UC & UI).
    set (LB' := (up, U, n) :: (cp, C, cl) :: LB) in *.
    assert (ENV4 : lx_env m4 ss4 [] LB' (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv4 canary).
    { eapply lx_env_blocks; [eapply (lx_env_heap m3 m4 ss3 ss4 _ [(up, U, n); (cp, C, cl)] LB); [exact ENV3| exact HPR4'| exact HP4| exact MI4| exact ST4| exact ERR4| exact AUX4]| exact HP4]. }
    rewrite E96 in ST4.

    assert (NEQ : cp <> up).
    { pose proof (HND _ _ _ HP4) as ND. cbn [map blk_id fst] in ND. inversion ND as [|? ? NI _]; subst. intros E. apply NI. left. exact E. }
    assert (SEPC : forall b, In b LB -> blk_addr b + blk_size b <= C \/ C + cl <= blk_addr b).
    { intros b Hb. pose proof (heap_sep ss3 [(cp, C, cl)] LB m3 (cp, C, cl) b HND HBD HP3 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
    assert (SEPU : forall b, In b ((cp, C, cl) :: LB) -> blk_addr b + blk_size b <= U \/ U + n <= blk_addr b).
    { intros b Hb. pose proof (heap_sep ss4 [(up, U, n)] ((cp, C, cl) :: LB) m4 (up, U, n) b HND HBD HP4 ltac:(left; reflexivity) Hb) as X. cbn [blk_addr blk_size fst snd] in X. lia. }
    assert (DC : D + zlength d <= C \/ C + cl <= D).
    { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPC bd Hbd). pose proof (LBR _ Hbd) as (_ & _ & BS & _). lia. }
    assert (DU : D + zlength d <= U \/ U + n <= D).
    { destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia|]. pose proof (SEPU bd ltac:(right; exact Hbd)). pose proof (LBR _ Hbd) as (_ & _ & BS & _). lia. }
    assert (CU : U + n <= C \/ C + cl <= U) by (pose proof (SEPU (cp, C, cl) ltac:(left; reflexivity)) as X; cbn [blk_addr blk_size fst snd] in X; lia).
    pose proof (box _ WLD4) as WLD4b.
    destruct WLD4 as (PRES4 & ESO4' & EFA4' & POK4 & ZST4 & MRP4 & WREST4). unfold zhc_statics, ZH_STATICS in ZST4. cbv beta delta [MallocRep.wz] in ZST4.

    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    apply box in CZ4. apply box in UZ4.
    unfold implM. iprefix.
    zstep. if_cases KU; zify_cond KU; rewrite ?unsigned_lit in KU by lia; [exfalso; lia|].
    zstep. do 6 zstep.
    fold (mod10_mach (bv_unsigned c0)). rewrite (mod10_mach_ok (bv_unsigned c0)) by lia. rewrite E0.
    rewrite (swrap32_id' (znth d 0 mod 10)) by lia.
    zstep. zstep. zs. zstep. zs. zstep. zstep. zstep.
    rewrite (land255_small (znth d 0 mod 10)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4' end.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG4'.
    destruct (frame_split4 m4' _ _ _ _ _ FR4 eq_refl eq_refl) as (FRJ4 & ULC4 & CLC4 & FRH4). clear FR4.
    assert (ENV4' : lx_env m4' ss4 [] LB' (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv4 canary).
    { eapply (lx_env_munch [(bv_unsigned sp + -96, bv_unsigned sp)] m4 m4'); [exact HFRAME| exact ENV4| exact MU| exact WM| assumption| rewrite E96; assumption| rewrite E96; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. clear - Ha SPB LOG LOSP RSP. lia. }
    assert (WLD4' : WLD sp LB D d n m s m4' ss4).
    { eapply (WLD_munch sp LB D d n m s lo _ m4 m4' ss4 PAYR); [| exact MU| exact WM| | unfold zhc_statics, ZH_STATICS; cbv beta delta [MallocRep.wz]; exact ZST4].
      - exact (unbox _ WLD4b).
      - intros a Ha. cbn [outside]. split; [| exact I]. destruct Ha as [Ha|[(b & Hb & Hr)|[Ha _]]]; [lia| destruct (LBR b Hb) as (_ & _ & _ & BC & _); lia| lia]. }
    assert (CZ4' : u8arr psegs m4' C (to_bytes (zrepeat 0 cl))).
    { rewrite to_bytes_zrepeat0. apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat cl)). eapply rw_cells_agree; [exact AG4'| exact (unbox _ CZ4)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. cbn [outside]. lia. }
    assert (UZ4' : u8arr psegs m4' U (to_bytes (zrepeat 0 n))).
    { rewrite to_bytes_zrepeat0. apply (u8arr_of_rw_cells psegs _ _ (Z.to_nat n)). eapply rw_cells_agree; [exact AG4'| exact (unbox _ UZ4)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. cbn [outside]. lia. }
    pose proof (box _ WLD4') as WLD4'b.
    destruct WLD4' as (PRES4' & _ & _ & POK4' & WR4'). pose proof POK4' as (DBY4 & _).
    assert (SRC4 : bytes_at psegs m4' (D + 3) (to_bytes (zdrop 3 d))).
    { unfold zdrop. rewrite to_bytes_skipn. pose proof DBY4 as X. rewrite <- (firstn_skipn 3 (to_bytes d)) in X. apply bytes_at_app in X. destruct X as [_ X].
      rewrite length_firstn, to_bytes_len, Nat.min_l in X by (unfold zlength in *; lia). exact X. }
    clear MU WM AG4' CZ4 UZ4.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss4 RP msx) end.
    eapply implM_bind.
    { eapply C2 with (s := ss4) (LB := LB') (cp := cp) (C := C) (cl := cl) (PL := bv_unsigned sp + -96 + 16) (NI := D + 3) (n := n) (lv := sel_level d)
                     (oldc := zrepeat 0 cl) (src := zdrop 3 d) (lo := lo) (B := B) (errv := errv4) (canary := canary);
        rewrite ?E96; unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, ZC_MIN, ZC_MAX;
        [ nm 1 ltac:(exact ENV4') | nm 2 ltac:(right; left; reflexivity) | nm 3 ltac:(exact CZ4') | nm 4 ltac:(unfold zrepeat, zlength; rewrite repeat_length; lia)
        | nm 5 ltac:(exact CLC4) | nm 6 ltac:(lia) | nm 7 ltac:(lia) | nm 8 ltac:(clear - SP16 RSP; Z.div_mod_to_equations; lia)
        | nm 9 ltac:(exact SRC4) | nm 10 ltac:(unfold zdrop; apply Forall_skipn_; exact DR) | nm 11 ltac:(unfold zdrop, zlength in *; rewrite length_skipn; lia)
        | nm 12 ltac:(destruct PIN0 as [EP|(bd & Hbd & B1 & B2)]; [exfalso; rewrite EP in SZ; unfold zlength in SZ; cbn in SZ; lia| exists bd; split; [right; right; exact Hbd| lia]])
        | nm 13 ltac:(lia) | nm 14 ltac:(lia) | nm 15 ltac:(reflexivity) | nm 16 ltac:(apply sel_level_range)
        | nm 17 ltac:(lia) | nm 18 ltac:(exact SPM) | nm 19 ltac:(exact FRM)
        | nm 20 ltac:(reflexivity) | nm 21 ltac:(unfold MallocRep.wz; f_equal; lia) | nm 22 ltac:(reflexivity) | nm 23 ltac:(reflexivity) | nm 24 ltac:(unfold sel_level; reflexivity) ]. }
    cbv beta. intros [[cout clen] crc] ss5 ms5 PO. unfold rcompress2_post in PO. cbn [fst snd] in PO.
    destruct PO as (z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & F5 & fc5 & m5 & rc5 & -> & ((errv5 & ENV5) & FRM5 & LXP5 & ESO5 & EFA5) & -> & -> & RCR5 & CARR5 & ECL & LCL & CF & CLC5).
    replace (ret_pc (Z_to_bv 64 0x15f8c)) with (Z_to_bv 64 0x15f8c) by (symmetry; rpc).
    rewrite E96 in LXP5.
    assert (HL' : forall b, In b LB -> In b LB') by (intros b Hb; right; right; exact Hb).
    assert (WLD5 : WLD sp LB D d n m s m5 ss5).
    { eapply (WLD_lx sp LB D d n m s lo LB' _ C cl m4' m5 ss4 ss5 PAYR LBR LOC ltac:(lia) ltac:(lia) (unbox _ WLD4'b) LXP5 HL');
        [ intros a Ha; cbn [rin_ivs fst snd] in Ha; lia | exact SEPC | exact CI | exact CC | exact ESO5 | exact EFA5 ]. }
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP5) as AG5.
    assert (NX5 : forall a, bv_unsigned sp + -96 <= a -> ~ (bv_unsigned sp + -96 + 16 <= a < bv_unsigned sp + -96 + 24) -> lx_client LB' (bv_unsigned sp + -96) [(C, C + cl); (bv_unsigned sp + -96 + 16, bv_unsigned sp + -96 + 16 + 8)] a).
    { intros a Ha Hn. apply stack_client; [exact Ha|]. cbn [rin_ivs fst snd]. lia. }
    assert (FRJ5 : rw_cells psegs m5 (bv_unsigned sp + -96) [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG5| exact FRJ4| intros a Ha; cbn in Ha; apply NX5; lia]).
    assert (ULC5 : rw_cells psegs m5 (bv_unsigned sp + -96 + 8) [C8 (Z_to_bv 64 n)]) by (eapply rw_cells_agree; [exact AG5| exact ULC4| intros a Ha; cbn in Ha; apply NX5; lia]).
    assert (FRH5 : rw_cells psegs m5 (bv_unsigned sp + -96 + 24) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree; [exact AG5| exact FRH4| intros a Ha; cbn in Ha; apply NX5; lia]).
    assert (UZ5 : u8arr psegs m5 U (to_bytes (zrepeat 0 n))).
    { eapply u8arr_agree; [exact AG5| exact UZ4'|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zrepeat in Ha. rewrite repeat_length, Z2Nat.id in Ha by lia.
      eapply block_client; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia|]. cbn [rin_ivs fst snd]. lia. }
    clear AG5 NX5 FRJ4 ULC4 FRH4 UZ4' CZ4' SRC4 CLC4.
    pose proof ENV5 as (HP5 & _ & _ & _ & _ & _ & _ & _ & ST5 & _ & _ & _ & _ & MI5). rewrite E96 in ST5.
    assert (ZL0 : 0 <= zlength cout) by (unfold zlength; lia).
    assert (CST : zstore (zrepeat 0 cl) 0 cout = cout ++ skipn (length cout) (zrepeat 0 cl)) by (apply zstore0_app; unfold zrepeat; rewrite repeat_length; unfold zlength in *; lia).

    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    cbv beta delta [MallocRep.wz] in CLC5. replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in CLC5 by (clear; lia).
    replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in ULC5 by (clear; lia). replace (bv_unsigned sp + -96 + 24) with (bv_unsigned sp + -72) in FRH5 by (clear; lia).
    unfold runcompress_stmt in UNC.
    pose proof (fz_wint_cases crc RCR5) as WC5.
    pose proof WLD5 as (_ & _ & _ & _ & ZST5 & _). unfold zhc_statics, ZH_STATICS in ZST5. cbv beta delta [MallocRep.wz] in ZST5.
    unfold implM. iprefix. zstep. zstep. if_cases KM5; zify_cond KM5.
    2:{
      (* oss-fuzz #16582: compress2 returned Z_MEM_ERROR (bne a0,s7 not taken): ld s3,8(s6) (s3 = n), then j to the
         check_decompress block, as the model does. *)
      assert (CRC5 : crc = -4) by fz_rc_m4 KM5 WC5.
      lazymatch goal with |- context [crc =? ?e] =>
        replace (crc =? e) with true by (symmetry; apply Z.eqb_eq; rewrite CRC5; vm_compute; reflexivity) end.
      zstep. zstep. clear MU WM.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss5 RP msx) end.
      cbn [negb]. rewrite ?E2.
      eapply fz_decomp with (m0 := m) (s0 := s) (mm := m5) (ss := ss5) (cout := cout) (n := n) (cl := cl);
        first [ exact ENV5 | exact WLD5 | exact FRM5 | exact FRJ5 | exact ULC5 | exact CLC5 | exact FRH5 | exact CARR5 | exact CF
              | exact SZ | exact DR | exact PAYR | exact LBR
              | exact CR | exact UR | exact NEQ | exact SEPC | exact SEPU | exact DC | exact LOC | exact LOSP0 | exact SPB | exact B63 | exact TP | exact SP16
              | reflexivity | apply zc_bound_mono; lia | lia ]. }
    assert (CRN5 : crc <> -4) by fz_rc_n4 KM5.
    lazymatch goal with |- context [crc =? ?e] =>
      replace (crc =? e) with false by (symmetry; apply Z.eqb_neq; intros CE; apply CRN5; rewrite CE; vm_compute; reflexivity) end.
    cbn [negb].
    do 5 zstep. clear MU WM.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss5 RP msx) end.
    rewrite (norm8_id cout CF).
    eapply implM_bind.
    { eapply UNC with (s := ss5) (LB := LB') (up := up) (cpS := cp) (U := U) (dlen := n) (PL := bv_unsigned sp + -88) (C := C) (cl := cl) (slen := clen)
                      (uc := zrepeat 0 n) (comprc := zstore (zrepeat 0 cl) 0 cout) (src := cout) (lo := lo) (B := B) (errv := errv5) (canary := canary);
        rewrite ?E96; unfold ZC_UNC_STACK, ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, ZC_MAX;
        [ nm 1 ltac:(exact ENV5) | nm 2 ltac:(left; reflexivity) | nm 3 ltac:(exact UZ5) | nm 4 ltac:(unfold zrepeat, zlength; rewrite repeat_length; lia)
        | nm 5 ltac:(exact ULC5) | nm 6 ltac:(lia) | nm 7 ltac:(lia) | nm 8 ltac:(clear - SP16 RSP; Z.div_mod_to_equations; lia)
        | nm 9 ltac:(right; left; reflexivity) | nm 10 ltac:(exact CARR5) | nm 11 ltac:(rewrite zstore_length; unfold zrepeat, zlength; rewrite repeat_length; lia)
        | nm 12 ltac:(rewrite CST; apply Forall_app; split; [exact CF| apply Forall_skipn_; unfold zrepeat; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia])
        | nm 13 ltac:(lia)
        | nm 14 ltac:(rewrite CST; unfold ztake; rewrite ECL; unfold zlength; rewrite Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity)
        | nm 15 ltac:(intros E; apply NEQ; symmetry; exact E)
        | nm 16 ltac:(pose proof (zo_boundC zc the_zapiC_ok (1048576 - 3) ltac:(unfold ZC_MAX; lia)); lia)
        | nm 17 ltac:(apply zc_bound_mono; lia)
        | nm 18 ltac:(lia) | nm 19 ltac:(exact SPM) | nm 20 ltac:(exact FRM5)
        | nm 21 ltac:(reflexivity) | nm 22 ltac:(unfold MallocRep.wz; f_equal; lia) | nm 23 ltac:(reflexivity) | nm 24 ltac:(reflexivity) ]. }
    cbv beta. intros [[uout ulen] urc] ss6 ms6 PO. unfold runcompress_post in PO. cbn [fst snd] in PO.
    destruct PO as (k0 & k1 & k2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & k3 & k4 & k5 & k6 & F6 & fc6 & m6 & rc6 & -> & ((errv6 & ENV6) & FRM6 & LXP6 & ESO6 & EFA6) & -> & -> & RCR6 & UARR6 & LUL & UL64 & ULC6).
    replace (ret_pc (Z_to_bv 64 0x15fb8)) with (Z_to_bv 64 0x15fb8) by (symmetry; rpc).
    rewrite E96 in LXP6.
    assert (WLD6 : WLD sp LB D d n m s m6 ss6).
    { eapply (WLD_lx sp LB D d n m s lo LB' _ U n m5 m6 ss5 ss6 PAYR LBR LOC ltac:(lia) ltac:(lia) WLD5 LXP6 HL');
        [ intros a Ha; cbn [rin_ivs fst snd] in Ha; lia | intros b Hb; apply SEPU; right; exact Hb | exact UI | exact UC | exact ESO6 | exact EFA6 ]. }
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP6) as AG6.
    assert (NX6 : forall a, bv_unsigned sp + -96 <= a -> ~ (bv_unsigned sp + -88 <= a < bv_unsigned sp + -80) -> lx_client LB' (bv_unsigned sp + -96) [(U, U + n); (bv_unsigned sp + -88, bv_unsigned sp + -88 + 8)] a).
    { intros a Ha Hn. apply stack_client; [exact Ha|]. cbn [rin_ivs fst snd]. lia. }
    assert (FRJ6 : rw_cells psegs m6 (bv_unsigned sp + -96) [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG6| exact FRJ5| intros a Ha; cbn in Ha; apply NX6; lia]).
    assert (CLC6 : rw_cells psegs m6 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 clen)]) by (eapply rw_cells_agree; [exact AG6| exact CLC5| intros a Ha; cbn in Ha; apply NX6; lia]).
    assert (FRH6 : rw_cells psegs m6 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree; [exact AG6| exact FRH5| intros a Ha; cbn in Ha; apply NX6; lia]).
    assert (LCC : Z.of_nat (length (to_bytes (zstore (zrepeat 0 cl) 0 cout))) = cl) by (rewrite to_bytes_len; pose proof (zstore_length cout (zrepeat 0 cl) 0) as X; unfold zlength in X; unfold zrepeat in *; rewrite repeat_length in X; lia).
    assert (CARR6 : u8arr psegs m6 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))).
    { eapply u8arr_agree; [exact AG6| exact CARR5|]. intros a Ha. rewrite LCC in Ha.
      eapply block_client; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia|]. cbn [rin_ivs fst snd]. lia. }
    clear AG6 NX6 FRJ5 CLC5 FRH5 CARR5 UZ5.
    pose proof ENV6 as (HP6 & LXS6 & ZLS6 & SEW6 & SSP6 & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E96 in ST6.
    pose proof (box _ WLD6) as WLD6b.
    destruct WLD6 as (PRES6 & ESO6' & EFA6' & POK6 & ZST6 & MRP6 & SOF6 & ADP6 & XCB6). unfold zhc_statics, ZH_STATICS in ZST6. cbv beta delta [MallocRep.wz] in ZST6.
    cbv beta delta [MallocRep.wz] in ULC6.
    assert (LUC : Z.of_nat (length (to_bytes (zstore (zrepeat 0 n) 0 uout))) = n) by (rewrite to_bytes_len; pose proof (zstore_length uout (zrepeat 0 n) 0) as X; unfold zlength in X; unfold zrepeat in *; rewrite repeat_length in X; lia).
    assert (LND : Z.of_nat (length (to_bytes (zdrop 3 d))) = n) by (rewrite to_bytes_len; unfold zdrop; rewrite length_skipn; unfold zlength in *; lia).

    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl psegs m6) as WM.
    pose proof (fz_wint_cases urc RCR6) as WC6.
    unfold implM. iprefix. zstep. zstep. if_cases KM6; zify_cond KM6.
    {
      (* oss-fuzz #16582: uncompress returned Z_MEM_ERROR (beq a0,s7 taken; s3 = n was loaded just before): the
         check_decompress block, as the model does. *)
      assert (URC6 : urc = -4) by fz_rc_m4 KM6 WC6.
      lazymatch goal with |- context [urc =? ?e] =>
        replace (urc =? e) with true by (symmetry; apply Z.eqb_eq; rewrite URC6; vm_compute; reflexivity) end.
      clear MU WM.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
      cbn [negb]. rewrite ?E2.
      eapply fz_decomp with (m0 := m) (s0 := s) (mm := m6) (ss := ss6) (cout := cout) (n := n) (cl := cl);
        first [ exact ENV6 | exact (unbox _ WLD6b) | exact FRM6 | exact FRJ6 | exact ULC6 | exact CLC6 | exact FRH6 | exact CARR6 | exact CF
              | exact SZ | exact DR | exact PAYR | exact LBR
              | exact CR | exact UR | exact NEQ | exact SEPC | exact SEPU | exact DC | exact LOC | exact LOSP0 | exact SPB | exact B63 | exact TP | exact SP16
              | reflexivity | apply zc_bound_mono; lia | lia ]. }
    assert (URN6 : urc <> -4) by fz_rc_n4 KM6.
    lazymatch goal with |- context [urc =? ?e] =>
      replace (urc =? e) with false by (symmetry; apply Z.eqb_neq; intros CE; apply URN6; rewrite CE; vm_compute; reflexivity) end.
    cbn [negb].
    zstep. zstep.
    if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by lia.
    {
      replace (n =? ulen) with false by (symmetry; apply Z.eqb_neq; exact KQ). cbn [negb].
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
      apply fz_check. }
    replace (n =? ulen) with true by (symmetry; apply Z.eqb_eq; exact KQ). cbn [negb].

    do 4 zstep. clear MU WM.
    rewrite <- LND.
    eapply evt_cut.
    { eapply (bcmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m6 (D + 3) U (to_bytes (zdrop 3 d)) (to_bytes (zstore (zrepeat 0 (Z.of_nat (length (to_bytes (zdrop 3 d))))) 0 uout)));
        rewrite ?LND; [ | destruct UARR6 as [X _]; exact X | rewrite !to_bytes_len in *; unfold zlength in *; lia | lia | lia | lia | lia | exact MI6 ].
      pose proof POK6 as (DBY6 & _). unfold zdrop. rewrite to_bytes_skipn. pose proof DBY6 as X. rewrite <- (firstn_skipn 3 (to_bytes d)) in X. apply bytes_at_app in X. destruct X as [_ X].
      rewrite length_firstn, to_bytes_len, Nat.min_l in X by (unfold zlength in *; lia). exact X. }
    cbv beta. rewrite !LND. intros ms7 (w0 & w1 & w2 & e0' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & w3 & w4 & w5 & w6 & m7 & -> & MU7 & WM7 & MI7 & CMP).
    replace (ret_pc (Z_to_bv 64 0x15fd8)) with (Z_to_bv 64 0x15fd8) by (symmetry; rpc).

    pose proof (agree_on_of_munch _ _ _ MU7 WM7) as AG7.
    assert (ENV7 : lx_env m7 ss6 [] LB' (Z_to_bv 64 (bv_unsigned sp + -96)) tp B lo errv6 canary).
    { eapply (lx_env_munch [] m6 m7); [exact HFRAME| exact ENV6| exact MU7| exact WM7| exact MI7| rewrite E96; eapply stk_agree; [exact AG7| exact ST6| intros a Ha; exact I]| rewrite E96; lia| constructor| intros a Ha; exact I]. }
    assert (FRJ7 : rw_cells psegs m7 (bv_unsigned sp + -96) [CB 8 (take 8 junk)]) by (eapply rw_cells_agree; [exact AG7| exact FRJ6| intros a Ha; exact I]).
    assert (ULC7 : rw_cells psegs m7 (bv_unsigned sp + -88) [C8 (Z_to_bv 64 ulen)]) by (eapply rw_cells_agree; [exact AG7| exact ULC6| intros a Ha; exact I]).
    assert (CLC7 : rw_cells psegs m7 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 clen)]) by (eapply rw_cells_agree; [exact AG7| exact CLC6| intros a Ha; exact I]).
    assert (FRH7 : rw_cells psegs m7 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree; [exact AG7| exact FRH6| intros a Ha; exact I]).
    assert (CARR7 : u8arr psegs m7 C (to_bytes (zstore (zrepeat 0 cl) 0 cout))) by (eapply u8arr_agree; [exact AG7| exact CARR6| intros a Ha; exact I]).
    assert (ZST7 : rw_cells psegs m7 239648 [C8 (Z_to_bv 64 (D + 3)); C8 (Z_to_bv 64 n)]) by (eapply rw_cells_agree; [exact AG7| exact ZST6| intros a Ha; exact I]).
    assert (WLD7 : WLD sp LB D d n m s m7 ss6).
    { eapply (WLD_munch sp LB D d n m s lo _ m6 m7 ss6 PAYR (unbox _ WLD6b) MU7 WM7); [intros a Ha; exact I| unfold zhc_statics, ZH_STATICS; cbv beta delta [MallocRep.wz]; exact ZST7]. }
    pose proof ENV7 as (HP7 & _ & _ & _ & _ & AUX7 & _ & _ & ST7 & _ & _ & ERR7 & _ & _). rewrite E96 in ST7. cbn [app] in HP7.
    clear AG7 FRJ6 ULC6 CLC6 FRH6 CARR6 ZST6 UARR6 HP6 LXS6 ZLS6 SEW6 SSP6 ST6 MI6.

    assert (EQV : to_bytes (zdrop 3 d) = to_bytes (zstore (zrepeat 0 n) 0 uout) <-> zlist_eqb (zdrop 3 d) (norm8 (bufC uout n)) = true).
    { rewrite zlist_eqb_eq, to_bytes_eq_norm8, (norm8_id (zdrop 3 d)) by (unfold zdrop; apply Forall_skipn_; exact DR).
      rewrite (bufC_store uout n) by lia. split; intros HH; exact HH. }

    pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl psegs m7) as WM.
    zstep. if_cases KNE; zify_cond KNE.
    {
      assert (NEQL : to_bytes (zdrop 3 d) <> to_bytes (zstore (zrepeat 0 n) 0 uout)).
      { destruct CMP as [[E ->]|[NE _]]; [exfalso; apply KNE; unfold MallocRep.wz; rewrite unsigned_lit by lia; reflexivity| exact NE]. }
      replace (zlist_eqb (zdrop 3 d) (norm8 (bufC uout n))) with false.
      2:{ symmetry. destruct (zlist_eqb (zdrop 3 d) (norm8 (bufC uout n))) eqn:EZ; [| reflexivity]. exfalso. apply NEQL. apply (proj2 EQV). reflexivity. }
      cbn [negb]. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
      apply fz_check. }
    assert (EQL : to_bytes (zdrop 3 d) = to_bytes (zstore (zrepeat 0 n) 0 uout)).
    { destruct CMP as [[E _]|[NE HNZ]]; [exact E| exfalso; apply HNZ; exact KNE]. }
    replace (zlist_eqb (zdrop 3 d) (norm8 (bufC uout n))) with true by (symmetry; apply EQV; exact EQL). cbn [negb].
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm ss6 RP msx) end.
    rewrite E2.
    eapply fz_decomp with (m0 := m) (s0 := s) (mm := m7) (ss := ss6) (cout := cout) (n := n) (cl := cl);
      first [ exact ENV7 | exact WLD7 | exact FRM6 | exact FRJ7 | exact ULC7 | exact CLC7 | exact FRH7 | exact CARR7 | exact CF | exact SZ | exact DR | exact PAYR | exact LBR
            | exact CR | exact UR | exact NEQ | exact SEPC | exact SEPU | exact DC | exact LOC | exact LOSP0 | exact SPB | exact B63 | exact TP | exact SP16
            | reflexivity | apply zc_bound_mono; lia | lia ].
  Qed.
End FZ.
End WithCeiling0.
