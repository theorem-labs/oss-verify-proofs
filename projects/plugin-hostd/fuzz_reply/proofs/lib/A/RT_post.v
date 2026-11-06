(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the one piece of the Bz -> W_sites bridge that every runtime lane needs,
   `aentry_post_of_walk`: a Bz interceptor/intrinsic walk that ends at the return address with a0 = r, whose only
   memory change is the stack window [sp - D, sp) and a list WR of written ranges, read back as W_sites.v's
   `aentry_post`.  Written here (R3Mem) by agreement with R1Str so that RT_kit.v imports it rather than restating it;
   it is FSstrlen.v's post_of_walk (a working branch 3210d71ee38, a Theorem Labs lane, itself a Theorem Labs lane's) with
   three changes: the pre is `ecall_pre` (no POISON-U), the post is W_sites' aentry_post at PI := PB_fr, and the
   written set WR / the result predicate Pr are parameters, so one lemma serves the read-only interceptors
   (WR := []) and the intrinsics (WR := [(d, d + n)]).
   The image facts (FR_IMG_TOP, cj_keep_high, mrd_high) are FSstrlen.v:97-147, 444-449 at fuzz_reply's image end;
   0x600000 is a valid ceiling for fuzz_reply.asan too (its last segment ends at 0x5fb000). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_tbl W_place W_pl W_img W_kit W_sites.
(* the ARx-generic twins (fuzz_reply.runtime_twins): the laws rt_laws and the post aentry_post_x *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_sites_x.
(* FCiface Requires YF0v, which sets Zify's euclidean-division flag to false globally; the header above ended with it
   true (W_sites' chain), and this file's importers (RT_strlen's lia) need that value: restore it. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.RegisterBridge.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRsl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_str.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module LM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.
Module L6 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Img0.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module LE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Exec.
Module LR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.RegisterBridge.
Module SL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRsl.
Module FRS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FRbz_str.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.D_kit.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_qck.
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_consts.
Module BE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.

(* the three trees name the same image *)
Lemma asegs_frsegs : BI.asegs = frsegs. Proof. reflexivity. Qed.
Lemma rsegs_frsegs : I0.rsegs = frsegs. Proof. reflexivity. Qed.

(* ---- the image: every loaded segment of fuzz_reply.asan ends below 0x600000 ---- *)
Definition FR_IMG_TOP : Z := 0x600000.
Definition seg_tops_below (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.
Lemma rsegs_below : seg_tops_below I0.rsegs FR_IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall segs top x n s,
  seg_tops_below segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma find_segment_high : forall x, FR_IMG_TOP <= x -> find_segment I0.rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment I0.rsegs x 1) as [s|] eqn:E; [|reflexivity].
  destruct (find_segment_below I0.rsegs FR_IMG_TOP x 1 s rsegs_below E ltac:(lia)) as [L|L]; lia.
Qed.

(* an address above the image and below TASK_SIZE keeps its byte in the normalized memory *)
Lemma cj_keep_high : forall x, FR_IMG_TOP <= x < TASK_SIZE -> NM.cj_drop I0.rsegs (Z_to_bv 64 x) = false.
Proof.
  intros x Hx. unfold TASK_SIZE, FR_IMG_TOP in Hx.
  assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by (apply BMS.unsigned_lit; lia).
  apply NM.cj_drop_false_intro.
  - unfold LM.ro_addr. rewrite Ex, (find_segment_high x ltac:(unfold FR_IMG_TOP; lia)). reflexivity.
  - right. rewrite Ex. unfold TASK_SIZE. lia.
Qed.

(* an address above the image reads only what the memory holds *)
Lemma mrd_high : forall m (a : word), FR_IMG_TOP <= bv_unsigned a -> BM.mrd BI.asegs m a = m a.
Proof.
  intros m a Ha. unfold BM.mrd. destruct (m a); [reflexivity|].
  match goal with |- ?f _ _ = None => unfold f end. unfold memory_read.
  change (Z.of_N 1) with 1. change BI.asegs with I0.rsegs.
  rewrite (find_segment_high (bv_unsigned a) Ha). reflexivity.
Qed.

(* ---- the written set: a decidable list of ranges ---- *)
Definition in_ivls (WR : list (Z * Z)) (a : Z) : Prop := Exists (fun iv => fst iv <= a < snd iv) WR.

Lemma outside_not_in_ivls : forall WR a, ~ in_ivls WR a -> BF.outside WR a.
Proof.
  induction WR as [|[lo hi] WR IH]; intros a Hn; [exact I|].
  cbn [BF.outside]. split.
  - intros Hr. apply Hn. apply Exists_cons_hd. cbn [fst snd]. exact Hr.
  - apply IH. intros Hex. apply Hn. apply Exists_cons_tl. exact Hex.
Qed.

Lemma outside_or_in : forall WR a, BF.outside WR a \/ in_ivls WR a.
Proof.
  induction WR as [|[lo hi] WR IH]; intros a; [left; exact I|].
  destruct (IH a) as [Ho|Hex]; [|right; apply Exists_cons_tl; exact Hex].
  destruct (Z_lt_le_dec a lo) as [L|L].
  - left. cbn [BF.outside]. split; [cbn [fst snd]; lia | exact Ho].
  - destruct (Z_lt_le_dec a hi) as [L2|L2].
    + right. apply Exists_cons_hd. cbn [fst snd]. lia.
    + left. cbn [BF.outside]. split; [cbn [fst snd]; lia | exact Ho].
Qed.

(* ---- registers ---- *)
Lemma getr_nz : forall regs (r : bv 5), bv_eqb r 0 = false -> YK11.getr regs r = reg_get regs r.
Proof. intros regs r H. unfold YK11.getr. rewrite H. reflexivity. Qed.

(* lib/Prog/CF/WriterCall.v:19-35, unchanged but for the Bz tree's ret_pc *)
Lemma land_m2_mod : forall u, Z.land u (-2) mod 2 = 0.
Proof.
  intros u. replace (Z.land u (-2)) with (Z.shiftl (Z.shiftr u 1) 1).
  - rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. apply Z.mod_mul. lia.
  - rewrite <- (Z.ldiff_ones_r u 1) by lia. rewrite Z.ldiff_land. reflexivity.
Qed.

Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> BMS.ret_pc k = k.
Proof.
  intros k H. assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. apply (f_equal bv_unsigned) in H.
    rewrite Z_to_bv_unsigned, Z.add_0_r in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
    rewrite <- H. pose proof (land_m2_mod (bv_unsigned k)).
    set (w := Z.land (bv_unsigned k) (-2)) in *. Z.div_mod_to_equations. lia. }
  transitivity (BMS.ret_pc (Z_to_bv 64 (bv_unsigned k))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite BMS.ret_pc_even; [apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range | exact E].
Qed.

(* the callee-saved registers of a walk's final register tree are the caller's *)
Lemma aregs_of_mkR : forall regs regs' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  L6.xregs_eqv (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
    (reg_get regs 8) (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
    (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
    (reg_get regs 27) t3 t4 t5 t6) regs' ->
  aregs_preserved regs regs'.
Proof.
  intros regs regs' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HX r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [->|Hc];
    [ rewrite !getr_nz by reflexivity;
      match goal with |- reg_get _ (Z_to_bv 5 ?k) = _ =>
        rewrite <- (HX (Z_to_bv 5 k)) by reflexivity; reflexivity end |]).
  subst r. rewrite !getr_nz by reflexivity. rewrite <- (HX (Z_to_bv 5 27)) by reflexivity. reflexivity.
Qed.

Lemma a0_of_mkR : forall regs' t1 t2 t3 t4 t5 t6 t7 t8 t9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31,
  L6.xregs_eqv (BF.mkR t1 t2 t3 t4 t5 t6 t7 t8 t9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31) regs' ->
  YK11.getr regs' 10 = a0.
Proof.
  intros. rewrite getr_nz by reflexivity.
  match goal with H : L6.xregs_eqv _ _ |- _ => rewrite <- (H 10%bv) by reflexivity end.
  reflexivity.
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* two readings of a memory that changed only where the hidden flag is clear *)
Lemma aview_keep : forall (Hb : word -> bool) (m m' : word -> option byte) a,
  (Hb (Z_to_bv 64 a) = false -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  aview frsegs Hb m' a = aview frsegs Hb m a.
Proof.
  intros Hb m m' a HE. apply aview_eq_of. unfold mrestrict.
  destruct (Hb (Z_to_bv 64 a)) eqn:E; [reflexivity|]. rewrite HE by reflexivity. reflexivity.
Qed.

Lemma aview_vis_keep : forall (Hb : word -> bool) (m m' : word -> option byte) a,
  (Hb (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  aview frsegs Hb m a <> None -> aview frsegs Hb m' a <> None.
Proof.
  intros Hb m m' a HP Hv. unfold aview, mbyte, mrestrict in Hv |- *.
  destruct (Hb (Z_to_bv 64 a)) eqn:E; [exact Hv|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  - destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em'; [cbn; discriminate|].
    exfalso. exact (HP eq_refl ltac:(discriminate) eq_refl).
  - destruct (m' (Z_to_bv 64 a)); [cbn; discriminate | exact Hv].
Qed.

(* THE BRIDGE: a Bz walk's post, read as W_sites_x' aentry_post_x over a generic allocator relation ARx (its head set
   Hp unchanged), from the four runtime laws rt_laws (lib/Rt/RTx.v).
   WR is the walk's written ranges (munch's tail), Wr the post's written set (WR included in it), and Pr the post's
   claim on the returned registers and memory, discharged from a0 = r and the final memory read off w_H and off
   cj_drop. aentry_post_of_walk below is this lemma at cgif's AR (FCiface.AR_nohp, Hp := []). *)
Lemma aentry_post_of_walk_x : forall B ARx, rt_laws frsegs B ARx ->
  forall (STK D : Z) (WR : list (Z * Z)) (Wr : Z -> Prop)
    (Pr : bvmap 5 word -> (word -> option byte) -> Prop) (r : Z)
    ly S Hp (W : world frsegs) regs mem md ms' model' c m'
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  ecall_pre_x frsegs B ARx ly S Hp W regs mem md ->
  ly_stk_lo ly + STK <= spZ regs ->
  NM.ro_agree I0.rsegs (mrestrict (w_H W) mem) ->
  0 <= D <= STK ->
  (forall a, in_ivls WR a -> Wr a) ->
  (forall a, Wr a -> ~ aowned B ly S a) ->
  (forall a, Wr a -> apresent (w_H W) mem a ->
     NM.cj_drop I0.rsegs (Z_to_bv 64 a) = false /\ m' (Z_to_bv 64 a) <> None) ->
  NM.ms_rel_cj I0.rsegs c
    (BMS.MS (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 (reg_get regs 8)
       (reg_get regs 9) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
       (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) t3 t4 t5 t6) fp_regs (BMS.ret_pc (reg_get regs 1)) fp_csr None m' (YK11.seg_rom BI.asegs)) ->
  NM.cj_same I0.rsegs (mrestrict (w_H W) mem) (ms_mem c) ->
  L6.ms_eqv c ms' ->
  BF.munch ([(spZ regs - D, spZ regs)] ++ WR) (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)) m' ->
  BF.stk BI.asegs m' (spZ regs - STK) (spZ regs) ->
  same_but_materialized md model' ->
  (forall regs'' mem'', YK11.getr regs'' 10 = Z_to_bv 64 r ->
     (forall a : word, w_H W a = false -> NM.cj_drop I0.rsegs a = false -> mem'' a = m' a) -> Pr regs'' mem'') ->
  aentry_post_x (PI := PB_fr) ARx STK ly S Hp W regs mem md Wr Pr W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros B ARx LAWS STK D WR Wr Pr r ly S Hp W regs mem md ms' model' c m'
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    Hpre HSTK RO HD HWR HWown HWpres Hrel Hsame Heqv MU ST Hsbm HPr.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & Hwin & Hgp & Htp).
  pose proof (rtl_layout _ _ _ LAWS ly S Hp W mem md HAR) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & V1 & V2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V3).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  remember (munrestrict H mem (ms_mem ms')) as mem'' eqn:Emem''.
  destruct Hrel as (Rr & Rf & Rpc & Rsvc & Rresv & Rfc & Rrom & Rmem).
  cbn [BMS.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem]
    in Rr, Rf, Rpc, Rsvc, Rresv, Rfc, Rrom, Rmem.
  destruct Heqv as (Er & Ef & Epc & Esvc & Eresv & Efc & Emem & Erom).
  rewrite Rr in Er.
  assert (MUc : BF.munch ([(sp - D, sp)] ++ WR) mR (ms_mem c))
    by exact (NM.munch_rel_cj I0.rsegs ([(sp - D, sp)] ++ WR) mR _ (ms_mem c) m'
                (NM.mem_rel_cj_normalize I0.rsegs mR RO) Rmem Hsame MU).
  (* off the window and off the written ranges the caller's memory is unchanged *)
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> BF.outside ([(sp - D, sp)] ++ WR) a ->
     mem'' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Ho. rewrite Emem''. unfold munrestrict. destruct (H (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
    rewrite <- Emem. rewrite (MUc (Z_to_bv 64 a)) by (rewrite BMS.unsigned_lit by lia; exact Ho).
    unfold mR, mrestrict. rewrite Eh. reflexivity. }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (sp - D <= a < sp) ->
     mem'' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha HnW Hn. apply KEEP0; [exact Ha|]. cbn [app BF.outside]. cbn [fst snd].
    split; [exact Hn|]. apply outside_not_in_ivls. intros Hex. exact (HnW (HWR a Hex)). }
  (* the whole STK window is present after the walk *)
  assert (WIN : forall a, sp - STK <= a < sp -> exists b, ms_mem ms' (Z_to_bv 64 a) = Some b).
  { intros a Ha. destruct ST as (_ & _ & STa). destruct (STa a Ha) as (_ & b & Hb).
    assert (K : NM.cj_drop I0.rsegs (Z_to_bv 64 a) = false)
      by (apply cj_keep_high; unfold FR_IMG_TOP, TASK_SIZE; lia).
    exists b. rewrite <- Emem. rewrite <- (NM.mem_rel_cj_keep I0.rsegs _ _ _ Rmem K).
    rewrite mrd_high in Hb by (unfold BM.wa; rewrite BMS.unsigned_lit by lia; unfold FR_IMG_TOP; lia).
    exact Hb. }
  assert (WRAP : forall a : Z, Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64) /\ 0 <= a mod 2 ^ 64 < 2 ^ 64).
  { intros a. split; [|apply Z.mod_pos_bound; lia]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
  (* a byte present before is present after *)
  assert (PRES : forall a, H (Z_to_bv 64 a) = false -> mem (Z_to_bv 64 a) <> None ->
     mem'' (Z_to_bv 64 a) <> None).
  { intros a Hh Hm. destruct (WRAP a) as (Ew & Hw). rewrite Ew in *. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_le_gt_dec (sp - D) a') as [L1|L1]; [destruct (Z_lt_ge_dec a' sp) as [L2|L2]|].
    - destruct (WIN a' ltac:(lia)) as (b & Hb). rewrite Emem''. unfold munrestrict. rewrite Hh, Hb. discriminate.
    - destruct (outside_or_in WR a') as [Ho|Hex].
      + rewrite KEEP0; [exact Hm | lia | cbn [app BF.outside]; cbn [fst snd]; split; [lia | exact Ho]].
      + destruct (mem (Z_to_bv 64 a')) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
        destruct (HWpres a' (HWR a' Hex) (conj Hh (ex_intro _ b Em))) as (K & Hm').
        rewrite Emem''. unfold munrestrict. rewrite Hh. rewrite <- Emem.
        rewrite <- (NM.mem_rel_cj_keep I0.rsegs _ _ _ Rmem K). exact Hm'.
    - destruct (outside_or_in WR a') as [Ho|Hex].
      + rewrite KEEP0; [exact Hm | lia | cbn [app BF.outside]; cbn [fst snd]; split; [lia | exact Ho]].
      + destruct (mem (Z_to_bv 64 a')) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
        destruct (HWpres a' (HWR a' Hex) (conj Hh (ex_intro _ b Em))) as (K & Hm').
        rewrite Emem''. unfold munrestrict. rewrite Hh. rewrite <- Emem.
        rewrite <- (NM.mem_rel_cj_keep I0.rsegs _ _ _ Rmem K). exact Hm'. }
  unfold aentry_post_x. split; [reflexivity|]. exists (ms_regs ms'), mem'', model'.
  split.
  { (* the configuration at the return address *)
    assert (Fpc : ms_pc_val ms' = w64 (raZ regs)).
    { rewrite <- Epc, Rpc. unfold raZ, w64. rewrite getr_nz by reflexivity. rewrite Z_to_bv_bv_unsigned.
      rewrite getr_nz in Hret by reflexivity. apply ret_pc_ok. exact Hret. }
    assert (Ffr : ms_fregs ms' = fp_regs) by congruence.
    assert (Fsvc : ms_svc_pending ms' = None) by congruence.
    assert (Frv : ms_resv ms' = None) by congruence.
    assert (Ffc : ms_fcsr ms' = fp_csr) by congruence.
    assert (From : ms_rom ms' = YK11.seg_rom frsegs) by (rewrite <- Erom, Rrom; reflexivity).
    unfold cfg_at, YK11.mkst, unrestrict. rewrite Fpc, Ffr, Fsvc, Frv, Ffc, From, Emem''. reflexivity. }
  split.
  { (* AR, by the frame law *)
    apply (rtl_frame _ _ _ LAWS ly S Hp W mem md mem'' model' HAR).
    - intros a Ha Hown. apply aview_keep. intros Eh.
      rewrite KEEP; [reflexivity | exact Ha | intros HW; exact (HWown a HW Hown) |].
      intros Hs. apply (rtl_stack _ _ _ LAWS ly S Hp W mem md a HAR); [lia | exact Hown].
    - intros a Hv'. apply (aview_vis_keep (w_H W) mem mem'' a); [|exact Hv'].
      intros Eh Hm. exact (PRES a Eh Hm).
    - exact V1.
    - exact V2.
    - exact V3.
    - intros a _ Hh. rewrite Emem''. unfold munrestrict. fold H in Hh. rewrite Hh. reflexivity. }
  split; [exact (aregs_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er)|].
  split; [exact Hsbm|].
  split.
  { apply HPr.
    - rewrite (a0_of_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Er). reflexivity.
    - intros x Hhx Hdx. rewrite Emem''. unfold munrestrict. rewrite Hhx. rewrite <- Emem.
      symmetry. exact (NM.mem_rel_cj_keep I0.rsegs _ _ _ Rmem Hdx). }
  split.
  { intros a Ha HnW Hs. apply aview_keep. intros Eh.
    rewrite KEEP; [reflexivity | exact Ha | exact HnW | intros Hc; apply Hs; lia]. }
  { intros a (Hh & b & Hb). split; [exact Hh|].
    destruct (mem'' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. exact (PRES a Hh ltac:(rewrite Hb; discriminate) E). }
Qed.

(* cgif's AR: the bridge at ARx := AR_nohp (Hp := []), whose laws rt_laws_AR gives from AR_laws. *)
Lemma aentry_post_of_walk : forall B, AR_laws frsegs B ->
  forall (STK D : Z) (WR : list (Z * Z)) (Wr : Z -> Prop)
    (Pr : bvmap 5 word -> (word -> option byte) -> Prop) (r : Z)
    ly S (W : world frsegs) regs mem md ms' model' c m'
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  ecall_pre frsegs B ly S W regs mem md ->
  ly_stk_lo ly + STK <= spZ regs ->
  NM.ro_agree I0.rsegs (mrestrict (w_H W) mem) ->
  0 <= D <= STK ->
  (forall a, in_ivls WR a -> Wr a) ->
  (forall a, Wr a -> ~ aowned B ly S a) ->
  (forall a, Wr a -> apresent (w_H W) mem a ->
     NM.cj_drop I0.rsegs (Z_to_bv 64 a) = false /\ m' (Z_to_bv 64 a) <> None) ->
  NM.ms_rel_cj I0.rsegs c
    (BMS.MS (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 (reg_get regs 8)
       (reg_get regs 9) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
       (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) t3 t4 t5 t6) fp_regs (BMS.ret_pc (reg_get regs 1)) fp_csr None m' (YK11.seg_rom BI.asegs)) ->
  NM.cj_same I0.rsegs (mrestrict (w_H W) mem) (ms_mem c) ->
  L6.ms_eqv c ms' ->
  BF.munch ([(spZ regs - D, spZ regs)] ++ WR) (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem)) m' ->
  BF.stk BI.asegs m' (spZ regs - STK) (spZ regs) ->
  same_but_materialized md model' ->
  (forall regs'' mem'', YK11.getr regs'' 10 = Z_to_bv 64 r ->
     (forall a : word, w_H W a = false -> NM.cj_drop I0.rsegs a = false -> mem'' a = m' a) -> Pr regs'' mem'') ->
  aentry_post (PI := PB_fr) B STK ly S W regs mem md Wr Pr W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros B LAWS. intros STK D WR Wr Pr r ly S W regs mem md ms' model' c m'
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre.
  exact (aentry_post_of_walk_x B (AR_nohp frsegs B) (rt_laws_AR frsegs B LAWS)
    STK D WR Wr Pr r ly S [] W regs mem md ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre).
Qed.

(* ---- the transport half: a Bz walk, which runs on the normalized memory at the canonical register tree, read
   on the machine at a donor call site.  FSstrlen.v:151-195, 305-348, 420-441, 452-515 (a Theorem Labs lane, itself
   a Theorem Labs lane's BzBridge.v and a Theorem Labs lane's), at fuzz_reply's image. ---- *)
Lemma wx_apart_fr : NM.wx_apart I0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma option_map_unsigned_inj : forall (o1 o2 : option byte),
  option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
  intros [b1|] [b2|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Lemma find_segment_spec : forall segs x n s, find_segment segs x n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|s0 r IH]; intros x n s H; cbn in H; [discriminate H|].
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n s H) as (Hi & H1 & H2). split; [right; exact Hi | lia].
Qed.

(* rom_view: the bytes the restricted memory holds at read-only image addresses are the image's *)
Lemma ro_agree_of_rom_view : forall (W : world frsegs) mem,
  rom_view frsegs W mem -> NM.ro_agree I0.rsegs (mrestrict (w_H W) mem).
Proof.
  intros W mem HR a Ha. unfold LM.ro_addr in Ha.
  destruct (find_segment I0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
  destruct (find_segment_spec _ _ _ _ E) as (Hin & H1 & H2).
  assert (Hro : in_rom frsegs (bv_unsigned a)).
  { exists s. split; [exact Hin|]. split; [apply negb_true_iff in Ha; exact Ha | lia]. }
  pose proof (HR _ Hro) as V. unfold aview, mbyte in V. rewrite !Z_to_bv_bv_unsigned in V.
  apply option_map_unsigned_inj. exact V.
Qed.

Lemma norm_keep_high : forall m (a : word), FR_IMG_TOP <= bv_unsigned a < TASK_SIZE ->
  NM.normalize_cj I0.rsegs m a = m a.
Proof.
  intros m a Ha. pose proof (cj_keep_high (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. reflexivity.
Qed.

(* a stack window above the image keeps its bytes in the normalized memory *)
Lemma stk_norm_high : forall m lo hi, FR_IMG_TOP <= lo -> hi <= TASK_SIZE ->
  BF.stk BI.asegs m lo hi -> BF.stk BI.asegs (NM.normalize_cj I0.rsegs m) lo hi.
Proof.
  intros m lo hi Hlo Hhi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (K : NM.normalize_cj I0.rsegs m (BM.wa a) = m (BM.wa a)).
  { apply norm_keep_high. rewrite BM.wa_unsigned by (unfold TASK_SIZE in Hhi; lia). lia. }
  split.
  - unfold wview. rewrite K. exact Hw.
  - exists b. unfold BM.mrd. rewrite K. exact Hb.
Qed.

(* the ASan range check of [x, x + n) on the normalized memory, from the donor's shadow facts *)
Lemma chk_norm : forall (H : word -> bool) mem x n,
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> n <= 2 ^ 40 -> BK.region_in_mem x n ->
  range_addressable (aview frsegs H mem) SHADOW_OFF x n -> shadow_hull_vis (aview frsegs H mem) x n ->
  BQ.chk_ok (NM.normalize_cj I0.rsegs (mrestrict H mem)) x n.
Proof.
  intros H mem x n Hx Hn Hxn H40 Hreg Hra Hhull.
  apply (BQ.chk_ok_agree (mrestrict H mem)); [| lia | lia |].
  - apply FRS.chk_ok_of_view; [lia | lia | lia | lia | exact Hreg | exact Hra |].
    apply FRS.hull_of_shadow_hull_vis. exact Hhull.
  - intros a Ha. apply norm_keep_high. unfold FR_IMG_TOP, TASK_SIZE. lia.
Qed.

Lemma bz_msteps_l : forall s s', BE.msteps BI.asegs s s' -> LE.msteps I0.rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply LE.msteps_refl.
  - eapply LE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma bz_evt_l : forall (Q : machine_state -> Prop) ms, BE.evt BI.asegs Q ms -> LE.evt I0.rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (bz_msteps_l ms ms' H) | exact HQ]. Qed.

Definition st_at (regs F : bvmap 5 word) (pc : word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None; ms_resv := None; ms_fcsr := fc;
     ms_mem := m; ms_rom := YK11.seg_rom frsegs |}.

Definition walk_at (Q : machine_state -> Prop) (m : word -> option byte) (a : machine_state) : Prop :=
  exists c s0, Q s0 /\ NM.ms_rel_cj I0.rsegs c s0 /\ NM.cj_same I0.rsegs m (ms_mem c) /\ L6.ms_eqv c a.

Lemma bz_transport : forall (Q : machine_state -> Prop) regs F pc fc m,
  NM.ro_agree I0.rsegs m ->
  BE.evt BI.asegs Q (BMS.MS (L6.mkR_of regs) F pc fc None (NM.normalize_cj I0.rsegs m) (YK11.seg_rom BI.asegs)) ->
  BE.evt BI.asegs (walk_at Q m) (st_at regs F pc fc m).
Proof.
  intros Q regs F pc fc m RO H.
  apply SL.evt_to_bz.
  pose proof (NM.evt_normalize_cj I0.rsegs Q (L6.mkR_of regs) F pc fc None m (YK11.seg_rom I0.rsegs) wx_apart_fr RO
    (bz_evt_l Q _ H)) as H2.
  assert (EQV : L6.ms_eqv (BMS.MS (L6.mkR_of regs) F pc fc None m (YK11.seg_rom I0.rsegs)) (st_at regs F pc fc m)).
  { unfold L6.ms_eqv, st_at, BMS.MS. cbn. split; [apply L6.xregs_eqv_sym, L6.mkR_of_eqv|].
    repeat split; reflexivity. }
  pose proof (LR.evt_register_transport I0.rsegs _ _ _ EQV H2) as H3.
  eapply LE.evt_mono; [exact H3|]. intros a (c & (s0 & HQ & Hrel & Hsame) & Heqv). exists c, s0. auto.
Qed.

(* ---- the runtime cells a walk reads, from the donor's val_mem facts ---- *)
Lemma keep_range : forall A n,
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  forall z, A <= z < A + Z.of_nat n -> NM.cj_drop I0.rsegs (Z_to_bv 64 z) = false.
Proof.
  intros A n Hb z Hz. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (z - A)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (A + (z - A)) with z in Hb by lia.
  apply negb_true_iff in Hb. exact Hb.
Qed.

Lemma agree_cells : forall (H : word -> bool) mem A n,
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 n) = true ->
  BD.agree_on (fun z => A <= z < A + Z.of_nat n) (mrestrict H mem) (NM.normalize_cj I0.rsegs (mrestrict H mem)).
Proof.
  intros H mem A n Hb a Ha.
  pose proof (keep_range A n Hb (bv_unsigned a) Ha) as K. rewrite Z_to_bv_bv_unsigned in K.
  unfold NM.normalize_cj. rewrite K. reflexivity.
Qed.

Lemma wview_of_mrd : forall m x b, BM.mrd BI.asegs m x = Some b -> LM.ro_addr I0.rsegs x = false ->
  wview BI.asegs m x <> None.
Proof.
  intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
  unfold BM.mrd in H. rewrite E in H.
  match type of H with ?f _ _ = _ => unfold f in H end. unfold memory_read in H.
  unfold LM.ro_addr in R. change (Z.of_N 1) with 1 in H. change BI.asegs with I0.rsegs in *.
  destruct (find_segment I0.rsegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable s); [|discriminate H].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
  exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Lemma rw_of_ro : forall m A cs, BSt.ro_cells BI.asegs m A cs ->
  forallb (fun i => negb (NM.cj_drop I0.rsegs (Z_to_bv 64 (A + Z.of_nat i)))) (seq 0 (BC.cells_size cs)) = true ->
  length (BC.cells_bytes cs) = BC.cells_size cs ->
  BSt.rw_cells BI.asegs m A cs.
Proof.
  intros m A cs (Hwf & HB) Hk Hl. split; [split; [exact Hwf | exact HB]|].
  destruct HB as (H0 & H1 & HB). split; [exact H0|]. split; [rewrite <- Hl; exact H1|].
  intros i Hi. pose proof (HB (Z.to_nat i) ltac:(lia)) as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error (BC.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  apply (wview_of_mrd m _ b Hr).
  pose proof (keep_range A _ Hk (A + i) ltac:(lia)) as K. unfold NM.cj_drop in K.
  apply orb_false_iff in K as [K _]. exact K.
Qed.

Lemma nth_Z_to_le_bytes : forall n z i, (i < n)%nat ->
  nth_error (Z_to_le_bytes n z) i = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i))).
Proof.
  induction n as [|n IH]; intros z i Hi; [lia|]. destruct i as [|i]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le_byte_8 : forall v i, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 i) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat i)).
Proof.
  intros v i Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, le_byte. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* an 8-byte value the donor reads (val_mem) is a C8 cell of the Bz tree *)
Lemma ro_c8_of_val_mem : forall m A v, 0 <= A -> A + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  val_mem frsegs m A 8 v -> BSt.ro_cells BI.asegs m A [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros m A v HA HA8 Hv HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [exact HA8|].
  intros i Hi. assert (Hi8 : (i < 8)%nat) by exact Hi.
  change (BM.mrd BI.asegs m (BM.wa (A + Z.of_nat i))) with (mbyte frsegs m (A + Z.of_nat i)).
  rewrite (HV i Hi8). rewrite le_byte_8 by exact Hv.
  unfold BM.le8, word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hi8. rewrite BMS.unsigned_lit by lia.
  reflexivity.
Qed.

Lemma seg_addr_below : forall a, BM.seg_addr I0.rsegs a = true -> bv_unsigned a < BM.UTOP.
Proof.
  intros a H. unfold BM.seg_addr in H.
  destruct (find_segment I0.rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_below I0.rsegs FR_IMG_TOP (bv_unsigned a) 1 s rsegs_below E ltac:(lia)) as [L|L];
    [unfold BM.UTOP, FR_IMG_TOP in *; lia | discriminate L].
Qed.

(* the Bz walks' memory invariant holds of every normalized memory *)
Lemma bz_mem_inv_normalize : forall m, BM.mem_inv BI.asegs (NM.normalize_cj I0.rsegs m).
Proof.
  intros m. apply BM.mem_inv_intro.
  - exact seg_addr_below.
  - intros x b Hx. unfold NM.normalize_cj in Hx. destruct (NM.cj_drop I0.rsegs x) eqn:E; [discriminate Hx|].
    destruct (NM.cj_drop_false I0.rsegs x E) as (Hro & Hin). split; [exact Hro|].
    destruct Hin as [Hs|Hlt]; [|unfold BM.UTOP, TASK_SIZE in *; lia].
    destruct (find_segment I0.rsegs (bv_unsigned x) 1) as [s|] eqn:Ef; [|exfalso; exact (Hs eq_refl)].
    destruct (find_segment_below I0.rsegs FR_IMG_TOP (bv_unsigned x) 1 s rsegs_below Ef ltac:(lia)) as [L|L];
      [unfold BM.UTOP, FR_IMG_TOP in *; lia | discriminate L].
Qed.

(* a one-byte flag the donor reads as 1 (val_mem) is a C1 cell of the Bz tree *)
Lemma ro_c1_one_of_val_mem : forall m A, 0 <= A -> A + 1 <= 2 ^ 64 ->
  val_mem frsegs m A 1 1 -> BSt.ro_cells BI.asegs m A [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros m A HA HA1 HV. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact HA|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  change (BM.mrd BI.asegs m (BM.wa (A + Z.of_nat 0))) with (mbyte frsegs m (A + Z.of_nat 0)).
  rewrite (HV 0%nat ltac:(cbn; lia)). reflexivity.
Qed.

Lemma ro_cons8 : forall m A w cs, BSt.ro_cells BI.asegs m A [BC.C8 w] -> BSt.ro_cells BI.asegs m (A + 8) cs ->
  BSt.ro_cells BI.asegs m A (BC.C8 w :: cs).
Proof.
  intros m A w cs (_ & B1) (W2 & B2). split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (BM.bytes_at_app BI.asegs m A _ _)). split; [exact B1|].
  assert (L : length (BM.le8 w) = 8%nat) by reflexivity. rewrite L. exact B2.
Qed.

End core.
