(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec StepTac StoreOk DriverCfg AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall PDrvHeap PDrvHeap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

Section HeapI.
Variable HI : heap_iface.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HOK : heap_ok PSEGS DCFG HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Variable HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop.
Variable INIT : hi_HS HI -> list ivl.
Hypothesis HOKI : heap_init_ok PSEGS DCFG HI HeapI INIT GP TP HTOP CELLS_NE 0x51310 8192.
(* [comment removed for export] *)
Hypothesis HOWNI : forall hs m md, HeapI hs m md -> forall x, ~ ioutside (hi_owned HI hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).
Hypothesis HERRI : forall hs m m' md, HeapI hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapI hs m' md.
Hypothesis HCELLI : forall hs m m' md, HeapI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapI hs m' md.

#[using="Type"] Lemma cellb_true_i : forall L x, cellb L x = true <-> ~ ioutside L (bv_unsigned x).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x. unfold cellb. destruct (HIface.outside_dec L (bv_unsigned x)); split; intros H; try tauto; discriminate. Qed.
#[using="Type"] Lemma cellb_false_i : forall L x, cellb L x = false <-> ioutside L (bv_unsigned x).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x. unfold cellb. destruct (HIface.outside_dec L (bv_unsigned x)); split; intros H; try tauto; try discriminate; exfalso; tauto. Qed.

#[using="GP TP HOKI HOWNI HERRI HCELLI"] Theorem heap_seg_init : forall E rgs hs m m' md,
  HeapI hs m md ->
  (forall x, ~ ioutside (INIT hs) (bv_unsigned x) -> outside E rgs x) ->
  (forall x, outside E rgs x -> m' x = m x) -> mem_grows m m' ->
  (forall a, ~ ioutside CELLS_NE a -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) ->
  avoid_heap3 IMG_LO IMG_END HTOP STATIC E rgs ->
  HeapI hs m' md.
Proof. LiaFast.lf_pins (fun (GP TP HOKI HOWNI HERRI HCELLI : LiaFast.U) => LiaFast.u0).
  intros E rgs hs m m' md Hh Hinit Hfr Hgr Hcel Hav.
  pose proof HOKI as (_ & Hframe).
  set (m1 := fun x : word => if cellb (CELLS_NE ++ ERRC) x then m x else m' x).
  set (m2 := fun x : word => if cellb ERRC x then m x else m' x).
  assert (H1 : HeapI hs m1 md).
  { apply (Hframe hs m m1 md (icompl (hi_owned HI hs ++ INIT hs)) Hh).
    - intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      assert (Hown0 : ~ ioutside (hi_owned HI hs ++ INIT hs) (bv_unsigned x)) by (intros Ho; apply (proj2 (icompl_spec _ _ Rx)) in Ho; exact (Ho Hx)).
      unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x) eqn:Hc; [reflexivity|]. apply cellb_false_i in Hc.
      destruct (outside_or_in E rgs x) as [Ho|(i & R & Hi & Hin)]; [exact (Hfr x Ho)|].
      destruct (HIface.outside_dec (INIT hs) (bv_unsigned x)) as [Hni|Hni]; [|exact (Hfr x (Hinit x Hni))].
      assert (Hown : ~ ioutside (hi_owned HI hs) (bv_unsigned x)) by (intros Ho; apply Hown0; apply ioutside_app; split; assumption).
      exfalso. destruct (HOWNI hs m md Hh _ Hown) as (B1 & B2).
      destruct (Hav i R x Hi Hin Hc) as [Q|(Q1 & Q2)]; [lia|]. destruct B2 as [B2|[B2|B2]]; [exact (B2 Q2) | lia | lia].
    - intros x Hx. unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x); [exact Hx | exact (Hgr x Hx)].
    - intros x Hx. pose proof (icompl_range _ _ Hx) as Rx. pose proof (proj1 (icompl_spec _ _ Rx) Hx) as Q. apply ioutside_app in Q. exact Q. }
  assert (H2 : HeapI hs m2 md).
  { apply (HCELLI hs m1 m2 md H1).
    - intros x Hx. unfold m1, m2. destruct (cellb ERRC x) eqn:He.
      + apply cellb_true_i in He. replace (cellb (CELLS_NE ++ ERRC) x) with true; [reflexivity|]. symmetry. apply cellb_true_i.
        rewrite ioutside_app. tauto.
      + apply cellb_false_i in He. replace (cellb (CELLS_NE ++ ERRC) x) with false; [reflexivity|]. symmetry. apply cellb_false_i.
        rewrite ioutside_app. tauto.
    - intros x Hx. unfold m1, m2 in *. destruct (cellb ERRC x) eqn:He.
      + replace (cellb (CELLS_NE ++ ERRC) x) with true in Hx; [exact Hx|]. symmetry. apply cellb_true_i. apply cellb_true_i in He.
        rewrite ioutside_app. tauto.
      + destruct (cellb (CELLS_NE ++ ERRC) x); [exact (Hgr x Hx) | exact Hx].
    - intros a Ha0.
      assert (Ha : ~ ioutside CELLS_NE a) by (cbn [ioutside CELLS_NE]; intros (A & B & _); destruct Ha0 as [Q|Q]; [exact (A Q) | exact (B Q)]).
      pose proof (Hcel a Ha) as Hv. unfold mrd in *. unfold m1, m2.
      assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small64; unfold two64; lia).
      assert (He : cellb ERRC (Z_to_bv 64 a) = false).
      { apply cellb_false_i. cbn [ioutside ERRC]. split; [|exact I]. rewrite Ua. lia. }
      assert (Hce : cellb (CELLS_NE ++ ERRC) (Z_to_bv 64 a) = true).
      { apply cellb_true_i. rewrite ioutside_app. intros [A _]. apply Ha. rewrite Ua in A. exact A. }
      rewrite He, Hce. exact Hv. }
  apply (HERRI hs m2 m' md H2).
  - intros x Hx. unfold m2. destruct (cellb ERRC x) eqn:Hie; [|reflexivity]. apply cellb_true_i in Hie. exfalso. exact (Hie Hx).
  - intros x Hx. unfold m2 in Hx. destruct (cellb ERRC x); [exact (Hgr x Hx) | exact Hx].
Qed.

(* [comment removed for export] *)
#[using="HOKI"] Lemma HMMDI : forall (fx : FPState) regs m md hs (n : Z) (ret : word) (K : TSet),
    HeapI hs m md -> md_ok md -> (U md + MCHARGE n <= UBOUND)%Z ->
    getr regs 10 = Z_to_bv 64 n -> (1 <= n <= 2^26)%Z ->
    getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
    getr regs 3 = GP -> getr regs 4 = TP ->
    (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - 8192)%Z ->
    stk PSEGS m (sp_of regs - 8192) (sp_of regs) ->
    (forall x : Z, ~ ioutside (INIT hs) x -> (sp_of regs <= x)%Z) ->
    (forall (fx' : FPState) regs' m' md' hs' (p : Z),
       @fp_csr fx' = @fp_csr fx -> hi_Heap HI hs' m' md' -> md_ok md' -> vm_only md md' -> (U md' <= U md + MCHARGE n)%Z ->
       getr regs' 10 = Z_to_bv 64 p -> (p mod 16 = 0)%Z ->
       blocks_add (hi_blocks HI hs) (hi_blocks HI hs') (p, n) -> ~ In (p, n) (hi_blocks HI hs) ->
       HIface.callee_saved regs regs' ->
       munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(p, p + n); (sp_of regs - 8192, sp_of regs)]%Z) m m' ->
       (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48)%Z -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
       stk PSEGS m' (sp_of regs - 8192) (sp_of regs) ->
       realizes_cfg PSEGS DCFG (mkCfg (@mkst fx' regs' ret m' (seg_rom PSEGS)) md') K) ->
    realizes_cfg PSEGS DCFG (mkCfg (@mkst fx regs (Z_to_bv 64 0x51310) m (seg_rom PSEGS)) md) K.
Proof. LiaFast.lf_pins (fun (HOKI : LiaFast.U) => LiaFast.u0).
  pose proof HOKI as (HM & _). intros fx regs m md hs n ret K Hh Hmd HU H10 Hn H1 Hra H3 H4 Hs16 Hs47 Htop Hstk Hinit Hk.
  apply (HM fx regs m md hs n ret K Hh Hmd HU H10 Hn H1 Hra H3 H4 Hs16 Hs47 Htop Hstk Hinit).
  intros fx' regs' m' md' hs' p Hfc Hh' Hmd' Hvo HU' Hkeep H10' Hp16 Hadd Hnin Hcs Hmunch Hstk'.
  apply (Hk fx' regs' m' md' hs' p Hfc Hh' Hmd' Hvo HU' H10' Hp16 Hadd Hnin Hcs Hmunch); [| exact Hstk'].
  intros a Ha. apply Hkeep. cbn [ioutside CELLS_NE]. intros (A & B & _). destruct Ha as [Ha|Ha]; [exact (A Ha) | exact (B Ha)].
Qed.

#[using="HOWNI"] Lemma avoid_ownedI : forall E L hs m md i R x, avoid_heap3 IMG_LO IMG_END HTOP STATIC E (s_rgs L) -> HeapI hs m md ->
  nth_error (s_rgs L) i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) -> ioutside (hi_owned HI hs) (bv_unsigned x).
Proof. LiaFast.lf_pins (fun (HOWNI : LiaFast.U) => LiaFast.u0).
  intros E L hs m md i R x Hav Hh Hi Hin Hc.
  destruct (HIface.outside_dec (hi_owned HI hs) (bv_unsigned x)) as [A|A]; [exact A|].
  exfalso. destruct (HOWNI hs m md Hh _ A) as (H1 & H2). destruct (Hav i R x Hi Hin Hc) as [H3|(H3 & H4)]; [lia|]. destruct H2 as [H2|[H2|H2]]; [exact (H2 H4) | lia | lia].
Qed.

#[using="HOK HOKI HOWNI"] Theorem fx_malloc_init : forall E L ms md hs (n : Z) (i0 i7 : nat) (o0 : Z) (sp : Z) R7 K,
  sden PSEGS E L ms -> s_pc L = 0x51310 -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  havoc_ok L [(i0, o0, 8192); (i7, 4, 4)] None = true ->
  nth_error (s_rgs L) i7 = Some R7 -> bv_unsigned (lden E (rg_base R7)) = 0x75b28 ->
  HeapI hs (ms_mem ms) md -> md_ok md -> U md + MCHARGE n <= UBOUND ->
  getr (ms_regs ms) 10 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 26 ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 -> getr (ms_regs ms) 3 = GP -> getr (ms_regs ms) 4 = TP ->
  getr (ms_regs ms) 2 = Z_to_bv 64 sp -> sp mod 16 = 0 -> 0xa0000 <= sp - 8192 -> sp <= 2 ^ 47 -> HTOP <= sp - 8192 ->
  frame_in E L i0 o0 8192 (sp - 8192) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E (s_rgs L) ->
  (forall x : Z, ~ ioutside (INIT hs) x -> sp <= x) ->
  (forall E' ms' md' hs' (p : Z), agree (s_next L) E E' ->
      sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None) ms' -> ms_rom ms' = ms_rom ms ->
      hi_Heap HI hs' (ms_mem ms') md' -> md_ok md' -> vm_only md md' -> U md' <= U md + MCHARGE n ->
      getr (ms_regs ms') 10 = Z_to_bv 64 p -> p mod 16 = 0 ->
      blocks_add (hi_blocks HI hs) (hi_blocks HI hs') (p, n) -> ~ In (p, n) (hi_blocks HI hs) ->
      munch (hi_owned HI hs ++ hi_owned HI hs' ++ [(p, p + n); (sp - 8192, sp)]) (ms_mem ms) (ms_mem ms') ->
      (forall a, (0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48) -> ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
      realizes PSEGS (mkCfg ms' md') K) ->
  realizes PSEGS (mkCfg ms md) K.
Proof. LiaFast.lf_pins (fun (HOK HOKI HOWNI : LiaFast.U) => LiaFast.u0).
  intros E L ms md hs n i0 i7 o0 sp R7 K Hd Hpc Hrv Hrom Hok Hi7 Hb7 Hheap Hmd HU H10 Hn Hra H3 H4 H2 Hs16 Hslo Hshi Htop Hfr Hav Hinit Hk.
  pose proof HOK as (_ & _ & _ & _ & Hblk). pose proof HMMDI as HM.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *. set (rom := seg_rom PSEGS) in *.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  assert (HSP : sp_of regs = sp) by (unfold sp_of; rewrite H2; apply u_small64; unfold two64; lia).
  destruct Hfr as (R0 & Hi0 & Ha0 & Hwk0 & Ho0 & Hn0).
  pose proof (sden_rg _ _ _ _ _ _ Hd Hi0) as HR0.
  assert (Hstk : stk PSEGS mem (sp - 8192) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (rg_ok_rw_byte PSEGS E _ R0 HR0 Hwk0 (o0 + (a - (sp - 8192))) ltac:(lia)) as [Hr Hw].
    replace (bv_unsigned (lden E (rg_base R0)) + (o0 + (a - (sp - 8192)))) with a in Hr, Hw by lia.
    split; [exact Hw|]. unfold mrd, wa. unfold rd1 in Hr. change (ms_mem ms) with mem in Hr.
    destruct (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom PSEGS (Z_to_bv 64 a) end) as [b|] eqn:He;
      [exists b; reflexivity | exfalso; exact (Hr eq_refl)]. }
  apply (HM fxs regs mem md hs n (getr regs 1) K Hheap Hmd HU H10 Hn eq_refl Hra H3 H4 ltac:(rewrite HSP; exact Hs16)
           ltac:(rewrite HSP; exact Hshi) ltac:(rewrite HSP; exact Htop) ltac:(rewrite HSP; exact Hstk) ltac:(rewrite HSP; exact Hinit)).
  intros fx' regs' m' md' hs' p Hfc Hheap' Hmd' Hvo HU' H10' Hp16 Hadd Hnin Hcs Hmunch Hcells Hstk'.
  rewrite HSP in Hmunch, Hstk'.
  set (ms' := @mkst fx' regs' (getr regs 1) m' rom).
  assert (Hpin : In (p, n) (hi_blocks HI hs')) by (apply Hadd; left; reflexivity).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by (unfold ms', mkst; cbn [ms_pc_val]; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPH = true -> rkey r <> 11%positive \/ None = @None lin ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. unfold ms', mkst; cbn [ms_regs]. exact (keeph_cs regs regs' r Hcs Hr). }
  assert (P3 : forall l, None = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l) by (intros l Hc; discriminate Hc).
  assert (Hout : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                   m' x = mem x).
  { intros i R x Hi Hin Hnf.
    destruct (HIface.outside_dec CELLS_NE (bv_unsigned x)) as [Hc1|Hc1].
    - destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
      + assert (Hc : ioutside (CELLS_NE ++ ERRC) (bv_unsigned x)) by (apply HIface.outside_app; split; assumption).
        apply Hmunch. apply HIface.outside_app. split; [exact (avoid_ownedI E L hs mem md i R x Hav Hheap Hi Hin Hc)|].
        apply HIface.outside_app. split; [exact (avoid_owned HI GP TP IMG_LO IMG_END HTOP STATIC HOK E L hs' m' md' i R x Hav Hheap' Hi Hin Hc)|].
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside]. split; [exact (avoid_block HI GP TP IMG_LO IMG_END HTOP STATIC HOK E L hs' m' md' i R x p n Hav Hheap' Hpin Hi Hin Hc)|]. split; [|exact I].
        intros Hx. apply Hnf. exists i0, o0, 8192, R0. split; [left; reflexivity|]. split; [exact Hi0|]. lia.
      + exfalso. apply Hnf. exists i7, 4, 4, R7. split; [right; left; reflexivity|]. split; [exact Hi7|]. rewrite Hb7.
        cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hcells. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside CELLS_NE] in Hc1.
      destruct (Z_le_gt_dec 0x63da0 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x63da8); [left; lia | | |];
        destruct (Z_le_gt_dec 0x95e40 (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) 0x95e48); try (right; lia);
        exfalso; apply Hc1; repeat split; lia. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) [(i0, o0, 8192); (i7, 4, 4)] x ->
                 ms_mem ms' x = ms_mem ms x) by (intros; unfold ms', mkst; cbn [ms_mem]; eapply Hout; eassumption).
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x ->
                 (rd1 PSEGS (ms_mem ms) x <> None -> rd1 PSEGS (ms_mem ms') x <> None) /\
                 (wview PSEGS (ms_mem ms) x <> None -> wview PSEGS (ms_mem ms') x <> None)).
  { intros i R x Hi Hin. unfold ms', mkst; cbn [ms_mem].
    destruct (HIface.outside_dec ERRC (bv_unsigned x)) as [Hc2|Hc2].
    - destruct (Z_le_gt_dec (sp - 8192) (bv_unsigned x)) as [A|A]; [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [B|B]|].
      + destruct Hstk' as (_ & _ & HS). destruct (HS (bv_unsigned x) ltac:(lia)) as [Hw (b & Hb)]. unfold wa in Hw, Hb.
        rewrite Z_to_bv_bv_unsigned in Hw, Hb. unfold mrd in Hb. unfold rd1. split; intros _; [rewrite Hb; discriminate | exact Hw].
      + unfold rd1, wview. rewrite (Hout i R x Hi Hin); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
      + unfold rd1, wview. rewrite (Hout i R x Hi Hin); [tauto|]. intros (j & o & k & R' & Hj & Hnj & Hx). destruct Hj as [Hj|[Hj|[]]]; injection Hj as <- <- <-.
        * rewrite Hi0 in Hnj. injection Hnj as <-. lia.
        * rewrite Hi7 in Hnj. injection Hnj as <-. rewrite Hb7 in Hx. cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2. lia.
    - (* [comment removed for export] *)
      cbn [OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside ERRC] in Hc2.
      assert (Hx : 0x75b2c <= bv_unsigned x < 0x75b30).
      { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Hc2. split; [exact C | exact I]. }
      assert (HS : seg_rom PSEGS x <> None /\ wview PSEGS (fun _ => None) x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x).
        assert (Q : bv_unsigned x = 0x75b2c \/ bv_unsigned x = 0x75b2d \/ bv_unsigned x = 0x75b2e \/ bv_unsigned x = 0x75b2f) by lia.
        destruct Q as [Q|[Q|[Q|Q]]]; rewrite Q; vm_compute; split; discriminate. }
      destruct HS as [HS1 HS2]. unfold rd1, wview in *. split; intros _; destruct (m' x); [discriminate | exact HS1 | discriminate | exact HS2]. }
  assert (P6 : frm_zero (ms_fcsr ms')) by (unfold ms', mkst; cbn [ms_fcsr]; rewrite Hfc; exact (sden_frm _ _ _ _ Hd)).
  destruct (havoc_call_sound2 PSEGS E L ms ms' (bv_unsigned (getr regs 1)) KEEPH [(i0, o0, 8192); (i7, 4, 4)] None Hok Hd P1 eq_refl eq_refl
              P6 P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' md' hs' p Ha' Hd' ltac:(unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom) Hheap' Hmd' Hvo HU' H10' Hp16 Hadd Hnin).
  - unfold ms', mkst; cbn [ms_mem]. exact Hmunch.
  - exact Hcells.
Qed.
End HeapI.
