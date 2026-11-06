(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StoreOk DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvExit PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs PDirCert PDir PLoopInv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.PDirCert OSSVerify.Proofs.fast_float.from_chars.lib.PDir OSSVerify.Proofs.fast_float.from_chars.lib.PLoopInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma outside_split : forall E rgs x, outside E (firstn 22 rgs) x -> outside E (skipn 22 rgs) x -> outside E rgs x.
Proof. intros E rgs x H1 H2. rewrite <- (firstn_skipn 22 rgs). unfold outside in *. apply Forall_app. split; assumption. Qed.

Lemma in_rg_or_out : forall E R x, in_rg E R x \/ (bv_unsigned x < bv_unsigned (lden E (rg_base R)) \/ bv_unsigned (lden E (rg_base R)) + rsz E R <= bv_unsigned x).
Proof. intros E R x. unfold in_rg. lia. Qed.

Section HeapG.
Variable HI : heap_iface.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HOK : heap_ok PSEGS DCFG HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.

(* [comment removed for export] *)
#[using="GP TP IMG_LO IMG_END HTOP STATIC HOK HERR HCELL"] Theorem heap_seg_g : forall E rgs hs m m' md,
  hi_Heap HI hs m md ->
  (forall x, outside E rgs x -> m' x = m x) -> mem_grows m m' ->
  (forall a, ~ ioutside CELLS_NE a -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) ->
  (forall i R x, nth_error rgs i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) ->
     ioutside (hi_owned HI hs) (bv_unsigned x)) ->
  hi_Heap HI hs m' md.
Proof. LiaFast.lf_pins (fun (GP TP IMG_LO IMG_END HTOP STATIC HOK HERR HCELL : LiaFast.U) => LiaFast.u0).
  intros E rgs hs m m' md Hh Hfr Hgr Hcel Hno.
  pose proof HOK as (_ & _ & _ & Hframe & _).
  set (m1 := fun x : word => if cellb (CELLS_NE ++ ERRC) x then m x else m' x).
  set (m2 := fun x : word => if cellb ERRC x then m x else m' x).
  assert (H1 : hi_Heap HI hs m1 md).
  { apply (Hframe hs m m1 md (icompl (hi_owned HI hs)) Hh).
    - intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      assert (Hown : ~ ioutside (hi_owned HI hs) (bv_unsigned x)) by (intros Ho; apply (proj2 (icompl_spec _ _ Rx)) in Ho; exact (Ho Hx)).
      unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x) eqn:Hc; [reflexivity|]. apply cellb_false in Hc.
      destruct (outside_or_in E rgs x) as [Ho|(i & R & Hi & Hin)]; [exact (Hfr x Ho)|].
      exfalso. exact (Hown (Hno i R x Hi Hin Hc)).
    - intros x Hx. unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x); [exact Hx | exact (Hgr x Hx)].
    - intros x Hx. pose proof (icompl_range _ _ Hx) as Rx. exact (proj1 (icompl_spec _ _ Rx) Hx). }
  assert (H2 : hi_Heap HI hs m2 md).
  { apply (HCELL hs m1 m2 md H1).
    - intros x Hx. unfold m1, m2. destruct (cellb ERRC x) eqn:He.
      + apply cellb_true in He. replace (cellb (CELLS_NE ++ ERRC) x) with true; [reflexivity|]. symmetry. apply cellb_true.
        rewrite ioutside_app. tauto.
      + apply cellb_false in He. replace (cellb (CELLS_NE ++ ERRC) x) with false; [reflexivity|]. symmetry. apply cellb_false.
        rewrite ioutside_app. tauto.
    - intros x Hx. unfold m1, m2 in *. destruct (cellb ERRC x) eqn:He.
      + replace (cellb (CELLS_NE ++ ERRC) x) with true in Hx; [exact Hx|]. symmetry. apply cellb_true. apply cellb_true in He.
        rewrite ioutside_app. tauto.
      + destruct (cellb (CELLS_NE ++ ERRC) x); [exact (Hgr x Hx) | exact Hx].
    - intros a Ha0.
      assert (Ha : ~ ioutside CELLS_NE a) by (cbn [ioutside CELLS_NE]; intros (A & B & _); destruct Ha0 as [Q|Q]; [exact (A Q) | exact (B Q)]).
      pose proof (Hcel a Ha) as Hv. unfold mrd in *. unfold m1, m2.
      assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small64; unfold two64; lia).
      assert (He : cellb ERRC (Z_to_bv 64 a) = false).
      { apply cellb_false. cbn [ioutside ERRC]. split; [|exact I]. rewrite Ua. lia. }
      assert (Hce : cellb (CELLS_NE ++ ERRC) (Z_to_bv 64 a) = true).
      { apply cellb_true. rewrite ioutside_app. intros [A _]. apply Ha. rewrite Ua in A. exact A. }
      rewrite He, Hce. exact Hv. }
  apply (HERR hs m2 m' md H2).
  - intros x Hx. unfold m2. destruct (cellb ERRC x) eqn:Hie; [|reflexivity]. apply cellb_true in Hie. exfalso. exact (Hie Hx).
  - intros x Hx. unfold m2 in Hx. destruct (cellb ERRC x); [exact (Hgr x Hx) | exact Hx].
Qed.

(* [comment removed for export] *)
#[using="GP TP IMG_LO IMG_END HTOP STATIC HOK"] Lemma block_not_owned : forall hs m md p n x, hi_Heap HI hs m md -> In (p, n) (hi_blocks HI hs) -> p <= x < p + n ->
  ioutside (hi_owned HI hs) x.
Proof. LiaFast.lf_pins (fun (GP TP IMG_LO IMG_END HTOP STATIC HOK : LiaFast.U) => LiaFast.u0).
  intros hs m md p n x Hh Hb Hx. pose proof HOK as (_ & _ & _ & _ & Hblk).
  destruct (Hblk hs m md Hh) as (Hbl & _). destruct (Hbl p n Hb) as (_ & _ & _ & Hd & _).
  exact (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.disjoint_outside _ p n x Hd Hx).
Qed.

(* [comment removed for export] *)
#[using="GP TP STATIC HOK"] Lemma block_heapx : forall hs m md p n x, hi_Heap HI hs m md -> In (p, n) (hi_blocks HI hs) -> p <= x < p + n ->
  x < HTOP /\ (x < IMG_LO \/ IMG_END <= x).
Proof. LiaFast.lf_pins (fun (GP TP STATIC HOK : LiaFast.U) => LiaFast.u0).
  intros hs m md p n x Hh Hb Hx. pose proof HOK as ((B1 & B2) & _ & _ & _ & Hblk).
  destruct (Hblk hs m md Hh) as (Hbl & _). destruct (Hbl p n Hb) as (_ & Hr & _). lia.
Qed.

(* [comment removed for export] *)
#[using="GP TP HOK"] Lemma not_owned_split : forall E rgs hs m md,
  hi_Heap HI hs m md ->
  avoid_heap3 IMG_LO IMG_END HTOP STATIC E (firstn 22 rgs) ->
  (forall R x, In R (skipn 22 rgs) -> in_rg E R x -> exists p n, In (p, n) (hi_blocks HI hs) /\ p <= bv_unsigned x < p + n) ->
  forall i R x, nth_error rgs i = Some R -> in_rg E R x -> ioutside (CELLS_NE ++ ERRC) (bv_unsigned x) ->
     ioutside (hi_owned HI hs) (bv_unsigned x).
Proof. LiaFast.lf_pins (fun (GP TP HOK : LiaFast.U) => LiaFast.u0).
  intros E rgs hs m md Hh Hav Hx i R x Hi Hin Hc.
  destruct (Nat.lt_ge_cases i 22) as [Hl|Hl].
  - assert (Hi' : nth_error (firstn 22 rgs) i = Some R) by (rewrite nth_error_firstn; destruct (Nat.ltb_spec i 22); [exact Hi | lia]).
    apply (avoid_owned HI GP TP IMG_LO IMG_END HTOP STATIC HOK E (with_rgs (SST 0 TEmpty [] [] 1 RNone) (firstn 22 rgs)) hs m md i R x Hav Hh Hi' Hin Hc).
  - assert (Hi' : nth_error (skipn 22 rgs) (i - 22) = Some R) by (rewrite nth_error_skipn; replace (22 + (i - 22))%nat with i by lia; exact Hi).
    destruct (Hx R x (nth_error_In _ _ Hi') Hin) as (p & n & Hb & Hpx).
    exact (block_not_owned hs m md p n _ Hh Hb Hpx).
Qed.
End HeapG.

Section LI2.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HTOPB : HTOP <= bv_unsigned sp0 - 65536.
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x97000 <= IMG_END.
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).

(* [comment removed for export] *)
Definition XBLK (E1 : valu) (rgs : list region) (hs : hi_HS HI) : Prop :=
  forall R x, In R (skipn 22 rgs) -> in_rg E1 R x -> exists p n, In (p, n) (hi_blocks HI hs) /\ p <= bv_unsigned x < p + n.

Definition shape21 (rgs : list region) : Prop := shape (firstn 22 rgs) = shape (s_rgs P_main2).

#[using="HOK"] Lemma outside_g : forall E' (S : sst) hs m md x, agree 200 E E' -> shape21 (s_rgs S) -> XBLK E' (s_rgs S) hs -> hi_Heap HI hs m md ->
  outside E (s_rgs P_main2) x -> ~ HEAPX IMG_LO IMG_END HTOP STATIC (bv_unsigned x) -> outside E' (s_rgs S) x.
Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
  intros E' S hs m md x Ha Hs Hx Hh Ho Hn. apply outside_split.
  - exact (outside_m2 sp0 av ev tid rdraw regs E' (with_rgs S (firstn 22 (s_rgs S))) x Ha Hs Ho).
  - unfold outside. apply Forall_forall. intros R HR. destruct (in_rg_or_out E' R x) as [Hin|Hout]; [|exact Hout].
    exfalso. destruct (Hx R x HR Hin) as (p & n & Hb & Hpx).
    destruct (block_heapx HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK hs m md p n _ Hh Hb Hpx) as [A B].
    apply Hn. unfold HEAPX. split; [exact A | right; exact B].
Qed.

#[using="HOK"] Lemma mfxr_fx_g : forall E' (S : sst) hs m0 md m m', agree 200 E E' -> shape21 (s_rgs S) -> XBLK E' (s_rgs S) hs -> hi_Heap HI hs m0 md ->
  (forall x, outside E' (s_rgs S) x -> m' x = m x) -> MFXR' m -> MFXR' m'.
Proof. LiaFast.lf_pins (fun (HOK : LiaFast.U) => LiaFast.u0).
  intros E' S hs m0 md m m' Ha Hs Hx Hh Hfr Hm x Ho Hn Hr. rewrite Hfr; [exact (Hm x Ho Hn Hr)|].
  exact (outside_g E' S hs m0 md x Ha Hs Hx Hh Ho Hn).
Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma heap_fx_g : forall E1 E2 (S L : sst) ms1 ms2 hs md,
  agree 200 E E1 -> agree 200 E E2 -> shape21 (s_rgs S) -> XBLK E1 (s_rgs S) hs ->
  sden PSEGS E1 S ms1 -> sden PSEGS E2 L ms2 -> cells_tmpl S = true -> cells_tmpl L = true ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  hi_Heap HI hs (ms_mem ms1) md -> hi_Heap HI hs (ms_mem ms2) md.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 E2 S L ms1 ms2 hs md Ha1 Ha2 Hs Hx Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hh.
  apply (heap_seg_g HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK HERR HCELL E1 (s_rgs S) hs (ms_mem ms1) (ms_mem ms2) md Hh Hfr Hgr).
  - intros a Ha. rewrite (cells_mrd av rdraw Hargc2 E2 L ms2 Hd2 ltac:(rewrite <- (Ha2 5%positive) by lia; reflexivity) Hc2 a Ha).
    rewrite (cells_mrd av rdraw Hargc2 E1 S ms1 Hd1 ltac:(rewrite <- (Ha1 5%positive) by lia; reflexivity) Hc1 a Ha). reflexivity.
  - apply (not_owned_split HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK E1 (s_rgs S) hs (ms_mem ms1) md Hh); [|exact Hx].
    exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E1 (firstn 22 (s_rgs S)) Ha1 Hs).
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HSTATI"] Lemma blk_keep_g : forall E1 (S : sst) m m' hs md p n a, agree 200 E E1 -> shape21 (s_rgs S) -> hi_Heap HI hs m md ->
  In (p, n) (hi_blocks HI hs) -> p <= a < p + n -> outside E1 (skipn 22 (s_rgs S)) (Z_to_bv 64 a) ->
  (forall x, outside E1 (s_rgs S) x -> m' x = m x) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 S m m' hs md p n a Ha1 Hs Hh Hb Hpa Hx Hfr. apply Hfr. apply outside_split; [|exact Hx].
  pose proof HOK as ((B1 & B2) & _ & _ & _ & Hblk). destruct (Hblk hs m md Hh) as (Hbl & _). destruct (Hbl p n Hb) as (_ & Hr & _).
  apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK E1 (firstn 22 (s_rgs S)) hs m md p n); [| exact Hh | exact Hb |].
  - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E1 (firstn 22 (s_rgs S)) Ha1 Hs).
  - pose proof (sp0_hi sp0 Hsp). rewrite u_small64 by (unfold two64; lia). lia.
Qed.
End LI2.
