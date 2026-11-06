(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvExit UDrvHeap UDrvHeap2 UDrvRead UDrvHeapI UbStartup UbStartupDefs UDirCert UDir ULoopInv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeapI OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.UDirCert OSSVerify.Proofs.fast_float.from_chars.lib.UDir OSSVerify.Proofs.fast_float.from_chars.lib.ULoopInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RSX (x : Z) : Prop := RS_LO <= x < RS_LO + 65536.

Fixpoint bvs_eqb (a b : list bval) : bool :=
  match a, b with [] , [] => true | x :: a', y :: b' => (bval_eqb x y && bvs_eqb a' b')%bool | _, _ => false end.
Lemma bvs_eqb_eq : forall a b, bvs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (bval_eqb_eq _ _ H1), (IH _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition cells_tmpl (L : sst) : bool :=
  (Nat.ltb 8 (length (s_rgs L)) &&
   lin_eqb (rg_base (rgn L 3)) (lconst 0x65a18) && Z.eqb (csz (rgn L 3)) 344 &&
   match rg_kind (rgn L 3) with RO => true | _ => false end &&
   lin_eqb (rg_base (rgn L 8)) (lconst 0x97c00) &&
   match get_bytes (rg_cont (rgn L 8)) 0 8 with Some bvs => bvs_eqb bvs (bvs_of (lvar 5) 8) | None => false end)%bool.

Section HIG.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HTOPB : HTOP <= bv_unsigned sp0 - 65536.
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x99000 <= IMG_END.
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x530c8 8192 0x52f88 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HNL : forall hs m md, hi_Heap HI hs m md -> NL m.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.

Variable HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop.
Variable INIT : hi_HS HI -> list ivl.
Hypothesis HOKI : heap_init_ok PSEGS DCFG HI HeapI INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) HTOP CELLS_NE 0x530c8 8192.
Hypothesis HOWNI : forall hs m md, HeapI hs m md -> forall x, ~ ioutside (hi_owned HI hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).
Hypothesis HERRI : forall hs m m' md, HeapI hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapI hs m' md.
Hypothesis HCELLI : forall hs m m' md, HeapI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapI hs m' md.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).
Local Notation a1s := (nth 1 av []).
(* [comment removed for export] *)
Definition INITO (hs : hi_HS HI) : Prop := forall x, ~ ioutside (INIT hs) x ->
  bv_unsigned sp0 + 24 <= x < 2 ^ 48 /\ (x < bv_unsigned p1 \/ bv_unsigned p1 + Z.of_nat (length a1s) < x).

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma init_out_m2 : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) ->
  bv_unsigned sp0 + 24 <= bv_unsigned x < 2 ^ 48 -> (bv_unsigned x < bv_unsigned p1 \/ bv_unsigned p1 + Z.of_nat (length a1s) < bv_unsigned x) ->
  outside E' rgs x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs Hx1 Hx2. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  unfold outside. apply Forall_forall. intros R HR. apply In_nth_error in HR as (i & Hi).
  pose proof (nth_shape rgs i R Hi) as Hsh. rewrite Hs, shape_m2_eq in Hsh.
  do 22 (destruct i as [|i]; [cbn [nth_error SHAPE_M2] in Hsh; injection Hsh as Hb Hz; unfold rsz; rewrite <- Hb, <- Hz; clear Hb Hz;
    rewrite ?u_lin0 by lia; rewrite ?u_lin1, ?u_lin2; rewrite ?HE by lia;
    change (E 1%positive) with sp0; rewrite ?(E_P1 sp0 av ev tid rdraw regs Hargc2);
    try (change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive); rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2));
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length (nth 1 av [])))) ;
    rewrite ?u_small64 by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia);
    rewrite ?Z.mod_small by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64 in *; lia); lia |]).
  cbn [nth_error SHAPE_M2] in Hsh. destruct i; discriminate Hsh.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI HOKI HOWNI HERRI HCELLI"] Lemma heap_fx_init : forall E1 E2 (S L : sst) ms1 ms2 hs md,
  agree 200 E E1 -> agree 200 E E2 -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  sden PSEGS E1 S ms1 -> sden PSEGS E2 L ms2 -> cells_tmpl S = true -> cells_tmpl L = true ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  HeapI hs (ms_mem ms1) md -> INITO hs -> HeapI hs (ms_mem ms2) md.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI HOKI HOWNI HERRI HCELLI : LiaFast.U) => LiaFast.u0).
  intros E1 E2 S L ms1 ms2 hs md Ha1 Ha2 Hs Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hh Hio.
  apply (heap_seg_init HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC HeapI INIT HOKI HOWNI HERRI HCELLI E1 (s_rgs S) hs (ms_mem ms1) (ms_mem ms2) md Hh).
  - intros x Hx. destruct (Hio _ Hx) as (X1 & X2). exact (init_out_m2 E1 (s_rgs S) x Ha1 Hs X1 X2).
  - exact Hfr.
  - exact Hgr.
  - intros a Ha. rewrite (cells_mrd av rdraw Hargc2 E2 L ms2 Hd2 ltac:(rewrite <- (Ha2 5%positive) by lia; reflexivity) Hc2 a Ha).
    rewrite (cells_mrd av rdraw Hargc2 E1 S ms1 Hd1 ltac:(rewrite <- (Ha1 5%positive) by lia; reflexivity) Hc1 a Ha). reflexivity.
  - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E1 (s_rgs S) Ha1 Hs).
Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2 HOK HOWNI"] Lemma mfxr_munch_init : forall hs hs' m m' md md' (W : list ivl),
  HeapI hs m md -> hi_Heap HI hs' m' md' -> munch (hi_owned HI hs ++ hi_owned HI hs' ++ W) m m' ->
  (forall x, ~ ioutside W x -> HEAPX IMG_LO IMG_END HTOP STATIC x \/ (bv_unsigned sp0 - 65536 <= x < bv_unsigned sp0)) -> MFXR' m -> MFXR' m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 HOK HOWNI : LiaFast.U) => LiaFast.u0).
  intros hs hs' m m' md md' W Hh Hh' Hmu Hw Hm.
  pose proof HOK as (_ & _ & _ & _ & HBLK).
  pose proof (HOWNI hs m md Hh) as Ho. destruct (HBLK hs' m' md' Hh') as (_ & Ho').
  apply (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC m m'); [|exact Hm]. intros x Hx Hr Hs. apply Hmu.
  apply HIface.outside_app. split.
  { destruct (HIface.outside_dec (hi_owned HI hs) (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hx.
    destruct (Ho _ A) as (A1 & A2). split; [lia | exact A2]. }
  apply HIface.outside_app. split.
  { destruct (HIface.outside_dec (hi_owned HI hs') (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hx.
    destruct (Ho' _ A) as (A1 & A2). split; [lia | exact A2]. }
  destruct (HIface.outside_dec W (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. destruct (Hw _ A) as [B|B]; [exact (Hx B) | exact (Hs B)].
Qed.
End HIG.
