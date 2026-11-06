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
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvData UDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UOpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require UDrvExit UDrvHeap UDrvHeap2 UDrvRead UbStartup UbStartupDefs UDirCert UDir.
Import OSSVerify.Proofs.fast_float.from_chars.lib.UDrvData OSSVerify.Proofs.fast_float.from_chars.lib.UDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.UOpenCert.UDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.UDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.UDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.UbStartup OSSVerify.Proofs.fast_float.from_chars.lib.UbStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.UDirCert OSSVerify.Proofs.fast_float.from_chars.lib.UDir.
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

Section LI.
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

Let E := E_main sp0 av ev tid (canary rdraw) regs.

#[using="Hsp"] Lemma SLf : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_lo sp0 Hsp). Qed.
#[using="Hsp"] Lemma SHf : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_hi sp0 Hsp). Qed.

(* [comment removed for export] *)
Definition MFXR (m : word -> option byte) : Prop :=
  forall x, outside E (s_rgs P_main2) x -> ~ HEAPX IMG_LO IMG_END HTOP STATIC (bv_unsigned x) -> ~ RSX (bv_unsigned x) -> m x = mem x.

#[using="Type"] Lemma mfxr_of_mf : forall m, (forall x, outside E (s_rgs P_main2) x -> m x = mem x) -> MFXR m.
Proof. LiaFast.lf_pins LiaFast.u0. intros m H x Hx _ _. exact (H x Hx). Qed.

#[using="Type"] Lemma outside_m2 : forall E' (S : sst) x, agree 200 E E' -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  outside E (s_rgs P_main2) x -> outside E' (s_rgs S) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E' S x Ha Hs Hx. apply (outside_agree 200 E E' _ x bases_main2 Ha) in Hx.
  exact (outside_shape E' (s_rgs P_main2) (s_rgs S) x Hs Hx).
Qed.

#[using="Type"] Lemma mfxr_fx : forall E' (S : sst) m m', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  (forall x, outside E' (s_rgs S) x -> m' x = m x) -> MFXR m -> MFXR m'.
Proof. LiaFast.lf_pins LiaFast.u0. intros E' S m m' Ha Hs Hfr Hm x Hx Hh Hr. rewrite Hfr; [exact (Hm x Hx Hh Hr)|]. exact (outside_m2 E' S x Ha Hs Hx). Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2"] Lemma mfxr_chg : forall m m', (forall x, ~ HEAPX IMG_LO IMG_END HTOP STATIC (bv_unsigned x) -> ~ RSX (bv_unsigned x) ->
     ~ (bv_unsigned sp0 - 65536 <= bv_unsigned x < bv_unsigned sp0) -> m' x = m x) -> MFXR m -> MFXR m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' Hc Hm x Hx Hh Hr. pose proof SLf. pose proof SHf. rewrite Hc; [exact (Hm x Hx Hh Hr) | exact Hh | exact Hr |].
  pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
  rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
  rewrite u_small64 in X0r by (unfold two64; lia). lia.
Qed.

(* [comment removed for export] *)
Definition SHAPE_M2 : list (lin * lin) := Eval vm_compute in shape (s_rgs P_main2).
#[using="Type"] Lemma shape_m2_eq : shape (s_rgs P_main2) = SHAPE_M2. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma rs_out : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) -> RSX (bv_unsigned x) -> outside E' rgs x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs Hx. pose proof SLf. pose proof SHf. unfold RSX, RS_LO in Hx.
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

#[using="uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI"] Lemma avoid_m2 : forall E' rgs, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E' rgs.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI : LiaFast.U) => LiaFast.u0).
  intros E' rgs Ha Hs i R x Hi Hin Hc.
  apply (avoid_od sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E' (rgs ++ [RPATH]) Ha) with (i := i) (R := R);
    [| | exact Hin | exact Hc].
  - unfold shape. rewrite map_app. change (List.map (fun R0 => (rg_base R0, rg_size R0)) rgs) with (shape rgs). rewrite Hs. vm_compute. reflexivity.
  - rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. rewrite Hi. discriminate.
Qed.

(* [comment removed for export] *)
#[using="av Hargc2 HIMG HOK"] Lemma blk_out : forall E' rgs hs m md p n x, avoid_heap3 IMG_LO IMG_END HTOP STATIC E' rgs -> hi_Heap HI hs m md ->
  In (p, n) (hi_blocks HI hs) -> p <= bv_unsigned x < p + n -> outside E' rgs x.
Proof. LiaFast.lf_pins (fun (av Hargc2 HIMG HOK : LiaFast.U) => LiaFast.u0).
  intros E' rgs hs m md p n x Hav Hh Hb Hx. destruct HIMG as [HI1 HI2].
  pose proof HOK as ((B1 & B2) & _ & _ & _ & Hblk). destruct (Hblk hs m md Hh) as (Hbl & _). destruct (Hbl p n Hb) as (_ & Hr & _).
  unfold outside. apply Forall_forall. intros R HR. apply In_nth_error in HR as (i & Hi).
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E' (rg_base R)))) as [A|A]; [left; exact A|].
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E' (rg_base R)) + rsz E' R)) as [C|C]; [|right; lia].
  exfalso. assert (Hin : in_rg E' R x) by (unfold in_rg; lia).
  destruct (HIface.outside_dec (CELLS_NE ++ ERRC) (bv_unsigned x)) as [Hc|Hc].
  - destruct (Hav i R x Hi Hin Hc) as [H1|(H1 & H2)]; destruct Hr as [Hr|Hr]; lia.
  - apply Hc. cbn [ioutside CELLS_NE ERRC app]. destruct Hr as [Hr|Hr]; repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition CELLV (a : Z) : option byte :=
  if (0x65b58 <=? a) && (a <? 0x65b60) then mrd PSEGS (fun _ => None) (Z_to_bv 64 a)
  else nth_error (Z_to_le_bytes 8 (bv_unsigned (canary rdraw))) (Z.to_nat (a - 0x97c00)).

#[using="av Hargc2"] Lemma cells_mrd : forall E0 L0 ms0, sden PSEGS E0 L0 ms0 -> E0 5%positive = canary rdraw -> cells_tmpl L0 = true ->
  forall a, ~ ioutside CELLS_NE a -> mrd PSEGS (ms_mem ms0) (Z_to_bv 64 a) = CELLV a.
Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E0 L0 ms0 Hd HE5 Hc a Ha. unfold cells_tmpl in Hc.
  apply andb_prop in Hc as [Hc Hg]. apply andb_prop in Hc as [Hc Hb8]. apply andb_prop in Hc as [Hc Hk3].
  apply andb_prop in Hc as [Hc Hz3]. apply andb_prop in Hc as [Hn Hb3].
  apply Nat.ltb_lt in Hn. apply lin_eqb_eq in Hb3, Hb8. apply Z.eqb_eq in Hz3.
  cbn [ioutside CELLS_NE] in Ha.
  assert (Hr : (0x65b58 <= a < 0x65b60) \/ (0x97c00 <= a < 0x97c08)).
  { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Ha. repeat split; lia. }
  unfold CELLV. destruct Hr as [Hr|Hr].
  - replace ((0x65b58 <=? a) && (a <? 0x65b60))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le || apply Z.ltb_lt; lia).
    pose proof (sden_rg _ _ _ _ _ _ Hd (rgn_eq L0 3 ltac:(lia))) as R3. destruct R3 as (_ & _ & A3 & _).
    destruct (rg_kind (rgn L0 3)) eqn:Hk; try discriminate Hk3.
    rewrite Hb3, (rsz_c E0 (rgn L0 3) 344 Hz3 ltac:(lia)) in A3. rewrite u_lconst in A3 by lia. destruct (A3 (a - 0x65a18) ltac:(lia)) as [Z3 Z3'].
    replace (0x65a18 + (a - 0x65a18)) with a in Z3, Z3' by lia. unfold mrd. rewrite Z3. reflexivity.
  - replace ((0x65b58 <=? a) && (a <? 0x65b60))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    destruct (get_bytes (rg_cont (rgn L0 8)) 0 8) as [bvs|] eqn:Hgb; [|discriminate Hg].
    apply bvs_eqb_eq in Hg. subst bvs.
    pose proof (rdn_trk_c E0 L0 ms0 8 0x97c00 0 8 _ Hd ltac:(lia) Hb8 ltac:(lia) ltac:(lia) Hgb) as X.
    rewrite bvs_of_den_lin, lden_lvar, HE5 in X. rewrite Z.add_0_r in X.
    pose proof (rdn_rd1 PSEGS (ms_mem ms0) 0x97c00 8 _ ltac:(lia) ltac:(unfold two64; lia) X (Z.to_nat (a - 0x97c00))) as Y.
    unfold mrd. destruct (nth_error (Z_to_le_bytes 8 (bv_unsigned (canary rdraw))) (Z.to_nat (a - 0x97c00))) as [b|] eqn:Hb'.
    + specialize (Y b eq_refl). rewrite Z2Nat.id in Y by lia. replace (0x97c00 + (a - 0x97c00)) with a in Y by lia. unfold rd1 in Y. exact Y.
    + exfalso. apply nth_error_None in Hb'. rewrite length_Z_to_le_bytes in Hb'. lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma heap_fx : forall E1 E2 (S L : sst) ms1 ms2 hs md,
  agree 200 E E1 -> agree 200 E E2 -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  sden PSEGS E1 S ms1 -> sden PSEGS E2 L ms2 -> cells_tmpl S = true -> cells_tmpl L = true ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  hi_Heap HI hs (ms_mem ms1) md -> hi_Heap HI hs (ms_mem ms2) md.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 E2 S L ms1 ms2 hs md Ha1 Ha2 Hs Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hh.
  apply (heap_seg HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) IMG_LO IMG_END HTOP STATIC HOK HERR HCELL E1 (s_rgs S) hs (ms_mem ms1) (ms_mem ms2) md Hh Hfr Hgr).
  - intros a Ha. rewrite (cells_mrd E2 L ms2 Hd2 ltac:(rewrite <- (Ha2 5%positive) by lia; reflexivity) Hc2 a Ha).
    rewrite (cells_mrd E1 S ms1 Hd1 ltac:(rewrite <- (Ha1 5%positive) by lia; reflexivity) Hc1 a Ha). reflexivity.
  - exact (avoid_m2 E1 (s_rgs S) Ha1 Hs).
Qed.

End LI.
