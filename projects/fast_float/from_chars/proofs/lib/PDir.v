(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SysNodesCfg AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvCall2 PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvHeapI.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeapI.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefMemchr RefStdioDefs RefExitBase RefStartup RefStartupDefs PUsageCert POpenCert POpen1 PDirCert PUsage3 PUsage4 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

Definition PRER : list byte := s2b "cli: read error on "%string.

Section UD.
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
(* [comment removed for export] *)
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HTOPB : HTOP <= bv_unsigned sp0 - 65536.
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x97000 <= IMG_END.
(* [comment removed for export] *)
Definition EXGX : list ivl := [(0x95e38, 0x95e40); (0x60b18, 0x60b20); (0x65058, 0x65059); (0x96290, 0x96298); (0x96280, 0x96288);
  (0x64ff8, 0x65000); (0x64f08, 0x64f10); (0x12fa0, 0x12fc0)].
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).
Local Notation a1s := (nth 1 av []).

#[using="Hsp"] Lemma SLd : 0x7fff80000000 <= bv_unsigned sp0. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_lo sp0 Hsp). Qed.
#[using="Hsp"] Lemma SHd : bv_unsigned sp0 <= 0x800000000000. Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). exact (sp0_hi sp0 Hsp). Qed.

(* [comment removed for export] *)
Definition HEAPX (x : Z) : Prop := x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).

(* [comment removed for export] *)
Definition MFX (m : word -> option byte) : Prop :=
  forall x, outside E (s_rgs P_main2) x -> ~ HEAPX (bv_unsigned x) -> bv_unsigned x <> bv_unsigned p1 -> m x = mem x.

#[using="Type"] Lemma mfx_of_mf : forall m, (forall x, outside E (s_rgs P_main2) x -> m x = mem x) -> MFX m.
Proof. LiaFast.lf_pins LiaFast.u0. intros m H x Hx _ _. exact (H x Hx). Qed.

#[using="sp0 ev uid tid hw rdraw regs mem Hva Hfits Htid ME Hargc2 IMG_LO IMG_END HIMG"] Lemma dot_a1s : path_is_dirref a1s = true -> a1s = [Z_to_bv 8 46].
Proof. LiaFast.lf_pins (fun (sp0 ev uid tid hw rdraw regs mem Hva Hfits Htid ME Hargc2 IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0).
  intros HD. destruct Hva as (_ & _ & _ & _ & Hs). rewrite Forall_forall in Hs.
  destruct av as [|a0 [|a1 [|? ?]]]; cbn in Hargc2; try discriminate. cbn [nth] in *.
  destruct (Hs a1 ltac:(cbn; tauto)) as [_ Hdd]. unfold path_is_dirref in HD. rewrite Hdd, orb_false_r in HD.
  apply path_eqb_eq in HD. exact HD.
Qed.


#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma outside_od : forall E' x, agree 200 E E' -> outside E (s_rgs P_main2) x -> bv_unsigned x <> bv_unsigned p1 ->
  outside E' (s_rgs U_od) x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' x Ha Hx Hp. pose proof SLd. pose proof SHd.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  apply (outside_agree 200 E E' _ x bases_main2 Ha) in Hx.
  apply (outside_shape E' (s_rgs P_main2 ++ [RPATH])); [vm_compute; reflexivity|].
  apply Forall_app. split; [exact Hx|]. constructor; [|constructor].
  unfold RPATH; rsz_simpl; cbn [RGz rg_base rg_size]. unfold P1. rewrite lden_lvar. rewrite <- (Ha 4%positive) by lia.
  change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive). rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2). lia.
Qed.

#[using="uid hw Hsp Hva Hve ME Hargc2"] Lemma mfx_fx : forall E' (S : sst) m m', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs U_od) ->
  (forall x, outside E' (s_rgs S) x -> m' x = m x) -> MFX m -> MFX m'.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' S m m' Ha Hs Hfr Hm x Hx Hh Hp. rewrite Hfr; [exact (Hm x Hx Hh Hp)|].
  apply (outside_shape E' (s_rgs U_od)); [exact Hs|]. exact (outside_od E' x Ha Hx Hp).
Qed.

(* [comment removed for export] *)
#[using="Hsp Hargc2"] Lemma mfx_stack : forall m m' (lo hi : Z), bv_unsigned sp0 - 65536 <= lo -> hi <= bv_unsigned sp0 ->
  (forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> MFX m -> MFX m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' lo hi H1 H2 Hfr Hm x Hx Hh Hp. pose proof SLd. pose proof SHd. rewrite Hfr; [exact (Hm x Hx Hh Hp)|].
  pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
  rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
  rewrite u_small64 in X0r by (unfold two64; lia). lia.
Qed.

#[using="Hsp Hargc2"] Lemma mfx_sw : forall m m' su bufp bufsz, sw_post m su 0x64e20 bufp bufsz m' ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 -> MFX m -> MFX m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' su bufp bufsz Hpost Hs1 Hs2 Hm x Hx Hh Hp. pose proof SLd. pose proof SHd.
  pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
  pose proof (outside_nth_c E _ x 5 (lconst 0x64e20) 232 RI TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X5r. cbn [RGz rg_base] in X5r.
  rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
  rewrite u_small64 in X0r by (unfold two64; lia). rewrite u_lconst in X5r by lia.
  rewrite (swp_agree _ _ _ _ _ _ Hpost x); [exact (Hm x Hx Hh Hp) | lia | lia | lia].
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX"] Lemma exit_glob_of_MFX : forall m, MFX m -> rdn PSEGS m (Z_to_bv 64 0x95e63) 1 = Some [Z_to_bv 8 0] -> exit_glob m.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX : LiaFast.U) => LiaFast.u0).
  intros m Hm Hnl. pose proof SLd as L.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (Hx : forall lo n, In (lo, n) EXG_RANGES -> lo <> 0x95e63 -> rdn PSEGS m (Z_to_bv 64 lo) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 lo) n).
  { intros lo n Hin Hne. pose proof exg_miss as HM. rewrite forallb_forall in HM. pose proof (HM _ Hin) as Hmo. cbv beta in Hmo.
    assert (Hb : 0x10000 <= lo /\ lo + Z.of_nat n <= 0x97000 /\ (forall i, 0 <= i < Z.of_nat n -> ~ ioutside EXGX (lo + i))).
    { unfold EXG_RANGES in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; split; [lia|]; split; [lia|];
        intros i Hi Hc; cbn [ioutside EXGX] in Hc; lia|]). destruct Hin. }
    destruct Hb as (Hb1 & Hb2 & Hb3).
    apply rdn_ext_rd1; [lia | unfold two64; lia |].
    intros i Hi. unfold rd1. rewrite (Hm _ (exg_outside2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 lo n i Hin Hi)).
    - rewrite (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME lo n i) by (lia || exact Hmo). reflexivity.
    - rewrite u_small64 by (unfold two64; lia). intros (Q1 & Q2). pose proof (HSTATX _ (Hb3 i Hi)) as Q3.
      destruct HIMG as [HI1 HI2]. destruct Q2 as [Q2|[Q2|Q2]]; [exact (Q2 Q3) | lia | lia].
    - rewrite u_small64 by (unfold two64; lia). lia. }
  pose proof exit_glob_pristine as P. unfold exit_glob in *.
  rewrite (Hx 0x95e38 4%nat), (Hx 0x60b18 8%nat), (Hx 0x65058 1%nat), (Hx 0x96290 8%nat), (Hx 0x96280 8%nat),
    (Hx 0x64ff8 8%nat), (Hx 0x64f08 8%nat) by (unfold EXG_RANGES; cbn; tauto || lia).
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition NL (m : word -> option byte) : Prop := rdn PSEGS m (Z_to_bv 64 0x95e63) 1 = Some [Z_to_bv 8 0].
Definition INV (m : word -> option byte) : Prop := MFX m /\ NL m.

#[using="av Hargc2"] Lemma nl_same : forall m m', m' (Z_to_bv 64 0x95e63) = m (Z_to_bv 64 0x95e63) -> NL m -> NL m'.
Proof. LiaFast.lf_pins (fun (av Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' He H. unfold NL in *. rewrite <- H. apply (rdn_ext_rd1 PSEGS m' m 0x95e63 1); [lia | unfold two64; lia |].
  intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold rd1. rewrite He. reflexivity.
Qed.

#[using="uid hw mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HIMG"] Lemma nl_outside : forall E', agree 200 E E' -> outside E' (s_rgs U_od) (Z_to_bv 64 0x95e63).
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0).
  intros E' Ha. pose proof SLd. pose proof SHd.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  apply (outside_od E' _ Ha); [| rewrite u_small64 by (unfold two64; lia); lia].
  pose proof (exg_outside2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 0x95e63 1 0 ltac:(unfold EXG_RANGES; cbn; tauto) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG"] Lemma inv_fx : forall E' (S : sst) m m', agree 200 E E' -> shape (s_rgs S) = shape (s_rgs U_od) ->
  (forall x, outside E' (s_rgs S) x -> m' x = m x) -> INV m -> INV m'.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG : LiaFast.U) => LiaFast.u0).
  intros E' S m m' Ha Hs Hfr [Hm Hn]. split; [exact (mfx_fx E' S m m' Ha Hs Hfr Hm)|].
  apply (nl_same m m'); [|exact Hn]. apply Hfr. apply (outside_shape E' (s_rgs U_od)); [exact Hs|]. exact (nl_outside E' Ha).
Qed.

#[using="Hsp Hargc2"] Lemma inv_stack : forall m m' (lo hi : Z), bv_unsigned sp0 - 65536 <= lo -> hi <= bv_unsigned sp0 ->
  (forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> INV m -> INV m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' lo hi H1 H2 Hfr [Hm Hn]. pose proof SLd. split; [exact (mfx_stack m m' lo hi H1 H2 Hfr Hm)|].
  apply (nl_same m m'); [|exact Hn]. apply Hfr. rewrite u_small64 by (unfold two64; lia). lia.
Qed.

#[using="Hsp Hargc2"] Lemma inv_sw : forall m m' su bufp bufsz, sw_post m su 0x64e20 bufp bufsz m' ->
  bv_unsigned sp0 - 65536 <= su - 112 -> su <= bv_unsigned sp0 -> INV m -> INV m'.
Proof. LiaFast.lf_pins (fun (Hsp Hargc2 : LiaFast.U) => LiaFast.u0).
  intros m m' su bufp bufsz Hpost Hs1 Hs2 [Hm Hn]. pose proof SLd. split; [exact (mfx_sw m m' su bufp bufsz Hpost Hs1 Hs2 Hm)|].
  apply (nl_same m m'); [|exact Hn]. apply (swp_agree _ _ _ _ _ _ Hpost); rewrite u_small64 by (unfold two64; lia); lia.
Qed.

#[using="Hargc2"] Lemma agree_nx : forall E1 E2 (L : sst), agree 200 E E1 -> (200 <= s_next L)%positive -> agree (s_next L) E1 E2 -> agree 200 E E2.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E1 E2 L H1 Hn H2 x Hx. rewrite (H1 x Hx). apply H2. lia. Qed.

#[using="Hargc2"] Lemma lden_sp0d : forall E' c, (forall x, (x < 200)%positive -> E' x = E x) -> -65536 <= c <= 0 ->
  lden E' (laddc SP0 c) = Z_to_bv 64 (bv_unsigned sp0 + c).
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E' c HE Hc. rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE by lia. reflexivity. Qed.


(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 HTOPB HIMG HSTATX"] Lemma dir_G : forall md E6 ms6 T, m_halted md = None -> m_vm_lazy md = [] -> path_is_dirref a1s = true -> agree 200 E E6 -> sden PSEGS E6 U_d3 ms6 -> ms_rom ms6 = seg_rom PSEGS ->
  INV (ms_mem ms6) ->
  (forall E8 ms8, agree 200 E E8 -> sden PSEGS E8 U_d4 ms8 -> ms_rom ms8 = seg_rom PSEGS -> INV (ms_mem ms8) -> realizes PSEGS (mkCfg ms8 md) T) ->
  realizes PSEGS (mkCfg ms6 md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 HTOPB HIMG HSTATX : LiaFast.U) => LiaFast.u0).
  intros md E6 ms6 T Hhd Hld HDR Ha6 Hd6 Hrom6 HI6 KB.
  pose proof (dot_a1s HDR) as HA1.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_d3 LD3 E6 ms6 md T TBL_P_ok IMG_P_ok cert_LD3 Hd6 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E1 ms1 HIn Hd1 Ha1' Hrom1 Hfr1' Hgr1. rewrite LD3_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha1 : agree 200 E E1) by exact (agree_nx E6 E1 U_d3 Ha6 ltac:(vm_compute; congruence) Ha1').
  assert (HI1 : INV (ms_mem ms1)) by exact (inv_fx E6 U_d3 _ _ Ha6 ltac:(vm_compute; reflexivity) Hfr1' HI6).
  rewrite Hrom6 in Hrom1.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  pose proof SLd as SL. pose proof SHd as SH.
  destruct (argv1_window sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (buf & Hbuf & Hpre & Hwin & Hbnd).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 0x54ab0) by (apply (getr_leaf_c PSEGS E1 Ld3); [exact Hd1 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms1) 2 = Z_to_bv 64 (bv_unsigned sp0 - 1120)).
  { rewrite (getr_leaf PSEGS E1 Ld3 ms1 2 (laddc SP0 (-1120)) Hd1) by (vm_compute; reflexivity). apply lden_sp0d; [exact HE1 | lia]. }
  assert (R10 : getr (ms_regs ms1) 10 = p1).
  { rewrite (getr_leaf PSEGS E1 Ld3 ms1 10 (lvar 4) Hd1) by (vm_compute; reflexivity). rewrite lden_lvar, HE1 by lia. exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
  assert (R11 : getr (ms_regs ms1) 11 = Z_to_bv 64 0x7fffffff) by (apply (getr_leaf_c PSEGS E1 Ld3); [exact Hd1 | vm_compute; reflexivity]).
  set (K := length (nth 1 av [])).
  assert (HK1 : K = 1%nat) by (unfold K; rewrite HA1; reflexivity).
  assert (HL : (S K <= length buf)%nat).
  { pose proof (f_equal (@length byte) Hpre) as Q. rewrite length_firstn, length_app in Q. cbn [length] in Q. unfold K1 in Q. fold K in Q. lia. }
  assert (HAg : agree 200 E1 E) by (intros x Hx; exact (HE1 x Hx)).
  (* [comment removed for export] *)
  assert (Hbuf1 : rdn PSEGS (ms_mem ms1) p1 (length buf) = Some buf).
  { rewrite <- Hbuf. pose proof (rdn_ext_rd1 PSEGS (ms_mem ms1) mem (bv_unsigned p1) (length buf)) as RX.
    rewrite Z_to_bv_bv_unsigned in RX. apply RX; [lia | unfold two64; lia |]. clear RX.
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hn0]; [|destruct (Z.eq_dec i 1) as [->|Hn1]].
    - assert (NB : nth_error buf 0 = Some (Z_to_bv 8 46)).
      { rewrite <- (firstn_skipn (S K) buf). rewrite nth_error_app1 by (rewrite length_firstn; lia).
        unfold K1 in Hpre. fold K in Hpre. rewrite Hpre, HA1. reflexivity. }
      pose proof (rdn_rd1 PSEGS mem (bv_unsigned p1) (length buf) buf ltac:(lia) ltac:(unfold two64; lia)
                    ltac:(rewrite Z_to_bv_bv_unsigned; exact Hbuf) 0 _ NB) as N1.
      assert (HR21 : nth_error (s_rgs Ld3) 22 = Some (RGz P1 1 RW (put_bytes TEmpty 0 [BK 46]))) by (vm_compute; reflexivity).
      pose proof (sden_tracked PSEGS E1 Ld3 ms1 22 _ 0 (BK 46) Hd1 HR21 ltac:(lia) ltac:(vm_compute; reflexivity)) as N2.
      cbn [RGz rg_base bden] in N2. rewrite Z.add_0_r in N2.
      assert (HW : lwf 200 P1 = true) by (vm_compute; reflexivity).
      rewrite (lden_agree 200 E1 E _ HW HAg) in N2. unfold P1 in N2. rewrite lden_lvar in N2.
      change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive) in N2. rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2) in N2.
      rewrite Z.add_0_r in N1 |- *. rewrite N1, N2. reflexivity.
    - assert (NB : nth_error buf 1 = Some (Z_to_bv 8 0)).
      { rewrite <- (firstn_skipn (S K) buf). rewrite nth_error_app1 by (rewrite length_firstn; lia).
        unfold K1 in Hpre. fold K in Hpre. rewrite Hpre, HA1. reflexivity. }
      pose proof (rdn_rd1 PSEGS mem (bv_unsigned p1) (length buf) buf ltac:(lia) ltac:(unfold two64; lia)
                    ltac:(rewrite Z_to_bv_bv_unsigned; exact Hbuf) 1 _ NB) as N1.
      assert (HR2 : nth_error (s_rgs Ld3) 2 = Some (RGz (ladd P1 X1) 1 RW (put_bytes TEmpty 0 [BK 0]))) by (vm_compute; reflexivity).
      pose proof (sden_tracked PSEGS E1 Ld3 ms1 2 _ 0 (BK 0) Hd1 HR2 ltac:(lia) ltac:(vm_compute; reflexivity)) as N2.
      cbn [RGz rg_base bden] in N2. rewrite Z.add_0_r in N2.
      assert (HW : lwf 200 (ladd P1 X1) = true) by (vm_compute; reflexivity).
      rewrite (lden_agree 200 E1 E _ HW HAg) in N2.
      pose proof (u_P1X1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as U. fold E in U. rewrite U in N2. fold K in N2. rewrite HK1 in N2.
      change (Z.of_nat 1) with 1 in N1, N2. rewrite N1, N2. reflexivity.
    - unfold rd1. destruct HI1 as [Hm1 _]. rewrite Hm1; [reflexivity | | | ].
      + apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2).
        * rewrite u_small64 by (unfold two64; lia). lia.
        * rewrite u_small64 by (unfold two64; lia). fold K. rewrite HK1. cbn. lia.
      + rewrite u_small64 by (unfold two64; lia). intros (Q & _). lia.
      + rewrite u_small64 by (unfold two64; lia). lia. }
  assert (MC : mchrH (ms_mem ms1) p1 buf (Z.of_nat K) 0x7fffffff).
  { constructor.
    - exact Hbuf1.
    - unfold K1 in Hwin. fold K in Hwin. lia.
    - lia.
    - lia.
    - rewrite Nat2Z.id. rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
      unfold K1 in Hpre. fold K in Hpre. rewrite Hpre. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - intros j Hj. rewrite Nat2Z.id, HK1 in Hj. replace j with 0%nat by lia.
      rewrite <- (firstn_skipn (S K) buf). rewrite app_nth1 by (rewrite length_firstn; lia).
      unfold K1 in Hpre. fold K in Hpre. rewrite Hpre, HA1. cbn. discriminate.
    - lia.
    - lia.
    - intros i Hi. destruct HI1 as [Hm1 _]. rewrite Hm1; [exact (rodata_clear_main2 sp0 av ev uid tid hw rdraw regs mem Hsp ME Hargc2 i Hi) | | |].
      + apply (outside_main2_rodata sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2). rewrite u_small64 by (unfold two64; lia). lia.
      + rewrite u_small64 by (unfold two64; lia). intros (Q1 & Q2). destruct HIMG as [HI1' HI2'].
        assert (Q3 : ioutside STATIC i) by (apply HSTATX; cbn [ioutside EXGX]; intros (_ & _ & _ & _ & _ & _ & _ & A & _); lia).
        destruct Q2 as [Q2|[Q2|Q2]]; [exact (Q2 Q3) | lia | lia].
      + rewrite u_small64 by (unfold two64; lia). lia. }
  assert (HOK : havoc_ok Ld3 [(0%nat, 64384, 32)] (Some X1) = true) by (vm_compute; reflexivity).
  assert (FRM : frame_in E1 Ld3 0 64384 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 1120)) - 32)).
  { rewrite u_small64 by (unfold two64; lia).
    apply (frame_sp sp0 SL SH E1 Ld3 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  apply (fx_strnlen E1 Ld3 ms1 md T p1 (Z_to_bv 64 (bv_unsigned sp0 - 1120)) (Z_to_bv 64 0x54ab0) buf (Z.of_nat K) 0x7fffffff 0 64384 X1
           Hd1 eq_refl eq_refl HOK FRM R1 R2 R10 R11 MC); [lia | rewrite u_small64 by (unfold two64; lia); lia
           | right; rewrite u_small64 by (unfold two64; lia); lia | vm_compute; reflexivity
           | unfold X1; rewrite lden_lvar, HE1 by lia; reflexivity | exact Hhd | exact Hld |].
  intros E' ms' Ha' Hd' Hfm Hrom'.
  apply (KB E' ms').
  - exact (agree_nx E1 E' Ld3 Ha1 ltac:(vm_compute; congruence) Ha').
  - replace (bv_unsigned (Z_to_bv 64 0x54ab0)) with 0x54ab0 in Hd' by (vm_compute; reflexivity). rewrite U_d4_eq in Hd'. exact Hd'.
  - rewrite Hrom'. exact Hrom1.
  - destruct Hfm as [Hout _]. apply (inv_stack (ms_mem ms1) (ms_mem ms') (bv_unsigned sp0 - 1152) (bv_unsigned sp0 - 1120)); [lia | lia | | exact HI1].
    intros x Hx. apply Hout. split; [|exact I]. unfold in_rng. intros Hin.
    rewrite (u_small64 (bv_unsigned sp0 - 1120)) in Hin by (unfold two64; lia).
    rewrite (u_small64 (bv_unsigned sp0 - 1120 - 32)) in Hin by (unfold two64; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 HIMG"] Lemma dir_H : forall md E8 ms8 T, m_halted md = None -> m_vm_lazy md = [] -> path_is_dirref a1s = true -> agree 200 E E8 -> sden PSEGS E8 U_d4 ms8 -> ms_rom ms8 = seg_rom PSEGS ->
  INV (ms_mem ms8) ->
  (forall E9 ms9, agree 200 E E9 -> sden PSEGS E9 U_d5t ms9 -> ms_rom ms9 = seg_rom PSEGS -> INV (ms_mem ms9) -> realizes PSEGS (mkCfg ms9 md) T) ->
  realizes PSEGS (mkCfg ms8 md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 HIMG : LiaFast.U) => LiaFast.u0).
  intros md E8 ms8 T Hhd Hld HDR Ha8 Hd8 Hrom8 HI8 KJ.
  pose proof (dot_a1s HDR) as HA1. pose proof SLd as SL. pose proof SHd as SH.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S2 U_d4 LD4 E8 ms8 md T TBL_P_ok IMG_P_ok cert_LD4 Hd8 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E1 ms1 HIn Hd1 Ha1' Hrom1 Hfr1 _. rewrite LD4_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha1 : agree 200 E E1) by exact (agree_nx E8 E1 U_d4 Ha8 ltac:(vm_compute; congruence) Ha1').
  assert (HI1 : INV (ms_mem ms1)) by exact (inv_fx E8 U_d4 _ _ Ha8 ltac:(vm_compute; reflexivity) Hfr1 HI8).
  rewrite Hrom8 in Hrom1.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S2 Ld4 LD4b E1 ms1 md T TBL_P_ok IMG_P_ok cert_LD4b Hd1 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E2 ms2 HIn Hd2 Ha2' Hrom2 Hfr2 _. rewrite LD4b_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha2 : agree 200 E E2) by exact (agree_nx E1 E2 Ld4 Ha1 ltac:(vm_compute; congruence) Ha2').
  assert (HI2 : INV (ms_mem ms2)) by exact (inv_fx E1 Ld4 _ _ Ha1 ltac:(vm_compute; reflexivity) Hfr2 HI1).
  rewrite Hrom1 in Hrom2.
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
  assert (HP2 : lden E2 P1 = p1).
  { unfold P1. rewrite lden_lvar, HE2 by lia. exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x53e98) by (apply (getr_leaf_c PSEGS E2 Ld4b); [exact Hd2 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (bv_unsigned sp0 - 541)).
  { rewrite (getr_leaf PSEGS E2 Ld4b ms2 10 (laddc SP0 (-541)) Hd2) by (vm_compute; reflexivity). apply lden_sp0d; [exact HE2 | lia]. }
  assert (R11 : getr (ms_regs ms2) 11 = p1) by (rewrite (getr_leaf PSEGS E2 Ld4b ms2 11 P1 Hd2) by (vm_compute; reflexivity); exact HP2).
  assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 1).
  { rewrite (getr_leaf PSEGS E2 Ld4b ms2 12 X1 Hd2) by (vm_compute; reflexivity). unfold X1. rewrite lden_lvar, HE2 by lia.
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))). rewrite HA1. reflexivity. }
  (* [comment removed for export] *)
  assert (BSRC : bytes_at PSEGS (ms_mem ms2) (bv_unsigned p1) [Z_to_bv 8 46]).
  { apply bytes_at_of_rdn; [lia | cbn; unfold two64; lia |].
    pose proof (sden_rg _ _ _ _ _ _ Hd2 (rgn_eq Ld4b 22 ltac:(vm_compute; lia))) as HR.
    pose proof (rg_rdn_gb PSEGS E2 _ _ 0 1 [BK 46] HR ltac:(lia) ltac:(vm_compute; reflexivity)) as X.
    replace (rg_base (rgn Ld4b 22)) with P1 in X by (vm_compute; reflexivity). rewrite HP2, Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  destruct (u8arr_of_rg E2 Ld4b ms2 0 (rgn Ld4b 0) 64995 1 Hd2 (rgn_eq Ld4b 0 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)
              ltac:(vm_compute; congruence)) as (old & Hlold & Hu8).
  replace (rg_base (rgn Ld4b 0)) with (laddc SP0 (-65536)) in Hu8 by (vm_compute; reflexivity).
  rewrite lden_laddc, HS2, u_small64 in Hu8 by (unfold two64; lia).
  replace (bv_unsigned sp0 + -65536 + 64995) with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 541))) in Hu8 by (rewrite u_small64 by (unfold two64; lia); lia).
  apply (fx_memcpy E2 Ld4b ms2 md T (Z_to_bv 64 (bv_unsigned sp0 - 541)) p1 1 [Z_to_bv 8 46] old [(0%nat, 64995, 1)] (laddc SP0 (-541))
           Hd2 eq_refl eq_refl hok_d5 Hrom2 R10 R11 R12 ltac:(rewrite R1; vm_compute; reflexivity) BSRC Hu8 Hlold eq_refl).
  - rewrite u_small64 by (unfold two64; lia). left. lia.
  - rewrite u_small64 by (unfold two64; lia). lia.
  - lia.
  - apply lden_sp0d; [exact HE2 | lia].
  - intros i R x Hi Hin Hx. exists 0%nat, 64995, 1, (rgn Ld4b 0). split; [left; reflexivity|]. split; [exact (rgn_eq Ld4b 0 ltac:(vm_compute; lia))|].
    replace (rg_base (rgn Ld4b 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
    rewrite lden_laddc, HS2, u_small64 by (unfold two64; lia). rewrite u_small64 in Hx by (unfold two64; lia). lia.
  - exact Hhd.
  - exact Hld.
  - intros E' ms' Ha' Hd' Hout Hgrow Hbs Hrom'.
    rewrite R1 in Hd'. replace (bv_unsigned (Z_to_bv 64 0x53e98)) with 0x53e98 in Hd' by (vm_compute; reflexivity). rewrite U_d5_eq in Hd'.
    assert (Ha3 : agree 200 E E') by exact (agree_nx E2 E' Ld4b Ha2 ltac:(vm_compute; congruence) Ha').
    assert (HE3 : forall x, (x < 200)%positive -> E' x = E x) by (intros x Hx; symmetry; exact (Ha3 x Hx)).
    apply (KJ E' ms' Ha3).
    + rewrite <- U_d5t_eq. apply (fx_upd_rg PSEGS E' U_d5 ms' 0 (rgn U_d5 0) (track (rgn U_d5 0) 64995 [BK 46]) Hd' (rgn_eq U_d5 0 ltac:(vm_compute; lia)) eq_refl eq_refl).
      * pose proof (sden_rg _ _ _ _ _ _ Hd' (rgn_eq U_d5 0 ltac:(vm_compute; lia))) as HR0.
        apply (rg_track_rdn PSEGS E' _ _ 64995 [BK 46] HR0 ltac:(lia) ltac:(vm_compute; congruence)).
        replace (rg_base (rgn U_d5 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
        rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. change (E 1%positive) with sp0.
        rewrite u_small64 by (unfold two64; lia). cbn [length map bden].
        pose proof (rdn_of_bytes_at _ _ _ Hbs) as X. rewrite u_small64 in X by (unfold two64; lia).
        replace (bv_unsigned sp0 + -65536 + 64995) with (bv_unsigned sp0 - 541) by lia. exact X.
      * exact wf_d5t.
    + rewrite Hrom'. exact Hrom2.
    + apply (inv_stack (ms_mem ms2) (ms_mem ms') (bv_unsigned sp0 - 541) (bv_unsigned sp0 - 540)); [lia | lia | | exact HI2].
      intros x Hx. apply Hout. rewrite u_small64 by (unfold two64; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG"] Lemma dir_J : forall md E8 ms8 T, m_halted md = None -> m_vm_lazy md = [] -> agree 200 E E8 -> sden PSEGS E8 U_d5t ms8 -> ms_rom ms8 = seg_rom PSEGS ->
  INV (ms_mem ms8) ->
  (forall E9 ms9, agree 200 E E9 -> sden PSEGS E9 U_d5b ms9 -> ms_rom ms9 = seg_rom PSEGS -> INV (ms_mem ms9) -> realizes PSEGS (mkCfg ms9 md) T) ->
  realizes PSEGS (mkCfg ms8 md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG : LiaFast.U) => LiaFast.u0).
  intros md E8 ms8 T Hhd Hld Ha8 Hd8 Hrom8 HI8 KJ.
  pose proof SLd as SL. pose proof SHd as SH.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S2 U_d5t LD5 E8 ms8 md T TBL_P_ok IMG_P_ok cert_LD5 Hd8 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E2 ms2 HIn Hd2 Ha2' Hrom2 Hfr2 _. rewrite LD5_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha2 : agree 200 E E2) by exact (agree_nx E8 E2 U_d5t Ha8 ltac:(vm_compute; congruence) Ha2').
  assert (HI2 : INV (ms_mem ms2)) by exact (inv_fx E8 U_d5t _ _ Ha8 ltac:(vm_compute; reflexivity) Hfr2 HI8).
  rewrite Hrom8 in Hrom2.
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x53e98) by (apply (getr_leaf_c PSEGS E2 Ld5a); [exact Hd2 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (bv_unsigned sp0 - 540)).
  { rewrite (getr_leaf PSEGS E2 Ld5a ms2 10 (LIN 18446744073709551075 [(1%positive, 1); (8%positive, 1)]) Hd2) by (vm_compute; reflexivity).
    apply bv_eq. rewrite u_lin2, HE2, HE2 by lia. change (E 1%positive) with sp0.
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))).
    rewrite (u_small64 (Z.of_nat (length a1s))) by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia).
    rewrite u_small64 by (unfold two64; lia).
    assert (HL1 : length a1s = 1%nat).
    { assert (Hf : In (FRange X1 1 1) (s_facts Ld5a)) by (vm_compute; tauto).
      pose proof (sden_fact PSEGS E2 Ld5a ms2 _ Hd2 Hf) as HF. cbn [fact_ok] in HF. unfold X1 in HF. rewrite lden_lvar, HE2 in HF by lia.
      change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))) in HF.
      rewrite u_small64 in HF by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia). lia. }
    rewrite HL1. rewrite mod_sp by lia. lia. }
  assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0x125f6) by (apply (getr_leaf_c PSEGS E2 Ld5a); [exact Hd2 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 1) by (apply (getr_leaf_c PSEGS E2 Ld5a); [exact Hd2 | vm_compute; reflexivity]).
  assert (BSRC : bytes_at PSEGS (ms_mem ms2) (bv_unsigned (Z_to_bv 64 0x125f6)) [Z_to_bv 8 10]).
  { rewrite u_small64 by (unfold two64; lia). apply bytes_at_of_rdn; [lia | cbn; unfold two64; lia |].
    replace (Z_to_bv 64 0x125f6) with (Z_to_bv 64 (0x125c5 + 49)) by reflexivity. cbn [length].
    rewrite (rdn_img_c E2 Ld5a ms2 16 0x125c5 49 1 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  destruct (u8arr_of_rg E2 Ld5a ms2 0 (rgn Ld5a 0) 64996 1 Hd2 (rgn_eq Ld5a 0 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)
              ltac:(vm_compute; congruence)) as (old & Hlold & Hu8).
  replace (rg_base (rgn Ld5a 0)) with (laddc SP0 (-65536)) in Hu8 by (vm_compute; reflexivity).
  rewrite lden_laddc, HS2, u_small64 in Hu8 by (unfold two64; lia).
  replace (bv_unsigned sp0 + -65536 + 64996) with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 540))) in Hu8 by (rewrite u_small64 by (unfold two64; lia); lia).
  apply (fx_memcpy E2 Ld5a ms2 md T (Z_to_bv 64 (bv_unsigned sp0 - 540)) (Z_to_bv 64 0x125f6) 1 [Z_to_bv 8 10] old [(0%nat, 64996, 1)] (laddc SP0 (-540))
           Hd2 eq_refl eq_refl hok_d5h Hrom2 R10 R11 R12 ltac:(rewrite R1; vm_compute; reflexivity) BSRC Hu8 Hlold eq_refl).
  - rewrite !u_small64 by (unfold two64; lia). right. lia.
  - rewrite u_small64 by (unfold two64; lia). lia.
  - rewrite u_small64 by (unfold two64; lia). lia.
  - apply lden_sp0d; [exact HE2 | lia].
  - intros i R x Hi Hin Hx. exists 0%nat, 64996, 1, (rgn Ld5a 0). split; [left; reflexivity|]. split; [exact (rgn_eq Ld5a 0 ltac:(vm_compute; lia))|].
    replace (rg_base (rgn Ld5a 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
    rewrite lden_laddc, HS2, u_small64 by (unfold two64; lia). rewrite u_small64 in Hx by (unfold two64; lia). lia.
  - exact Hhd.
  - exact Hld.
  - intros E' ms' Ha' Hd' Hout Hgrow Hbs Hrom'.
    rewrite R1 in Hd'. replace (bv_unsigned (Z_to_bv 64 0x53e98)) with 0x53e98 in Hd' by (vm_compute; reflexivity). rewrite U_d5h_eq in Hd'.
    assert (Ha3 : agree 200 E E') by exact (agree_nx E2 E' Ld5a Ha2 ltac:(vm_compute; congruence) Ha').
    assert (HE3 : forall x, (x < 200)%positive -> E' x = E x) by (intros x Hx; symmetry; exact (Ha3 x Hx)).
    apply (KJ E' ms' Ha3).
    + rewrite <- U_d5b_eq. apply (fx_upd_rg PSEGS E' U_d5h ms' 0 (rgn U_d5h 0) (track (rgn U_d5h 0) 64996 [BK 10]) Hd' (rgn_eq U_d5h 0 ltac:(vm_compute; lia)) eq_refl eq_refl).
      * pose proof (sden_rg _ _ _ _ _ _ Hd' (rgn_eq U_d5h 0 ltac:(vm_compute; lia))) as HR0.
        apply (rg_track_rdn PSEGS E' _ _ 64996 [BK 10] HR0 ltac:(lia) ltac:(vm_compute; congruence)).
        replace (rg_base (rgn U_d5h 0)) with (laddc SP0 (-65536)) by (vm_compute; reflexivity).
        rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE3 by lia. change (E 1%positive) with sp0.
        rewrite u_small64 by (unfold two64; lia). cbn [length map bden].
        pose proof (rdn_of_bytes_at _ _ _ Hbs) as X. rewrite u_small64 in X by (unfold two64; lia).
        replace (bv_unsigned sp0 + -65536 + 64996) with (bv_unsigned sp0 - 540) by lia. exact X.
      * exact wf_d5b.
    + rewrite Hrom'. exact Hrom2.
    + apply (inv_stack (ms_mem ms2) (ms_mem ms') (bv_unsigned sp0 - 540) (bv_unsigned sp0 - 539)); [lia | lia | | exact HI2].
      intros x Hx. apply Hout. rewrite u_small64 by (unfold two64; lia). lia.
Qed.


Definition PEND21 : list byte := PRER ++ [Z_to_bv 8 46] ++ [Z_to_bv 8 10].

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX"] Lemma dir_K : forall md E8 ms8, m_halted md = None -> m_vm_lazy md = [] ->
  fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> agree 200 E E8 -> sden PSEGS E8 U_d5b ms8 -> ms_rom ms8 = seg_rom PSEGS -> INV (ms_mem ms8) ->
  realizes PSEGS (mkCfg ms8 md) (t_emit (W 2 PEND21) (t_exit (exit_code 2) (m_fs md))).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HIMG HSTATX : LiaFast.U) => LiaFast.u0).
  intros md E8 ms8 Hhd Hld Hfd2d Ha8 Hd8 Hrom8 HI8. pose proof SLd as SL. pose proof SHd as SH.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_d5b LD5b E8 ms8 md _ TBL_P_ok IMG_P_ok cert_LD5b Hd8 ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E2 ms2 HIn Hd2 Ha2' Hrom2 Hfr2 _. rewrite LD5b_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha2 : agree 200 E E2) by exact (agree_nx E8 E2 U_d5b Ha8 ltac:(vm_compute; congruence) Ha2').
  assert (HI2 : INV (ms_mem ms2)) by exact (inv_fx E8 U_d5b _ _ Ha8 ltac:(vm_compute; reflexivity) Hfr2 HI8).
  rewrite Hrom8 in Hrom2.
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (HS2 : lden E2 SP0 = sp0) by (unfold SP0; rewrite lden_lvar, HE2 by lia; reflexivity).
  assert (HL1 : length a1s = 1%nat).
  { assert (Hf : In (FRange X1 1 1) (s_facts Ld5)) by (vm_compute; tauto).
    pose proof (sden_fact PSEGS E2 Ld5 ms2 _ Hd2 Hf) as HF. cbn [fact_ok] in HF. unfold X1 in HF. rewrite lden_lvar, HE2 in HF by lia.
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))) in HF.
    rewrite u_small64 in HF by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia). lia. }
  assert (R1 : getr (ms_regs ms2) 1 = Z_to_bv 64 0x54410) by (apply (getr_leaf_c PSEGS E2 Ld5); [exact Hd2 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (bv_unsigned sp0 - 576)).
  { rewrite (getr_leaf PSEGS E2 Ld5 ms2 2 (laddc SP0 (-576)) Hd2) by (vm_compute; reflexivity). apply lden_sp0d; [exact HE2 | lia]. }
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 0x64e20) by (apply (getr_leaf_c PSEGS E2 Ld5); [exact Hd2 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms2) 11 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 Ld5); [exact Hd2 | vm_compute; reflexivity]).
  assert (R12 : getr (ms_regs ms2) 12 = Z_to_bv 64 0) by (apply (getr_leaf_c PSEGS E2 Ld5); [exact Hd2 | vm_compute; reflexivity]).
  assert (F40 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 539)))).
  { rewrite (rdn_trk_c E2 Ld5 ms2 5 0x64e20 40 8 (bvs_of (LIN 18446744073709551076 [(1%positive, 1); (8%positive, 1)]) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, u_lin2, HE2, HE2 by lia. change (E 1%positive) with sp0. change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))).
    rewrite HL1. rewrite (u_small64 (Z.of_nat 1)) by (unfold two64; lia). rewrite mod_sp by lia. unfold word_to_le_bytes.
    rewrite u_small64 by (unfold two64; lia). f_equal. f_equal. lia. }
  assert (F56 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E2 Ld5 ms2 5 0x64e20 56 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0d E2 (-560) HE2) by lia. reflexivity. }
  assert (F88 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 - 560)))).
  { rewrite (rdn_trk_c E2 Ld5 ms2 5 0x64e20 88 8 (bvs_of (laddc SP0 (-560)) 8) Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
    rewrite bvs_of_den_lin, (lden_sp0d E2 (-560) HE2) by lia. reflexivity. }
  assert (F96 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 80))).
  { rewrite (rdn_trk_c E2 Ld5 ms2 5 0x64e20 96 8 [BK 80; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0; BK 0] Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (F120 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
  { rewrite (rdn_img_c E2 Ld5 ms2 5 0x64e20 120 4 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (F48 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (0x64e20 + 48)) 8 = Some (repeat (Z_to_bv 8 0) 8)).
  { rewrite (rdn_img_c E2 Ld5 ms2 5 0x64e20 48 8 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
               ltac:(right; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (SWF : sw_file (ms_mem ms2) 0x64e20 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 539) 2 (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80)).
  { constructor; assumption. }
  assert (SSP : ssp_cells (ms_mem ms2) (lden E2 (lvar 5))).
  { split.
    - replace (Z_to_bv 64 0x63da0) with (Z_to_bv 64 (0x63c60 + 320)) by reflexivity.
      rewrite (rdn_img_c E2 Ld5 ms2 3 0x63c60 320 8 Hd2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia)
                 ltac:(left; vm_compute; reflexivity) ltac:(lia) ltac:(vm_compute; congruence) ltac:(vm_compute; reflexivity)). bvlit.
    - replace (Z_to_bv 64 0x95e40) with (Z_to_bv 64 (0x95e40 + 0)) by reflexivity.
      rewrite (rdn_trk_c E2 Ld5 ms2 8 0x95e40 0 8 (bvs_of (lvar 5) 8) Hd2
                 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
      rewrite bvs_of_den_lin. reflexivity. }
  assert (RDP : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (length PEND21) = Some PEND21).
  { replace (bv_unsigned sp0 - 560) with (bv_unsigned sp0 + -65536 + 64976) by lia.
    rewrite (rdn_trk_sp sp0 SL SH E2 Ld5 ms2 0 (-65536) 64976 (length PEND21)
               [BK 99; BK 108; BK 105; BK 58; BK 32; BK 114; BK 101; BK 97; BK 100; BK 32; BK 101; BK 114; BK 114; BK 111; BK 114; BK 32; BK 111; BK 110; BK 32; BK 46; BK 10] Hd2
               ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) HS2 ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)). bvlit. }
  assert (FRM : frame_in E2 Ld5 0 64848 112 (bv_unsigned sp0 - 576 - 112)).
  { apply (frame_sp sp0 SL SH E2 Ld5 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | exact HS2 | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia]. }
  assert (HWF : state_wf (sw_template Ld5 (bv_unsigned (Z_to_bv 64 0x54410)) 0 64848 5 (laddc SP0 (-560)) (lconst 80) (lconst 0)) = true).
  { rewrite u_small64 by (unfold two64; lia). rewrite U_d6_eq. exact wf_d6. }
  apply (rzc_conseq PSEGS DCFG _ (t_emit (map (WriteEv (Z_to_bv 64 2)) (PEND21 ++ [])) (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md)))));
    [| apply tail_1].
  apply (fx_stdio_write E2 Ld5 ms2 md _ (bv_unsigned sp0 - 576) 0x64e20 (bv_unsigned sp0 - 560) (bv_unsigned sp0 - 539) 2
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp0 - 560)) (Z_to_bv 64 80) (lden E2 (lvar 5)) (Z_to_bv 64 0x54410) PEND21 []
           0 64848 5 (rgn Ld5 5) (laddc SP0 (-560)) (lconst 80) (lconst 0)
           Hd2 eq_refl eq_refl Hrom2 hok_d6 HWF FRM (rgn_eq Ld5 5 ltac:(vm_compute; lia)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) R2 R10 R11 R12 R1); try lia.
  + exact SWF.
  + exact SSP.
  + exact F48.
  + exact Hfd2d.
  + exact Hhd.
  + exact Hld.
  + unfold TASK_SIZE. lia.
  + replace (length PEND21) with 21%nat by reflexivity. lia.
  + vm_compute. reflexivity.
  + replace (length PEND21) with 21%nat by reflexivity. cbn [length]. lia.
  + replace (length PEND21) with 21%nat by reflexivity. cbn [length]. lia.
  + left. rewrite !u_small64 by (unfold two64; lia). lia.
  + rewrite !u_small64 by (unfold two64; lia). unfold TASK_SIZE. lia.
  + exact RDP.
  + reflexivity.
  + vm_compute. reflexivity.
  + apply t_emit_has_nil.
  + apply (lden_sp0d E2 (-560) HE2). lia.
  + apply lden_lconst.
  + apply lden_lconst.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + intros E4 ms4 Ha5 Hd4 Hpost4 Hrom4.
    rewrite u_small64 in Hd4 by (unfold two64; lia). rewrite U_d6_eq in Hd4.
    assert (Ha5' : agree 200 E E4) by exact (agree_nx E2 E4 Ld5 Ha2 ltac:(vm_compute; congruence) Ha5).
    assert (HI4 : INV (ms_mem ms4)) by exact (inv_sw (ms_mem ms2) (ms_mem ms4) _ _ _ Hpost4 ltac:(lia) ltac:(lia) HI2).
    rewrite Hrom2 in Hrom4.
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_d6 LD6 E4 ms4 md _ TBL_P_ok IMG_P_ok cert_LD6 Hd4
             ltac:(vm_compute; reflexivity) Hhd Hld).
    intros L E5 ms5 HIn Hd5 Ha6 Hrom5 Hfr5 _. rewrite LD6_eq in HIn. destruct HIn as [<-|[]].
    assert (Ha6' : agree 200 E E5) by exact (agree_nx E4 E5 U_d6 Ha5' ltac:(vm_compute; congruence) Ha6).
    assert (HE5 : forall x, (x < 200)%positive -> E5 x = E x) by (intros x Hx; symmetry; exact (Ha6' x Hx)).
    assert (HI5 : INV (ms_mem ms5)) by exact (inv_fx E4 U_d6 _ _ Ha5' ltac:(vm_compute; reflexivity) Hfr5 HI4).
    rewrite Hrom4 in Hrom5.
    apply (fx_exit E5 Ld6 ms5 md (Z_to_bv 64 2) [] Hd5 eq_refl eq_refl Hrom5).
    apply (exit_pre_gen sp0 tid SL SH Htid E5 Ld6 ms5 md (-128) 0 3 5 6 7 21 65264 (rg_cont (rgn Ld6 5)) (rg_cont (rgn Ld6 7)) RW Hd5).
    * unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
    * unfold T. rewrite lden_lvar, HE5 by lia. reflexivity.
    * lia.
    * exact (exit_glob_of_MFX _ (proj1 HI5) (proj2 HI5)).
    * exact Hhd.
    * exact Hld.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * unfold c5_clean. repeat split; vm_compute; reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * vm_compute. reflexivity.
    * apply (frame_sp sp0 SL SH E5 Ld6 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
      unfold SP0. rewrite lden_lvar, HE5 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HNL : forall hs m md, hi_Heap HI hs m md -> NL m.
(* [comment removed for export] *)
Definition IMGIV : list ivl := [(0x63c60, 0x63db8); (0x63bf0, 0x63c10); (0x64e20, 0x64f08); (0x64f10, 0x64ff8); (0x75b28, 0x75b30);
  (0x95e40, 0x95e48); (0x75060, 0x75078); (0x962a0, 0x966a8); (0x10481, 0x10499); (0x10bd5, 0x10bf5); (0x10f35, 0x10f6d);
  (0x11bc5, 0x11bed); (0x12875, 0x1287d); (0x125c5, 0x12605); (0x12bcd, 0x12bf5); (0x12f25, 0x12f2d); (0x13018, 0x13028); (0x18330, 0x18540); (0x95c18, 0x95d40)].
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.
(* [comment removed for export] *)
Variable HeapI : hi_HS HI -> (word -> option byte) -> Model -> Prop.
Variable INIT : hi_HS HI -> list ivl.
Hypothesis HOKI : heap_init_ok PSEGS DCFG HI HeapI INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP CELLS_NE 0x51310 8192.
Hypothesis HOWNI : forall hs m md, HeapI hs m md -> forall x, ~ ioutside (hi_owned HI hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < IMG_LO \/ IMG_END <= x).
Hypothesis HERRI : forall hs m m' md, HeapI hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapI hs m' md.
Hypothesis HCELLI : forall hs m m' md, HeapI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapI hs m' md.

#[using="Type"] Lemma nth_shape : forall rgs i R, nth_error rgs i = Some R -> nth_error (shape rgs) i = Some (rg_base R, rg_size R).
Proof. LiaFast.lf_pins LiaFast.u0. intros rgs i R H. unfold shape. rewrite nth_error_map, H. reflexivity. Qed.

Definition SHAPE_OD : list (lin * lin) := Eval vm_compute in shape (s_rgs U_od).
#[using="Type"] Lemma shape_od_eq : shape (s_rgs U_od) = SHAPE_OD. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

#[using="uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI"] Lemma avoid_od : forall E' rgs, agree 200 E E' -> shape rgs = shape (s_rgs U_od) -> avoid_heap3 IMG_LO IMG_END HTOP STATIC E' rgs.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 HTOPB HIMG HSTATI : LiaFast.U) => LiaFast.u0).
  intros E' rgs Ha Hs i R x Hi Hin Hc. pose proof SLd. pose proof SHd. destruct HIMG as [HI1 HI2].
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  pose proof (nth_shape rgs i R Hi) as Hsh. rewrite Hs, shape_od_eq in Hsh. unfold in_rg, rsz in Hin.
  do 23 (destruct i as [|i]; [cbn [nth_error SHAPE_OD] in Hsh; injection Hsh as Hb Hz; rewrite <- Hb, <- Hz in Hin; clear Hb Hz;
    rewrite ?u_lin0 in Hin by lia; rewrite ?u_lin1, ?u_lin2 in Hin; rewrite ?HE in Hin by lia;
    change (E 1%positive) with sp0 in Hin; rewrite ?(E_P1 sp0 av ev tid rdraw regs Hargc2) in Hin;
    try (change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive) in Hin; rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2) in Hin);
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))) in Hin;
    rewrite ?u_small64 in Hin by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia);
    rewrite ?Z.mod_small in Hin by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64 in *; lia);
    first [ left; lia | right; split; [lia|]; apply HSTATI; [cbn [ioutside IMGIV]; intros Hq; repeat (destruct Hq as [?Hq Hq]); lia | exact Hc] ] |]).
  cbn [nth_error SHAPE_OD] in Hsh. destruct i; discriminate Hsh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma init_out_od : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs U_od) ->
  bv_unsigned sp0 + 24 <= bv_unsigned x < 2 ^ 48 -> (bv_unsigned x < bv_unsigned p1 \/ bv_unsigned p1 + Z.of_nat (length a1s) < bv_unsigned x) ->
  outside E' rgs x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs Hx1 Hx2. pose proof SLd. pose proof SHd.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  unfold outside. apply Forall_forall. intros R HR. apply In_nth_error in HR as (i & Hi).
  pose proof (nth_shape rgs i R Hi) as Hsh. rewrite Hs, shape_od_eq in Hsh.
  do 23 (destruct i as [|i]; [cbn [nth_error SHAPE_OD] in Hsh; injection Hsh as Hb Hz; unfold rsz; rewrite <- Hb, <- Hz; clear Hb Hz;
    rewrite ?u_lin0 by lia; rewrite ?u_lin1, ?u_lin2; rewrite ?HE by lia;
    change (E 1%positive) with sp0; rewrite ?(E_P1 sp0 av ev tid rdraw regs Hargc2);
    try (change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive); rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2));
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s)));
    rewrite ?u_small64 by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia);
    rewrite ?Z.mod_small by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64 in *; lia); lia |]).
  cbn [nth_error SHAPE_OD] in Hsh. destruct i; discriminate Hsh.
Qed.

#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 IMG_LO IMG_END HIMG"] Lemma dir_entry : forall E2 ms2, path_is_dirref a1s = true -> agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) -> sden PSEGS E2 U_od ms2.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0).
  intros E2 ms2 HDR Ha2 Hd2 Hmf2. pose proof (dot_a1s HDR) as HA1. pose proof SLd. pose proof SHd.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (HP1 : lden E2 P1 = p1) by (unfold P1; rewrite lden_lvar, HE2 by lia; exact (E_P1 sp0 av ev tid rdraw regs Hargc2)).
  assert (UP1 : bv_unsigned (lden E2 P1) = bv_unsigned p1) by (rewrite HP1; reflexivity).
  (* [comment removed for export] *)
  pose proof (rdn_argv1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as RA. rewrite HA1 in RA.
  pose proof (bytes_at_of_rdn mem (bv_unsigned p1) [Z_to_bv 8 46; Z_to_bv 8 0] ltac:(lia) ltac:(cbn; unfold two64; lia)
                ltac:(rewrite Z_to_bv_bv_unsigned; exact RA)) as BA.
  pose proof (bytes_at_rdn PSEGS mem (bv_unsigned p1) _ 0 1 BA ltac:(cbn; lia)) as R1. cbn [firstn skipn] in R1.
  rewrite Z.add_0_r in R1. unfold wa in R1.
  assert (HO : outside E (s_rgs P_main2) (Z_to_bv 64 (bv_unsigned p1))).
  { apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2); rewrite u_small64 by (unfold two64; lia); [lia|].
    rewrite HA1. cbn. lia. }
  assert (R2 : rdn PSEGS (ms_mem ms2) (Z_to_bv 64 (bv_unsigned p1)) 1 = Some [Z_to_bv 8 46]).
  { rewrite <- R1. apply (rdn_ext_rd1 PSEGS (ms_mem ms2) mem (bv_unsigned p1) 1); [lia | unfold two64; lia |].
    intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold rd1. rewrite (Hmf2 _ HO). reflexivity. }
  rewrite <- U_od_eq. apply fx_add_fact.
  - apply fx_add_rg; [exact Hd2 | exact wf_od | | ].
    + change RPATH with (track (RGz P1 1 RW TEmpty) 0 [BK 46]).
      apply rg_track_rdn; [| lia | rsz_simpl; cbn; lia | ].
      * apply rg_rw_empty_ok; rewrite ?UP1; [lia | unfold two64; lia |].
        intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r.
        pose proof (rdn_overlay PSEGS 0xa0000 (ms_mem ms2) (bv_unsigned p1) 1 [Z_to_bv 8 46] PSEGS_top ltac:(lia) ltac:(unfold two64; lia) R2 0 ltac:(lia)) as X.
        rewrite Z.add_0_r in X. rewrite X. discriminate.
      * cbn [RGz rg_base track RGz length]. rewrite UP1, Z.add_0_r, R2. reflexivity.
    + cbn [s_rgs U_ofd]. unfold rg_disj.
      repeat (apply Forall_cons; [unfold RPATH; rsz_simpl; cbn [RGz rg_base rg_size]; rewrite UP1;
        rewrite ?u_lin0 by lia; rewrite ?u_lin1, ?u_lin2; rewrite ?HE2 by lia;
        change (E 1%positive) with sp0;
        try (change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive); rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2));
        change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))); rewrite ?HA1;
        rewrite ?u_small64 by (unfold two64; cbn; lia);
        rewrite ?Z.mod_small by (unfold two64 in *; cbn; lia); cbn [length Z.of_nat Pos.of_succ_nat]; lia |]).
      apply Forall_nil.
  - vm_compute. reflexivity.
  - cbn [fact_ok]. unfold X1. rewrite lden_lvar, HE2 by lia. change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length a1s))).
    rewrite HA1. vm_compute. split; discriminate.
Qed.

#[using="uid hw Hsp Hva Hve Hfits Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HOK HNL HSTATI HOKI HOWNI HERRI HCELLI"] Theorem dir_path : path_is_dirref a1s = true -> forall model E2 ms2 hs0,
  m_halted model = None -> m_vm_lazy model = [] -> m_fds model = FDS0 -> U model <= UB0 ->
  agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) ->
  HeapI hs0 (ms_mem ms2) (with_fds (fd_insert FDS0 (Z_to_bv 64 3) FdDir) model) ->
  (forall x, ~ ioutside (INIT hs0) x -> bv_unsigned sp0 + 24 <= x < 2 ^ 48 /\ (x < bv_unsigned p1 \/ bv_unsigned p1 + Z.of_nat (length a1s) < x)) ->
  realizes PSEGS (mkCfg ms2 (with_fds (fd_insert FDS0 (Z_to_bv 64 3) FdDir) model)) (t_die (msg_read_error a1s) (m_fs model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Hfits Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATX HOK HNL HSTATI HOKI HOWNI HERRI HCELLI : LiaFast.U) => LiaFast.u0).
  intros HDR model E2 ms2 hs0 Hh Hl Hfds HU0 Ha2 Hd2 Hrom2 Hmf2 Hheap Hio.
  pose proof (dot_a1s HDR) as HA1. pose proof SLd as SL. pose proof SHd as SH. destruct HIMG as [HI1 HI2].
  set (md0 := with_fds (fd_insert FDS0 (Z_to_bv 64 3) FdDir) model) in *.
  assert (Hh0 : m_halted md0 = None) by (unfold md0; rewrite with_fds_halted; exact Hh).
  assert (Hl0 : m_vm_lazy md0 = []) by (unfold md0; rewrite with_fds_lazy; exact Hl).
  pose proof (dir_entry E2 ms2 HDR Ha2 Hd2 Hmf2) as Hd2'.
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_od LD1 E2 ms2 md0 _ TBL_P_ok IMG_P_ok cert_LD1 Hd2' ltac:(vm_compute; reflexivity) Hh0 Hl0).
  intros L E3 ms3 HIn Hd3 Ha3' Hrom3 Hfr3 Hgr3. rewrite LD1_eq in HIn. destruct HIn as [<-|[]].
  assert (Ha3 : agree 200 E E3) by exact (agree_nx E2 E3 U_od Ha2 ltac:(vm_compute; congruence) Ha3').
  assert (HE3 : forall x, (x < 200)%positive -> E3 x = E x) by (intros x Hx; symmetry; exact (Ha3 x Hx)).
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  rewrite Hrom2 in Hrom3.
  (* [comment removed for export] *)
  assert (Hcel3 : forall a, ~ ioutside CELLS_NE a -> mrd PSEGS (ms_mem ms3) (Z_to_bv 64 a) = mrd PSEGS (ms_mem ms2) (Z_to_bv 64 a)).
  { intros a Ha. cbn [ioutside CELLS_NE] in Ha.
    assert (Hr : (0x63da0 <= a < 0x63da8) \/ (0x95e40 <= a < 0x95e48)).
    { apply Decidable.not_not; [unfold Decidable.decidable; lia|]. intros C. apply Ha. repeat split; lia. }
    destruct Hr as [Hr|Hr].
    - (* [comment removed for export] *)
      pose proof (sden_rg _ _ _ _ _ _ Hd3 (rgn_eq Ld1 3 ltac:(vm_compute; lia))) as R3.
      pose proof (sden_rg _ _ _ _ _ _ Hd2' (rgn_eq U_od 3 ltac:(vm_compute; lia))) as R3'.
      destruct R3 as (_ & _ & A3 & _). destruct R3' as (_ & _ & A3' & _).
      replace (rg_kind (rgn Ld1 3)) with RO in A3 by (vm_compute; reflexivity). replace (rg_kind (rgn U_od 3)) with RO in A3' by (vm_compute; reflexivity).
      replace (rg_base (rgn Ld1 3)) with (lconst 0x63c60) in A3 by (vm_compute; reflexivity).
      replace (rg_base (rgn U_od 3)) with (lconst 0x63c60) in A3' by (vm_compute; reflexivity).
      rszv_in A3. rszv_in A3'.
      rewrite u_lconst in A3, A3' by lia. destruct (A3 (a - 0x63c60) ltac:(lia)) as [Z3 _]. destruct (A3' (a - 0x63c60) ltac:(lia)) as [Z3' _].
      replace (0x63c60 + (a - 0x63c60)) with a in Z3, Z3' by lia. unfold mrd. rewrite Z3, Z3'. reflexivity.
    - (* [comment removed for export] *)
      assert (Hv : forall L0 E0 ms0, sden PSEGS E0 L0 ms0 -> (forall x, (x < 200)%positive -> E0 x = E x) -> (8 < length (s_rgs L0))%nat ->
                 rg_base (rgn L0 8) = lconst 0x95e40 -> get_bytes (rg_cont (rgn L0 8)) 0 8 = Some (bvs_of (lvar 5) 8) ->
                 mrd PSEGS (ms_mem ms0) (Z_to_bv 64 a) = nth_error (Z_to_le_bytes 8 (bv_unsigned (canary rdraw))) (Z.to_nat (a - 0x95e40))).
      { intros L0 E0 ms0 Hd0 HE0 Hn Hb Hg. pose proof (rdn_trk_c E0 L0 ms0 8 0x95e40 0 8 _ Hd0 Hn Hb ltac:(lia) ltac:(lia) Hg) as X.
        rewrite bvs_of_den_lin, lden_lvar, HE0 in X by lia. change (E 5%positive) with (canary rdraw) in X. rewrite Z.add_0_r in X.
        pose proof (rdn_rd1 PSEGS (ms_mem ms0) 0x95e40 8 _ ltac:(lia) ltac:(unfold two64; lia) X (Z.to_nat (a - 0x95e40))) as Y.
        unfold mrd. destruct (nth_error (Z_to_le_bytes 8 (bv_unsigned (canary rdraw))) (Z.to_nat (a - 0x95e40))) as [b|] eqn:Hb'.
        - specialize (Y b eq_refl). rewrite Z2Nat.id in Y by lia. replace (0x95e40 + (a - 0x95e40)) with a in Y by lia. unfold rd1 in Y. exact Y.
        - exfalso. apply nth_error_None in Hb'. rewrite length_Z_to_le_bytes in Hb'. lia. }
      rewrite (Hv Ld1 E3 ms3 Hd3 HE3 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      rewrite (Hv U_od E2 ms2 Hd2' HE2 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). reflexivity. }
  assert (Hin2 : forall x, ~ ioutside (INIT hs0) (bv_unsigned x) -> outside E2 (s_rgs U_od) x).
  { intros x Hx. destruct (Hio _ Hx) as (X1 & X2). exact (init_out_od E2 (s_rgs U_od) x Ha2 eq_refl X1 X2). }
  pose proof (heap_seg_init HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HeapI INIT HOKI HOWNI HERRI HCELLI E2 (s_rgs U_od) hs0 (ms_mem ms2) (ms_mem ms3) md0
                Hheap Hin2 Hfr3 Hgr3 Hcel3 (avoid_od E2 (s_rgs U_od) Ha2 eq_refl)) as Hheap3.
  assert (HI3 : MFX (ms_mem ms3)) by exact (mfx_fx E2 U_od _ _ Ha2 eq_refl Hfr3 (mfx_of_mf _ Hmf2)).
  (* [comment removed for export] *)
  assert (R1 : getr (ms_regs ms3) 1 = Z_to_bv 64 0x2268c) by (apply (getr_leaf_c PSEGS E3 Ld1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)).
  { rewrite (getr_leaf PSEGS E3 Ld1 ms3 2 (laddc SP0 (-128)) Hd3) by (vm_compute; reflexivity). apply lden_sp0d; [exact HE3 | lia]. }
  assert (R3 : getr (ms_regs ms3) 3 = Z_to_bv 64 0x10800) by (apply (getr_leaf_c PSEGS E3 Ld1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x75bd0) by (apply (getr_leaf_c PSEGS E3 Ld1); [exact Hd3 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms3) 10 = Z_to_bv 64 65536) by (apply (getr_leaf_c PSEGS E3 Ld1); [exact Hd3 | vm_compute; reflexivity]).
  pose proof (sp0_al sp0 Hsp) as Al.
  apply (fx_malloc_init HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK HeapI INIT HOKI HOWNI E3 Ld1 ms3 md0 hs0 65536 0 7 57216
           (bv_unsigned sp0 - 128) (rgn Ld1 7) _ Hd3 eq_refl eq_refl Hrom3 hok_d2 (rgn_eq Ld1 7 ltac:(vm_compute; lia))
           ltac:(replace (rg_base (rgn Ld1 7)) with (lconst 0x75b28) by (vm_compute; reflexivity); apply u_lconst; lia)
           Hheap3 (conj Hh0 Hl0) ltac:(unfold md0; rewrite U_with_fds; unfold MCHARGE, UBOUND, UB0 in *; lia) R10 ltac:(lia) ltac:(rewrite R1; vm_compute; reflexivity) R3 R4 R2 ltac:(lia) ltac:(lia) ltac:(unfold valid_sp in Hsp; lia) ltac:(lia)).
  - apply (frame_sp sp0 SL SH E3 Ld1 0 (-65536)); [vm_compute; lia | vm_compute; reflexivity | | lia | vm_compute; reflexivity | lia | vm_compute; congruence | lia].
    unfold SP0. rewrite lden_lvar, HE3 by lia. reflexivity.
  - exact (avoid_od E3 (s_rgs Ld1) Ha3 ltac:(vm_compute; reflexivity)).
  - intros x Hx. destruct (Hio x Hx) as [Hx1 _]. lia.
  - intros E4 ms4 md4 hs4 p Ha4' Hd4 Hrom4 Hheap4 Hmd4 Hvo HU4 H10' Hp16 Hadd Hnin Hmunch Hcells4.
    destruct Hmd4 as [Hh4 Hl4].
    assert (Ha4 : agree 200 E E4) by exact (agree_nx E3 E4 Ld1 Ha3 ltac:(vm_compute; congruence) Ha4').
    rewrite R1 in Hd4. replace (bv_unsigned (Z_to_bv 64 0x2268c)) with 0x2268c in Hd4 by (vm_compute; reflexivity).
    rewrite Hrom3 in Hrom4.
    pose proof HOK as (_ & _ & _ & _ & Hblk).
    destruct (Hblk hs4 (ms_mem ms4) md4 Hheap4) as (Hbl & _).
    destruct (Hbl p 65536 ltac:(apply Hadd; left; reflexivity)) as (_ & Hr & _).
    assert (Hp : 16 <= p <= 140737488355328) by (destruct Hr as [Hr|Hr]; unfold valid_sp in Hsp; lia).
    assert (Hd4' : sden PSEGS E4 U_d2 ms4).
    { rewrite <- U_d2_eq. apply fx_add_fact; [exact Hd4 | vm_compute; reflexivity |].
      cbn [fact_ok]. rewrite <- (getr_leaf PSEGS E4 _ ms4 10 (lvar (NXD1 + 10)) Hd4) by (vm_compute; reflexivity).
      rewrite H10', u_small64 by (unfold two64; lia). lia. }
    assert (HI4 : INV (ms_mem ms4)).
    { split; [|exact (HNL hs4 (ms_mem ms4) md4 Hheap4)].
      intros x Hx Hhx Hp1. rewrite Hmunch; [exact (HI3 x Hx Hhx Hp1)|].
      pose proof (HOWNI hs0 (ms_mem ms3) md0 Hheap3) as Ho0. pose proof (Hblk hs4 (ms_mem ms4) md4 Hheap4) as (_ & Ho4).
      apply ioutside_app. split.
      { destruct (HIface.outside_dec (hi_owned HI hs0) (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hhx.
        destruct (Ho0 _ A) as (B1 & B2). split; [lia | exact B2]. }
      apply ioutside_app. split.
      { destruct (HIface.outside_dec (hi_owned HI hs4) (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hhx.
        destruct (Ho4 _ A) as (B1 & B2). split; [lia | exact B2]. }
      cbn [ioutside]. split; [|split; [|exact I]].
      - intros Hin. apply Hhx. split; [destruct Hr as [Hr|Hr]; lia|]. destruct Hr as [Hr|Hr]; [right; left; lia | right; right; lia].
      - pose proof (outside_nth_c E _ x 0 (laddc SP0 (-65536)) 65536 RW TEmpty Hx eq_refl ltac:(unfold two64; lia)) as X0r. cbn [RGz rg_base] in X0r.
        rewrite lden_laddc in X0r. unfold SP0 in X0r. rewrite lden_lvar in X0r. change (E 1%positive) with sp0 in X0r.
        rewrite u_small64 in X0r by (unfold two64; lia). lia. }
    (* [comment removed for export] *)
    apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 S1 U_d2 LD2 E4 ms4 md4 _ TBL_P_ok IMG_P_ok cert_LD2 Hd4' ltac:(vm_compute; reflexivity) Hh4 Hl4).
    intros L E5 ms5 HIn Hd5 Ha5' Hrom5 Hfr5 _. rewrite LD2_eq in HIn. destruct HIn as [<-|[]].
    assert (Ha5 : agree 200 E E5) by exact (agree_nx E4 E5 U_d2 Ha4 ltac:(vm_compute; congruence) Ha5').
    assert (HI5 : INV (ms_mem ms5)) by exact (inv_fx E4 U_d2 _ _ Ha4 ltac:(vm_compute; reflexivity) Hfr5 HI4).
    rewrite Hrom4 in Hrom5.
    assert (Q17 : getr (ms_regs ms5) 17 = Z_to_bv 64 63) by (apply (getr_leaf_c PSEGS E5 Ld2); [exact Hd5 | vm_compute; reflexivity]).
    assert (Q10 : getr (ms_regs ms5) 10 = Z_to_bv 64 3) by (apply (getr_leaf_c PSEGS E5 Ld2); [exact Hd5 | vm_compute; reflexivity]).
    assert (Q11 : getr (ms_regs ms5) 11 = Z_to_bv 64 0x65059) by (apply (getr_leaf_c PSEGS E5 Ld2); [exact Hd5 | vm_compute; reflexivity]).
    assert (Q12 : getr (ms_regs ms5) 12 = Z_to_bv 64 65536) by (apply (getr_leaf_c PSEGS E5 Ld2); [exact Hd5 | vm_compute; reflexivity]).
    assert (HFD : fd_lookup (m_fds md4) (fd32 (getr (ms_regs ms5) 10)) = Some FdDir).
    { rewrite (vm_only_fds md0 md4 Hvo), Q10. unfold md0. rewrite with_fds_fds. vm_compute. reflexivity. }
    destruct (mk_tbl_ranges_ecall PSEGS RS_P 0x5ee74 ltac:(rewrite <- TBL_P_eq; vm_compute; reflexivity)) as (w & Hw & Hec).
    rewrite (sden_mkst PSEGS E5 Ld2 ms5 Hd5 eq_refl).
    apply (rzc_ecall PSEGS DCFG (ms_regs ms5) _ (ms_mem ms5) (ms_rom ms5) md4 w _ Hh4 Hl4 Hw Hec).
    rewrite Hrom5.
    apply (@rzc_read_dir _ PSEGS DCFG (ms_regs ms5) _ (ms_mem ms5) md4 _ Hh4 Hl4 Q17 HFD ltac:(rewrite Q11, Q12; vm_compute; reflexivity)).
    rewrite <- Hrom5.
    apply (fx_sys_ret E5 Ld2 ms5 md4 (errno_ret EISDIR) (Some (lconst 18446744073709551595)) _ Hd5 hok_d3
             ltac:(intros l Hc; injection Hc as <-; rewrite lden_lconst; unfold errno_ret, EISDIR; apply bv_eq; reflexivity)
             ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)).
    intros E6 ms6 Ha6' Hd6 Hm6 Hr6 _.
    replace (s_pc Ld2 + 4) with 0x5ee78 in Hd6 by (vm_compute; reflexivity). rewrite U_d3_eq in Hd6.
    assert (Ha6 : agree 200 E E6) by exact (agree_nx E5 E6 Ld2 Ha5 ltac:(vm_compute; congruence) Ha6').
    assert (HI6 : INV (ms_mem ms6)) by (rewrite Hm6; exact HI5).
    assert (Hrom6 : ms_rom ms6 = seg_rom PSEGS) by (rewrite Hr6; exact Hrom5).
    assert (Hfd2' : fd_lookup (m_fds md4) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { rewrite (vm_only_fds md0 md4 Hvo). unfold md0. rewrite with_fds_fds. vm_compute. reflexivity. }
    replace (t_die (msg_read_error a1s) (m_fs model)) with (t_emit (W 2 PEND21) (t_exit (exit_code 2) (m_fs md4))).
    2:{ rewrite (vm_only_fs md0 md4 Hvo). unfold md0. rewrite with_fds_fs, HA1. reflexivity. }
    apply (dir_G md4 E6 ms6 _ Hh4 Hl4 HDR Ha6 Hd6 Hrom6 HI6).
    intros E8 ms8 Ha8 Hd8 Hrom8 HI8.
    apply (dir_H md4 E8 ms8 _ Hh4 Hl4 HDR Ha8 Hd8 Hrom8 HI8).
    intros E9 ms9 Ha9 Hd9 Hrom9 HI9.
    apply (dir_J md4 E9 ms9 _ Hh4 Hl4 Ha9 Hd9 Hrom9 HI9).
    intros E10 ms10 Ha10 Hd10 Hrom10 HI10.
    exact (dir_K md4 E10 ms10 Hh4 Hl4 Hfd2' Ha10 Hd10 Hrom10 HI10).
Qed.
End UD.
