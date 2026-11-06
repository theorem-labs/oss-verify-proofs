(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StoreOk MemSplit DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SysNodesCfg AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 RefStdioDefs RefExitBase PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PRefused PEofCert PDrvExit2 PEof1 PEofWalk PHdrCalc PEof2 PLoopInv2 Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rg_rw_stk : forall E0 m base n A, bv_unsigned (lden E0 base) = A -> 0 <= n -> A + n < two64 -> stk PSEGS m A (A + n) ->
  rg_ok PSEGS E0 m (RGz base n RW TEmpty).
Proof.
  intros E0 m base n A HA Hn Hf (_ & _ & Hs). pose proof (u_range E0 base) as RB. rewrite HA in RB.
  unfold rg_ok. rewrite (rsz_RGz E0 base n RW TEmpty) by lia.
  cbv zeta. cbn [RGz rg_base rg_size rg_kind rg_cont]. rewrite HA.
  assert (Hf' : A + n <= two64) by lia. refine (conj Hn (conj Hf' (conj _ _))).
  - intros i Hi. destruct (Hs (A + i) ltac:(lia)) as [Hw (b & Hb)]. unfold wa in *. split; [|exact Hw].
    unfold rd1. unfold mrd in Hb. rewrite Hb. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rg_disj_bytes : forall E0 R1 R2, 0 < rsz E0 R1 -> 0 < rsz E0 R2 ->
  (forall i, 0 <= i < rsz E0 R2 -> bv_unsigned (lden E0 (rg_base R2)) + i < bv_unsigned (lden E0 (rg_base R1)) \/
                                    bv_unsigned (lden E0 (rg_base R1)) + rsz E0 R1 <= bv_unsigned (lden E0 (rg_base R2)) + i) ->
  rg_disj E0 R1 R2.
Proof.
  intros E0 R1 R2 H1 H2 H. unfold rg_disj. cbv zeta.
  set (A1 := bv_unsigned (lden E0 (rg_base R1))) in *. set (A2 := bv_unsigned (lden E0 (rg_base R2))) in *.
  destruct (Z_le_gt_dec (A2 + rsz E0 R2) A1) as [C|C]; [right; exact C|].
  destruct (Z_lt_ge_dec A1 A2) as [D|D].
  - pose proof (H 0 ltac:(lia)) as X. lia.
  - pose proof (H (A1 - A2) ltac:(lia)) as X. lia.
Qed.

Lemma firstn1_skipn : forall {A} (l : list A) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  intros A l. induction l as [|x l IH]; intros i d Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma config_len_eq : forall data : list byte, (2 <= length data)%nat ->
  Z.of_nat (config_len data) = bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * (bv_unsigned (nth 1 data (Z_to_bv 8 0)) mod 128).
Proof.
  intros data Hl. unfold config_len, cfg_word.
  set (u0 := bv_unsigned (nth 0 data (Z_to_bv 8 0))). set (u1 := bv_unsigned (nth 1 data (Z_to_bv 8 0))).
  pose proof (bv_unsigned_in_range _ (nth 0 data (Z_to_bv 8 0))) as R0. pose proof (bv_unsigned_in_range _ (nth 1 data (Z_to_bv 8 0))) as R1.
  unfold bv_modulus in R0, R1. change (2 ^ Z.of_N 8) with 256 in R0, R1. fold u0 u1 in R0, R1.
  pose proof (Z.mod_pos_bound u1 128 ltac:(lia)) as M1. pose proof (Z.div_mod u1 128 ltac:(lia)) as D1.
  rewrite (Z.mod_unique (u0 + 256 * u1) 32768 (u1 / 128) (u0 + 256 * (u1 mod 128))); [| lia | lia].
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Section E3.
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
Hypothesis HIMG : IMG_LO <= 0x10000 /\ 0x97000 <= IMG_END.
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.
Variable HI : heap_iface.
Hypothesis HOK : heap_ok PSEGS DCFG HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.
Hypothesis HNL : forall hs m md, hi_Heap HI hs m md -> NL m.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.
Hypothesis HMV : forall hs m md md', hi_Heap HI hs m md -> m_vmmaps md' = m_vmmaps md -> m_halted md' = None -> m_vm_lazy md' = [] -> hi_Heap HI hs m md'.
Hypothesis HSTATR : forall x, RSX x -> ioutside STATIC x.
Variable data : list byte.
Variable fs0 : Fs.Fs.
Hypothesis Hlk : fs_lookup fs0 (nth 1 av []) = Some data.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation HDHEAD' := (HDHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).

(* [comment removed for export] *)
Definition TRHEAD (E3 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E3 /\ sden PSEGS E3 Ltr ms /\ ms_rom ms = seg_rom PSEGS /\ E3 N0 = Z_to_bv 64 len /\ E3 BUF = Z_to_bv 64 buf /\
  E3 CLV = Z_to_bv 64 (Z.of_nat (config_len data)) /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  (config_len data <> 0%nat -> mrd PSEGS (ms_mem ms) (Z_to_bv 64 (buf + 2)) = Some (nth 2 data (Z_to_bv 8 0))) /\
  len = Z.of_nat (length data) /\ 6 + Z.of_nat (config_len data) <= len < cap /\ CAPOKU cap md.

#[using="Type"] Lemma keeph5_ne : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPH5 = true ->
  r <> Z_to_bv 5 21 /\ r <> Z_to_bv 5 10 /\ r <> Z_to_bv 5 11 /\ r <> Z_to_bv 5 18.
Proof. LiaFast.lf_pins LiaFast.u0. intros r H. repeat split; intros Hr; subst r; vm_compute in H; discriminate H. Qed.

Definition FC_tr : fact := Eval vm_compute in FCond BC_LTU (lvar N0) (laddc (lvar CLV) 6) false.
Definition FC_ov : fact := Eval vm_compute in FCond BC_LTU (lvar N0) (laddc (lvar CLV) 6) true.
#[using="tid Htid IMG_LO IMG_END HIMG"] Lemma FC_tr_in : In FC_tr (s_facts Ltr0). Proof. LiaFast.lf_pins (fun (tid Htid IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0). vm_compute. tauto. Qed.
#[using="tid Htid IMG_LO IMG_END HIMG"] Lemma FC_ov_in : In FC_ov (s_facts Lov0). Proof. LiaFast.lf_pins (fun (tid Htid IMG_LO IMG_END HIMG : LiaFast.U) => LiaFast.u0). vm_compute. tauto. Qed.
#[using="Type"] Lemma FC_tr_eq : FC_tr = FCond BC_LTU (lvar N0) (laddc (lvar CLV) 6) false. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma FC_ov_eq : FC_ov = FCond BC_LTU (lvar N0) (laddc (lvar CLV) 6) true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma rgs_uh : s_rgs U_h = s_rgs Lhd ++ [BMR]. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rgs_pos_b : forallb (fun R => Z.ltb 0 (csz R)) (s_rgs Lhd) = true. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rgs_pos : forall R, In R (s_rgs Lhd) -> 0 < csz R.
Proof. LiaFast.lf_pins LiaFast.u0. intros R HR. pose proof rgs_pos_b as X. rewrite forallb_forall in X. apply Z.ltb_lt. exact (X R HR). Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI"] Theorem header_entry : forall E2 ms md hs len cap buf,
  HDHEAD' E2 ms md hs len cap buf ->
  (forall E3 ms3, TRHEAD E3 ms3 md hs len cap buf ->
     realizes PSEGS (mkCfg ms3 md) (t_emit (W 1 (zero_lines (n_calls data))) (t_exit (exit_code 0) fs0))) ->
  realizes PSEGS (mkCfg ms md) (t_body data fs0).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 HTOPB HIMG HSTATX HOK HERR HCELL HNL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E2 ms md hs len cap buf (Ha2 & Hd2 & Hrom2 & HN2 & HB2 & Hm2 & Hh2 & Hhd & Hld & Hfd & Hfs & Hblk & Hba & HL & Hlen & Hcap) KTR.
  pose proof (capoku_bounds cap md Hcap) as Hcb. pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH.
  destruct HIMG as [HI1 HI2].
  pose proof HOK as ((HB1' & HB2') & _ & _ & _ & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh2) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & Hstk & _ & _).
  assert (Hbr' : 16 <= buf /\ buf + cap <= HTOP) by (destruct Hbr as [Hbr|Hbr]; lia).
  (* [comment removed for export] *)
  set (d0 := nth 0 data (Z_to_bv 8 0)). set (d1 := nth 1 data (Z_to_bv 8 0)).
  set (CL := bv_unsigned d0 + 256 * (bv_unsigned d1 mod 128)).
  assert (HCL : Z.of_nat (config_len data) = CL) by (apply config_len_eq; lia).
  assert (HCLr : 0 <= CL <= 32767).
  { pose proof (bv_unsigned_in_range _ d0) as R0. pose proof (bv_unsigned_in_range _ d1) as R1.
    unfold bv_modulus in R0, R1. change (2 ^ Z.of_N 8) with 256 in R0, R1. pose proof (Z.mod_pos_bound (bv_unsigned d1) 128 ltac:(lia)). unfold CL. lia. }
  assert (Hrd : forall i, (i < length data)%nat -> rdn PSEGS (ms_mem ms) (v_addi (Z_to_bv 64 buf) (Z.of_nat i)) 1 = Some [nth i data (Z_to_bv 8 0)]).
  { intros i Hi. pose proof (bytes_at_rdn PSEGS (ms_mem ms) buf data i 1 Hba ltac:(lia)) as X.
    rewrite (firstn1_skipn data i (Z_to_bv 8 0) Hi) in X.
    unfold v_addi. rewrite (u_small64 buf) by (unfold two64; lia). exact X. }
  (* [comment removed for export] *)
  assert (HT : forall T1, T1 = t_emit (W 1 (zero_lines (n_calls data))) (t_exit (exit_code 0) fs0) ->
             t_body data fs0 = if (length data <? 6 + config_len data)%nat then t_die msg_overrun fs0 else T1).
  { intros T1 ->. unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (HE2 : forall x, (x < 200)%positive -> E2 x = E x) by (intros x Hx; symmetry; exact (Ha2 x Hx)).
  assert (H9 : getr (ms_regs ms) 9 = Z_to_bv 64 buf).
  { rewrite (getr_leaf PSEGS E2 Lhd ms 9 (lvar BUF) Hd2) by (vm_compute; reflexivity). rewrite lden_lvar. exact HB2. }
  rewrite (sden_mkst PSEGS E2 Lhd ms Hd2 eq_refl).
  replace (Z_to_bv 64 (s_pc Lhd)) with (Z_to_bv 64 0x2273c) by (vm_compute; reflexivity). rewrite Hrom2.
  apply (@hdr_walk (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_mem ms) md _ (Z_to_bv 64 buf) d0 d1 Hhd Hld H9
           ltac:(exact (Hrd 1%nat ltac:(lia))) ltac:(exact (Hrd 0%nat ltac:(lia)))).
  set (ms' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (HREGS (ms_regs ms) d0 d1) (Z_to_bv 64 0x22750) (ms_mem ms) (seg_rom PSEGS)).
  destruct (havoc_call_sound PSEGS E2 Lhd ms ms' 0x22750 KEEPH5 [] None hok_hd Hd2) as (E' & Ha' & Hd').
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { exact (sden_frm _ _ _ _ Hd2). }
  { intros r Hr _. unfold ms', mkst, HREGS; cbn [ms_regs].
    rewrite !getr_other by (intros Hc; rewrite Hc in Hr; vm_compute in Hr; discriminate Hr). reflexivity. }
  { intros l Hl. discriminate Hl. }
  { intros i R x _ _ _. reflexivity. }
  { intros i R x _ _ Hx. exact Hx. }
  rewrite U_h0_eq in Hd'.
  assert (HE'2 : forall x, (x < s_next Lhd)%positive -> E' x = E2 x) by (intros x Hx; symmetry; exact (Ha' x Hx)).
  assert (Ha'0 : agree 200 E E') by (intros x Hx; etransitivity; [exact (Ha2 x Hx) | apply Ha'; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
  (* [comment removed for export] *)
  assert (HCLV : E' CLV = Z_to_bv 64 CL).
  { pose proof (sden_getr PSEGS E' U_h0 ms' Hd' (Z_to_bv 5 18)) as X.
    replace (rget (s_regs U_h0) (rkey (Z_to_bv 5 18))) with (lvar CLV) in X by (vm_compute; reflexivity).
    rewrite lden_lvar in X. rewrite <- X. unfold ms', mkst, HREGS; cbn [ms_regs].
    replace (Z_to_bv 5 18) with (18%bv : reg) by (apply bv_eq; reflexivity).
    rewrite getr_same by (intros Hc; discriminate Hc). apply bv_eq. rewrite hdr_calc, Z_to_bv_unsigned. unfold CL.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). fold CL. rewrite (Z.mod_small CL) by lia. reflexivity. }
  assert (HBUF' : E' BUF = Z_to_bv 64 buf) by (rewrite HE'2 by (vm_compute; reflexivity); exact HB2).
  assert (HN' : E' N0 = Z_to_bv 64 len) by (rewrite HE'2 by (vm_compute; reflexivity); exact HN2).
  (* [comment removed for export] *)
  assert (UB : bv_unsigned (lden E' (rg_base BMR)) = buf + 2 + CL).
  { cbn [BMR RGz rg_base]. rewrite u_lin2, HBUF', HCLV, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    rewrite (Z.mod_small buf) by lia. rewrite (Z.mod_small CL) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Hdh : sden PSEGS E' U_h ms').
  { rewrite <- U_h_eq. apply fx_add_rg.
    - apply fx_add_fact; [exact Hd' | vm_compute; reflexivity |]. cbn [fact_ok]. rewrite lden_lvar, HCLV, Z_to_bv_unsigned.
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia. lia.
    - rewrite U_h_eq. exact wf_h.
    - apply (rg_rw_stk E' (ms_mem ms') (rg_base BMR) 4 (buf + 2 + CL) UB ltac:(lia) ltac:(unfold two64; lia)).
      unfold ms', mkst; cbn [ms_mem]. apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms) buf (buf + 2 + CL) (buf + cap)) in Hstk as [_ Hstk2]; [|lia].
      apply (OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk_split PSEGS (ms_mem ms) (buf + 2 + CL) (buf + 2 + CL + 4) (buf + cap)) in Hstk2 as [Hstk3 _]; [exact Hstk3 | lia].
    - cbn [s_rgs add_fact]. rewrite Forall_forall. intros R' HR'.
      assert (HR'L : In R' (s_rgs Lhd)) by (replace (s_rgs U_h0) with (s_rgs Lhd) in HR' by (vm_compute; reflexivity); exact HR').
      pose proof (rgs_pos R' HR'L) as Hp.
      apply In_nth_error in HR'L as (i & Hi).
      apply rg_disj_bytes; [rewrite (csz_rsz E' R') by lia; lia | unfold BMR; rsz_simpl; lia |].
      intros j Hj. unfold BMR in Hj. rsz_simpl_in Hj. rewrite UB.
      assert (HO : outside E' (s_rgs Lhd) (Z_to_bv 64 (buf + 2 + CL + j))).
      { apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC (conj HI1 HI2) HI HOK E' (s_rgs Lhd) hs (ms_mem ms) md buf cap); [| exact Hh2 | exact Hblk |].
        - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATI E' (s_rgs Lhd) Ha'0 ltac:(vm_compute; reflexivity)).
        - rewrite u_small64 by (unfold two64; lia). lia. }
      pose proof (outside_nth E' _ _ i R' HO Hi) as X. rewrite u_small64 in X by (unfold two64; lia). exact X. }
  (* [comment removed for export] *)
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 STR U_h LH1 E' ms' md _ TBL_P_ok IMG_P_ok cert_LH1 Hdh ltac:(vm_compute; reflexivity) Hhd Hld).
  intros L E3 ms3 HIn Hd3 Ha3' Hrom3 Hfr3 Hgr3.
  assert (Ha3 : agree 200 E E3) by (intros x Hx; etransitivity; [exact (Ha'0 x Hx) | apply Ha3'; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]]).
  assert (HE3' : forall x, (x < s_next U_h)%positive -> E3 x = E' x) by (intros x Hx; symmetry; exact (Ha3' x Hx)).
  assert (HCLV3 : E3 CLV = Z_to_bv 64 CL) by (rewrite HE3' by (vm_compute; reflexivity); exact HCLV).
  assert (HBUF3 : E3 BUF = Z_to_bv 64 buf) by (rewrite HE3' by (vm_compute; reflexivity); exact HBUF').
  assert (HN3 : E3 N0 = Z_to_bv 64 len) by (rewrite HE3' by (vm_compute; reflexivity); exact HN').
  unfold ms' in Hrom3, Hfr3, Hgr3; cbn [ms_rom ms_mem mkst] in Hrom3, Hfr3, Hgr3.
  (* [comment removed for export] *)
  assert (XB : XBLK HI E' (s_rgs U_h) hs).
  { intros R x HR Hin. rewrite rgs_uh in HR. rewrite skipn_app in HR. replace (skipn 22 (s_rgs Lhd)) with (@nil region) in HR by (vm_compute; reflexivity).
    replace (22 - length (s_rgs Lhd))%nat with O in HR by (vm_compute; reflexivity). cbn [skipn app] in HR. destruct HR as [<-|[]].
    unfold in_rg in Hin. rewrite UB in Hin. unfold BMR in Hin. rsz_simpl_in Hin. exists buf, cap. split; [exact Hblk | lia]. }
  assert (S21 : shape21 (s_rgs U_h)) by (vm_compute; reflexivity).
  assert (Hh3 : hi_Heap HI hs (ms_mem ms3) md).
  { apply (heap_fx_g sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HI HOK HERR HCELL HSTATI
             E' E3 U_h L ms' ms3 hs md Ha'0 Ha3 S21 XB Hdh Hd3 ltac:(vm_compute; reflexivity)); [| exact Hfr3 | exact Hgr3 | exact Hh2].
    rewrite LH1_eq in HIn. destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity. }
  assert (Hm3 : MFXR' (ms_mem ms3)).
  { apply (mfxr_fx_g sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI HOK E' U_h hs (ms_mem ms) md (ms_mem ms) (ms_mem ms3) Ha'0 S21 XB Hh2 Hfr3 Hm2). }
  assert (Hd2b : config_len data <> 0%nat -> mrd PSEGS (ms_mem ms3) (Z_to_bv 64 (buf + 2)) = Some (nth 2 data (Z_to_bv 8 0))).
  { intros Hc. assert (Hc' : 1 <= CL) by lia.
    unfold mrd. rewrite (blk_keep_g sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HI HOK HSTATI
                          E' U_h (ms_mem ms) (ms_mem ms3) hs md buf cap (buf + 2) Ha'0 S21 Hh2 Hblk ltac:(lia)).
    - pose proof (Hrd 2%nat ltac:(lia)) as X. unfold v_addi in X.
      rewrite (u_small64 buf) in X by (unfold two64; lia). change (Z.of_nat 2) with 2 in X.
      pose proof (rdn_rd1 PSEGS (ms_mem ms) (buf + 2) 1 _ ltac:(lia) ltac:(unfold two64; lia) X 0 _ eq_refl) as Y.
      rewrite Z.add_0_r in Y. exact Y.
    - rewrite rgs_uh, skipn_app. replace (skipn 22 (s_rgs Lhd)) with (@nil region) by (vm_compute; reflexivity).
      replace (22 - length (s_rgs Lhd))%nat with O by (vm_compute; reflexivity). cbn [skipn app].
      constructor; [|constructor]. rewrite UB. rewrite u_small64 by (unfold two64; lia). left. lia.
    - exact Hfr3. }
  rewrite (HT _ eq_refl).
  rewrite LH1_eq in HIn. destruct HIn as [<-|[<-|[]]].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E3 Ltr0 ms3 _ Hd3 FC_tr_in) as HF. rewrite FC_tr_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_laddc, !lden_lvar, HN3, HCLV3 in HF. unfold bv_ltu in HF. apply Z.ltb_ge in HF.
    rewrite (u_small64 CL) in HF by (unfold two64; lia). rewrite !u_small64 in HF by (unfold two64; lia).
    replace (length data <? 6 + config_len data)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    pose proof (fx_weaken PSEGS E3 Ltr0 ms3 (firstn 22 (s_rgs Ltr0)) WS21 Hd3 wk_tr ltac:(rewrite Ltr_eq; exact wf_tr)) as Hd4. rewrite Ltr_eq in Hd4.
    apply (KTR E3 ms3). split; [exact Ha3|]. split; [exact Hd4|]. split; [rewrite Hrom3; reflexivity|]. split; [exact HN3|]. split; [exact HBUF3|].
    split; [rewrite HCLV3, HCL; reflexivity|]. split; [exact Hm3|]. split; [exact Hh3|]. split; [exact Hhd|]. split; [exact Hld|].
    split; [exact Hfd|]. split; [exact Hfs|]. split; [exact Hblk|]. split; [exact Hd2b|]. split; [exact HL|]. split; [lia | exact Hcap].
  - (* [comment removed for export] *)
    pose proof (sden_fact PSEGS E3 Lov0 ms3 _ Hd3 FC_ov_in) as HF. rewrite FC_ov_eq in HF. cbn [fact_ok branch_taken] in HF.
    rewrite lden_laddc, !lden_lvar, HN3, HCLV3 in HF. unfold bv_ltu in HF. apply Z.ltb_lt in HF.
    rewrite (u_small64 CL) in HF by (unfold two64; lia). rewrite !u_small64 in HF by (unfold two64; lia).
    replace (length data <? 6 + config_len data)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    pose proof (fx_weaken PSEGS E3 Lov0 ms3 (firstn 22 (s_rgs Lov0)) WS21 Hd3 wk_ov ltac:(rewrite Lov_eq; exact wf_ov)) as Hd4. rewrite Lov_eq in Hd4.
    apply (overrun_path sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Htid ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB (conj HI1 HI2) HSTATX
             HI HOK HERR HCELL HNL HSTATI fs0 E3 ms3 md hs cap buf Ha3 Hd4 ltac:(rewrite Hrom3; reflexivity) HBUF3 Hm3 Hh3 Hhd Hld Hfd Hfs Hblk).
Qed.
End E3.
