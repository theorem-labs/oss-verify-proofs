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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall2 PUsageCert POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv PLoop1 PEofCert PEof1 PLoopInv2 PEof3 PTgtCert PLoop2 PLoop3 PTgt1 PTgt2 PDrvFuzz Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Local Notation stk := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.stk.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition PRO : list (Z * Z) := [(0x10000, 0x22000); (0x64de0, 0x64de4)].

Lemma u_fz_ok : forall u kc, 0 <= kc <= 3 -> u <= UT0 + kc * FUZZ_CHARGE -> u + FUZZ_CHARGE <= UBOUND.
Proof.
  intros u kc Hk Hu. assert (HF : FUZZ_CHARGE = 12583728) by reflexivity. assert (HT : UT0 = 494927872) by reflexivity.
  assert (HB : UBOUND = 1073741824) by reflexivity. rewrite HF, HT in Hu. rewrite HF, HB. nia.
Qed.

(* [comment removed for export] *)
Definition KRO (x : Z) : Prop := 0x16100 <= x < 0x16120 \/ 0x182a8 <= x < 0x18327.

Section T3.
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
(* [comment removed for export] *)
Hypothesis HFZ : fuzz_contract PSEGS DCFG (hi_HS HI) (hi_Heap HI) (hi_blocks HI) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0)
  IMG_LO IMG_END HTOP STATIC CELLS_NE 0x22b18 8496 PRO.
Hypothesis HSRO : forall x, 0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4 -> ~ KRO x -> ioutside STATIC x.
Hypothesis HKRO : forall hs m md, hi_Heap HI hs m md -> pristine m 0x16100 0x16120 /\ pristine m 0x182a8 0x18327.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation TRHEAD' := (TRHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0).
Local Notation CL := (Z.of_nat (config_len data)).
Local Notation CALLS := (Z.of_nat (n_calls data)).



Local Notation seg_xfer' := (seg_xfer sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI).
Local Notation avoid_m2' := (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI).
Local Notation mfxr_chg' := (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC).

(* [comment removed for export] *)
Definition ITHEAD (F : sst) (kc : Z) (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf al ow : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 F ms /\ ms_rom ms = seg_rom PSEGS /\ E1 N0 = Z_to_bv 64 len /\ E1 BUF = Z_to_bv 64 buf /\
  E1 CLV = Z_to_bv 64 CL /\ E1 RV = Z_to_bv 64 CALLS /\ E1 AV = Z_to_bv 64 al /\ E1 OV = Z_to_bv 64 ow /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDS0 /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  len = Z.of_nat (length data) /\ 6 + CL <= len < cap /\ CAPOK cap /\ U md <= UT0 + kc * FUZZ_CHARGE /\
  ((len = 6 + CL /\ al = 0x75070 /\ ow = 0) \/ (6 + CL < len /\ al = ow /\ In (ow, len - 6 - CL) (hi_blocks HI hs) /\ 16 <= ow)).

#[using="Hargc2"] Lemma fz_ithead : forall E5 ms md hs len cap buf al ow,
  PTgt2.FZHEAD sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC HI data fs0 E5 ms md hs len cap buf al ow -> ITHEAD G0 0 E5 ms md hs len cap buf al ow.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E5 ms md hs len cap buf al ow (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 (conj A13
    (conj A14 (conj A15 (conj A16 (conj A17 (conj A18 (conj A19 (conj _ A21)))))))))))))))))))). lia.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma rodata_idx : forall E' rgs x i R, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) -> 0x10000 <= bv_unsigned x < 0x22000 ->
  nth_error rgs i = Some R -> in_rg E' R x -> (11 <= i <= 20)%nat.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' rgs x i R Ha Hs Hx Hi Hin. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  assert (HE : forall y, (y < 200)%positive -> E' y = E y) by (intros y Hy; symmetry; exact (Ha y Hy)).
  pose proof (nth_shape rgs i R Hi) as Hsh. rewrite Hs, shape_m2_eq in Hsh. unfold in_rg, rsz in Hin.
  do 22 (destruct i as [|i]; [cbn [nth_error SHAPE_M2] in Hsh; injection Hsh as Hb Hz; rewrite <- Hb, <- Hz in Hin; clear Hb Hz;
    rewrite ?u_lin0 in Hin by lia; rewrite ?u_lin1, ?u_lin2 in Hin; rewrite ?HE in Hin by lia;
    change (E 1%positive) with sp0 in Hin; rewrite ?(E_P1 sp0 av ev tid rdraw regs Hargc2) in Hin;
    try (change (E 4%positive) with (E_main sp0 av ev tid (canary rdraw) regs 4%positive) in Hin; rewrite (E_P1 sp0 av ev tid rdraw regs Hargc2) in Hin);
    change (E 8%positive) with (Z_to_bv 64 (Z.of_nat (length (nth 1 av [])))) in Hin;
    rewrite ?u_small64 in Hin by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64; lia);
    rewrite ?Z.mod_small in Hin by (pose proof (valid_argv_str_len av 1 Hva ltac:(lia)); unfold two64 in *; lia); lia |]).
  cbn [nth_error SHAPE_M2] in Hsh. destruct i; discriminate Hsh.
Qed.

(* [comment removed for export] *)
#[using="uid hw mem Hsp Hva Hve ME Hargc2"] Lemma fmin_out : forall E' rgs x, agree 200 E E' -> shape rgs = shape (s_rgs P_main2) -> 0x64de0 <= bv_unsigned x < 0x64de4 -> outside E' rgs x.
Proof. LiaFast.lf_pins (fun (uid hw mem Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E' rgs x Ha Hs Hx. pose proof (sp0_lo sp0 Hsp). pose proof (sp0_hi sp0 Hsp).
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

Definition ro_kinds (F : sst) : bool := forallb (fun i => match rg_kind (rgn F i) with RO => true | _ => false end) (seq 11 10).

#[using="Type"] Lemma mfxr_nowhere : forall E1 (F : sst) ms x, agree 200 E E1 -> shape (s_rgs F) = shape (s_rgs P_main2) ->
  outside E1 (s_rgs F) x -> ~ HEAPX IMG_LO IMG_END HTOP STATIC (bv_unsigned x) -> ~ RSX (bv_unsigned x) -> MFXR' (ms_mem ms) ->
  ms_mem ms x = mem x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E1 F ms x Ha Hs Ho Hh Hr Hm. apply Hm; [|exact Hh | exact Hr].
  apply (outside_agree 200 E1 E (s_rgs P_main2) x bases_main2 (fun y Hy => eq_sym (Ha y Hy))).
  exact (outside_shape E1 (s_rgs F) (s_rgs P_main2) x (eq_sym Hs) Ho).
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HIMG HOK HSRO HKRO"] Lemma pristine_ro : forall E1 (F : sst) ms hs md, agree 200 E E1 -> sden PSEGS E1 F ms -> shape (s_rgs F) = shape (s_rgs P_main2) ->
  ro_kinds F = true -> (22 <= length (s_rgs F))%nat -> MFXR' (ms_mem ms) -> hi_Heap HI hs (ms_mem ms) md ->
  Forall (fun r => pristine (ms_mem ms) (fst r) (snd r)) PRO.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HIMG HOK HSRO HKRO : LiaFast.U) => LiaFast.u0).
  intros E1 F ms hs md Ha Hd Hs Hk Hl Hm Hh. destruct HIMG as [HI1 HI2]. pose proof HOK as ((HB1 & HB2) & _).
  destruct (HKRO hs (ms_mem ms) md Hh) as ((_ & _ & K1) & (_ & _ & K2)).
  assert (Hnh : forall x, (0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4) -> ~ KRO x -> ~ HEAPX IMG_LO IMG_END HTOP STATIC x).
  { intros x Hx Hkx (H1 & H2). destruct H2 as [H2|[H2|H2]]; [exact (H2 (HSRO x Hx Hkx)) | lia | lia]. }
  assert (Hnr : forall x, (0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4) -> ~ RSX x) by (intros x Hx Hc; unfold RSX, RS_LO in Hc; lia).
  unfold PRO. constructor; [|constructor; [|constructor]]; cbn [fst snd].
  - split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hc : (0x16100 <= i < 0x16120) \/ (0x182a8 <= i < 0x18327) \/ ~ KRO i) by (unfold KRO; lia).
    destruct Hc as [Hc|[Hc|Hc]]; [exact (K1 i Hc) | exact (K2 i Hc) |]. unfold wa.
    assert (Ux : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small64; unfold two64; lia).
    destruct (outside_or_in E1 (s_rgs F) (Z_to_bv 64 i)) as [Ho|(j & R & Hj & Hin)].
    + rewrite (mfxr_nowhere E1 F ms _ Ha Hs Ho ltac:(rewrite Ux; apply Hnh; [lia | exact Hc]) ltac:(rewrite Ux; apply Hnr; lia) Hm).
      replace i with (0x10000 + (i - 0x10000)) by lia.
      apply (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME 0x10000 (Z.to_nat 73728) (i - 0x10000));
        [lia | rewrite Z2Nat.id by lia; lia | vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
    + pose proof (rodata_idx E1 (s_rgs F) (Z_to_bv 64 i) j R Ha Hs ltac:(rewrite Ux; lia) Hj Hin) as Hj'.
      pose proof (sden_rg _ _ _ _ _ _ Hd Hj) as HR. destruct HR as (_ & _ & HA & _).
      assert (HkR : rg_kind R = RO).
      { unfold ro_kinds in Hk. rewrite forallb_forall in Hk. pose proof (Hk j ltac:(apply in_seq; lia)) as X.
        unfold rgn in X. rewrite (nth_error_nth _ _ _ Hj) in X. destruct (rg_kind R); [discriminate | reflexivity | discriminate | discriminate | discriminate]. }
      unfold in_rg in Hin. rewrite HkR in HA. destruct (HA (bv_unsigned (Z_to_bv 64 i) - bv_unsigned (lden E1 (rg_base R))) ltac:(lia)) as [X _].
      replace (bv_unsigned (lden E1 (rg_base R)) + (bv_unsigned (Z_to_bv 64 i) - bv_unsigned (lden E1 (rg_base R)))) with i in X by lia. exact X.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold wa.
    assert (Ux : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small64; unfold two64; lia).
    rewrite (mfxr_nowhere E1 F ms _ Ha Hs (fmin_out E1 (s_rgs F) _ Ha Hs ltac:(rewrite Ux; lia)) ltac:(rewrite Ux; apply Hnh; [lia | unfold KRO; lia]) ltac:(rewrite Ux; apply Hnr; lia) Hm).
    replace i with (0x64de0 + (i - 0x64de0)) by lia.
    apply (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME 0x64de0 4 (i - 0x64de0)); [lia | lia | vm_compute; reflexivity | lia].
Qed.

(* [comment removed for export] *)
Definition fz_tmpl (F : sst) : bool :=
  (Z.eqb (s_pc F) 0x22b18 && match s_resv F with RNone => true | _ => false end &&
   lin_eqb (rget (s_regs F) (rk 1)) (lconst 0x229d4) && lin_eqb (rget (s_regs F) (rk 2)) (laddc SP0 (-208)) &&
   lin_eqb (rget (s_regs F) (rk 3)) (lconst 0x10800) && lin_eqb (rget (s_regs F) (rk 4)) (lconst 0x75bd0) &&
   lin_eqb (rget (s_regs F) (rk 10)) (lvar AV) && lin_eqb (rget (s_regs F) (rk 11)) NF &&
   havoc_ok F ZFP (Some (lconst 0)) && Nat.ltb 21 (length (s_rgs F)) &&
   lin_eqb (rg_base (rgn F 7)) (lconst 0x75b28) && lin_eqb (rg_base (rgn F 0)) (laddc SP0 (-65536)) &&
   match rg_kind (rgn F 0) with RW => true | _ => false end && Z.eqb (csz (rgn F 0)) 65536 &&
   shape_eqb (s_rgs F) (s_rgs P_main2) && ro_kinds F && Pos.leb 502 (s_next F))%bool.

#[using="Type"] Lemma fz_tmpl_spec : forall F, fz_tmpl F = true ->
  s_pc F = 0x22b18 /\ s_resv F = RNone /\ rget (s_regs F) (rk 1) = lconst 0x229d4 /\ rget (s_regs F) (rk 2) = laddc SP0 (-208) /\
  rget (s_regs F) (rk 3) = lconst 0x10800 /\ rget (s_regs F) (rk 4) = lconst 0x75bd0 /\
  rget (s_regs F) (rk 10) = lvar AV /\ rget (s_regs F) (rk 11) = NF /\ havoc_ok F ZFP (Some (lconst 0)) = true /\
  (21 < length (s_rgs F))%nat /\ rg_base (rgn F 7) = lconst 0x75b28 /\ rg_base (rgn F 0) = laddc SP0 (-65536) /\
  rg_kind (rgn F 0) = RW /\ csz (rgn F 0) = 65536 /\ shape (s_rgs F) = shape (s_rgs P_main2) /\ ro_kinds F = true /\ (502 <= s_next F)%positive.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros F H. unfold fz_tmpl in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?H] end.
  repeat match goal with
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
         | H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H
         | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
         | H : shape_eqb _ _ = true |- _ => apply shape_eqb_eq in H
         | H : Pos.leb _ _ = true |- _ => apply Pos.leb_le in H
         end.
  destruct (s_resv F); try discriminate. destruct (rg_kind (rgn F 0)); try discriminate.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HSTATI HFZ HSRO HKRO"] Theorem fuzz_step : forall (F : sst) (kc : Z) E1 ms md hs len cap buf al ow T,
  fz_tmpl F = true -> 0 <= kc <= 3 ->
  ITHEAD F kc E1 ms md hs len cap buf al ow ->
  (forall E2 ms2 md2 hs2, ITHEAD (havoc_call F 0x229d4 KEEPH ZFP (Some (lconst 0))) (kc + 1) E2 ms2 md2 hs2 len cap buf al ow ->
      realizes PSEGS (mkCfg ms2 md2) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HSTATI HFZ HSRO HKRO : LiaFast.U) => LiaFast.u0).
  intros F kc E1 ms md hs len cap buf al ow T Hft Hkc
    (Ha1 & Hd1 & Hrom1 & HN1 & HB1 & HC1 & HR1 & HAV1 & HOV1 & Hm1 & Hh1 & Hhd & Hld & Hfd & Hfs & Hblk & HL & Hlen & Hcap & HU1 & Hpay) K.
  destruct (fz_tmpl_spec F Hft) as (Gpc & Grv & G1 & G2 & G3 & G4 & G10 & G11 & Gok & Gln & G7 & G0b & G0k & G0s & Gsh & Gro & Gnx).
  pose proof (capok_bounds cap Hcap) as Hcb. destruct HIMG as [HI1 HI2].
  pose proof (sp0_lo sp0 Hsp) as SL. pose proof (sp0_hi sp0 Hsp) as SH. pose proof (sp0_al sp0 Hsp) as Al.
  pose proof HOK as ((HB1' & HB2') & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & _). destruct (HBL buf cap Hblk) as (Hcap1 & Hbr & _ & _ & _).
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x229d4) by (exact (getr_leaf_c PSEGS E1 F ms 1 _ Hd1 G1)).
  assert (R2 : getr (ms_regs ms) 2 = Z_to_bv 64 (bv_unsigned sp0 - 208)).
  { rewrite (getr_leaf PSEGS E1 F ms 2 (laddc SP0 (-208)) Hd1 G2). rewrite lden_laddc. unfold SP0. rewrite lden_lvar, HE1 by lia. reflexivity. }
  assert (R3 : getr (ms_regs ms) 3 = Z_to_bv 64 0x10800) by (exact (getr_leaf_c PSEGS E1 F ms 3 _ Hd1 G3)).
  assert (R4 : getr (ms_regs ms) 4 = Z_to_bv 64 0x75bd0) by (exact (getr_leaf_c PSEGS E1 F ms 4 _ Hd1 G4)).
  assert (R10 : getr (ms_regs ms) 10 = Z_to_bv 64 al) by (rewrite (getr_leaf PSEGS E1 F ms 10 (lvar AV) Hd1 G10), lden_lvar; exact HAV1).
  assert (R11 : getr (ms_regs ms) 11 = Z_to_bv 64 (len - 6 - CL)).
  { rewrite (getr_leaf PSEGS E1 F ms 11 NF Hd1 G11). apply bv_eq. rewrite (u_NF E1 len CL HN1 HC1) by lia.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity. }
  apply (fx_fuzz HI (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) IMG_LO IMG_END HTOP STATIC HOK 8496 PRO HFZ E1 F ms md hs (len - 6 - CL) 0 7 56832
           (bv_unsigned sp0 - 208) (rgn F 7) T Hd1 Gpc Grv Hrom1 Gok (rgn_eq F 7 ltac:(lia)) ltac:(rewrite G7; apply u_lconst; lia)
           Hh1 (conj Hhd Hld) (u_fz_ok (U md) kc Hkc HU1) R11 ltac:(lia)).
  - destruct Hpay as [(A & B & C) | (A & B & C & D)]; [left; lia|]. right. destruct (HBL ow (len - 6 - CL) C) as (_ & Hor & _).
    rewrite R10, u_small64 by (unfold two64; unfold valid_sp in Hsp; destruct Hor as [Hor|Hor]; lia). rewrite B. exact C.
  - rewrite R1. vm_compute. reflexivity.
  - exact R3.
  - exact R4.
  - exact R2.
  - lia.
  - lia.
  - lia.
  - unfold valid_sp in Hsp. lia.
  - lia.
  - apply (frame_sp sp0 SL SH E1 F 0 (-65536)); [lia | exact G0b | unfold SP0; rewrite lden_lvar, HE1 by lia; reflexivity | lia | rewrite G0k; reflexivity | lia | rewrite (csz_rsz E1 (rgn F 0)) by lia; lia | lia].
  - exact (avoid_m2' E1 (s_rgs F) Ha1 Gsh).
  - exact (pristine_ro E1 F ms hs md Ha1 Hd1 Gsh Gro ltac:(lia) Hm1 Hh1).
  - intros E2 ms2 md2 hs2 Ha12 Hd2 Hrom2 Hh2 Hmd2 Hvo HU2 Hsame Hmunch Hblks Hcells.
    destruct Hmd2 as [Hh2l Hl2l]. rewrite R1, u_small64 in Hd2 by (unfold two64; lia). rewrite Hrom1 in Hrom2.
    assert (HE21 : forall x, (x < s_next F)%positive -> E2 x = E1 x) by (intros x Hx; symmetry; exact (Ha12 x Hx)).
    assert (Hlt : forall x, (x < 502)%positive -> (x < s_next F)%positive) by (intros x Hx; lia).
    destruct (HBLK hs2 (ms_mem ms2) md2 Hh2) as (HBL2 & _).
    apply (K E2 ms2 md2 hs2). split; [intros x Hx; etransitivity; [exact (Ha1 x Hx) | apply Ha12; lia]|].
    split; [exact Hd2|]. split; [exact Hrom2|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HN1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HB1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HC1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HR1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HAV1|].
    split; [rewrite HE21 by (apply Hlt; vm_compute; reflexivity); exact HOV1|].
    split.
    { apply (mfxr_chg' (ms_mem ms)); [|exact Hm1].
      intros x Hx Hr Hs. apply Hmunch. apply HIface.outside_app. split.
      - destruct (HIface.outside_dec STATIC (bv_unsigned x)) as [A|A]; [exact A|]. exfalso. apply Hx. split; [|left; exact A].
        pose proof (HB2' _ A). lia.
      - cbn [ioutside]. split; [intros Hc; apply Hx; split; [lia | right; left; lia]|].
        split; [intros Hc; apply Hx; split; [lia | right; right; lia]|]. split; [|exact I]. intros Hc. apply Hs. lia. }
    split; [exact Hh2|]. split; [exact Hh2l|]. split; [exact Hl2l|].
    split; [rewrite (vm_only_fds md md2 Hvo); exact Hfd|]. split; [rewrite (vm_only_fs md md2 Hvo); exact Hfs|].
    split; [apply Hsame; exact Hblk|]. split; [exact HL|]. split; [lia|]. split; [exact Hcap|].
    split; [lia|].
    destruct Hpay as [(A & B & C) | (A & B & C & D)]; [left; split; [exact A | split; assumption] | right; split; [exact A | split; [exact B | split; [apply Hsame; exact C | exact D]]]].
Qed.

End T3.
