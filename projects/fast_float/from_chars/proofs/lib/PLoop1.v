(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StoreOk MemSplit DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SysNodesCfg AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxPlan FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvExit PDrvSys PDrvHeap PDrvHeap2 PDrvRead RefStartup RefStartupDefs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import POpenCert POpen1 PDirCert PDir PLoopCert PLoopInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

Lemma u_lin2k : forall E c x y k1 k2, bv_unsigned (lden E (LIN c [(x, k1); (y, k2)])) = (c + k1 * bv_unsigned (E x) + k2 * bv_unsigned (E y)) mod 2^64.
Proof.
  intros E c x y k1 k2. unfold lden, lz. cbn [l_c l_t tsum]. unfold vz. rewrite Z.add_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fd_insert_twice : forall fds (fd : word) e e', fd_insert (fd_insert fds fd e) fd e' = fd_insert fds fd e'.
Proof.
  intros fds fd e e'. unfold fd_insert. cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb]. f_equal.
  induction fds as [|[k v] r IH]; [reflexivity|]. cbn [List.filter fst]. destruct (bv_eqb k fd) eqn:Hk; cbn [negb]; [exact IH|].
  cbn [List.filter fst]. rewrite Hk. cbn [negb]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition FC_ra : fact := Eval vm_compute in nth 0 (s_facts Lra) (FRange (lconst 0) 0 0).
Definition FC_rb : fact := Eval vm_compute in nth 0 (s_facts Lrb) (FRange (lconst 0) 0 0).
Lemma FC_ra_in : In FC_ra (s_facts Lra). Proof. vm_compute. tauto. Qed.
Lemma FC_rb_in : In FC_rb (s_facts Lrb). Proof. vm_compute. tauto. Qed.
Lemma FC_ra_eq : FC_ra = FCond BC_LTU (LIN 0 [(N0, 18446744073709551615); (C0, 1)]) (lconst 65536) false. Proof. vm_compute. reflexivity. Qed.
Lemma FC_rb_eq : FC_rb = FCond BC_LTU (LIN 0 [(N0, 18446744073709551615); (C0, 1)]) (lconst 65536) true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lden_caplen : forall E1 len cap, E1 N0 = Z_to_bv 64 len -> E1 C0 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2^64 ->
  bv_unsigned (lden E1 (LIN 0 [(N0, 18446744073709551615); (C0, 1)])) = cap - len.
Proof.
  intros E1 len cap HN HC Hl Hc. rewrite u_lin2k, HN, HC. rewrite !u_small64 by (unfold two64; lia).
  replace (0 + 18446744073709551615 * len + 1 * cap) with ((cap - len) + len * 2^64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition CAPOK (cap : Z) : Prop := exists j : nat, (j <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat j.
Lemma capok_bounds : forall cap, CAPOK cap -> 65536 <= cap <= 67108864.
Proof.
  intros cap (j & Hj & ->). split.
  - assert (1 <= 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg || (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia); lia). lia.
  - assert (2 ^ Z.of_nat j <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Definition CAPOKU (cap : Z) (md : Model) : Prop := CAPOK cap /\ UOK cap md.
Lemma capoku_bounds : forall cap md, CAPOKU cap md -> 65536 <= cap <= 67108864.
Proof. intros cap md [H _]. exact (capok_bounds cap H). Qed.

Section L1.
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
(* [comment removed for export] *)
Hypothesis HSTATR : forall x, RSX x -> ioutside STATIC x.
(* [comment removed for export] *)
Variable data : list byte.
Variable fs0 : Fs.Fs.
Hypothesis Hlk : fs_lookup fs0 (nth 1 av []) = Some data.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation a1s := (nth 1 av []).
Local Notation MFXR' := (MFXR sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC).
Local Notation HEAPX' := (HEAPX IMG_LO IMG_END HTOP STATIC).

Definition FDF (len : Z) : list (word * FdEntry) := fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 len)).

(* [comment removed for export] *)
Definition LHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 LOOPT ms /\ ms_rom ms = seg_rom PSEGS /\
  E1 N0 = Z_to_bv 64 len /\ E1 C0 = Z_to_bv 64 cap /\ E1 BUF = Z_to_bv 64 buf /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDF len /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  bytes_at PSEGS (ms_mem ms) buf (firstn (Z.to_nat len) data) /\
  0 <= len < cap /\ len <= Z.of_nat (length data) /\ CAPOKU cap md.

(* [comment removed for export] *)
Definition RHEAD (E1 : valu) (ms : machine_state) (md : Model) (hs : hi_HS HI) (len cap buf n : Z) : Prop :=
  agree 200 E E1 /\ sden PSEGS E1 U_r ms /\ ms_rom ms = seg_rom PSEGS /\
  E1 N0 = Z_to_bv 64 len /\ E1 C0 = Z_to_bv 64 cap /\ E1 BUF = Z_to_bv 64 buf /\ E1 NR = Z_to_bv 64 n /\
  MFXR' (ms_mem ms) /\ hi_Heap HI hs (ms_mem ms) md /\ m_halted md = None /\ m_vm_lazy md = [] /\
  m_fds md = FDF (len + n) /\ m_fs md = fs0 /\ In (buf, cap) (hi_blocks HI hs) /\
  bytes_at PSEGS (ms_mem ms) buf (firstn (Z.to_nat len) data) /\
  bytes_at PSEGS (ms_mem ms) RS_LO (firstn (Z.to_nat n) (skipn (Z.to_nat len) data)) /\
  n = Z.min (Z.min (cap - len) 65536) (Z.of_nat (length data) - len) /\
  0 <= len < cap /\ len <= Z.of_nat (length data) /\ CAPOKU cap md.



(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI"] Lemma seg_xfer : forall E1 E2 (S L : sst) ms1 ms2 hs md (p : Z) bs,
  agree 200 E E1 -> agree (s_next S) E1 E2 -> (200 <= s_next S)%positive -> shape (s_rgs S) = shape (s_rgs P_main2) ->
  sden PSEGS E1 S ms1 -> sden PSEGS E2 L ms2 -> cells_tmpl S = true -> cells_tmpl L = true ->
  (forall x, outside E1 (s_rgs S) x -> ms_mem ms2 x = ms_mem ms1 x) -> mem_grows (ms_mem ms1) (ms_mem ms2) ->
  MFXR' (ms_mem ms1) -> hi_Heap HI hs (ms_mem ms1) md ->
  (exists n, In (p, n) (hi_blocks HI hs) /\ Z.of_nat (length bs) <= n) -> bytes_at PSEGS (ms_mem ms1) p bs ->
  agree 200 E E2 /\ MFXR' (ms_mem ms2) /\ hi_Heap HI hs (ms_mem ms2) md /\ bytes_at PSEGS (ms_mem ms2) p bs.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI : LiaFast.U) => LiaFast.u0).
  intros E1 E2 S L ms1 ms2 hs md p bs Ha1 Ha12 Hnx Hs Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hm Hh (n & Hb & Hn) Hba.
  assert (Ha2 : agree 200 E E2) by (intros x Hx; rewrite (Ha1 x Hx); apply Ha12; lia).
  split; [exact Ha2|]. split; [exact (mfxr_fx sp0 av ev tid rdraw regs mem IMG_LO IMG_END HTOP STATIC E1 S _ _ Ha1 Hs Hfr Hm)|].
  split; [exact (heap_fx sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HI HOK HERR HCELL HSTATI
                    E1 E2 S L ms1 ms2 hs md Ha1 Ha2 Hs Hd1 Hd2 Hc1 Hc2 Hfr Hgr Hh)|].
  destruct Hba as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (B3 i Hi).
  unfold mrd. rewrite Hfr; [reflexivity|].
  apply (blk_out av Hargc2 IMG_LO IMG_END HTOP STATIC HIMG HI HOK E1 (s_rgs S) hs (ms_mem ms1) md p n); [| exact Hh | exact Hb |].
  - exact (avoid_m2 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 IMG_LO IMG_END HTOP STATIC HTOPB HIMG HSTATI E1 (s_rgs S) Ha1 Hs).
  - rewrite u_small64 by (unfold two64; lia). lia.
Qed.

#[using="Type"] Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3. Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HMV HSTATR Hlk"] Theorem head_to_r : forall E1 ms md hs len cap buf T,
  LHEAD E1 ms md hs len cap buf ->
  (forall E2 ms2 md2 n, RHEAD E2 ms2 md2 hs len cap buf n -> realizes PSEGS (mkCfg ms2 md2) T) ->
  realizes PSEGS (mkCfg ms md) T.
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 HTOPB HIMG HOK HERR HCELL HSTATI HMV HSTATR Hlk : LiaFast.U) => LiaFast.u0).
  intros E1 ms md hs len cap buf T (Ha1 & Hd1 & Hrom1 & HN & HC & HB & Hm1 & Hh1 & Hhl & Hlz & Hfd & Hfs & Hblk & Hba & Hlen & Hld & Hcap) Hk.
  pose proof (capoku_bounds cap md Hcap) as Hcb. destruct HIMG as [HI1 HI2].
  pose proof HOK as ((HB1 & HB2) & _ & _ & HFRAME & HBLK).
  destruct (HBLK hs (ms_mem ms) md Hh1) as (HBL & HOWN).
  destruct (HBL buf cap Hblk) as (_ & Hbr & _).
  apply (rzc_fx_explore_fg PSEGS DCFG TBL_P IMG_P 4000 SL1 LOOPT LI E1 ms md _ TBL_P_ok IMG_P_ok cert_LI Hd1 ltac:(vm_compute; reflexivity) Hhl Hlz).
  intros L E2 ms2 HIn Hd2 Ha12 Hrom2 Hfr2 Hgr2.
  assert (HLc : cells_tmpl L = true) by (rewrite LI_eq in HIn; destruct HIn as [<-|[<-|[]]]; vm_compute; reflexivity).
  destruct (seg_xfer E1 E2 LOOPT L ms ms2 hs md buf (firstn (Z.to_nat len) data) Ha1 Ha12 ltac:(vm_compute; congruence)
              ltac:(vm_compute; reflexivity) Hd1 Hd2 ltac:(vm_compute; reflexivity) HLc Hfr2 Hgr2 Hm1 Hh1
              ltac:(exists cap; split; [exact Hblk | rewrite length_firstn; lia]) Hba) as (Ha2 & Hm2 & Hh2 & Hba2).
  assert (HN2 : E2 N0 = Z_to_bv 64 len) by (rewrite <- (Ha12 N0) by (vm_compute; reflexivity); exact HN).
  assert (HC2 : E2 C0 = Z_to_bv 64 cap) by (rewrite <- (Ha12 C0) by (vm_compute; reflexivity); exact HC).
  assert (HB2' : E2 BUF = Z_to_bv 64 buf) by (rewrite <- (Ha12 BUF) by (vm_compute; reflexivity); exact HB).
  rewrite Hrom1 in Hrom2.
  (* [comment removed for export] *)
  assert (Hwant : exists want sg, want = Z.min (cap - len) 65536 /\ sden PSEGS (ecomp E2 sg) Lr ms2 /\ agree NXR E2 (ecomp E2 sg) /\
                    getr (ms_regs ms2) 12 = Z_to_bv 64 want).
  { rewrite LI_eq in HIn. destruct HIn as [<-|[<-|[]]].
    - exists 65536, sig_ra. pose proof (sden_fact PSEGS E2 Lra ms2 _ Hd2 FC_ra_in) as HF. rewrite FC_ra_eq in HF.
      cbn [fact_ok branch_taken] in HF. unfold bv_ltu in HF. rewrite (lden_caplen E2 len cap HN2 HC2 ltac:(lia) ltac:(lia)), u_lconst in HF by lia.
      apply Z.ltb_ge in HF.
      split; [lia|]. split; [exact (entails_sden PSEGS E2 Lra Lr sig_ra ms2 (sden_0 _ _ _ _ Hd2) ent_ra Lr_wf)|].
      split; [exact (fixed_below_agree E2 sig_ra NXR ltac:(vm_compute; reflexivity))|].
      apply (getr_leaf_c PSEGS E2 Lra); [exact Hd2 | vm_compute; reflexivity].
    - exists (cap - len), sig_rb. pose proof (sden_fact PSEGS E2 Lrb ms2 _ Hd2 FC_rb_in) as HF. rewrite FC_rb_eq in HF.
      cbn [fact_ok branch_taken] in HF. unfold bv_ltu in HF. rewrite (lden_caplen E2 len cap HN2 HC2 ltac:(lia) ltac:(lia)), u_lconst in HF by lia.
      apply Z.ltb_lt in HF.
      split; [lia|]. split; [exact (entails_sden PSEGS E2 Lrb Lr sig_rb ms2 (sden_0 _ _ _ _ Hd2) ent_rb Lr_wf)|].
      split; [exact (fixed_below_agree E2 sig_rb NXR ltac:(vm_compute; reflexivity))|].
      rewrite (getr_leaf PSEGS E2 Lrb ms2 12 (LIN 0 [(N0, 18446744073709551615); (C0, 1)]) Hd2) by (vm_compute; reflexivity).
      apply bv_eq. rewrite (lden_caplen E2 len cap HN2 HC2 ltac:(lia) ltac:(lia)). rewrite u_small64 by (unfold two64; lia). reflexivity. }
  destruct Hwant as (want & sg & Hw & Hd3 & Ha23 & H12).
  set (E3 := ecomp E2 sg) in *.
  assert (Ha3 : agree 200 E E3) by (intros x Hx; rewrite (Ha2 x Hx); apply Ha23; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms2) 10 = Z_to_bv 64 3) by (apply (getr_leaf_c PSEGS E3 Lr); [exact Hd3 | vm_compute; reflexivity]).
  set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)).
  assert (Hbs : bs = firstn (Z.to_nat want) (skipn (Z.to_nat len) data)).
  { unfold bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite !u_small64 by (unfold two64; lia). reflexivity. }
  assert (Hbl : Z.of_nat (length bs) = Z.min want (Z.of_nat (length data) - len)).
  { rewrite Hbs, length_firstn, length_skipn. lia. }
  apply (fx_read E3 Lr ms2 md a1s (Z_to_bv 64 len) data want T Hd3 eq_refl eq_refl Hrom2 Hhl Hlz
           ltac:(apply (getr_leaf_c PSEGS E3 Lr); [exact Hd3 | vm_compute; reflexivity])
           ltac:(rewrite Hfd, R10, fd32_3; unfold FDF, fd_insert; cbn [fd_lookup]; rewrite bv_eqb_refl; reflexivity)
           ltac:(rewrite Hfs; exact Hlk)
           ltac:(apply (getr_leaf_c PSEGS E3 Lr); [exact Hd3 | vm_compute; reflexivity])
           H12 ltac:(lia) hok_r).
  - intros i R x Hi Hin HRS.
    pose proof (rs_out sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2 E3 (s_rgs Lr) x Ha3 ltac:(vm_compute; reflexivity) HRS) as Ho.
    pose proof (outside_nth E3 _ x i R Ho Hi) as Hx. unfold in_rg in Hin. lia.
  - intros E4 ms4 Ha34 Hd4 Hrom4 Hm4 H10. fold bs in Hm4, H10 |- *.
    assert (Hba' : Z.of_nat (length bs) <= 65536) by lia.
    assert (HNR : E4 NR = len_word bs).
    { rewrite <- H10. rewrite (getr_leaf PSEGS E4 _ ms4 10 (lvar NR) Hd4) by (vm_compute; reflexivity). rewrite lden_lvar. reflexivity. }
    assert (Hd4' : sden PSEGS E4 U_r ms4).
    { rewrite <- U_r_eq. apply fx_add_fact; [exact Hd4 | vm_compute; reflexivity |].
      cbn [fact_ok]. rewrite lden_lvar, HNR. unfold len_word. rewrite u_small64 by (unfold two64; lia). lia. }
    assert (Ha4 : agree 200 E E4) by (intros x Hx; rewrite (Ha3 x Hx); apply Ha34; apply (Pos.lt_trans _ 200); [exact Hx | vm_compute; reflexivity]).
    assert (HE43 : forall x, (x < NXR)%positive -> E4 x = E2 x).
    { intros x Hx. rewrite <- (Ha34 x) by (apply (Pos.lt_trans _ NXR); [exact Hx | vm_compute; reflexivity]). symmetry. apply Ha23. exact Hx. }
    apply (Hk E4 ms4 _ (Z.of_nat (length bs))). unfold RHEAD. rewrite Hm4.
    (* [comment removed for export] *)
    assert (Hdisj : buf + len <= RS_LO \/ RS_LO + 65536 <= buf).
    { unfold RS_LO. destruct Hbr as [Hbr|Hbr]; lia. }
    split; [exact Ha4|]. split; [exact Hd4'|]. split; [exact Hrom4|].
    split; [rewrite HE43 by (vm_compute; reflexivity); exact HN2|].
    split; [rewrite HE43 by (vm_compute; reflexivity); exact HC2|].
    split; [rewrite HE43 by (vm_compute; reflexivity); exact HB2'|].
    split; [rewrite HNR; reflexivity|].
    split.
    { apply (mfxr_chg sp0 av ev tid rdraw regs mem Hsp Hargc2 IMG_LO IMG_END HTOP STATIC (ms_mem ms2)); [|exact Hm2].
      intros x Hx Hr _. rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 RS_LO) with (wa RS_LO). rewrite write_to_mem_spec by (unfold RS_LO; lia).
      unfold RSX in Hr.
      destruct (Z.leb_spec0 RS_LO (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (RS_LO + Z.of_nat (length bs))); cbn [andb]; [lia | reflexivity..]. }
    split.
    { apply (HMV hs _ md _); [|reflexivity | rewrite ?with_fds_halted; assumption | rewrite ?with_fds_lazy; assumption].
      apply (HFRAME hs (ms_mem ms2) _ md [(RS_LO, RS_LO + 65536)] Hh2).
      - intros x Hx. rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 RS_LO) with (wa RS_LO). rewrite write_to_mem_spec by (unfold RS_LO; lia).
        cbn [ioutside] in Hx.
        destruct (Z.leb_spec0 RS_LO (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (RS_LO + Z.of_nat (length bs))); cbn [andb]; [|reflexivity..].
        exfalso. apply (proj1 Hx). lia.
      - intros x Hx. exact (wbytes_grows bs (ms_mem ms2) (Z_to_bv 64 RS_LO) x Hx).
      - intros x Hx. destruct (HIface.outside_dec (hi_owned HI hs) x) as [A|A]; [exact A|]. exfalso.
        destruct (HBLK hs (ms_mem ms2) md Hh2) as (_ & Hown2). destruct (Hown2 x A) as (O1 & O2).
        assert (Hrx : RSX x) by (cbn [ioutside] in Hx; unfold RSX; apply Decidable.not_not; [unfold Decidable.decidable; lia|]; intros C; apply Hx; split; [lia | exact I]).
        pose proof (HSTATR x Hrx) as Hst. unfold RSX, RS_LO in Hrx. destruct O2 as [O2|[O2|O2]]; [exact (O2 Hst) | lia | lia]. }
    split; [rewrite with_fds_halted; exact Hhl|]. split; [rewrite with_fds_lazy; exact Hlz|].
    split.
    { rewrite with_fds_fds, Hfd, R10, fd32_3. unfold FDF. rewrite fd_insert_twice. f_equal. f_equal. f_equal.
      apply bv_eq. unfold len_word. rewrite bv_add_unsigned, !u_small64 by (unfold two64; lia). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.mod_small by lia. reflexivity. }
    split; [rewrite with_fds_fs; exact Hfs|].
    split; [exact Hblk|].
    split; [rewrite <- write_to_mem_wbytes; apply bytes_at_write_other; [exact Hba2 | unfold RS_LO; lia | unfold RS_LO; lia |];
            rewrite length_firstn; unfold RS_LO in *; lia|].
    split.
    { rewrite <- write_to_mem_wbytes. replace (firstn (Z.to_nat (Z.of_nat (length bs))) (skipn (Z.to_nat len) data)) with bs.
      - apply bytes_at_write_same; unfold RS_LO; lia.
      - rewrite Nat2Z.id. rewrite Hbs at 2. rewrite Hbs at 1. rewrite length_firstn.
        destruct (Nat.le_ge_cases (Z.to_nat want) (length (skipn (Z.to_nat len) data))) as [A|A].
        + rewrite Nat.min_l by exact A. reflexivity.
        + rewrite Nat.min_r by exact A. rewrite firstn_all2 by exact A. rewrite firstn_all. reflexivity. }
    split; [rewrite Hbl, Hw; lia|].
    split; [exact Hlen|]. split; [exact Hld | exact Hcap].
Qed.

End L1.
