(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SEG0_LO : Z := 65536.
Definition SEG0_HI : Z := 1679360.

Lemma seg0_base : Z.of_N (seg_base seg0) = SEG0_LO. Proof. vm_compute. reflexivity. Qed.
Lemma seg0_size : Z.of_N (seg_size seg0) = SEG0_HI - SEG0_LO. Proof. vm_compute. reflexivity. Qed.
Lemma seg0_chunk_len : to_Z (PrimString.length (chunk_of seg0)) = 2 * (SEG0_HI - SEG0_LO). Proof. vm_compute. reflexivity. Qed.
Lemma asegs_0 : nth_error ctasegs 0 = Some seg0. Proof. rewrite asegs_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition ib (z : Z) : option int := img_byte ctasegs 0 (of_Z z).

Lemma ib_int (x : int) : img_byte ctasegs 0 x = ib (to_Z x).
Proof. unfold ib. rewrite of_to_Z. reflexivity. Qed.

Lemma add_small (x y : int) : to_Z x + to_Z y < wB -> to_Z (x + y)%uint63 = to_Z x + to_Z y.
Proof. intros H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.

Lemma seg0_off_Some (a : Z) (x : int) : seg0_off ctasegs a = Some x -> SEG0_LO <= a < SEG0_HI /\ to_Z x = a - SEG0_LO.
Proof.
  unfold seg0_off. rewrite asegs_eq. rewrite seg0_base, seg0_size.
  destruct ((SEG0_LO <=? a) && (a <? SEG0_LO + (SEG0_HI - SEG0_LO)) && negb (seg_writable seg0)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [lia|]. apply of_Z_spec || (rewrite of_Z_spec; apply Z.mod_small; unfold SEG0_LO, SEG0_HI in *; rewrite wB_eq; unfold two63; lia).
Qed.

(* [comment removed for export] *)
Lemma img_strlen_spec : forall (fuel : nat) (x acc len : int),
  img_strlen ctasegs fuel 0 x acc = Some len -> to_Z x + Z.of_nat fuel < wB -> to_Z acc + Z.of_nat fuel < wB ->
  exists k : nat, (k < fuel)%nat /\ to_Z len = to_Z acc + Z.of_nat k
    /\ (forall j, (j < k)%nat -> exists v, ib (to_Z x + Z.of_nat j) = Some v /\ to_Z v <> 0)
    /\ ib (to_Z x + Z.of_nat k) = Some 0%uint63.
Proof.
  induction fuel as [|f IH]; intros x acc len H Bx Bacc; cbn [img_strlen] in H; [discriminate|].
  rewrite ib_int in H. destruct (ib (to_Z x)) as [b|] eqn:Eb; [|discriminate].
  destruct (b =? 0)%uint63 eqn:Hb; [apply Uint63.eqb_spec in Hb; subst b | apply Uint63.eqb_false_spec in Hb].
  - injection H as <-. exists 0%nat. change (Z.of_nat 0%nat) with 0. rewrite !Z.add_0_r. split; [lia|]. split; [lia|]. split; [intros j Hj; lia | exact Eb].
  - assert (Ex1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (apply add_small; change (to_Z 1%uint63) with 1; lia).
    assert (Ea1 : to_Z (acc + 1)%uint63 = to_Z acc + 1) by (apply add_small; change (to_Z 1%uint63) with 1; lia).
    destruct (IH _ _ _ H ltac:(rewrite Ex1; lia) ltac:(rewrite Ea1; lia)) as (k & Hk & Elen & Hnz & Hnul). rewrite Ex1 in Hnz, Hnul. rewrite Ea1 in Elen.
    exists (Datatypes.S k). split; [lia|]. split; [lia|]. split.
    + intros j Hj. destruct j as [|j]; [change (Z.of_nat 0%nat) with 0; rewrite Z.add_0_r; exists b; split; [exact Eb | intros E; apply Hb; apply to_Z_inj; rewrite E; reflexivity]|].
      destruct (Hnz j ltac:(lia)) as (v & Hv & Hv0). exists v. replace (to_Z x + Z.of_nat (Datatypes.S j)) with (to_Z x + 1 + Z.of_nat j) by lia. auto.
    + replace (to_Z x + Z.of_nat (Datatypes.S k)) with (to_Z x + 1 + Z.of_nat k) by lia. exact Hnul.
Qed.

Lemma img_bytes_ok_spec : forall (fuel : nat) (x : int),
  img_bytes_ok ctasegs fuel 0 x = true -> to_Z x + Z.of_nat fuel < wB -> forall j, (j < fuel)%nat -> exists v, ib (to_Z x + Z.of_nat j) = Some v.
Proof.
  induction fuel as [|f IH]; intros x H Bx j Hj; [lia|]. cbn [img_bytes_ok] in H. rewrite ib_int in H.
  destruct (ib (to_Z x)) as [b|] eqn:Eb; [|discriminate].
  assert (Ex1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (apply add_small; change (to_Z 1%uint63) with 1; lia).
  destruct j as [|j]; [change (Z.of_nat 0%nat) with 0; rewrite Z.add_0_r; exists b; exact Eb|].
  destruct (IH _ H ltac:(rewrite Ex1; lia) j ltac:(lia)) as [v Hv]. rewrite Ex1 in Hv. exists v.
  replace (to_Z x + Z.of_nat (Datatypes.S j)) with (to_Z x + 1 + Z.of_nat j) by lia. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma seg0_ro_byte (a : Z) (v : int) : SEG0_LO <= a < SEG0_HI -> ib (a - SEG0_LO) = Some v ->
  ro_byte ctasegs a (Z_to_bv 8 (to_Z v)) /\ to_Z v < 256.
Proof.
  intros Ha Hv. unfold ib in Hv.
  assert (Ex : to_Z (of_Z (a - SEG0_LO)) = a - SEG0_LO) by (rewrite of_Z_spec; apply Z.mod_small; unfold SEG0_LO, SEG0_HI in *; rewrite wB_eq; unfold two63; lia).
  destruct (img_byte_spec ctasegs 0 seg0 (chunk_of seg0) _ v asegs_0 seg0_chunk Hv ltac:(rewrite Ex, seg0_chunk_len; lia) ltac:(rewrite Ex; unfold SEG0_LO, SEG0_HI in *; lia)) as [Hsb Hv256].
  rewrite Ex in Hsb. split; [|exact Hv256]. split; [|apply ro_addr_seg0; unfold SEG0_LO, SEG0_HI in *; lia].
  unfold seg_rom, memory_read. rewrite wa_unsigned by (unfold SEG0_LO, SEG0_HI in *; lia). change (Z.of_N 1) with 1.
  rewrite (find_seg0_in a ltac:(unfold SEG0_LO, SEG0_HI in *; lia)), seg0_rd, seg0_base. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  rewrite Hsb. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ibyte (z : Z) : byte := match ib z with Some v => Z_to_bv 8 (to_Z v) | None => Z_to_bv 8 0 end.

Lemma ib_run_bytes (m : word -> option byte) (a : Z) : forall (k : nat), mem_inv ctasegs m ->
  SEG0_LO <= a -> a + Z.of_nat k <= SEG0_HI -> (forall j, (j < k)%nat -> exists v, ib (a - SEG0_LO + Z.of_nat j) = Some v) ->
  bytes_at ctasegs m a (map (fun j => ibyte (a - SEG0_LO + Z.of_nat j)) (seq 0 k)).
Proof.
  intros k MI Ha Hk Hall. split; [unfold SEG0_LO in *; lia|]. rewrite length_map, length_seq. split; [unfold SEG0_HI in *; lia|].
  intros i Hi. rewrite nth_error_map, nth_error_seq. replace (Nat.ltb i k) with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add].
  destruct (Hall i Hi) as [v Hv]. unfold ibyte at 1. rewrite Hv.
  destruct (seg0_ro_byte (a + Z.of_nat i) v ltac:(lia) ltac:(replace (a + Z.of_nat i - SEG0_LO) with (a - SEG0_LO + Z.of_nat i) by lia; exact Hv)) as [Hro _].
  exact (mem_inv_ro_read ctasegs m _ _ MI Hro).
Qed.

Lemma gds_cover_In (lo n : Z) : gds_cover GDESC lo n = true -> exists g, In g GDESC /\ gd_beg g <= lo /\ lo + n <= gd_beg g + gd_size g.
Proof.
  intros H. unfold gds_cover in H. apply existsb_exists in H as (g & Hin & E). apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
  exists g. unfold gd_beg, gd_size. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HkStrlen.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_stk : stk_okx (xp_stk xp).
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok ctasegs rho t (xp_rgsh xp) m.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv ctasegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok ctasegs SHBW (ghost RT) JA FInvA).

Lemma PC_STRLEN_Z : wbv PC_STRLEN = Z_to_bv 64 e_strlen. Proof. reflexivity. Qed.

Lemma hkA_strlen_ok : xhook_okA hkA_strlen.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_strlen, hk_at in Hh. destruct (w_eqb (s_pc S) PC_STRLEN) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_strlen in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && (x_calls cd <? CALLS_MAX)) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Ecalls]. apply andb_prop in Eg as [Etp Esp]. apply Z.ltb_lt in Ecalls. unfold CALLS_MAX in Ecalls.
  destruct (rget S X10) as [sv| | |] eqn:Ea10; try discriminate. destruct (wh sv) eqn:Ehs; [discriminate|].
  destruct (seg0_off ctasegs (to_Z (wl sv))) as [x|] eqn:Eoff; [|discriminate].
  destruct (img_strlen ctasegs 4096 0 x 0) as [len|] eqn:Elen; [|discriminate].
  destruct (seg0_off ctasegs (to_Z (wl sv) + to_Z len + 8)) as [xe|] eqn:Eoff8; [|discriminate].
  destruct (gds_cover GDESC (to_Z (wl sv)) (to_Z len + 1) && img_bytes_ok ctasegs 7 0 (x + len + 1)%uint63) eqn:Ecov; [|discriminate].
  apply andb_prop in Ecov as [Ecov Eslk].
  destruct (xclobber_stack RT_STACK S (s_mem S)) as [Mc|] eqn:Ecl; [|discriminate].
  destruct (xret S (VC (W false len)) Mc (s_next S)) as [S1|] eqn:Ert; [|discriminate]. injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (o & rgs & Esp2 & Eho & Egs & Eabs & Edf & Ho16 & Hrt & Hosz & Ewr & ->).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R ctasegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & _ & _).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Esp2 in D2'. rewrite Ea10 in D10. cbn [den] in D1', D2', D10.
  unfold xtp_ok in Etp. destruct (rget S X4) as [tpw| | |]; try discriminate. apply w_eqb_true_iff in Etp. subst tpw. cbn [den] in D4.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem ctasegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabs) as [Esz _].
  destruct (call_geometry RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m o x2 HF Eho Ho16 Hrt ltac:(lia) D2') as (Espv & Hcall & Hspc).
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & Hcnt & Hagr).
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r.
  (* [comment removed for export] *)
  set (s := to_Z (wl sv)) in *.
  pose proof (to_Z_bounded (wl sv)) as Bs. pose proof (to_Z_bounded len) as Blen. pose proof (to_Z_bounded x) as Bx.
  destruct (seg0_off_Some _ _ Eoff) as [Hs Ex]. destruct (seg0_off_Some _ _ Eoff8) as [Hs8 _]. clear Eoff8 xe.
  destruct (img_strlen_spec 4096 x 0%uint63 len Elen ltac:(rewrite Ex; unfold SEG0_LO, SEG0_HI in *; rewrite wB_eq; unfold two63; lia)
              ltac:(change (to_Z 0%uint63) with 0; rewrite wB_eq; unfold two63; lia)) as (k & Hk & Elenk & Hnz & Hnul).
  change (to_Z 0%uint63) with 0 in Elenk. rewrite Z.add_0_l in Elenk. rewrite Ex in Hnz, Hnul.
  assert (Exl0 : to_Z (x + len)%uint63 = to_Z x + to_Z len) by (apply add_small; rewrite wB_eq; unfold two63, SEG0_LO, SEG0_HI in *; lia).
  assert (Exl : to_Z (x + len + 1)%uint63 = s - SEG0_LO + Z.of_nat k + 1).
  { rewrite add_small; rewrite Exl0; change (to_Z 1%uint63) with 1; [rewrite Ex, Elenk; lia | rewrite wB_eq; unfold two63, SEG0_LO, SEG0_HI in *; lia]. }
  pose proof (img_bytes_ok_spec 7 _ Eslk ltac:(rewrite Exl; unfold SEG0_LO, SEG0_HI in *; rewrite wB_eq; unfold two63; lia)) as Hslk. rewrite Exl in Hslk.
  set (str := map (fun j => ibyte (s - SEG0_LO + Z.of_nat j)) (seq 0 k)).
  set (slack := map (fun j => ibyte (s - SEG0_LO + Z.of_nat j)) (seq (Datatypes.S k) 7)).
  assert (Lstr : length str = k) by (unfold str; rewrite length_map, length_seq; reflexivity).
  assert (Lslack : length slack = 7%nat) by (unfold slack; rewrite length_map, length_seq; reflexivity).
  assert (Hbytes : bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack)).
  { assert (E : str ++ Z_to_bv 8 0 :: slack = map (fun j => ibyte (s - SEG0_LO + Z.of_nat j)) (seq 0 (k + 8))).
    { replace (k + 8)%nat with (k + (1 + 7))%nat by lia. rewrite (seq_app k (1 + 7) 0), map_app. unfold str. f_equal.
      rewrite (seq_app 1 7 (0 + k)), map_app. replace (0 + k)%nat with k by lia. replace (k + 1)%nat with (Datatypes.S k) by lia.
      change (Z_to_bv 8 0 :: slack) with ([Z_to_bv 8 0] ++ slack). f_equal. cbn [seq map]. unfold ibyte. rewrite Hnul. reflexivity. }
    rewrite E. apply (ib_run_bytes m s (k + 8) Hmi); [lia | unfold SEG0_HI in *; lia |].
    intros j Hj. destruct (Nat.lt_ge_cases j k) as [L|L]; [destruct (Hnz j L) as (v & Hv & _); exists v; exact Hv|].
    destruct (Nat.eq_dec j k) as [->|N]; [exists 0%uint63; exact Hnul|].
    destruct (Hslk (j - k - 1)%nat ltac:(lia)) as [v Hv]. exists v. replace (s - SEG0_LO + Z.of_nat j) with (s - SEG0_LO + Z.of_nat k + 1 + Z.of_nat (j - k - 1)) by lia. exact Hv. }
  assert (Hnin : ~ In (Z_to_bv 8 0) str).
  { unfold str. intros Hin. apply in_map_iff in Hin as (j & Ej & Hj). apply in_seq in Hj.
    destruct (Hnz j ltac:(lia)) as (v & Hv & Hv0). unfold ibyte in Ej. rewrite Hv in Ej.
    destruct (seg0_ro_byte (s + Z.of_nat j) v ltac:(lia) ltac:(replace (s + Z.of_nat j - SEG0_LO) with (s - SEG0_LO + Z.of_nat j) by lia; exact Hv)) as [_ Hv256].
    pose proof (f_equal bv_unsigned Ej) as E'. rewrite !Z_to_bv_unsigned in E'. unfold bv_wrap, bv_modulus in E'. change (2 ^ Z.of_N 8) with 256 in E'.
    rewrite !Z.mod_small in E' by (pose proof (to_Z_bounded v); lia). exact (Hv0 E'). }
  (* [comment removed for export] *)
  destruct (gds_cover_In _ _ Ecov) as (gd & Hgd & Hgd1 & Hgd2). fold s in Hgd1, Hgd2.
  destruct (GDESC_bounds gd Hgd) as (G1 & G2 & G3 & G4 & G5). unfold GD_IMG_END in G5.
  assert (Hacc : acc ctasegs m s (Z.of_nat k + 1)).
  { apply (acc_sub ctasegs m (gd_beg gd) (gd_size gd)); [|lia|lia].
    apply (acc_ushadow ctasegs m (gd_beg gd) (gd_size gd)); [apply Z.mod_divide; [lia|]; apply Z.mod_divide in G1; [|lia]; destruct G1 as [q Hq]; exists (4 * q); lia | lia | lia |].
    exact (af_lib_sh RT AF _ _ gd HART Hgd). }
  (* [comment removed for export] *)
  intros c Hc. rewrite Epc, PC_STRLEN_Z in Hc.
  apply (rc_strlen RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m s str slack lo PMc_fdfs PMc_mat); rewrite ?Lstr, ?Lslack; try assumption.
  - rewrite D10. unfold wbv, wZ, s. rewrite Ehs. reflexivity.
  - lia.
  - pose proof (Z.mod_pos_bound (- (s + Z.of_nat k + 1)) 8 ltac:(lia)). lia.
  - unfold SEG0_LO, SEG0_HI in *. lia.
  - left. unfold SEG0_LO, SEG0_HI, SEGTOP_A, STACK_WIN in *. lia.
  - split; [intros _; split; [exact Hacc|]|].
    + right; right; right. unfold SEG0_LO, SEG0_HI, SEGTOP_A in *. lia.
    + left. unfold SEG0_LO, SEG0_HI, SEGTOP_A, STACK_WIN in *. lia.
  - intros c' Hc'. destruct (ASTA_unpack RT (g_S RT g) PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & _ & Hstk') & Hpex & _) & Hc'').
    destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
    rewrite Espv in Hstk', Hpex.
    assert (Hpres : rt_pres (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) (B0A + to_Z (wl o)) m m').
    { intros a Ha. apply Hpex; [exact Ha | lia]. }
    apply (K g rho ms' (agree_below_refl _ _)); [|exact Hc''].
    subst ms'.
    destruct (clobber_dirs xp XP_ro (s_mem S) rgs (wl o) Egs Ewr) as [Hd Hrs].
    pose proof (to_Z_bounded (wl o)) as Bo.
    assert (HF' : FMemA g rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) (mset (s_mem S) T_STK (drop_below rgs (wl o))) (s_next S) m').
    { apply (FMem_after_call RT CL lo sp0 r m0 cr0 anc xp XP_ro g rho cd (s_mem S) _ (s_next S) m m' (g_S RT g) (B0A + to_Z (wl o)) HF HART' MI' Hstk'); try reflexivity; try assumption; try lia.
      - apply (kept_stack sp0 _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [unfold B0, SEGTOP_A, STACK_WIN in *; lia | tauto | intros; lia].
      - rewrite Hlive in Hpres. apply (kept_caller CL sp0 xp _ _ _ 0 0 m m' (pres_ex_of_pres _ _ _ m m' Hpres)); [lia | intros; lia]. }
    split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    + intros rho2 Hag. cbn [s_next] in Hag. destruct (HRall rho2 Hag) as [HRg2 HRm2].
      apply (R_return rho2 S (VC (W false len)) _ (s_abs S) (s_next S) ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
               t0' t1' t2' (Z_to_bv 64 (Z.of_nat k)) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom ctasegs) HRg2 D1').
      { cbn [den]. unfold wbv, wZ. cbn [wh wl]. rewrite Elenk. reflexivity. }
      exact (Rmem_clobbered RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) o rgs HF HRm2 Hag Egs Eabs Edf Ewr Ho16 Hosz HART' MI' Hstk' Hpres eq_refl eq_refl).
    + intros rho2 Hag. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp g rho rho2 _ _ _ m' HF' Hag).
Qed.

End HkStrlen.
