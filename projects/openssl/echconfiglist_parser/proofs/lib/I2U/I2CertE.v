(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_SR ECH_Xpres ECH_LibState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import
  I2Inv I2NodeLib I2NodeM I2Start I2Top I2Cert.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gblock (g : gblk) : block := (g_id g, g_addr g, to_Z (g_size g)).

(* [comment removed for export] *)
Fixpoint xlookup {A} (k : int) (l : list (int * A)) : option A :=
  match l with [] => None | (k', v) :: r => if (k' =? k)%uint63 then Some v else xlookup k r end.
Lemma xlookup_In : forall {A} k (l : list (int * A)) v, xlookup k l = Some v -> In (k, v) l.
Proof.
  induction l as [|[k' v'] l IH]; intros v H; cbn in H; [discriminate|].
  destruct (k' =? k)%uint63 eqn:E; [apply Uint63.eqb_spec in E; subst; injection H as ->; left; reflexivity | right; exact (IH v H)].
Qed.
Fixpoint xblookup (i off : int) (l : list (int * int * xval)) : option xval :=
  match l with [] => None | (i', o', v) :: r => if ((i' =? i) && (o' =? off))%uint63 then Some v else xblookup i off r end.
Lemma xblookup_In : forall i off l v, xblookup i off l = Some v -> In (i, off, v) l.
Proof.
  induction l as [|[[i' o'] v'] l IH]; intros v H; cbn in H; [discriminate|].
  destruct ((i' =? i) && (o' =? off))%uint63 eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Uint63.eqb_spec in E1. apply Uint63.eqb_spec in E2. subst. injection H as ->. left. reflexivity.
  - right. exact (IH v H).
Qed.

(* [comment removed for export] *)
Definition xs_byte (X : export) (a : int) : option int :=
  let j := (a land 7)%uint63 in let c := (a - j)%uint63 in
  match xlookup c (x_cells X) with
  | Some (XW w) => Some (w_byte j w)
  | Some (XBytes mask w) => if mask_bit mask j then Some (w_byte j w) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition xb_byte (X : export) (i off : int) : option int :=
  let j := (off land 7)%uint63 in let c := (off - j)%uint63 in
  match xblookup i c (x_bcells X) with
  | Some (XW w) => Some (w_byte j w)
  | Some (XBytes mask w) => if mask_bit mask j then Some (w_byte j w) else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint xs_bytes_ok (X : export) (a : int) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => match xs_byte X a with Some v => (bv_unsigned b =? to_Z v)%Z | None => false end && xs_bytes_ok X (a + 1)%uint63 r
  end.
Fixpoint xb_bytes_ok (X : export) (i off : int) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => match xb_byte X i off with Some v => (bv_unsigned b =? to_Z v)%Z | None => false end && xb_bytes_ok X i (off + 1)%uint63 r
  end.
(* [comment removed for export] *)
Fixpoint wr_static_b (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match wview usegs (fun _ => None) (wa a) with Some _ => true | None => false end && wr_static_b (a + 1) n'
  end.
Fixpoint cells_wfb (cs : list Cells.cell) : bool :=
  match cs with [] => true | Cells.CB n bs :: r => Nat.eqb (length bs) n && cells_wfb r | _ :: r => cells_wfb r end.
Lemma cells_wfb_wf : forall cs, cells_wfb cs = true -> cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|]. cbn [cells_wfb] in H. cbn [cells_wf].
  destruct c; try (split; [exact I | exact (IH H)]).
  apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. split; [exact H1 | exact (IH H2)].
Qed.

(* [comment removed for export] *)
Definition xs_cells_ok (X : export) (A : int) (cs : list Cells.cell) : bool :=
  cells_wfb cs && (to_Z A + Z.of_nat (cells_size cs) <=? 2 ^ 62)%Z
  && xs_bytes_ok X A (cells_bytes cs) && wr_static_b (to_Z A) (cells_size cs).
Definition xb_cells_ok (X : export) (i off : int) (cs : list Cells.cell) : bool :=
  cells_wfb cs && (to_Z off + Z.of_nat (cells_size cs) <=? 2 ^ 62)%Z && xb_bytes_ok X i off (cells_bytes cs)
  && (to_Z off + Z.of_nat (cells_size cs) <=? to_Z (nth (Z.to_nat (to_Z i)) (x_sizes X) 0%uint63))%Z.

(* [comment removed for export] *)
Definition xb_arr_ok (X : export) (i off : int) (bs : list byte) : bool :=
  ((to_Z off + Z.of_nat (length bs) <=? 2 ^ 62)%Z) && xb_bytes_ok X i off bs
  && (to_Z off + Z.of_nat (length bs) <=? to_Z (nth (Z.to_nat (to_Z i)) (x_sizes X) 0%uint63))%Z.

(* [comment removed for export] *)
Definition inb (a : int) (l : list int) : bool := existsb (fun b => (b =? a)%uint63) l.
Definition static_client_b (A n : Z) : bool :=
  ((0x2c5000 <=? A) && (A + n <=? 0x358000)
   && ((A + n <=? RLIBC) || (RCTX + 936 <=? A)) && ((A + n <=? RERRNO) || (RERRNO + 4 <=? A))
   && ((A + n <=? RSSP_GUARD) || (RSSP_GUARD + 8 <=? A)) && ((A + n <=? RGOT_SSP) || (RGOT_SSP + 8 <=? A))
   && ((A + n <=? RVMLOCK) || (RVMLOCK + 4 <=? A)))%Z.
(* [comment removed for export] *)
Definition cell_avoids (K : i2consts) (A n : Z) (c : int) : bool :=
  ((to_Z c + 8 <=? A) || (A + n <=? to_Z c))%Z
  || forallb (fun j : int => ((to_Z c + to_Z j <? A) || (A + n <=? to_Z c + to_Z j))%Z || inb (c + j)%uint63 (c_rb K)) ho_iseq8.
Definition unw_range (K : i2consts) (A n : Z) : bool :=
  static_client_b A n && forallb (cell_avoids K A n) (c_xw K) && cell_avoids K A n (c_errcell K).

(* [comment removed for export] *)
Fixpoint in_ivls_b (XL : list (Z * Z)) (a : Z) : bool :=
  match XL with [] => false | (lo, hi) :: r => ((lo <=? a) && (a <? hi))%Z || in_ivls_b r a end.
Lemma in_ivls_b_spec : forall XL a, in_ivls_b XL a = true -> rin_ivs XL a.
Proof.
  induction XL as [|[lo hi] XL IH]; intros a H; cbn in *; [discriminate|].
  apply orb_true_iff in H as [H|H]; [left; apply andb_true_iff in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; lia | right; exact (IH a H)].
Qed.
(* [comment removed for export] *)
Definition xw_in (K : i2consts) (XL : list (Z * Z)) : bool :=
  forallb (fun c : int => forallb (fun j : int => inb (c + j)%uint63 (c_rb K) || in_ivls_b XL (to_Z c + to_Z j)) ho_iseq8) (c_xw K)
  && forallb (fun j : int => inb (c_errcell K + j)%uint63 (c_rb K)
                             || ((RERRNO <=? to_Z (c_errcell K) + to_Z j) && (to_Z (c_errcell K) + to_Z j <? RERRNO + 4))%Z) ho_iseq8.

(* [comment removed for export] *)
Definition zsum (l : list int) : Z := fold_right (fun n acc => to_Z n + acc) 0 l.
Definition zbig (l : list int) : Z := fold_right (fun n acc => HeapSR_iface.big1 (to_Z n) + acc) 0 l.

Lemma NoDup_app_intro : forall {A} (l1 l2 : list A),
  List.NoDup l1 -> List.NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. cbn. inversion H1; subst. constructor.
  - intros K. apply in_app_or in K. destruct K as [K|K]; [exact (H3 K) | exact (Hd y (or_introl eq_refl) K)].
  - apply IH; [assumption | assumption |]. intros a Ha. apply Hd. right. exact Ha.
Qed.

Lemma lb_bytes_app : forall l1 l2, lb_bytes (l1 ++ l2) = lb_bytes l1 + lb_bytes l2.
Proof. unfold lb_bytes. induction l1 as [|b l1 IH]; intros l2; cbn [fold_right app]; [reflexivity | rewrite IH; lia]. Qed.
Lemma lb_big_app : forall l1 l2, lb_big (l1 ++ l2) = lb_big l1 + lb_big l2.
Proof. unfold lb_big. induction l1 as [|b l1 IH]; intros l2; cbn [fold_right app]; [reflexivity | rewrite IH; lia]. Qed.

(* [comment removed for export] *)
Section End_.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable IMX : fimage.
  Variable K : i2consts.
  Hypothesis HK : K_ok K = true.
  Hypothesis HHx : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HHx.
  Variables (Q : i2env) (st' : i2st) (rho' : int -> word) (ms1 : machine_state) (mo1 : Model)
            (s' : PState) (LB' : list block) (G' : list gblk) (X : export).
  Hypothesis X1 : I2RX H IMX K Q st' rho' ms1 mo1 s' LB' G'.
  Hypothesis HG0 : q_G0 Q = [].
  Hypothesis Hsizes : map g_size (rev G') = x_sizes X.
  Let m1 := ms_mem ms1.
  Let F' := i_F st'.

  (* [comment removed for export] *)
  Definition LBN : list block := map gblock (rev G').

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_perm : Permutation LB' (LBN ++ q_LB0 Q).
  Proof.
    pose proof (r_heap _ _ _ _ _ _ _ _ _ _ _ X1) as Xheap. pose proof (r_Gin _ _ _ _ _ _ _ _ _ _ _ X1) as XGin. pose proof (r_Gnodup _ _ _ _ _ _ _ _ _ _ _ X1) as XGnd. pose proof (r_Gnew _ _ _ _ _ _ _ _ _ _ _ X1) as XGnew. pose proof (r_LB0 _ _ _ _ _ _ _ _ _ _ _ X1) as XLB0. pose proof (r_named0 _ _ _ _ _ _ _ _ _ _ _ X1) as Xnamed. pose proof (r_LBsub _ _ _ _ _ _ _ _ _ _ _ X1) as XLBsub.
    apply Permutation.NoDup_Permutation.
    - pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ Xheap) as Hnd. exact (NoDup_map_inv _ _ Hnd).
    - apply NoDup_app_intro.
      + unfold LBN. apply (NoDup_map_inv blk_id). rewrite map_map. cbn [gblock blk_id fst].
        change (fun x : gblk => g_id x) with g_id. rewrite map_rev. apply NoDup_rev. exact XGnd.
      + destruct Xnamed as [_ Hnd0]. exact (NoDup_map_inv _ _ Hnd0).
      + intros b Hb Hb0. unfold LBN in Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
        pose proof (proj1 (Forall_forall _ _) XGnew g Hg) as [Hn | [_ Hid]]; [rewrite HG0 in Hn; exact Hn|].
        apply (Hid (gblock g) Hb0); [rewrite HG0; cbn; tauto | reflexivity].
    - intros b. rewrite in_app_iff. split.
      + intros Hb. destruct (XLBsub b Hb) as [Hb0 | (g & Hg & ->)]; [right; exact Hb0 | left].
        unfold LBN. apply in_map_iff. exists g. split; [reflexivity | exact (proj1 (in_rev _ _) Hg)].
      + intros [Hb | Hb].
        * unfold LBN in Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
          exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg)).
        * apply (XLB0 b Hb). rewrite HG0. cbn. tauto.
  Qed.

  Lemma post_heap : hs_RHEAP H s' (LBN ++ q_LB0 Q) m1.
  Proof.
    pose proof (r_heap _ _ _ _ _ _ _ _ _ _ _ X1) as Xheap.
    assert (Hperm : RHEAP_perm_law H) by (pose proof HHx as HX; unfold heap_sr_hyps_x in HX; tauto).
    exact (Hperm _ _ _ _ Xheap post_perm).
  Qed.

  Lemma post_block_range : forall b, In b (LBN ++ q_LB0 Q) -> rblock_range (blk_addr b) (blk_size b).
  Proof. intros b Hb. exact (HH_RHEAP_block_range H HH _ _ _ b post_heap Hb). Qed.

  Lemma LBN_length : Z.of_nat (length LBN) = Z.of_nat (length (x_sizes X)).
  Proof. unfold LBN. rewrite <- Hsizes, !length_map. reflexivity. Qed.

  Lemma LBN_bytes : lb_bytes LBN = zsum (x_sizes X).
  Proof.
    unfold LBN. rewrite <- Hsizes. generalize (rev G') as l. induction l as [|g l IH]; [reflexivity|].
    cbn [map]. unfold lb_bytes, zsum in *. cbn [fold_right]. rewrite IH. reflexivity.
  Qed.

  Lemma LBN_big : lb_big LBN = zbig (x_sizes X).
  Proof.
    unfold LBN. rewrite <- Hsizes. generalize (rev G') as l. induction l as [|g l IH]; [reflexivity|].
    cbn [map]. unfold lb_big, zbig in *. cbn [fold_right]. rewrite IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_of_LBN : forall i g, blk_of G' i = Some g ->
    In (gblock g) LBN /\ In g G' /\ g_size g = nth (Z.to_nat (to_Z i)) (x_sizes X) 0%uint63.
  Proof.
    intros i g Hg. unfold blk_of in Hg. split; [|split].
    - unfold LBN. apply in_map_iff. exists g. split; [reflexivity | exact (nth_error_In _ _ Hg)].
    - apply (proj2 (in_rev _ _)). exact (nth_error_In _ _ Hg).
    - rewrite <- Hsizes.
      assert (E : nth_error (map g_size (rev G')) (Z.to_nat (to_Z i)) = Some (g_size g)) by (rewrite nth_error_map, Hg; reflexivity).
      symmetry. exact (nth_error_nth _ _ _ E).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_R : R usegs (im_ro IMX) rho' F' ms1.
  Proof.
    pose proof (r_Rn _ _ _ _ _ _ _ _ _ _ _ X1) as XRn. pose proof (r_rho0 _ _ _ _ _ _ _ _ _ _ _ X1) as Xr0.
    exact (XRn rho' (agree_refl _ rho' Xr0)).
  Qed.

  Lemma post_regs : ms_regs ms1 =
    Frame.mkR (rv rho' F' 1) (rv rho' F' 2) (rv rho' F' 3) (rv rho' F' 4) (rv rho' F' 5) (rv rho' F' 6) (rv rho' F' 7) (rv rho' F' 8)
              (rv rho' F' 9) (rv rho' F' 10) (rv rho' F' 11) (rv rho' F' 12) (rv rho' F' 13) (rv rho' F' 14) (rv rho' F' 15) (rv rho' F' 16)
              (rv rho' F' 17) (rv rho' F' 18) (rv rho' F' 19) (rv rho' F' 20) (rv rho' F' 21) (rv rho' F' 22) (rv rho' F' 23) (rv rho' F' 24)
              (rv rho' F' 25) (rv rho' F' 26) (rv rho' F' 27) (rv rho' F' 28) (rv rho' F' 29) (rv rho' F' 30) (rv rho' F' 31).
  Proof.
    pose proof (r_canon _ _ _ _ _ _ _ _ _ _ _ X1) as Xcan.
    rewrite (canonR_R usegs (im_ro IMX) rho' F' ms1 post_R Xcan) at 1. reflexivity.
  Qed.

  Lemma wa_plus : forall a z, bv_add (wa a) (Z_to_bv 64 z) = wa (a + z).
  Proof.
    intros a z. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
  Qed.

  Section Regs.
    Hypothesis HXR : xregs_sem rho' G' F' (x_regs X).

    Lemma xreg_sem : forall k xv, xlookup k (x_regs X) = Some xv -> xval_sem rho' G' (rv rho' F' (to_Z k)) xv.
    Proof.
      intros k xv Hl. apply xlookup_In in Hl. unfold xregs_sem in HXR. rewrite Forall_forall in HXR.
      specialize (HXR _ Hl). cbn [fst snd] in HXR. unfold rv. rewrite of_to_Z. exact HXR.
    Qed.

    Lemma xreg_W : forall k c, xlookup k (x_regs X) = Some (XW c) -> rv rho' F' (to_Z k) = wbv c.
    Proof. intros k c Hl. exact (xreg_sem k _ Hl). Qed.

    Lemma xreg_V : forall k v, xlookup k (x_regs X) = Some (XV v) -> to_Z (vtag v) < to_Z (q_n0 Q) ->
      rv rho' F' (to_Z k) = dv (q_rho0 Q) v.
    Proof.
      intros k v Hl Hv. pose proof (xreg_sem k _ Hl) as E. cbn [xval_sem] in E. rewrite E.
      pose proof (r_agree _ _ _ _ _ _ _ _ _ _ _ X1) as Xag.
      exact (dv_agree _ _ _ v Xag Hv).
    Qed.

    Lemma xreg_New : forall k i off, xlookup k (x_regs X) = Some (XNew i off) ->
      exists g, blk_of G' i = Some g /\ rv rho' F' (to_Z k) = wa (g_addr g + to_Z off).
    Proof.
      intros k i off Hl. pose proof (xreg_sem k _ Hl) as (g & Hg & E). exists g. split; [exact Hg|]. rewrite E. apply wa_plus.
    Qed.

    (* [comment removed for export] *)
    Lemma xreg_entry : forall d x W k t r, q_rho0 Q = rho_of K d x W ->
      xlookup k (x_regs X) = Some (XV (FV t w_zero)) -> opq_tag_ok t = true -> to_Z t < to_Z (q_n0 Q) ->
      reg_of_tag d t = Some r -> rv rho' F' (to_Z k) = x (to_Z r).
    Proof.
      intros d x W k t r HQ Hl Ho Hn Hr. rewrite (xreg_V k _ Hl Hn). destruct (opq_tag_ok_spec t Ho) as (Ht & E0 & E1).
      rewrite dv_tag_zero by slia. rewrite HQ. unfold rho_of. rewrite E0, E1, Hr. reflexivity.
    Qed.

    Lemma xreg_sp : forall d x W, q_rho0 Q = rho_of K d x W -> q_sp0 Q = bv_unsigned (x 2) ->
      xlookup 2%uint63 (x_regs X) = Some (XV (FV 1 (W64 0 (c_stack K)))) -> rv rho' F' 2 = x 2.
    Proof.
      intros d x W HQ Hsp Hl. change 2 with (to_Z 2%uint63). rewrite (xreg_V 2%uint63 _ Hl).
      2:{ pose proof (r_n0 _ _ _ _ _ _ _ _ _ _ _ X1) as Xn0. cbn [vtag]. change (to_Z 1%uint63) with 1. slia. }
      rewrite (fk_dv_plain (q_rho0 Q)) by (cbn [vtag]; change (to_Z 1%uint63) with 1; slia). cbn [vtag vw].
      rewrite HQ. unfold rho_of. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota. cbv beta.
      unfold wbv. rewrite wZ_even_top by reflexivity. cbn [wlo]. rewrite wa_plus.
      unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned.
      replace (bv_unsigned (x 2) - to_Z (c_stack K) + to_Z (c_stack K)) with (bv_unsigned (x 2)) by slia.
      apply bv_wrap_small. apply bv_unsigned_in_range.
    Qed.
  End Regs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma le8_wbv : forall w, le8 (wbv w) = w_bytes w.
  Proof. intros w. rewrite <- wbytes8_le8. unfold wbytes8. apply store_bytes_64. Qed.

  Lemma In8_of_range : forall j : int, 0 <= to_Z j < 8 -> In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63.
  Proof.
    intros j Hj.
    assert (E : j = of_Z (to_Z j)) by (symmetry; apply of_to_Z).
    assert (C : to_Z j = 0 \/ to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5 \/ to_Z j = 6 \/ to_Z j = 7) by slia.
    rewrite E. destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn; tauto.
  Qed.

  Lemma land7_split : forall a : int, to_Z (a land 7)%uint63 = to_Z a mod 8 /\ to_Z (a - (a land 7))%uint63 = to_Z a - to_Z a mod 8
                                       /\ 0 <= to_Z a mod 8 < 8.
  Proof.
    intros a. pose proof (i63_range a). rewrite to_Z_land7. split; [reflexivity|]. split; [|slia].
    rewrite toZ_sub_small by (rewrite to_Z_land7; slia). rewrite to_Z_land7. reflexivity.
  Qed.

  Section Cells_.
    Hypothesis HXC : xcells_sem rho' G' m1 (x_cells X).

    Lemma xcell_sem_at : forall c xv, xlookup c (x_cells X) = Some xv -> xcell_sem rho' G' m1 (to_Z c) xv.
    Proof.
      intros c xv Hl. apply xlookup_In in Hl. unfold xcells_sem in HXC. rewrite Forall_forall in HXC.
      exact (HXC _ Hl).
    Qed.

    Lemma xs_byte_sound : forall a v, xs_byte X a = Some v ->
      mrd usegs m1 (wa (to_Z a)) = Some (Z_to_bv 8 (to_Z v)) /\ 0 <= to_Z v < 256.
    Proof.
      intros a v Hb. unfold xs_byte in Hb. destruct (land7_split a) as (Ej & Ec & Hj8).
      set (j := (a land 7)%uint63) in *. set (c := (a - j)%uint63) in *.
      destruct (xlookup c (x_cells X)) as [xv|] eqn:El; [|discriminate].
      pose proof (xcell_sem_at c xv El) as Hs.
      assert (Ea : to_Z a = to_Z c + Z.of_nat (Z.to_nat (to_Z j))) by slia.
      destruct xv as [|w|u|idx off|mask w]; try discriminate Hb.
      - injection Hb as <-. cbn [xcell_sem xval_sem] in Hs. destruct Hs as (w' & (_ & _ & HB) & Ew). subst w'.
        rewrite le8_wbv, length_w_bytes in HB. split; [|apply to_Z_w_byte_lt; slia].
        rewrite Ea, (HB (Z.to_nat (to_Z j))) by slia. apply w_bytes_nth_byte. slia.
      - cbn [xcell_sem] in Hs. destruct (mask_bit mask j) eqn:Em; [|discriminate]. injection Hb as <-.
        split; [|apply to_Z_w_byte_lt; slia].
        replace (to_Z a) with (to_Z c + to_Z j) by slia. apply (Hs j); [apply In8_of_range; slia | exact Em].
    Qed.

    Lemma xs_bytes_sound : forall bs a, xs_bytes_ok X a bs = true -> to_Z a + Z.of_nat (length bs) <= 2 ^ 62 ->
      forall i, (i < length bs)%nat -> mrd usegs m1 (wa (to_Z a + Z.of_nat i)) = nth_error bs i.
    Proof.
      induction bs as [|b r IH]; intros a Hok Hbd i Hi; [cbn in Hi; slia|].
      cbn [xs_bytes_ok] in Hok. apply andb_true_iff in Hok as [Hh Ht].
      destruct (xs_byte X a) as [v|] eqn:Eb; [|discriminate]. apply Z.eqb_eq in Hh.
      destruct (xs_byte_sound a v Eb) as [Hm Hv]. pose proof (i63_range a). cbn [length] in Hbd.
      destruct i as [|i].
      - cbn [nth_error]. rewrite Z.add_0_r, Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hh. apply bv_wrap_small.
        change (bv_modulus 8) with 256. slia.
      - cbn [nth_error]. cbn [length] in Hi.
        assert (Ea1 : to_Z (a + 1)%uint63 = to_Z a + 1) by (rewrite toZ_add_small; change (to_Z 1%uint63) with 1; slia).
        replace (to_Z a + Z.of_nat (S i)) with (to_Z (a + 1)%uint63 + Z.of_nat i) by slia.
        apply IH; [exact Ht | slia | slia].
    Qed.

    Lemma wr_static_sound : forall m a n, wr_static_b a n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at usegs m a (Z.of_nat n).
    Proof.
      intros m a n Hw Ha Hb. split; [exact Ha|]. split; [exact Hb|].
      revert a Hw Ha Hb. induction n as [|n IH]; intros a Hw Ha Hb i Hi; [slia|].
      cbn [wr_static_b] in Hw. apply andb_true_iff in Hw as [Hh Ht].
      destruct (Z.eq_dec i 0) as [->|Hne].
      - rewrite Z.add_0_r. destruct (wview usegs (fun _ => None) (wa a)) as [b0|] eqn:E; [|discriminate].
        unfold wview in *. destruct (m (wa a)); [discriminate|]. rewrite E. discriminate.
      - replace (a + i) with (a + 1 + (i - 1)) by slia. apply (IH (a + 1) Ht); slia.
    Qed.

    Lemma post_rw_cells : forall A cs, xs_cells_ok X A cs = true -> rw_cells usegs m1 (to_Z A) cs.
    Proof.
      intros A cs Hok. unfold xs_cells_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[[Hwf Hsz] Hb] Hw].
      apply cells_wfb_wf in Hwf. apply Z.leb_le in Hsz. pose proof (i63_range A).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      split; [split; [exact Hwf|]|].
      - split; [slia|]. split; [rewrite Hlen; slia|]. apply xs_bytes_sound; [exact Hb | rewrite Hlen; slia].
      - apply wr_static_sound; [exact Hw | slia | slia].
    Qed.

    Lemma post_ptr_cell : forall c i off, xlookup c (x_cells X) = Some (XNew i off) ->
      exists g, blk_of G' i = Some g /\ bytes_at usegs m1 (to_Z c) (le8 (wa (g_addr g + to_Z off))).
    Proof.
      intros c i off Hl. pose proof (xcell_sem_at c _ Hl) as Hs. cbn [xcell_sem xval_sem] in Hs. destruct Hs as (w & HB & (g & Hg & Ew)). subst w.
      exists g. split; [exact Hg|].
      rewrite wa_plus in HB. exact HB.
    Qed.

    Lemma post_ptr_rw : forall c i off, xlookup c (x_cells X) = Some (XNew i off) -> wr_static_b (to_Z c) 8 = true ->
      exists g, blk_of G' i = Some g /\ rw_cells usegs m1 (to_Z c) [C8 (wa (g_addr g + to_Z off))].
    Proof.
      intros c i off Hl Hw. destruct (post_ptr_cell c i off Hl) as (g & Hg & HB). exists g. split; [exact Hg|].
      pose proof HB as (H0 & H1 & _). rewrite length_le8 in H1.
      split; [split; [exact (conj I I)|]|].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
      - cbn [cells_size csize]. apply wr_static_sound; [exact Hw | exact H0 | exact H1].
    Qed.
    Lemma post_ptr_rw0 : forall c i, xlookup c (x_cells X) = Some (XNew i 0%uint63) -> wr_static_b (to_Z c) 8 = true ->
      exists g, blk_of G' i = Some g /\ rw_cells usegs m1 (to_Z c) [C8 (wa (g_addr g))].
    Proof.
      intros c i Hl Hw. destruct (post_ptr_rw c i 0%uint63 Hl Hw) as (g & Hg & R). exists g. split; [exact Hg|].
      change (to_Z 0%uint63) with 0 in R. rewrite Z.add_0_r in R. exact R.
    Qed.
  End Cells_.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section BCells_.
    Hypothesis HXB : xbcells_sem rho' G' m1 (x_bcells X).

    Lemma xbcell_sem_at : forall i g c xv, blk_of G' i = Some g -> xblookup i c (x_bcells X) = Some xv -> xv <> XAny ->
      xcell_sem rho' G' m1 (g_addr g + to_Z c) xv.
    Proof.
      intros i g c xv Hg Hl Hne. apply xblookup_In in Hl. unfold xbcells_sem in HXB. rewrite Forall_forall in HXB.
      destruct (HXB _ Hl) as [Ha | (g' & Hg' & Hs)]; [exfalso; exact (Hne Ha)|]. cbn [fst snd] in Hg', Hs.
      rewrite Hg in Hg'. injection Hg' as <-. exact Hs.
    Qed.

    Lemma xb_byte_sound : forall i g off v, blk_of G' i = Some g -> xb_byte X i off = Some v ->
      mrd usegs m1 (wa (g_addr g + to_Z off)) = Some (Z_to_bv 8 (to_Z v)) /\ 0 <= to_Z v < 256.
    Proof.
      intros i g off v Hg Hb. unfold xb_byte in Hb. destruct (land7_split off) as (Ej & Ec & Hj8).
      set (j := (off land 7)%uint63) in *. set (c := (off - j)%uint63) in *.
      destruct (xblookup i c (x_bcells X)) as [xv|] eqn:El; [|discriminate].
      assert (Ea : to_Z off = to_Z c + Z.of_nat (Z.to_nat (to_Z j))) by slia.
      destruct xv as [|w|u|idx o2|mask w]; try discriminate Hb.
      - injection Hb as <-. pose proof (xbcell_sem_at i g c _ Hg El ltac:(discriminate)) as Hs.
        cbn [xcell_sem xval_sem] in Hs. destruct Hs as (w' & (_ & _ & HB) & Ew). subst w'.
        rewrite le8_wbv, length_w_bytes in HB. split; [|apply to_Z_w_byte_lt; slia].
        rewrite Ea, Z.add_assoc, (HB (Z.to_nat (to_Z j))) by slia. apply w_bytes_nth_byte. slia.
      - destruct (mask_bit mask j) eqn:Em; [|discriminate]. injection Hb as <-.
        pose proof (xbcell_sem_at i g c _ Hg El ltac:(discriminate)) as Hs. cbn [xcell_sem] in Hs.
        split; [|apply to_Z_w_byte_lt; slia].
        replace (g_addr g + to_Z off) with (g_addr g + to_Z c + to_Z j) by slia. apply (Hs j); [apply In8_of_range; slia | exact Em].
    Qed.

    Lemma xb_bytes_sound : forall i g bs off, blk_of G' i = Some g -> xb_bytes_ok X i off bs = true ->
      to_Z off + Z.of_nat (length bs) <= 2 ^ 62 ->
      forall k, (k < length bs)%nat -> mrd usegs m1 (wa (g_addr g + to_Z off + Z.of_nat k)) = nth_error bs k.
    Proof.
      intros i g bs. induction bs as [|b r IH]; intros off Hg Hok Hbd k Hk; [cbn in Hk; slia|].
      cbn [xb_bytes_ok] in Hok. apply andb_true_iff in Hok as [Hh Ht].
      destruct (xb_byte X i off) as [v|] eqn:Eb; [|discriminate]. apply Z.eqb_eq in Hh.
      destruct (xb_byte_sound i g off v Hg Eb) as [Hm Hv]. pose proof (i63_range off). cbn [length] in Hbd.
      destruct k as [|k].
      - cbn [nth_error]. rewrite Z.add_0_r, Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hh. apply bv_wrap_small.
        change (bv_modulus 8) with 256. slia.
      - cbn [nth_error]. cbn [length] in Hk.
        assert (Ea1 : to_Z (off + 1)%uint63 = to_Z off + 1) by (rewrite toZ_add_small; change (to_Z 1%uint63) with 1; slia).
        replace (g_addr g + to_Z off + Z.of_nat (S k)) with (g_addr g + to_Z (off + 1)%uint63 + Z.of_nat k) by slia.
        apply IH; [exact Hg | exact Ht | slia | slia].
    Qed.

    Lemma post_blk_rw_cells : forall i g off cs, blk_of G' i = Some g -> xb_cells_ok X i off cs = true ->
      rw_cells usegs m1 (g_addr g + to_Z off) cs.
    Proof.
      intros i g off cs Hg Hok. unfold xb_cells_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[[Hwf Ho] Hb] Hsz].
      apply cells_wfb_wf in Hwf. apply Z.leb_le in Ho. apply Z.leb_le in Hsz. pose proof (i63_range off).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      destruct (blk_of_LBN i g Hg) as (HinN & HinG & Esz). rewrite <- Esz in Hsz.
      pose proof (r_Gin _ _ _ _ _ _ _ _ _ _ _ X1) as XGin. pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range (g_size g)).
      split; [split; [exact Hwf|]|].
      - split; [slia|]. split; [rewrite Hlen; slia|]. intros k Hk. apply (xb_bytes_sound i g); [exact Hg | exact Hb | rewrite Hlen; slia | exact Hk].
      - split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z off + k) ltac:(slia))).
    Qed.

    Lemma post_blk_arr : forall i g off bs, blk_of G' i = Some g -> xb_arr_ok X i off bs = true ->
      bytes_at usegs m1 (g_addr g + to_Z off) bs /\ wr_at usegs m1 (g_addr g + to_Z off) (Z.of_nat (length bs)).
    Proof.
      intros i g off bs Hg Hok. unfold xb_arr_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[Ho Hb] Hsz].
      apply Z.leb_le in Ho. apply Z.leb_le in Hsz. pose proof (i63_range off).
      destruct (blk_of_LBN i g Hg) as (HinN & HinG & Esz). rewrite <- Esz in Hsz.
      pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range (g_size g)).
      split.
      - split; [slia|]. split; [slia|]. intros k Hk. apply (xb_bytes_sound i g); [exact Hg | exact Hb | slia | exact Hk].
      - split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z off + k) ltac:(slia))).
    Qed.

    Lemma post_blk_ptr : forall i g c i2 off, blk_of G' i = Some g -> xblookup i c (x_bcells X) = Some (XNew i2 off) ->
      to_Z c + 8 <= to_Z (g_size g) ->
      exists g2, blk_of G' i2 = Some g2 /\ rw_cells usegs m1 (g_addr g + to_Z c) [C8 (wa (g_addr g2 + to_Z off))].
    Proof.
      intros i g c i2 off Hg Hl Hc. pose proof (xbcell_sem_at i g c _ Hg Hl ltac:(discriminate)) as Hs. cbn [xcell_sem xval_sem] in Hs.
      destruct Hs as (w & HB & (g2 & Hg2 & Ew)). subst w.
      exists g2. split; [exact Hg2|]. rewrite wa_plus in HB. pose proof HB as (H0 & H1 & _). rewrite length_le8 in H1.
      destruct (blk_of_LBN i g Hg) as (_ & HinG & _).
      pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range c).
      split; [split; [exact (conj I I)|]|].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
      - cbn [cells_size csize]. split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z c + k) ltac:(slia))).
    Qed.
    Lemma post_blk_ptr0 : forall i g c i2, blk_of G' i = Some g -> xblookup i c (x_bcells X) = Some (XNew i2 0%uint63) ->
      to_Z c + 8 <= to_Z (g_size g) ->
      exists g2, blk_of G' i2 = Some g2 /\ rw_cells usegs m1 (g_addr g + to_Z c) [C8 (wa (g_addr g2))].
    Proof.
      intros i g c i2 Hg Hl Hc. destruct (post_blk_ptr i g c i2 0%uint63 Hg Hl Hc) as (g2 & Hg2 & R). exists g2. split; [exact Hg2|].
      change (to_Z 0%uint63) with 0 in R. rewrite Z.add_0_r in R. exact R.
    Qed.
  End BCells_.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma inb_spec : forall a l, inb a l = true -> In a l.
  Proof.
    intros a l Hi. unfold inb in Hi. apply existsb_In in Hi as [b [Hb E]]. apply Uint63.eqb_spec in E. subst. exact Hb.
  Qed.

  Lemma post_frame : forall a, 0 <= a < 2 ^ 64 -> client0 Q a -> ~ xw_addr K a -> ~ err_addr K a -> m1 (wa a) = q_m0 Q (wa a).
  Proof.
    intros a Ha Hc Hx He. pose proof (r_frame _ _ _ _ _ _ _ _ _ _ _ X1) as Xframe.
    apply (Xframe a Ha Hc); [| exact Hx | exact He]. intros (g & Hg & _). rewrite HG0 in Hg. exact Hg.
  Qed.

  Lemma static_client_b_spec : forall A n a, static_client_b A n = true -> A <= a < A + n ->
    0x2c5000 <= a < 0x358000 /\ ~ ralloc_static a.
  Proof.
    intros A n a Hs Ha. unfold static_client_b in Hs. rewrite !andb_true_iff, !orb_true_iff in Hs.
    destruct Hs as [[[[[[H1 H2] H3] H4] H5] H6] H7]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    repeat match goal with H : (_ <=? _)%Z = true \/ (_ <=? _)%Z = true |- _ => rewrite !Z.leb_le in H end.
    unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. split; slia.
  Qed.

  Lemma cell_avoids_spec : forall A n c a, cell_avoids K A n c = true -> A <= a < A + n -> to_Z c <= a < to_Z c + 8 -> a < 2 ^ 62 -> rb_addr K a.
  Proof.
    intros A n c a Hv Ha Hc Ha62. unfold cell_avoids in Hv. apply orb_true_iff in Hv as [Hv|Hv].
    - exfalso. apply orb_true_iff in Hv as [Hv|Hv]; apply Z.leb_le in Hv; slia.
    - rename Hv into H0. pose proof H0 as H'. clear H0. rename H' into Hv. rewrite forallb_forall in Hv. pose proof (i63_range c).
      set (j := of_Z (a - to_Z c)). assert (Ej : to_Z j = a - to_Z c) by (subst j; apply toZ_of_Z_small; slia).
      specialize (Hv j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)).
      rewrite !orb_true_iff in Hv. destruct Hv as [[Hv|Hv]|Hv]; [apply Z.ltb_lt in Hv; slia | apply Z.leb_le in Hv; slia |].
      apply inb_spec in Hv. exists (c + j)%uint63. split; [exact Hv|]. rewrite toZ_add_small; slia.
  Qed.

  Lemma unw_range_sound : forall A n a, unw_range K A n = true -> A <= a < A + n ->
    (0x2c5000 <= a < 0x358000 /\ ~ ralloc_static a) /\ ~ xw_addr K a /\ ~ err_addr K a.
  Proof.
    intros A n a Hu Ha. unfold unw_range in Hu. rewrite !andb_true_iff in Hu. destruct Hu as [[Hs Hx] He].
    split; [exact (static_client_b_spec A n a Hs Ha)|]. rewrite forallb_forall in Hx. split.
    - intros [(c & Hc & Hin) Hnrb]. pose proof (static_client_b_spec A n a Hs Ha). exact (Hnrb (cell_avoids_spec A n c a (Hx c Hc) Ha Hin ltac:(slia))).
    - intros [Hin Hnrb]. pose proof (static_client_b_spec A n a Hs Ha). exact (Hnrb (cell_avoids_spec A n _ a He Ha Hin ltac:(slia))).
  Qed.

  Lemma post_magree : forall A n, unw_range K A n = true -> magree (in_range A n) (q_m0 Q) m1.
  Proof.
    intros A n Hu a Ha Hr. destruct (unw_range_sound A n a Hu Hr) as (Hs & Hx & He).
    assert (E : m1 (wa a) = q_m0 Q (wa a)) by (apply post_frame; [exact Ha | right; left; exact Hs | exact Hx | exact He]).
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  (* [comment removed for export] *)
  Lemma post_magree_block : forall b, In b (q_LB0 Q) -> rblock_range (blk_addr b) (blk_size b) ->
    magree (in_range (blk_addr b) (blk_size b)) (q_m0 Q) m1.
  Proof.
    intros b Hb Hr a Ha Hin. unfold in_range in Hin. destruct Hr as (_ & _ & _ & _ & Himg).
    destruct (HK_err K HK) as (Eea & _ & Hbi & _ & _ & _ & _ & _). unfold RERRNO in Eea.
    pose proof (i63_range (c_errcell K)). pose proof (i63_range (c_errbi K)).
    assert (E : m1 (wa a) = q_m0 Q (wa a)).
    { apply post_frame; [exact Ha | right; right; exists b; split; [exact Hb | exact Hin] | |].
      - intros [(c & Hcin & Hc) _]. pose proof (xw_cell_ok_spec c (HK_xw K HK c Hcin)) as (_ & Hlo & Hhi & _). slia.
      - intros [Hc _]. slia. }
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  Lemma post_xpres : forall XL, xw_in K XL = true ->
    (forall b, In b (q_LB0 Q) -> rblock_range (blk_addr b) (blk_size b)) ->
    xpres (q_LB0 Q) (q_sp0 Q) XL (q_m0 Q) m1.
  Proof.
    intros XL Hw HLB0 a Ha [Hc Hx]. unfold xw_in in Hw. apply andb_true_iff in Hw as [Hxw Herr].
    pose proof (r_lo _ _ _ _ _ _ _ _ _ _ _ X1) as Xlo.
    destruct (HK_err K HK) as (Eea & _ & _ & _ & _ & _ & _ & _). unfold RERRNO in Eea.
    pose proof (i63_range (c_errcell K)). pose proof (i63_range (c_errbi K)). pose proof (i63_range (c_stack K)). hcb.
    assert (E : m1 (wa a) = q_m0 Q (wa a)).
    { apply post_frame; [exact Ha | exact Hc | |].
      - intros [(c & Hcin & Hin) Hnrb]. rewrite forallb_forall in Hxw. specialize (Hxw c Hcin). rewrite forallb_forall in Hxw.
        pose proof (xw_cell_ok_spec c (HK_xw K HK c Hcin)) as (_ & _ & Hc8 & _).
        pose proof (i63_range c). set (j := of_Z (a - to_Z c)). assert (Ej : to_Z j = a - to_Z c) by (subst j; apply toZ_of_Z_small; slia).
        specialize (Hxw j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)). apply orb_true_iff in Hxw as [Hb|Hb].
        + apply Hnrb. apply inb_spec in Hb. exists (c + j)%uint63. split; [exact Hb | rewrite toZ_add_small; slia].
        + apply Hx. replace a with (to_Z c + to_Z j) by slia. exact (in_ivls_b_spec _ _ Hb).
      - intros [Hin Hnrb]. rewrite forallb_forall in Herr.
        set (j := of_Z (a - to_Z (c_errcell K))). assert (Ej : to_Z j = a - to_Z (c_errcell K)) by (subst j; apply toZ_of_Z_small; slia).
        specialize (Herr j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)). apply orb_true_iff in Herr as [Hb|Hb].
        + apply Hnrb. apply inb_spec in Hb. exists (c_errcell K + j)%uint63. split; [exact Hb | rewrite toZ_add_small; slia].
        + apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
          unfold client0, rclient_addr, ralloc_static, RERRNO, RLIBC, RCTX in *.
          destruct Hc as [Hc|[[_ Hc]|(b & Hb0 & Hr)]]; [slia | apply Hc; slia |].
          pose proof (HLB0 b Hb0) as (_ & _ & _ & _ & Himg). slia. }
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_errno : exists errv', rw_cells usegs m1 (errA K) [C4 errv'].
  Proof.
    pose proof (r_err _ _ _ _ _ _ _ _ _ _ _ X1) as Xerr.
    exact (rw_c4_of_stk usegs m1 (errA K) Xerr).
  Qed.
  Lemma post_inv : mem_inv usegs m1.
  Proof. pose proof (r_inv _ _ _ _ _ _ _ _ _ _ _ X1) as Xinv. exact Xinv. Qed.
  Lemma post_stk : stk usegs m1 (q_lo Q) (q_sp0 Q).
  Proof. pose proof (r_stk _ _ _ _ _ _ _ _ _ _ _ X1) as Xstk. exact Xstk. Qed.
  Lemma post_auxv : hs_rauxv_ok H m1 (q_B Q).
  Proof. pose proof (r_auxv _ _ _ _ _ _ _ _ _ _ _ X1) as Xaux. exact Xaux. Qed.
  Lemma post_krel : hs_KREL H s' mo1.
  Proof. pose proof (r_krel _ _ _ _ _ _ _ _ _ _ _ X1) as Xkrel. exact Xkrel. Qed.
  Lemma post_mpres : hs_MPRES H (q_mo0 Q) mo1.
  Proof. pose proof (r_mpres _ _ _ _ _ _ _ _ _ _ _ X1) as Xmp. exact Xmp. Qed.

  (* [comment removed for export] *)
  Lemma post_errno_kept : forall t d x W, q_rho0 Q = rho_of K d x W -> opq_tag_ok t = true -> to_Z t < to_Z (q_n0 Q) ->
    reg_of_tag d t = None ->
    (to_Z t < 2 ^ 60 -> errno_sem K m1 (rho' t)) ->
    rw_cells usegs m1 (errA K) [C4 (wlookup W t)].
  Proof.
    intros t d x W HQ Ho Hn Hr Hsem. destruct (opq_tag_ok_spec t Ho) as (Ht & E0 & E1).
    specialize (Hsem ltac:(slia)).
    pose proof (r_agree _ _ _ _ _ _ _ _ _ _ _ X1) as Xag. pose proof (r_err _ _ _ _ _ _ _ _ _ _ _ X1) as Xerr.
    assert (Et : rho' t = wlookup W t).
    { destruct Xag as [_ Hag]. rewrite (Hag t Hn), HQ. unfold rho_of. rewrite E0, E1, Hr. reflexivity. }
    destruct post_errno as [ev Hrw]. pose proof Hrw as [[_ (H0 & H1 & HB)] HW].
    split; [split; [exact (conj I I)|]| exact HW]. split; [exact H0|]. split; [exact H1|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. intros i Hi. rewrite length_le4 in Hi.
    unfold errno_sem in Hsem. unfold errA. rewrite (Hsem i Hi), Et. symmetry. apply nth_error_le4_le8. exact Hi.
  Qed.
End End_.
