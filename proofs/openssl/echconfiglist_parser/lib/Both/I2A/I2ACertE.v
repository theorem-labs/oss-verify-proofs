(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0 ECH_ALib.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ACert I2AStart I2ATop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gblock (g : gblk) : block := (g_id g, g_addr g, to_Z (g_size g)).

(* [comment removed for export] *)
Fixpoint xlookup {T} (k : int) (l : list (int * T)) : option T :=
  match l with [] => None | (k', v) :: r => if (k' =? k)%uint63 then Some v else xlookup k r end.
Lemma xlookup_In : forall {T} k (l : list (int * T)) v, xlookup k l = Some v -> In (k, v) l.
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
  | S n' => match wview asegs (fun _ => None) (wa a) with Some _ => true | None => false end && wr_static_b (a + 1) n'
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
  (((0x571000 <=? A) && (A + n <=? 0x5ea848)) || ((0x5ed1a0 <=? A) && (A + n <=? 0x673c00))
   || ((0x6a7248 <=? A) && (A + n <=? 0x6a7298)) || ((0xbccf50 <=? A) && (A + n <=? 0xc03570)))%Z.
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
  && forallb (fun j : int => inb (c_errcell K + j)%uint63 (c_rb K) || in_ivls_b XL (to_Z (c_errcell K) + to_Z j)) ho_iseq8.

(* [comment removed for export] *)
Definition zsum (l : list int) : Z := fold_right (fun n acc => to_Z n + acc) 0 l.

Lemma NoDup_app_intro : forall {T} (l1 l2 : list T),
  List.NoDup l1 -> List.NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. cbn. inversion H1; subst. constructor.
  - intros K. apply in_app_or in K. destruct K as [K|K]; [exact (H3 K) | exact (Hd y (or_introl eq_refl) K)].
  - apply IH; [assumption | assumption |]. intros a Ha. apply Hd. right. exact Ha.
Qed.

Lemma lb_bytes_app : forall l1 l2, lb_bytes (l1 ++ l2) = lb_bytes l1 + lb_bytes l2.
Proof. unfold lb_bytes. induction l1 as [|b l1 IH]; intros l2; cbn [fold_right app]; [reflexivity | rewrite IH; lia]. Qed.

Lemma inb_spec : forall a l, inb a l = true -> In a l.
Proof.
  intros a l Hi. unfold inb in Hi. apply existsb_exists in Hi as [b [Hb E]]. apply Uint63.eqb_spec in E. subst. exact Hb.
Qed.

Lemma aimg_client_w_hi : forall lo hi, aimg_client_w lo hi -> hi <= 0xc03570.
Proof. intros lo hi Hw. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in Hw. lia. Qed.

(* [comment removed for export] *)
Section End_.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Let IM := im_ro IMX.
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  (* [comment removed for export] *)
  Lemma scratch_high_gen : forall LF m XS0 a, as_RFS H LF m -> Forall (fs_scratch H LF) XS0 -> rin_ivs XS0 a -> AIMG_TOP <= a.
  Proof.
    intros LF m XS0 a R FX Ha.
    induction XS0 as [|[lo hi] XS' IH]; [exact (False_ind _ Ha)|].
    pose proof (Forall_inv FX) as F1. pose proof (Forall_inv_tail FX) as F2. cbn [rin_ivs fst snd] in Ha.
    destruct Ha as [Ha|Ha]; [| exact (IH F2 Ha)].
    destruct F1 as [E|(k & ff & fp & FF & E)].
    - injection E as -> ->. pose proof (RFS_fsb H HH _ _ R) as (B1 & _). slia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (HK0 & R1 & R2 & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & _).
      pose proof (fsz_pos k ltac:(slia)) as FZ. pose proof (RFS_fsb H HH _ _ R) as (B1 & _).
      unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
      destruct E as [E|[E|E]]; injection E as -> ->; [slia | slia |].
      unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val in Ha. slia.
  Qed.
  Lemma scratch_apart_gen : forall LF m XS0 O n a, as_RFS H LF m -> Forall (fs_scratch H LF) XS0 -> fsobj H LF O n ->
    0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n -> O <= a < O + n -> ~ rin_ivs XS0 a.
  Proof.
    intros LF m XS0 O n a R FX OB HO Hn Htop Happ Ha Hs.
    induction XS0 as [|[lo hi] XS' IH]; [exact (False_ind _ Hs)|].
    pose proof (Forall_inv FX) as F1. pose proof (Forall_inv_tail FX) as F2. cbn [rin_ivs fst snd] in Hs.
    destruct Hs as [Hs|Hs]; [| exact (IH F2 Hs)].
    pose proof (fsobj_scratch H HH LF O n m (lo, hi) R OB HO Hn Htop Happ F1) as D. cbn [fst snd] in D. slia.
  Qed.

  Variables (Q : i2aenv) (st' : i2ast) (rho' : int -> word) (msF1 : machine_state) (mo1 : Model) (ms1 : machine_state)
            (s' : as_St H) (LB' : list block) (G' : list gblk) (XS : list (Z * Z)) (X : export).
  Hypothesis X1 : I2RAX H IMX A Q st' rho' msF1 mo1 s' LB' G' [] XS ms1.
  Hypothesis HG0 : q_G0 Q = [].
  Hypothesis Hsizes : map g_size (rev G') = x_sizes X.
  Let m1 := ms_mem ms1.
  Let F' := a_F st'.

  (* [comment removed for export] *)
  Definition LBN : list block := map gblock (rev G').

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_perm : Permutation LB' (LBN ++ q_LB0 Q).
  Proof.
    pose proof (r_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xheap. pose proof (r_Gin _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGin.
    pose proof (r_Gnodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGnd. pose proof (r_Gnew _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGnew.
    pose proof (r_LB0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XLB0. pose proof (r_named0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xnamed.
    pose proof (r_LBsub _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XLBsub.
    apply Permutation.NoDup_Permutation.
    - pose proof (ah_nodup H HH _ _ _ Xheap) as Hnd. exact (NoDup_map_inv _ _ Hnd).
    - apply NoDup_app_intro.
      + unfold LBN. apply (NoDup_map_inv blk_id). rewrite map_map. cbn [gblock blk_id fst].
        change (fun x : gblk => g_id x) with g_id. rewrite map_rev. apply NoDup_rev. exact XGnd.
      + destruct Xnamed as [_ Hnd0]. exact (NoDup_map_inv _ _ Hnd0).
      + intros b Hb Hb0. unfold LBN in Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
        pose proof (proj1 (Forall_forall _ _) XGnew g Hg) as [Hn | [_ [Hid _]]]; [rewrite HG0 in Hn; exact Hn|].
        apply (Hid (gblock g) Hb0); [rewrite HG0; cbn; tauto | reflexivity].
    - intros b. rewrite in_app_iff. split.
      + intros Hb. destruct (XLBsub b Hb) as [Hb0 | (g & Hg & ->)]; [right; exact Hb0 | left].
        unfold LBN. apply in_map_iff. exists g. split; [reflexivity | exact (proj1 (in_rev _ _) Hg)].
      + intros [Hb | Hb].
        * unfold LBN in Hb. apply in_map_iff in Hb as (g & <- & Hg). apply (proj2 (in_rev _ _)) in Hg.
          exact (proj1 (proj1 (Forall_forall _ _) XGin g Hg)).
        * apply (XLB0 b Hb). rewrite HG0. cbn. tauto.
  Qed.

  Lemma post_heap : as_RHEAP H s' (LBN ++ q_LB0 Q) m1.
  Proof.
    pose proof (r_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xheap.
    exact (HHx_rheap_perm H HHx _ _ _ _ Xheap post_perm).
  Qed.

  Lemma post_block_range : forall b, In b (LBN ++ q_LB0 Q) -> ablock_range H (blk_addr b) (blk_size b).
  Proof. intros b Hb. exact (ah_blocks H HH _ _ _ b post_heap Hb). Qed.

  Lemma LBN_length : Z.of_nat (length LBN) = Z.of_nat (length (x_sizes X)).
  Proof. unfold LBN. rewrite <- Hsizes, !length_map. reflexivity. Qed.

  Lemma LBN_bytes : lb_bytes LBN = zsum (x_sizes X).
  Proof.
    unfold LBN. rewrite <- Hsizes. generalize (rev G') as l. induction l as [|g l IH]; [reflexivity|].
    cbn [map]. unfold lb_bytes, zsum in *. cbn [fold_right]. rewrite IH. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_of_LBN : forall i g, blk_ofA G' i = Some g ->
    In (gblock g) LBN /\ In g G' /\ g_size g = nth (Z.to_nat (to_Z i)) (x_sizes X) 0%uint63.
  Proof.
    intros i g Hg. unfold blk_ofA in Hg. split; [|split].
    - unfold LBN. apply in_map_iff. exists g. split; [reflexivity | exact (nth_error_In _ _ Hg)].
    - apply (proj2 (in_rev _ _)). exact (nth_error_In _ _ Hg).
    - rewrite <- Hsizes.
      assert (E : nth_error (map g_size (rev G')) (Z.to_nat (to_Z i)) = Some (g_size g)) by (rewrite nth_error_map, Hg; reflexivity).
      symmetry. exact (nth_error_nth _ _ _ E).
  Qed.

  (* [comment removed for export] *)
  Section Shad_.
    Hypothesis HSHAD : Forall (fun g => addressable m1 (g_addr g) (to_Z (g_size g))) G'.
    Lemma post_shad : forall i g, blk_ofA G' i = Some g -> addressable m1 (blk_addr (gblock g)) (blk_size (gblock g)).
    Proof.
      intros i g Hg. destruct (blk_of_LBN i g Hg) as (_ & HinG & _). cbn [gblock blk_addr blk_size fst snd].
      exact (proj1 (Forall_forall _ _) HSHAD g HinG).
    Qed.
  End Shad_.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_R : R asegs IM rho' F' ms1.
  Proof.
    pose proof (r_Rn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XRn. pose proof (r_rho0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xr0.
    exact (XRn rho' (agree_refl _ rho' Xr0)).
  Qed.

  Lemma post_regs : ms_regs ms1 =
    Frame.mkR (rv rho' F' 1) (rv rho' F' 2) (rv rho' F' 3) (rv rho' F' 4) (rv rho' F' 5) (rv rho' F' 6) (rv rho' F' 7) (rv rho' F' 8)
              (rv rho' F' 9) (rv rho' F' 10) (rv rho' F' 11) (rv rho' F' 12) (rv rho' F' 13) (rv rho' F' 14) (rv rho' F' 15) (rv rho' F' 16)
              (rv rho' F' 17) (rv rho' F' 18) (rv rho' F' 19) (rv rho' F' 20) (rv rho' F' 21) (rv rho' F' 22) (rv rho' F' 23) (rv rho' F' 24)
              (rv rho' F' 25) (rv rho' F' 26) (rv rho' F' 27) (rv rho' F' 28) (rv rho' F' 29) (rv rho' F' 30) (rv rho' F' 31).
  Proof.
    pose proof (r_canon _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xcan.
    rewrite (canonR_R asegs IM rho' F' ms1 post_R Xcan) at 1. reflexivity.
  Qed.

  Lemma wa_plus : forall a z, bv_add (wa a) (Z_to_bv 64 z) = wa (a + z).
  Proof.
    intros a z. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
  Qed.

  Section Regs.
    Hypothesis HXR : xregs_semA rho' G' F' (x_regs X).

    Lemma xreg_sem : forall k xv, xlookup k (x_regs X) = Some xv -> xval_semA rho' G' (rv rho' F' (to_Z k)) xv.
    Proof.
      intros k xv Hl. apply xlookup_In in Hl. unfold xregs_semA in HXR. rewrite Forall_forall in HXR.
      specialize (HXR _ Hl). cbn [fst snd] in HXR. unfold rv. rewrite of_to_Z. exact HXR.
    Qed.

    Lemma xreg_W : forall k c, xlookup k (x_regs X) = Some (XW c) -> rv rho' F' (to_Z k) = wbv c.
    Proof. intros k c Hl. exact (xreg_sem k _ Hl). Qed.

    Lemma xreg_V : forall k v, xlookup k (x_regs X) = Some (XV v) -> to_Z (vtag v) < to_Z (q_n0 Q) ->
      rv rho' F' (to_Z k) = dv (q_rho0 Q) v.
    Proof.
      intros k v Hl Hv. pose proof (xreg_sem k _ Hl) as E. cbn [xval_semA] in E. rewrite E.
      pose proof (r_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xag.
      exact (dv_agree _ _ _ v Xag Hv).
    Qed.

    Lemma xreg_New : forall k i off, xlookup k (x_regs X) = Some (XNew i off) ->
      exists g, blk_ofA G' i = Some g /\ rv rho' F' (to_Z k) = wa (g_addr g + to_Z off).
    Proof.
      intros k i off Hl. pose proof (xreg_sem k _ Hl) as (g & Hg & E). exists g. split; [exact Hg|]. rewrite E. apply wa_plus.
    Qed.

    (* [comment removed for export] *)
    Lemma xreg_entry : forall d x W k t r, q_rho0 Q = rho_ofA K d x W ->
      xlookup k (x_regs X) = Some (XV (FV t w_zero)) -> opq_tag_ok t = true -> to_Z t < to_Z (q_n0 Q) ->
      reg_of_tag d t = Some r -> rv rho' F' (to_Z k) = x (to_Z r).
    Proof.
      intros d x W k t r HQ Hl Ho Hn Hr. rewrite (xreg_V k _ Hl Hn). destruct (opq_tag_ok_spec t Ho) as (Ht & E0 & E1 & E2 & E3).
      rewrite dv_tag_zero by slia. rewrite HQ. unfold rho_ofA. rewrite E0, E1, E2, E3, Hr. reflexivity.
    Qed.

    Lemma xreg_sp : forall d x W, q_rho0 Q = rho_ofA K d x W -> q_sp0 Q = bv_unsigned (x 2) ->
      xlookup 2%uint63 (x_regs X) = Some (XV (FV 1 (W64 0 (c_stack K)))) -> rv rho' F' 2 = x 2.
    Proof.
      intros d x W HQ Hsp Hl. change 2 with (to_Z 2%uint63). rewrite (xreg_V 2%uint63 _ Hl).
      2:{ pose proof (r_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xn0. cbn [vtag]. change (to_Z 1%uint63) with 1. slia. }
      rewrite (fk_dv_plain (q_rho0 Q)) by (cbn [vtag]; change (to_Z 1%uint63) with 1; slia). cbn [vtag vw].
      rewrite HQ. unfold rho_ofA. change ((1 =? 0)%uint63) with false. change ((1 =? 1)%uint63) with true. cbv iota. cbv beta.
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
    Hypothesis HXC : xcells_semA rho' G' m1 (x_cells X).

    Lemma xcell_sem_at : forall c xv, xlookup c (x_cells X) = Some xv -> xcell_semA rho' G' m1 (to_Z c) xv.
    Proof.
      intros c xv Hl. apply xlookup_In in Hl. unfold xcells_semA in HXC. rewrite Forall_forall in HXC.
      exact (HXC _ Hl).
    Qed.

    Lemma xs_byte_sound : forall a v, xs_byte X a = Some v ->
      mrd asegs m1 (wa (to_Z a)) = Some (Z_to_bv 8 (to_Z v)) /\ 0 <= to_Z v < 256.
    Proof.
      intros a v Hb. unfold xs_byte in Hb. destruct (land7_split a) as (Ej & Ec & Hj8).
      set (j := (a land 7)%uint63) in *. set (c := (a - j)%uint63) in *.
      destruct (xlookup c (x_cells X)) as [xv|] eqn:El; [|discriminate].
      pose proof (xcell_sem_at c xv El) as Hs.
      assert (Ea : to_Z a = to_Z c + Z.of_nat (Z.to_nat (to_Z j))) by slia.
      destruct xv as [|w|u|idx off|mask w]; try discriminate Hb.
      - injection Hb as <-. cbn [xcell_semA xval_semA] in Hs. destruct Hs as (w' & (_ & _ & HB) & Ew). subst w'.
        rewrite le8_wbv, length_w_bytes in HB. split; [|apply to_Z_w_byte_lt; slia].
        rewrite Ea, (HB (Z.to_nat (to_Z j))) by slia. apply w_bytes_nth_byte. slia.
      - cbn [xcell_semA] in Hs. destruct (mask_bit mask j) eqn:Em; [|discriminate]. injection Hb as <-.
        split; [|apply to_Z_w_byte_lt; slia].
        replace (to_Z a) with (to_Z c + to_Z j) by slia. apply (Hs j); [apply In8_of_range; slia | exact Em].
    Qed.

    Lemma xs_bytes_sound : forall bs a, xs_bytes_ok X a bs = true -> to_Z a + Z.of_nat (length bs) <= 2 ^ 62 ->
      forall i, (i < length bs)%nat -> mrd asegs m1 (wa (to_Z a + Z.of_nat i)) = nth_error bs i.
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

    Lemma wr_static_sound : forall m a n, wr_static_b a n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at asegs m a (Z.of_nat n).
    Proof.
      intros m a n Hw Ha Hb. split; [exact Ha|]. split; [exact Hb|].
      revert a Hw Ha Hb. induction n as [|n IH]; intros a Hw Ha Hb i Hi; [slia|].
      cbn [wr_static_b] in Hw. apply andb_true_iff in Hw as [Hh Ht].
      destruct (Z.eq_dec i 0) as [->|Hne].
      - rewrite Z.add_0_r. destruct (wview asegs (fun _ => None) (wa a)) as [b0|] eqn:E; [|discriminate].
        unfold wview in *. destruct (m (wa a)); [discriminate|]. rewrite E. discriminate.
      - replace (a + i) with (a + 1 + (i - 1)) by slia. apply (IH (a + 1) Ht); slia.
    Qed.

    Lemma post_rw_cells : forall A0 cs, xs_cells_ok X A0 cs = true -> rw_cells asegs m1 (to_Z A0) cs.
    Proof.
      intros A0 cs Hok. unfold xs_cells_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[[Hwf Hsz] Hb] Hw].
      apply cells_wfb_wf in Hwf. apply Z.leb_le in Hsz. pose proof (i63_range A0).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      split; [split; [exact Hwf|]|].
      - split; [slia|]. split; [rewrite Hlen; slia|]. apply xs_bytes_sound; [exact Hb | rewrite Hlen; slia].
      - apply wr_static_sound; [exact Hw | slia | slia].
    Qed.

    Lemma post_ptr_cell : forall c i off, xlookup c (x_cells X) = Some (XNew i off) ->
      exists g, blk_ofA G' i = Some g /\ bytes_at asegs m1 (to_Z c) (le8 (wa (g_addr g + to_Z off))).
    Proof.
      intros c i off Hl. pose proof (xcell_sem_at c _ Hl) as Hs. cbn [xcell_semA xval_semA] in Hs. destruct Hs as (w & HB & (g & Hg & Ew)). subst w.
      exists g. split; [exact Hg|].
      rewrite wa_plus in HB. exact HB.
    Qed.

    Lemma post_ptr_rw : forall c i off, xlookup c (x_cells X) = Some (XNew i off) -> wr_static_b (to_Z c) 8 = true ->
      exists g, blk_ofA G' i = Some g /\ rw_cells asegs m1 (to_Z c) [C8 (wa (g_addr g + to_Z off))].
    Proof.
      intros c i off Hl Hw. destruct (post_ptr_cell c i off Hl) as (g & Hg & HB). exists g. split; [exact Hg|].
      pose proof HB as (H0 & H1 & _). rewrite length_le8 in H1.
      split; [split; [exact (conj I I)|]|].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
      - cbn [cells_size csize]. apply wr_static_sound; [exact Hw | exact H0 | exact H1].
    Qed.
    Lemma post_ptr_rw0 : forall c i, xlookup c (x_cells X) = Some (XNew i 0%uint63) -> wr_static_b (to_Z c) 8 = true ->
      exists g, blk_ofA G' i = Some g /\ rw_cells asegs m1 (to_Z c) [C8 (wa (g_addr g))].
    Proof.
      intros c i Hl Hw. destruct (post_ptr_rw c i 0%uint63 Hl Hw) as (g & Hg & R). exists g. split; [exact Hg|].
      change (to_Z 0%uint63) with 0 in R. rewrite Z.add_0_r in R. exact R.
    Qed.
  End Cells_.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section BCells_.
    Hypothesis HXB : xbcells_semA rho' G' m1 (x_bcells X).

    Lemma xbcell_sem_at : forall i g c xv, blk_ofA G' i = Some g -> xblookup i c (x_bcells X) = Some xv -> xv <> XAny ->
      xcell_semA rho' G' m1 (g_addr g + to_Z c) xv.
    Proof.
      intros i g c xv Hg Hl Hne. apply xblookup_In in Hl. unfold xbcells_semA in HXB. rewrite Forall_forall in HXB.
      destruct (HXB _ Hl) as [Ha | (g' & Hg' & Hs)]; [exfalso; exact (Hne Ha)|]. cbn [fst snd] in Hg', Hs.
      rewrite Hg in Hg'. injection Hg' as <-. exact Hs.
    Qed.

    Lemma xb_byte_sound : forall i g off v, blk_ofA G' i = Some g -> xb_byte X i off = Some v ->
      mrd asegs m1 (wa (g_addr g + to_Z off)) = Some (Z_to_bv 8 (to_Z v)) /\ 0 <= to_Z v < 256.
    Proof.
      intros i g off v Hg Hb. unfold xb_byte in Hb. destruct (land7_split off) as (Ej & Ec & Hj8).
      set (j := (off land 7)%uint63) in *. set (c := (off - j)%uint63) in *.
      destruct (xblookup i c (x_bcells X)) as [xv|] eqn:El; [|discriminate].
      assert (Ea : to_Z off = to_Z c + Z.of_nat (Z.to_nat (to_Z j))) by slia.
      destruct xv as [|w|u|idx o2|mask w]; try discriminate Hb.
      - injection Hb as <-. pose proof (xbcell_sem_at i g c _ Hg El ltac:(discriminate)) as Hs.
        cbn [xcell_semA xval_semA] in Hs. destruct Hs as (w' & (_ & _ & HB) & Ew). subst w'.
        rewrite le8_wbv, length_w_bytes in HB. split; [|apply to_Z_w_byte_lt; slia].
        rewrite Ea, Z.add_assoc, (HB (Z.to_nat (to_Z j))) by slia. apply w_bytes_nth_byte. slia.
      - destruct (mask_bit mask j) eqn:Em; [|discriminate]. injection Hb as <-.
        pose proof (xbcell_sem_at i g c _ Hg El ltac:(discriminate)) as Hs. cbn [xcell_semA] in Hs.
        split; [|apply to_Z_w_byte_lt; slia].
        replace (g_addr g + to_Z off) with (g_addr g + to_Z c + to_Z j) by slia. apply (Hs j); [apply In8_of_range; slia | exact Em].
    Qed.

    Lemma xb_bytes_sound : forall i g bs off, blk_ofA G' i = Some g -> xb_bytes_ok X i off bs = true ->
      to_Z off + Z.of_nat (length bs) <= 2 ^ 62 ->
      forall k, (k < length bs)%nat -> mrd asegs m1 (wa (g_addr g + to_Z off + Z.of_nat k)) = nth_error bs k.
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

    Lemma post_blk_rw_cells : forall i g off cs, blk_ofA G' i = Some g -> xb_cells_ok X i off cs = true ->
      rw_cells asegs m1 (g_addr g + to_Z off) cs.
    Proof.
      intros i g off cs Hg Hok. unfold xb_cells_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[[Hwf Ho] Hb] Hsz].
      apply cells_wfb_wf in Hwf. apply Z.leb_le in Ho. apply Z.leb_le in Hsz. pose proof (i63_range off).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      destruct (blk_of_LBN i g Hg) as (HinN & HinG & Esz). rewrite <- Esz in Hsz.
      pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range (g_size g)).
      split; [split; [exact Hwf|]|].
      - split; [slia|]. split; [rewrite Hlen; slia|]. intros k Hk. apply (xb_bytes_sound i g); [exact Hg | exact Hb | rewrite Hlen; slia | exact Hk].
      - split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z off + k) ltac:(slia))).
    Qed.

    Lemma post_blk_arr : forall i g off bs, blk_ofA G' i = Some g -> xb_arr_ok X i off bs = true ->
      bytes_at asegs m1 (g_addr g + to_Z off) bs /\ wr_at asegs m1 (g_addr g + to_Z off) (Z.of_nat (length bs)).
    Proof.
      intros i g off bs Hg Hok. unfold xb_arr_ok in Hok. rewrite !andb_true_iff in Hok. destruct Hok as [[Ho Hb] Hsz].
      apply Z.leb_le in Ho. apply Z.leb_le in Hsz. pose proof (i63_range off).
      destruct (blk_of_LBN i g Hg) as (HinN & HinG & Esz). rewrite <- Esz in Hsz.
      pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range (g_size g)).
      split.
      - split; [slia|]. split; [slia|]. intros k Hk. apply (xb_bytes_sound i g); [exact Hg | exact Hb | slia | exact Hk].
      - split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z off + k) ltac:(slia))).
    Qed.

    Lemma post_blk_ptr : forall i g c i2 off, blk_ofA G' i = Some g -> xblookup i c (x_bcells X) = Some (XNew i2 off) ->
      to_Z c + 8 <= to_Z (g_size g) ->
      exists g2, blk_ofA G' i2 = Some g2 /\ rw_cells asegs m1 (g_addr g + to_Z c) [C8 (wa (g_addr g2 + to_Z off))].
    Proof.
      intros i g c i2 off Hg Hl Hc. pose proof (xbcell_sem_at i g c _ Hg Hl ltac:(discriminate)) as Hs. cbn [xcell_semA xval_semA] in Hs.
      destruct Hs as (w & HB & (g2 & Hg2 & Ew)). subst w.
      exists g2. split; [exact Hg2|]. rewrite wa_plus in HB. pose proof HB as (H0 & H1 & _). rewrite length_le8 in H1.
      destruct (blk_of_LBN i g Hg) as (_ & HinG & _).
      pose proof (r_Gstk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XGstk.
      pose proof (proj1 (Forall_forall _ _) XGstk g HinG) as (S0 & S1 & Sw). pose proof (i63_range c).
      split; [split; [exact (conj I I)|]|].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
      - cbn [cells_size csize]. split; [slia|]. split; [slia|]. intros k Hk. apply (proj1 (Sw (g_addr g + to_Z c + k) ltac:(slia))).
    Qed.
    Lemma post_blk_ptr0 : forall i g c i2, blk_ofA G' i = Some g -> xblookup i c (x_bcells X) = Some (XNew i2 0%uint63) ->
      to_Z c + 8 <= to_Z (g_size g) ->
      exists g2, blk_ofA G' i2 = Some g2 /\ rw_cells asegs m1 (g_addr g + to_Z c) [C8 (wa (g_addr g2))].
    Proof.
      intros i g c i2 Hg Hl Hc. destruct (post_blk_ptr i g c i2 0%uint63 Hg Hl Hc) as (g2 & Hg2 & R). exists g2. split; [exact Hg2|].
      change (to_Z 0%uint63) with 0 in R. rewrite Z.add_0_r in R. exact R.
    Qed.
  End BCells_.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_frame : forall a, 0 <= a < 2 ^ 64 -> client0 H Q a -> ~ xw_addr A a -> ~ err_addr A a -> ~ rin_ivs XS a ->
    m1 (wa a) = q_m0 Q (wa a).
  Proof.
    intros a Ha Hc Hx He Hs. pose proof (r_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xframe.
    apply (Xframe a Ha Hc); [| exact Hx | exact He | exact Hs]. intros (g & Hg & _). rewrite HG0 in Hg. exact Hg.
  Qed.

  Lemma static_client_b_spec : forall A0 n a, static_client_b A0 n = true -> A0 <= a < A0 + n -> aimg_client a /\ a < 0xc03570.
  Proof.
    intros A0 n a Hs Ha. unfold static_client_b in Hs. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hs.
    unfold aimg_client. slia.
  Qed.

  (* [comment removed for export] *)
  Lemma LF_of_nil : LF_of Q [] = q_LF0 Q.
  Proof. reflexivity. Qed.
  Lemma post_rfs : as_RFS H (q_LF0 Q) m1.
  Proof. pose proof (r_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xrfs. rewrite LF_of_nil in Xrfs. exact Xrfs. Qed.
  Lemma post_xs : Forall (fs_scratch H (q_LF0 Q)) XS.
  Proof. exact (r_XS _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.

  Lemma scratch_high : forall a, rin_ivs XS a -> AIMG_TOP <= a.
  Proof. intros a Ha. exact (scratch_high_gen _ _ _ a post_rfs post_xs Ha). Qed.

  Lemma cell_avoids_spec : forall A0 n c a, cell_avoids K A0 n c = true -> A0 <= a < A0 + n -> to_Z c <= a < to_Z c + 8 -> a < 2 ^ 62 ->
    rb_addr A a.
  Proof.
    intros A0 n c a Hv Ha Hc Ha62. unfold cell_avoids in Hv. apply orb_true_iff in Hv as [Hv|Hv].
    - exfalso. apply orb_true_iff in Hv as [Hv|Hv]; apply Z.leb_le in Hv; slia.
    - rename Hv into H0. pose proof H0 as H'. clear H0. rename H' into Hv. rewrite forallb_forall in Hv. pose proof (i63_range c).
      set (j := of_Z (a - to_Z c)). assert (Ej : to_Z j = a - to_Z c) by (subst j; apply toZ_of_Z_small; slia).
      specialize (Hv j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)).
      rewrite !orb_true_iff in Hv. destruct Hv as [[Hv|Hv]|Hv]; [apply Z.ltb_lt in Hv; slia | apply Z.leb_le in Hv; slia |].
      apply inb_spec in Hv. exists (c + j)%uint63. split; [exact Hv|]. rewrite toZ_add_small; slia.
  Qed.

  Lemma unw_range_sound : forall A0 n a, unw_range K A0 n = true -> A0 <= a < A0 + n ->
    (aimg_client a /\ a < 0xc03570) /\ ~ xw_addr A a /\ ~ err_addr A a.
  Proof.
    intros A0 n a Hu Ha. unfold unw_range in Hu. rewrite !andb_true_iff in Hu. destruct Hu as [[Hs Hx] He].
    split; [exact (static_client_b_spec A0 n a Hs Ha)|]. rewrite forallb_forall in Hx. split.
    - intros [(c & Hc & Hin) Hnrb]. pose proof (static_client_b_spec A0 n a Hs Ha). exact (Hnrb (cell_avoids_spec A0 n c a (Hx c Hc) Ha Hin ltac:(slia))).
    - intros [Hin Hnrb]. pose proof (static_client_b_spec A0 n a Hs Ha). exact (Hnrb (cell_avoids_spec A0 n _ a He Ha Hin ltac:(slia))).
  Qed.

  Lemma post_magree : forall A0 n, unw_range K A0 n = true -> magree (in_range A0 n) (q_m0 Q) m1.
  Proof.
    intros A0 n Hu a Ha Hr. destruct (unw_range_sound A0 n a Hu Hr) as ((Hs & Hlt) & Hx & He).
    assert (E : m1 (wa a) = q_m0 Q (wa a)).
    { apply post_frame; [exact Ha | right; left; exact Hs | exact Hx | exact He |].
      intros Hin. pose proof (scratch_high a Hin). unfold AIMG_TOP in *. slia. }
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  (* [comment removed for export] *)
  Lemma post_magree_block : forall b, In b (q_LB0 Q) -> magree (in_range (blk_addr b) (blk_size b)) (q_m0 Q) m1.
  Proof.
    intros b Hb a Ha Hin. unfold in_range in Hin.
    pose proof (r_LB0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as XLB0.
    assert (HbL : In b (LBN ++ q_LB0 Q)) by (apply in_or_app; right; exact Hb).
    pose proof (post_block_range b HbL) as (R0 & R16 & Rn & Rtop & Rce & Rfs & Rapp).
    destruct (HK_err A HK) as (_ & _ & _ & Ew & _). pose proof (aimg_client_w_hi _ _ Ew) as Ehi.
    pose proof (i63_range (c_errcell K)).
    assert (E : m1 (wa a) = q_m0 Q (wa a)).
    { apply post_frame; [exact Ha | right; right; left; exists b; split; [exact Hb | exact Hin] | | |].
      - intros [(c & Hcin & Hc) _]. pose proof (xw_cell_ok_spec c (HK_xw A HK c Hcin)) as (_ & _ & _ & Hhi & _).
        unfold AIMG_TOP in *. slia.
      - intros [Hc _]. unfold AIMG_TOP in *. slia.
      - acb. destruct b as [[p Ab] nb]. cbn [blk_addr blk_size fst snd] in *.
        pose proof (fsobj_block H HH _ _ _ (q_LF0 Q) p Ab nb post_heap HbL) as OB.
        exact (scratch_apart_gen _ _ _ Ab nb a post_rfs post_xs OB ltac:(slia) Rn ltac:(unfold AAPP_HI; slia) Rapp Hin). }
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  Lemma post_xpres : forall XL, xw_in K XL = true -> xpres H (q_LB0 Q) (q_sp0 Q) (XS ++ XL) (q_m0 Q) m1.
  Proof.
    intros XL Hw a Ha [Hc Hx]. unfold xw_in in Hw. apply andb_true_iff in Hw as [Hxw Herr].
    rewrite rin_ivs_app in Hx.
    pose proof (i63_range (c_errcell K)).
    assert (E : m1 (wa a) = q_m0 Q (wa a)).
    { apply post_frame; [exact Ha | exact Hc | | | intros K'; apply Hx; left; exact K'].
      - intros [(c & Hcin & Hin) Hnrb]. rewrite forallb_forall in Hxw. specialize (Hxw c Hcin). rewrite forallb_forall in Hxw.
        pose proof (xw_cell_ok_spec c (HK_xw A HK c Hcin)) as (_ & _ & _ & Hc8 & _).
        pose proof (i63_range c). set (j := of_Z (a - to_Z c)). assert (Ej : to_Z j = a - to_Z c) by (subst j; apply toZ_of_Z_small; slia).
        specialize (Hxw j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)). apply orb_true_iff in Hxw as [Hb|Hb].
        + apply Hnrb. apply inb_spec in Hb. exists (c + j)%uint63. split; [exact Hb | rewrite toZ_add_small; slia].
        + apply Hx. right. replace a with (to_Z c + to_Z j) by slia. exact (in_ivls_b_spec _ _ Hb).
      - intros [Hin Hnrb]. rewrite forallb_forall in Herr.
        destruct (HK_err A HK) as (Eea & _ & _ & Ew & _). pose proof (aimg_client_w_hi _ _ Ew) as Ehi.
        set (j := of_Z (a - to_Z (c_errcell K))). assert (Ej : to_Z j = a - to_Z (c_errcell K)) by (subst j; apply toZ_of_Z_small; slia).
        specialize (Herr j ltac:(rewrite ho_iseq8_eq; apply in_iseq; slia)). apply orb_true_iff in Herr as [Hb|Hb].
        + apply Hnrb. apply inb_spec in Hb. exists (c_errcell K + j)%uint63. split; [exact Hb | rewrite toZ_add_small; slia].
        + apply Hx. right. replace a with (to_Z (c_errcell K) + to_Z j) by slia. exact (in_ivls_b_spec _ _ Hb). }
    split; [exact E|]. unfold wview. rewrite E. exact (fun h => h).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_errno : exists errv', rw_cells asegs m1 (errA A) [C4 errv'].
  Proof.
    pose proof (r_err _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xerr.
    exact (rw_c4_of_stk asegs m1 (errA A) Xerr).
  Qed.
  Lemma post_inv : mem_inv asegs m1.
  Proof. exact (r_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_stk : stk asegs m1 (q_lo Q) (q_sp0 Q).
  Proof. exact (r_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_auxv : as_rauxv_ok H m1 (q_B Q).
  Proof. exact (r_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_akrel : as_AKREL H s' (mkCfg msF1 mo1).
  Proof. exact (r_akrel _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_mpres : as_MPRES H (q_mo0 Q) mo1.
  Proof. exact (r_mpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_aconst : ACONST m1.
  Proof. exact (r_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_stack0 : stack0 m1 (q_lo Q) (q_shi Q).
  Proof. exact (r_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_chain : as_chain H m1 (q_s0 Q) (q_CH0 Q).
  Proof. exact (r_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1). Qed.
  Lemma post_AL : a_cs st' = [] -> as_AL H s' >= q_AL0 Q - csum H (q_cs Q).
  Proof.
    intros Hcs. pose proof (r_AL _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as (done & Hd & HAL).
    rewrite Hcs, app_nil_r in Hd. subst done. exact HAL.
  Qed.

  (* [comment removed for export] *)
  Lemma post_errno_kept : forall t d x W, q_rho0 Q = rho_ofA K d x W -> opq_tag_ok t = true -> to_Z t < to_Z (q_n0 Q) ->
    reg_of_tag d t = None ->
    (to_Z t < 2 ^ 60 -> errno_semA K m1 (rho' t)) ->
    rw_cells asegs m1 (errA A) [C4 (wlookup W t)].
  Proof.
    intros t d x W HQ Ho Hn Hr Hsem. destruct (opq_tag_ok_spec t Ho) as (Ht & E0 & E1 & E2 & E3).
    specialize (Hsem ltac:(slia)).
    pose proof (r_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as Xag.
    assert (Et : rho' t = wlookup W t).
    { destruct Xag as [_ Hag]. rewrite (Hag t Hn), HQ. unfold rho_ofA. rewrite E0, E1, E2, E3, Hr. reflexivity. }
    destruct post_errno as [ev Hrw]. pose proof Hrw as [[_ (H0 & H1 & HB)] HW].
    split; [split; [exact (conj I I)|]| exact HW]. split; [exact H0|]. split; [exact H1|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. intros i Hi. rewrite length_le4 in Hi.
    unfold errno_semA in Hsem. unfold errA. rewrite (Hsem i Hi), Et. symmetry. apply nth_error_le4_le8. exact Hi.
  Qed.
End End_.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Csum.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Definition mbytes1 (e : int * int * int) : Z :=
    match e with (k, a, b) =>
      if (k =? 0)%uint63 then to_Z a else if (k =? 1)%uint63 then 0 else if (k =? 2)%uint63 then to_Z b else to_Z a + to_Z b end.
  Definition fbytes1 (e : int * int * int) : Z :=
    match e with (k, a, b) => if (k =? 0)%uint63 then 0 else if (k =? 1)%uint63 then to_Z a else if (k =? 2)%uint63 then to_Z a else 0 end.
  Definition msum (l : list (int * int * int)) : Z := fold_right (fun e acc => mbytes1 e + acc) 0 l.
  Definition fsum (l : list (int * int * int)) : Z := fold_right (fun e acc => fbytes1 e + acc) 0 l.
  Lemma mbytes1_nonneg : forall e, 0 <= mbytes1 e.
  Proof. intros [[k a] b]. unfold mbytes1. pose proof (i63_range a). pose proof (i63_range b). destruct (k =? 0)%uint63; [slia|]. destruct (k =? 1)%uint63; [slia|]. destruct (k =? 2)%uint63; slia. Qed.
  Lemma fbytes1_nonneg : forall e, 0 <= fbytes1 e.
  Proof. intros [[k a] b]. unfold fbytes1. pose proof (i63_range a). destruct (k =? 0)%uint63; [slia|]. destruct (k =? 1)%uint63; [slia|]. destruct (k =? 2)%uint63; slia. Qed.
  Lemma msum_nonneg : forall l, 0 <= msum l.
  Proof. induction l as [|e l IH]; cbn [msum fold_right]; [slia|]. unfold msum in IH. pose proof (mbytes1_nonneg e). slia. Qed.
  Lemma fsum_nonneg : forall l, 0 <= fsum l.
  Proof. induction l as [|e l IH]; cbn [fsum fold_right]; [slia|]. unfold fsum in IH. pose proof (fbytes1_nonneg e). slia. Qed.

  Lemma csum_bound : forall l, csum H l <= as_Cm H (msum l) + as_Cf H (fsum l).
  Proof.
    pose proof (ah_costs H HH) as (M0 & Mm & F0 & Fm & Ms & Fs).
    induction l as [|e l IH].
    - cbn [csum msum fsum fold_right]. pose proof (M0 0 ltac:(slia)). pose proof (F0 0 ltac:(slia)). slia.
    - cbn [csum msum fsum fold_right]. unfold csum, msum, fsum in IH.
      set (CR := fold_right (fun e0 acc => cost1 H e0 + acc) 0 l) in *.
      set (MR := fold_right (fun e0 acc => mbytes1 e0 + acc) 0 l) in *.
      set (FR := fold_right (fun e0 acc => fbytes1 e0 + acc) 0 l) in *.
      pose proof (msum_nonneg l : 0 <= MR) as HMR. pose proof (fsum_nonneg l : 0 <= FR) as HFR.
      destruct e as [[k a] b]. unfold cost1, mbytes1, fbytes1. pose proof (i63_range a). pose proof (i63_range b).
      destruct (k =? 0)%uint63.
      { pose proof (Ms (to_Z a) MR ltac:(slia) HMR). rewrite Z.add_0_l. slia. }
      destruct (k =? 1)%uint63.
      { pose proof (Fs (to_Z a) FR ltac:(slia) HFR). rewrite Z.add_0_l. slia. }
      destruct (k =? 2)%uint63.
      { pose proof (Ms (to_Z b) MR ltac:(slia) HMR). pose proof (Fs (to_Z a) FR ltac:(slia) HFR). slia. }
      pose proof (Ms (to_Z a + to_Z b) MR ltac:(slia) HMR). rewrite Z.add_0_l. slia.
  Qed.

  (* [comment removed for export] *)
  Lemma csum_le : forall l MB FB, msum l <= MB -> fsum l <= FB -> csum H l <= as_Cm H MB + as_Cf H FB.
  Proof.
    intros l MB FB HM HF. pose proof (ah_costs H HH) as (M0 & Mm & F0 & Fm & Ms & Fs).
    pose proof (csum_bound l). pose proof (msum_nonneg l). pose proof (fsum_nonneg l).
    pose proof (Mm (msum l) MB ltac:(slia)). pose proof (Fm (fsum l) FB ltac:(slia)). slia.
  Qed.
End Csum.
