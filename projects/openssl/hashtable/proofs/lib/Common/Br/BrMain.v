(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxRn FxHandoff FxDrive.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec AsanAcct BackingAlgebra AsanCeil AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan CxPlanSound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrPure BrLedger BrKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record bdata : Type := BD {
  bd_vt : vtab;
  bd_tl : ttab;
  bd_xt : list (int * AX2.lin);     (* [comment removed for export] *)
  bd_teq : list teq;                (* [comment removed for export] *)
  bd_tb : list (int * Z * Z);       (* [comment removed for export] *)
  bd_ts : int;
  bd_tc : Z;
  bd_ah : Z;
  bd_resid : list nat               (* [comment removed for export] *)
}.

Definition tb_ok (rho : int -> word) (TB : list (int * Z * Z)) : Prop :=
  Forall (fun b => let '(t, lo, hi) := b in lo <= bv_unsigned (rho t) <= hi) TB.

Fixpoint tb_get (TB : list (int * Z * Z)) (t : int) : option (Z * Z) :=
  match TB with
  | [] => None
  | (t', lo, hi) :: r => if (t' =? t)%uint63 then Some (lo, hi) else tb_get r t
  end.

Definition TOPMAXz : Z := 0x7fffff800000.
Definition CEILz : Z := 0x7fff7f800000.
Definition STKz : Z := 8388608.

Section Check.
Variable IM : fimage.
Variable A : CAP.atable.
Variable Rb Lim : Z.
Variable BD : bdata.
Variable keep : list int.      (* [comment removed for export] *)
Variable KF : list hfact.      (* [comment removed for export] *)
Variable F : fstate.
Variable L : fledger.

Local Notation VT := (bd_vt BD).
Local Notation TL := (bd_tl BD).
Local Notation XT := (bd_xt BD).
Local Notation TEQ := (bd_teq BD).
Local Notation M := (f_mem F).
Local Notation ts := (bd_ts BD).
Local Notation tc := (bd_tc BD).

(* [comment removed for export] *)
Definition tbnd (t : int) : option (Z * Z) :=
  let b0 := (0, 2 ^ 64 - 1) in
  let b1 := match iget t M with
            | Some rg => (Z.max (fst b0) (to_Z (rg_clo rg)), Z.min (snd b0) (to_Z (rg_chi rg)))
            | None => b0
            end in
  let b2 := match tb_get (bd_tb BD) t with
            | Some (lo, hi) => (Z.max (fst b1) lo, Z.min (snd b1) hi)
            | None => b1
            end in
  Some (ledger_bnd TOPMAXz (fl_maps L) t (fst b2) (snd b2)).

Definition visb (t : int) (o n : Z) : bool :=
  if (t =? 0)%uint63 then (CAP.img_lo A <=? o) && (o + n <=? CAP.img_hi A)
  else if (t =? ts)%uint63 then (tc - STKz <=? o) && (o + n <=? tc + bd_ah BD)
  else ledger_vis_b L t o n.

Definition nosegb (t : int) (o n : Z) : bool :=
  ((t =? ts)%uint63 && (tc - STKz <=? o) && (o + n <=? tc + 2 ^ 40))
  || (negb (t =? 0)%uint63 && in_entry_b L t o n).

Definition kentry_check (k : AX2.kentry) : bool :=
  match k with
  | AX2.KWord a w v => kword_ok IM VT M TL XT TEQ visb a w v
                       || kword_slots_ok IM VT M TL XT TEQ visb (kf_slots IM M keep KF) a w v
  | AX2.KWr a n => kwr_ok IM VT M TL XT visb (kf_wr M keep KF) a n
  | AX2.KUnk a n => kunk_ok IM VT M TL XT visb nosegb (kf_wr M keep KF) a n
  | AX2.KZero a n => kzero_ok IM VT M TL XT visb nosegb (kf_slots IM M keep KF) a n
  | AX2.KRange e lo hi => krange_ok VT M TL XT tbnd e lo hi
  | AX2.KAlign e m => kalign_ok VT M TL XT e m
  | AX2.KDisj a1 n1 a2 n2 => kdisj_ok VT M TL XT ts tc (in_entry_b L) a1 n1 a2 n2
  | _ => false
  end.

(* [comment removed for export] *)
Definition mem_nat (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.

Fixpoint kn_check (i : nat) (kn : list AX2.kentry) : bool :=
  match kn with
  | [] => true
  | k :: r => (mem_nat i (bd_resid BD) || kentry_check k) && kn_check (Datatypes.S i) r
  end.

Fixpoint resid_kn (i : nat) (kn : list AX2.kentry) : list AX2.kentry :=
  match kn with
  | [] => []
  | k :: r => if mem_nat i (bd_resid BD) then k :: resid_kn (Datatypes.S i) r else resid_kn (Datatypes.S i) r
  end.

Definition regs_check (regs : list AX2.expr) : bool :=
  forallb (fun i => val_match VT TL XT TEQ (nth i regs (AX2.ELit 0)) (FxState.rget F (of_Z (Z.of_nat i)))) (seq 1 31).

Definition amap_check (m : CAP.amap) (e : fent) : bool :=
  let '(t, off, len) := e in
  match CAP.am_len m with
  | AX2.ELit l => (l =? to_Z len)
  | _ => false
  end
  && match aview VT M TL XT (AX2.SA (CAP.am_base m) 0) with
     | Some (t', o') => (t' =? t)%uint63 && (o' =? to_Z off)
     | None => false
     end
  && match CAP.am_kind m with
     | CAP.KRW => true
     | CAP.KNONE => mem_fent e (fl_na L)
     | _ => false
     end.

Fixpoint maps_check (ms : list CAP.amap) (es : list fent) : bool :=
  match ms, es with
  | [], [] => true
  | m :: ms', e :: es' => amap_check m e && maps_check ms' es'
  | _, _ => false
  end.

Definition brk_check (e : AX2.expr) : bool :=
  match iget (fl_brk L) M with
  | Some rgb => val_match VT TL XT TEQ e (FV (fl_brk L) (W64 0 (rg_len rgb)))
  | None => false
  end.

Definition is_nil {T : Type} (l : list T) : bool := match l with [] => true | _ => false end.

Definition bridge_check (CS : CAP.acs) : bool :=
  let ss := CAP.a_ss CS in
  (* [comment removed for export] *)
  match f_resv F with None => true | Some _ => false end
  && (AX2.s_pc ss =? to_Z (f_pc F))
  && is_nil (AX2.s_log ss)
  (* [comment removed for export] *)
  && tl_ok VT M TL
  && (0 <=? bd_ah BD) && (bd_ah BD <=? 2 ^ 40)
  && (0 <=? CAP.img_lo A) && (CAP.img_hi A <=? CEILz)
  && match aview VT M TL XT (AX2.SA CAP.e_spw 0) with
     | Some (t, o) => (t =? ts)%uint63 && (o =? tc)
     | None => false
     end
  (* [comment removed for export] *)
  && regs_check (AX2.s_regs ss)
  && kn_check 0 (AX2.s_know ss)
  (* [comment removed for export] *)
  && maps_check (CAP.a_maps CS) (fl_maps L)
  && brk_check (CAP.a_brk CS)
  && (Rb + fl_S L <=? CAP.a_totsz CS)
  && (fl_S L <=? CAP.a_eager CS)
  && (fl_S L <=? Lim)
  && is_nil (CAP.a_vis CS) && is_nil (CAP.a_ghost CS)
  && (0 <=? CAP.a_abytes CS).

End Check.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_sizes_live : forall l, CXS.sum_sizes l = live_bytes l.
Proof. induction l as [|[a s] r IH]; [reflexivity|]. cbn [CXS.sum_sizes live_bytes snd]. rewrite IH. reflexivity. Qed.

Lemma in_ivs_true z l : CXS.in_ivs z l = true <-> exists p, In p l /\ e_lo p <= z < e_hi p.
Proof.
  unfold CXS.in_ivs. rewrite existsb_exists. split.
  - intros (p & Hp & Hb). cbn beta in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists p. split; [exact Hp|]. unfold e_hi, e_lo, e_sz. lia.
  - intros (p & Hp & H1). exists p. split; [exact Hp|]. unfold e_hi, e_lo, e_sz in H1.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivs_false z l : (forall p, In p l -> ~ (e_lo p <= z < e_hi p)) -> CXS.in_ivs z l = false.
Proof.
  intros H. destruct (CXS.in_ivs z l) eqn:E; [|reflexivity].
  apply in_ivs_true in E as (p & Hp & Hz). exfalso. exact (H p Hp Hz).
Qed.

(* [comment removed for export] *)
Lemma adr_unsigned_z rho t z :
  0 <= bv_unsigned (rho t) + z < 2 ^ 64 -> bv_unsigned (adr rho t z) = bv_unsigned (rho t) + z.
Proof.
  intros H. unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

Section Sound.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable R0 : list (word * word).
Variable Rb Lim : Z.
Variable rl : role.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Hypothesis HRb : live_bytes R0 <= Rb.
(* [comment removed for export] *)
Variable A : CAP.atable.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis RES_cover : forall z, CAP.img_lo A <= z < CAP.img_hi A -> CXS.in_ivs z R0 = true.
Hypothesis HULL_ne : CAP.img_lo A < CAP.img_hi A.
Hypothesis HR0 : R0 = segments_reserved segs.
(* [comment removed for export] *)
Variable BD : bdata.
Variable xv : nat -> word.
Variable xb : nat -> list byte.

Variable n : int.
Variable rho : int -> word.
Variable F : fstate.
Variable L : fledger.
Variable ms : machine_state.
Variable m : Model.
Variable CS : CAP.acs.
Variable KF : list hfact.

Local Notation VT := (bd_vt BD).
Local Notation TL := (bd_tl BD).
Local Notation XT := (bd_xt BD).
Local Notation TEQ := (bd_teq BD).
Local Notation M := (f_mem F).
Local Notation ts := (bd_ts BD).
Local Notation tc := (bd_tc BD).
Local Notation V := (m_vmmaps m).
Local Notation E := (env_of rho xv xb VT).

Hypothesis HD : DInvX cfg segs IM R0 Lim rl keep mem0 XI xtags fr0 fc0 rom0 hi n rho F L ms m.
Hypothesis Hfr0 : fr0 = bvmap_empty.
Hypothesis Hfc0 : fc0 = Z_to_bv 32 0.
Hypothesis Hrom0 : rom0 = seg_rom segs.
Hypothesis Hchk : bridge_check IM A Rb Lim BD keep KF F L CS = true.
Hypothesis HTB : tb_ok rho (bd_tb BD).
Hypothesis HTEQ : teq_ok rho (bd_teq BD).
Hypothesis HXT : xt_ok rho xv xb (bd_vt BD) (bd_xt BD).
(* [comment removed for export] *)
Variable ms0 : machine_state.
Hypothesis HIM : image_ok segs IM.
Hypothesis Hms0 : ms_mem ms0 = mem0.
Hypothesis HKF : Forall (hholds segs rho ms0) KF.
Hypothesis Hisp : bv_unsigned (vm_init_sp V) = ISP.
Hypothesis Hisp2 : ISP = bv_unsigned (rho ts) + tc.
Hypothesis HargH : forall a, argH E a = true -> ISP + bd_ah BD <= bv_unsigned a.

(* [comment removed for export] *)
Let HDI : DInv cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F L ms m := proj1 HD.

Lemma br_rho0 : rho 0%uint63 = Z_to_bv 64 0.
Proof. exact (proj1 (proj2 HDI)). Qed.

Lemma br_R : R segs IM rho F ms.
Proof. exact (Rn_R segs IM n rho F ms (proj1 HDI) br_rho0). Qed.

Lemma br_mem : mem_ok segs IM rho M (ms_mem ms).
Proof. exact (R_mem _ _ _ _ _ br_R). Qed.

Lemma br_regions : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 br_mem t rg Hg)). Qed.

Lemma br_sep : regions_sep rho M.
Proof. exact (proj2 br_mem). Qed.

Lemma br_nolazy : model_nolazy m.
Proof. exact (DInv_nolazy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDI). Qed.

Lemma br_inv : ledger_inv R0 Lim (fl_c L) (fl_S L) V.
Proof. destruct HDI as (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma br_halt : m_halted m = None.
Proof. destruct HDI as (_ & _ & H & _). exact H. Qed.

Lemma br_exact : vm_maps V = map (den rho) (fl_maps L) /\ vm_noaccess V = map (den rho) (fl_na L).
Proof. exact (DInvX_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD). Qed.

Lemma br_mirror : mirror rho L M V.
Proof. destruct HDI as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma br_in_maps : Forall (ent_in M) (fl_maps L).
Proof.
  destruct br_mirror as (H & _ & _). apply Forall_forall. intros e He.
  exact (proj1 (proj1 (ent_ok_iff rho M _ e) (proj1 (Forall_forall _ _) H e He))).
Qed.

Lemma br_in_na : Forall (ent_in M) (fl_na L).
Proof.
  destruct br_mirror as (_ & H & _). apply Forall_forall. intros e He.
  exact (proj1 (proj1 (ent_ok_iff rho M _ e) (proj1 (Forall_forall _ _) H e He))).
Qed.

Lemma br_alloc_top : alloc_top V = ISP - STKz /\ CEILz <= alloc_top V <= TOPMAXz.
Proof.
  destruct br_inv as [_ _ Hlo Hhi _ _ _ _ _ _ _ _ _ _ _ _].
  unfold alloc_top, stack_max_size, sp_window_lo, sp_window_hi, CEILz, TOPMAXz, STKz in *. lia.
Qed.


(* [comment removed for export] *)
Lemma chk_parts :
  f_resv F = None
  /\ AX2.s_pc (CAP.a_ss CS) = to_Z (f_pc F)
  /\ AX2.s_log (CAP.a_ss CS) = []
  /\ tl_ok VT M TL = true
  /\ 0 <= bd_ah BD <= 2 ^ 40
  /\ 0 <= CAP.img_lo A /\ CAP.img_hi A <= CEILz
  /\ aview VT M TL XT (AX2.SA CAP.e_spw 0) = Some (ts, tc)
  /\ regs_check BD F (AX2.s_regs (CAP.a_ss CS)) = true
  /\ kn_check IM A BD keep KF F L 0 (AX2.s_know (CAP.a_ss CS)) = true
  /\ maps_check BD F L (CAP.a_maps CS) (fl_maps L) = true
  /\ brk_check BD F L (CAP.a_brk CS) = true
  /\ Rb + fl_S L <= CAP.a_totsz CS
  /\ fl_S L <= CAP.a_eager CS
  /\ fl_S L <= Lim
  /\ CAP.a_vis CS = [] /\ CAP.a_ghost CS = []
  /\ 0 <= CAP.a_abytes CS.
Proof.
  pose proof Hchk as H. unfold bridge_check in H.
  apply andb_prop in H as [H H19]. apply andb_prop in H as [H H18]. apply andb_prop in H as [H H17].
  apply andb_prop in H as [H H16]. apply andb_prop in H as [H H15]. apply andb_prop in H as [H H14].
  apply andb_prop in H as [H H13]. apply andb_prop in H as [H H12]. apply andb_prop in H as [H H11].
  apply andb_prop in H as [H H10]. apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8].
  apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split. { destruct (f_resv F); [discriminate | reflexivity]. }
  split. { apply Z.eqb_eq. exact H2. }
  split. { destruct (AX2.s_log (CAP.a_ss CS)); [reflexivity | discriminate]. }
  split; [exact H4|].
  split. { apply Z.leb_le in H5, H6. lia. }
  split. { apply Z.leb_le. exact H7. }
  split. { apply Z.leb_le. exact H8. }
  split. { destruct (aview VT M TL XT (AX2.SA CAP.e_spw 0)) as [[t o]|]; [|discriminate].
           apply andb_prop in H9 as [Ha Hb]. apply Uint63.eqb_spec in Ha. apply Z.eqb_eq in Hb. subst. reflexivity. }
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
  split. { apply Z.leb_le. exact H14. }
  split. { apply Z.leb_le. exact H15. }
  split. { apply Z.leb_le. exact H16. }
  split. { destruct (CAP.a_vis CS); [reflexivity | discriminate]. }
  split. { destruct (CAP.a_ghost CS); [reflexivity | discriminate]. }
  apply Z.leb_le. exact H19.
Qed.

Lemma br_isp_range : CEILz + STKz <= ISP <= TOPMAXz + STKz.
Proof. destruct br_alloc_top as [E1 E2]. lia. Qed.

(* [comment removed for export] *)
Lemma br_visb_sound : forall t o len, visb A BD L t o len = true ->
  forall j, 0 <= j < len -> CXS.hid A argH E CS m (adr rho t (o + j)) = false.
Proof.
  intros t o len Hv j Hj.
  destruct chk_parts as (_ & _ & _ & _ & Hah & Hlo & Hhi & _).
  destruct br_alloc_top as [Eat Hat]. pose proof br_isp_range as Hir.
  unfold CEILz, TOPMAXz, STKz in *.
  assert (Hmain : forall z, bv_unsigned (adr rho t (o + j)) = z ->
            CXS.vis A E CS m (adr rho t (o + j)) = true -> z < ISP + bd_ah BD ->
            CXS.hid A argH E CS m (adr rho t (o + j)) = false).
  { intros z Ez Hvis Hlt. unfold CXS.hid. rewrite Hvis. cbn [negb]. rewrite orb_false_r.
    destruct (argH E (adr rho t (o + j))) eqn:Ea; [|reflexivity].
    apply HargH in Ea. lia. }
  unfold visb in Hv. destruct (t =? 0)%uint63 eqn:Et0.
  - apply Uint63.eqb_spec in Et0. subst t. apply andb_prop in Hv as [H1 H2]. apply Z.leb_le in H1, H2.
    assert (Ez : bv_unsigned (adr rho 0%uint63 (o + j)) = o + j).
    { rewrite adr_unsigned_z; rewrite br_rho0; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia. }
    apply (Hmain (o + j) Ez); [|lia].
    unfold CXS.vis. rewrite Ez. unfold CXS.in_hull.
    replace (CAP.img_lo A <=? o + j) with true by (symmetry; apply Z.leb_le; lia).
    replace (o + j <? CAP.img_hi A) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (t =? ts)%uint63 eqn:Ets.
    + apply Uint63.eqb_spec in Ets. subst t. apply andb_prop in Hv as [H1 H2]. apply Z.leb_le in H1, H2.
      unfold STKz in H1.
      assert (Ez : bv_unsigned (adr rho ts (o + j)) = bv_unsigned (rho ts) + o + j).
      { rewrite adr_unsigned_z; lia. }
      apply (Hmain _ Ez); [|lia].
      unfold CXS.vis. rewrite Ez.
      replace (alloc_top V <=? bv_unsigned (rho ts) + o + j) with true by (symmetry; apply Z.leb_le; lia).
      rewrite orb_true_r. reflexivity.
    + destruct br_exact as [Hmaps Hna].
      destruct (ledger_vis_sound rho M L V R0 Lim _ _ br_regions br_sep br_inv Hmaps Hna br_in_maps br_in_na
                  t o len Hv (bv_unsigned (rho t) + o + j) ltac:(lia)) as (Hin & Hnot & Hlt).
      assert (Ez : bv_unsigned (adr rho t (o + j)) = bv_unsigned (rho t) + o + j).
      { destruct Hin as (p & _ & Hp1 & _). pose proof (br_u64 (fst p)). unfold e_lo in Hp1.
        rewrite adr_unsigned_z; lia. }
      apply (Hmain _ Ez); [|lia].
      unfold CXS.vis. rewrite Ez.
      rewrite (proj2 (in_ivs_true _ _) Hin), (in_ivs_false _ _ Hnot).
      rewrite (proj1 br_nolazy). cbn. rewrite orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma tb_get_sound : forall TB t lo hi', tb_ok rho TB -> tb_get TB t = Some (lo, hi') ->
  lo <= bv_unsigned (rho t) <= hi'.
Proof.
  induction TB as [|[[t' l] h] r IH]; intros t lo hi' Hok Hg; [discriminate|].
  cbn [tb_get] in Hg. unfold tb_ok in Hok. pose proof (Forall_inv Hok) as Hh. pose proof (Forall_inv_tail Hok) as Hr.
  cbn beta iota in Hh.
  destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t'. injection Hg as <- <-. exact Hh.
  - exact (IH t lo hi' Hr Hg).
Qed.

Lemma br_tbnd_sound : forall t lo hi', tbnd BD F L t = Some (lo, hi') -> lo <= bv_unsigned (rho t) <= hi'.
Proof.
  intros t lo hi' Hb. unfold tbnd in Hb. injection Hb as Hb.
  apply (f_equal fst) in Hb as Hb1. apply (f_equal snd) in Hb as Hb2. cbn [fst snd] in Hb1, Hb2.
  rewrite <- Hb1, <- Hb2. clear Hb Hb1 Hb2.
  destruct br_exact as [Hmaps _]. destruct br_alloc_top as [_ Hat].
  apply (ledger_bnd_sound rho M L V R0 Lim _ _ br_regions br_inv Hmaps br_in_maps TOPMAXz (proj2 Hat));
    [intros e He; exact He|].
  pose proof (br_u64 (rho t)) as Hu.
  assert (H1 : fst (match iget t M with
                    | Some rg => (Z.max 0 (to_Z (rg_clo rg)), Z.min (2 ^ 64 - 1) (to_Z (rg_chi rg)))
                    | None => (0, 2 ^ 64 - 1) end) <= bv_unsigned (rho t)
               <= snd (match iget t M with
                    | Some rg => (Z.max 0 (to_Z (rg_clo rg)), Z.min (2 ^ 64 - 1) (to_Z (rg_chi rg)))
                    | None => (0, 2 ^ 64 - 1) end)).
  { destruct (iget t M) as [rg|] eqn:Hg; cbn [fst snd]; [|lia].
    pose proof (br_regions t rg Hg) as Hro. unfold region_ok in Hro.
    (* [comment removed for export] *)
    assert (Hcb : to_Z (rg_clo rg) <= bv_unsigned (rho t) <= to_Z (rg_chi rg)) by (decompose [and] Hro; split; assumption).
    lia. }
  cbn [fst snd] in *.
  destruct (tb_get (bd_tb BD) t) as [[l h]|] eqn:Hg; cbn [fst snd]; [|exact H1].
  pose proof (tb_get_sound _ t l h HTB Hg). lia.
Qed.

Lemma br_in_entry_sound : forall t o len, in_entry_b L t o len = true ->
  exists e, bv_unsigned (rho t) + o + len <= e /\ e <= alloc_top V /\ e mod 4096 = 0.
Proof.
  intros t o len Hb. destruct br_exact as [Hmaps _].
  destruct (in_entry_sound rho M L V R0 Lim _ _ br_regions br_inv Hmaps br_in_maps t o len Hb)
    as (e & H1 & H2 & H3 & _).
  exists e. repeat split; assumption.
Qed.

Lemma br_HAT : alloc_top V = bv_unsigned (rho ts) + tc - 8388608.
Proof. destruct br_alloc_top as [E1 _]. unfold STKz in E1. lia. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma br_regs : AX2S.regs_ok E (AX2.s_regs (CAP.a_ss CS)) (ms_regs ms).
Proof.
  destruct chk_parts as (_ & _ & _ & HTL & _ & _ & _ & _ & Hrg & _).
  unfold AX2S.regs_ok. intros r. unfold getr, AX2.sr_get.
  destruct (bv_eqb r 0) eqn:Er; [reflexivity|].
  pose proof (DInv_reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HDI) as Hreg.
  unfold Sem.rget in Hreg. change (is_x0 r) with (bv_eqb r 0) in Hreg. rewrite Er in Hreg.
  change (c_regs (core_of ms)) with (ms_regs ms) in Hreg. rewrite Hreg.
  unfold regs_check in Hrg. rewrite forallb_forall in Hrg.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  assert (Hr0 : bv_unsigned r <> 0).
  { intros E0. unfold bv_eqb in Er. rewrite E0 in Er. discriminate. }
  specialize (Hrg (AX2.ridx r)). unfold AX2.ridx in *.
  rewrite Z2Nat.id in Hrg by lia.
  symmetry. apply (val_match_sound rho xv xb VT M TL XT TEQ br_regions br_rho0 HTL HXT HTEQ).
  apply Hrg. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma amap_check_sound mp e :
  amap_check BD F L mp e = true -> ent_in M e ->
  CXS.amap_den E mp = den rho e
  /\ (CAP.am_kind mp = CAP.KRW \/ (CAP.am_kind mp = CAP.KNONE /\ In e (fl_na L))).
Proof.
  destruct chk_parts as (_ & _ & _ & HTL & _).
  destruct e as [[t off] len]. unfold amap_check. intros Hc Hent.
  apply andb_prop in Hc as [Hc Hkind]. apply andb_prop in Hc as [Hlen Hbase].
  destruct (CAP.am_len mp) as [l| | | | | | |] eqn:El; try discriminate. apply Z.eqb_eq in Hlen. subst l.
  destruct (aview VT M TL XT (AX2.SA (CAP.am_base mp) 0)) as [[t' o']|] eqn:Hav; [|discriminate].
  apply andb_prop in Hbase as [Ht Ho]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Ho. subst t' o'.
  pose proof (aview_sound rho xv xb VT M TL XT br_regions br_rho0 HTL HXT _ t (to_Z off) Hav) as Hs.
  unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. rewrite Z.add_0_r in Hs.
  split.
  - unfold CXS.amap_den, den. rewrite El. cbn [AX2.edenot]. f_equal.
    destruct Hent as (rg & Hg & Hlo & Hhi).
    destruct (br_regions t rg Hg) as (_ & _ & Hb & _).
    pose proof (i63_range off). pose proof (i63_range len). pose proof (i63_range (rg_len rg)).
    apply bv_eq. rewrite Hs. symmetry. apply adr_unsigned_z. pose proof (br_u64 (rho t)). lia.
  - destruct (CAP.am_kind mp); try discriminate; [left; reflexivity | right; split; [reflexivity|]].
    apply mem_fent_In. exact Hkind.
Qed.

Lemma maps_check_sound : forall mps es,
  maps_check BD F L mps es = true -> Forall (ent_in M) es ->
  CXS.maps_match E mps (map (den rho) es)
  /\ Forall (fun mp => CAP.am_kind mp = CAP.KRW
                       \/ (CAP.am_kind mp = CAP.KNONE /\ In (CXS.amap_den E mp) (map (den rho) (fl_na L)))) mps.
Proof.
  induction mps as [|mp mps IH]; intros [|e es] Hc Hent; try discriminate.
  - split; [reflexivity | constructor].
  - cbn [maps_check] in Hc. apply andb_prop in Hc as [Hc1 Hc2].
    destruct (amap_check_sound mp e Hc1 (Forall_inv Hent)) as [Hden Hkind].
    destruct (IH es Hc2 (Forall_inv_tail Hent)) as [Hmm Hks].
    split.
    + cbn [CXS.maps_match map].
      assert (Hfog : CAP.is_fog mp = false).
      { unfold CAP.is_fog. destruct Hkind as [-> | [-> _]]; reflexivity. }
      rewrite Hfog. right. exists (map (den rho) es). split; [rewrite Hden; reflexivity | exact Hmm].   (* [comment removed for export] *)
    + constructor; [|exact Hks]. destruct Hkind as [Hk | [Hk Hin]]; [left; exact Hk | right; split; [exact Hk|]].
      rewrite Hden. apply in_map. exact Hin.
Qed.

Lemma br_brk : vm_brk V = AX2.edenot E (CAP.a_brk CS).
Proof.
  destruct chk_parts as (_ & _ & _ & HTL & _ & _ & _ & _ & _ & _ & _ & Hbrk & _).
  unfold brk_check in Hbrk. destruct br_mirror as (_ & _ & rgb & Hg & Hb).
  rewrite Hg in Hbrk.
  rewrite (val_match_sound rho xv xb VT M TL XT TEQ br_regions br_rho0 HTL HXT HTEQ _ _ Hbrk).
  rewrite <- Hb. symmetry. apply (dv_adr rho); [|reflexivity].
  exact (proj1 (br_regions _ rgb Hg)).
Qed.

(* [comment removed for export] *)
Lemma br_seps : CXS.seps (vm_maps V).
Proof.
  destruct br_inv as [_ _ _ _ _ _ _ _ Hd _ _ _ _ _ _ _]. revert Hd.
  induction (vm_maps V) as [|p l IH]; intros Hd; [constructor|].
  destruct Hd as [Hp Hl]. constructor; [|exact (IH Hl)].
  apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hp q Hq) as Hpq.
  unfold CXS.iv_disjoint. unfold e_disj, e_hi, e_lo, e_sz in Hpq. exact Hpq.
Qed.

Lemma br_wf : model_ivs_wf m.
Proof.
  destruct br_inv as [_ _ Hsplo _ _ _ Htop _ _ _ _ Hna _ _ _ _].
  pose proof (alloc_top_lt V) as Hat. unfold two_pow_64 in Hat.
  assert (Hmaps : forall p, In p (vm_maps V) -> e_hi p <= 2 ^ 64).
  { intros p Hp. pose proof (proj1 (Forall_forall _ _) Htop p Hp) as [_ H2]. lia. }
  unfold model_ivs_wf. split; [|split; [|split]].
  - intros q Hq. unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S. specialize (Hmaps q Hq).
    unfold e_hi, e_lo, e_sz in Hmaps. exact Hmaps.
  - intros q Hq. pose proof (proj1 (Forall_forall _ _) Hna q Hq) as (_ & p & Hp & _ & Hin).
    specialize (Hmaps p Hp). unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S.
    unfold e_hi, e_lo, e_sz in *. lia.
  - rewrite (proj1 br_nolazy). intros q [].
  - unfold init_sp_ok. exact Hsplo.
Qed.

Lemma br_bounds :
  Forall (fun iv => 0 < bv_unsigned (snd iv)
                    /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CAP.img_lo A \/ CAP.img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= alloc_top V) (vm_maps V).
Proof.
  destruct br_inv as [_ _ _ _ Hpos Hal Htop HdR _ _ _ _ _ _ _ _].
  apply Forall_forall. intros p Hp.
  pose proof (proj1 (Forall_forall _ _) Hpos p Hp) as H1.
  pose proof (proj1 (Forall_forall _ _) Hal p Hp) as [H2 H3].
  pose proof (proj1 (Forall_forall _ _) Htop p Hp) as [H4 H5].
  pose proof (proj1 (Forall_forall _ _) HdR p Hp) as H6.
  unfold e_hi, e_lo, e_sz, page_size in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  destruct (Z_le_gt_dec (bv_unsigned (fst p) + bv_unsigned (snd p)) (CAP.img_lo A)) as [Ha|Ha]; [left; exact Ha|].
  destruct (Z_le_gt_dec (CAP.img_hi A) (bv_unsigned (fst p))) as [Hb|Hb]; [right; exact Hb|].
  exfalso. set (z := Z.max (bv_unsigned (fst p)) (CAP.img_lo A)).
  pose proof (RES_cover z ltac:(unfold z; lia)) as Hin.
  apply in_ivs_true in Hin as (r & Hr & Hz).
  pose proof (proj1 (Forall_forall _ _) H6 r Hr) as Hd.
  unfold e_disj, e_hi, e_lo, e_sz in *. unfold z in Hz. lia.
Qed.

Lemma br_nasub : forall z, CXS.in_ivs z (vm_noaccess V) = true -> CXS.in_ivs z (vm_maps V) = true.
Proof.
  intros z Hz. destruct br_inv as [_ _ _ _ _ _ _ _ _ _ _ Hna _ _ _ _].
  apply in_ivs_true in Hz as (q & Hq & Hzq). apply in_ivs_true.
  pose proof (proj1 (Forall_forall _ _) Hna q Hq) as (_ & p & Hp & Hin1 & Hin2).
  exists p. split; [exact Hp|]. lia.
Qed.

Lemma br_eager : eager_used m <= fl_S L.
Proof.
  destruct br_inv as [_ _ _ _ _ _ _ _ _ _ Hsz _ _ _ _ _].
  pose proof (vm_backing_used_le_live m (proj2 br_nolazy)) as H1.
  rewrite vm_backing_used_split, (proj2 br_nolazy) in H1. cbn [length] in H1. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma br_hid_false_z : forall t o len, ledger_vis_b L t o len = true ->
  forall z, bv_unsigned (rho t) + o <= z < bv_unsigned (rho t) + o + len ->
    CXS.hid A argH E CS m (Z_to_bv 64 z) = false.
Proof.
  intros t o len Hv z Hz. destruct br_exact as [Hmaps Hna].
  destruct br_alloc_top as [Eat Hat]. unfold CEILz, TOPMAXz, STKz in *.
  destruct chk_parts as (_ & _ & _ & _ & Hah & _).
  destruct (ledger_vis_sound rho M L V R0 Lim _ _ br_regions br_sep br_inv Hmaps Hna br_in_maps br_in_na
              t o len Hv z Hz) as (Hin & Hnot & Hlt).
  assert (Ez : bv_unsigned (Z_to_bv 64 z) = z).
  { destruct Hin as (p & _ & Hp1 & _). pose proof (br_u64 (fst p)). unfold e_lo in Hp1.
    apply br_lit_small. lia. }
  unfold CXS.hid.
  assert (Hvis : CXS.vis A E CS m (Z_to_bv 64 z) = true).
  { unfold CXS.vis. rewrite Ez. rewrite (proj2 (in_ivs_true _ _) Hin), (in_ivs_false _ _ Hnot).
    rewrite (proj1 br_nolazy). cbn. rewrite orb_true_r. reflexivity. }
  rewrite Hvis. cbn [negb]. rewrite orb_false_r.
  destruct (argH E (Z_to_bv 64 z)) eqn:Ea; [|reflexivity].
  apply HargH in Ea. rewrite Ez in Ea. lia.
Qed.

Lemma br_nosegb_sound : forall t o len, nosegb BD L t o len = true ->
  forall j, 0 <= j < len -> find_segment segs (bv_unsigned (adr rho t (o + j))) 1 = None.
Proof.
  intros t o len Hv j Hj. unfold nosegb in Hv.
  destruct chk_parts as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  destruct br_alloc_top as [Eat Hat]. pose proof br_isp_range as Hir.
  unfold CEILz, TOPMAXz, STKz in *.
  apply orb_prop in Hv as [Hv|Hv].
  - apply andb_prop in Hv as [Hv H3]. apply andb_prop in Hv as [H1 H2].
    apply Uint63.eqb_spec in H1. subst t. apply Z.leb_le in H2, H3.
    assert (Ez : bv_unsigned (adr rho ts (o + j)) = bv_unsigned (rho ts) + o + j).
    { rewrite adr_unsigned_z; lia. }
    apply SEGS_in_hull. rewrite Ez. unfold CXS.in_hull.
    replace (bv_unsigned (rho ts) + o + j <? CAP.img_hi A) with false by (symmetry; apply Z.ltb_ge; lia).
    apply andb_false_r.
  - apply andb_prop in Hv as [_ He]. destruct br_exact as [Hmaps _].
    destruct (in_entry_sound rho M L V R0 Lim _ _ br_regions br_inv Hmaps br_in_maps t o len He)
      as (e & He1 & He2 & _ & p & Hp & Hplo & -> & _).
    pose proof (proj1 (Forall_forall _ _) br_bounds p Hp) as (_ & _ & _ & Hhull & _).
    pose proof (br_u64 (fst p)) as Hu. unfold e_hi, e_lo, e_sz in *.
    assert (Ez : bv_unsigned (adr rho t (o + j)) = bv_unsigned (rho t) + o + j).
    { rewrite adr_unsigned_z; lia. }
    apply SEGS_in_hull. rewrite Ez. unfold CXS.in_hull.
    destruct Hhull as [Hb|Hb].
    + replace (CAP.img_lo A <=? bv_unsigned (rho t) + o + j) with false by (symmetry; apply Z.leb_gt; lia).
      reflexivity.
    + replace (bv_unsigned (rho t) + o + j <? CAP.img_hi A) with false by (symmetry; apply Z.ltb_ge; lia).
      apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma br_frame : forall t, In t keep -> forall rg x, iget t M = Some rg ->
  bv_unsigned (rho t) + to_Z (rg_lo rg) <= bv_unsigned x < bv_unsigned (rho t) + to_Z (rg_len rg) ->
  ms_mem ms x = ms_mem ms0 x.
Proof.
  intros t Ht rg x Hg Hx. destruct HDI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr).
  rewrite Hms0. exact (proj2 (Hfr t Ht) rg x Hg Hx).
Qed.

Lemma br_xslots_sound : forall t o sls, kf_slots IM M keep KF t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs (ms_mem ms) (adr rho t (o / 8 * 8 + Z.of_nat j))).
Proof. exact (kf_slots_sound segs IM rho M keep KF ms0 (ms_mem ms) HIM br_rho0 br_regions HKF br_frame). Qed.

Lemma br_xwrb_sound : forall t o len, kf_wr M keep KF t o len = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + len <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + len -> wview segs (ms_mem ms) (adr rho t x) <> None.
Proof. exact (kf_wr_sound segs rho M keep KF ms0 (ms_mem ms) br_regions HKF br_frame). Qed.

(* [comment removed for export] *)
Lemma br_kept_mem : forall t o len, In t keep -> ledger_vis_b L t o len = true ->
  forall i, 0 <= i < len ->
    CXS.Mr A argH E CS m (ms_mem ms) (adr rho t (o + i)) = mem0 (adr rho t (o + i))
    /\ bv_unsigned (adr rho t (o + i)) = bv_unsigned (rho t) + o + i.
Proof.
  intros t o len Ht Hv i Hi. destruct br_exact as [Hmaps _].
  pose proof Hv as Hv'. unfold ledger_vis_b in Hv'. apply andb_prop in Hv' as [He _].
  destruct (in_entry_sound rho M L V R0 Lim _ _ br_regions br_inv Hmaps br_in_maps t o len He)
    as (e & He1 & He2 & _ & p & Hp & Hplo & -> & rg & Hg & Hrlo & Hrhi).
  pose proof (br_u64 (fst p)) as Hu. pose proof (alloc_top_lt V) as Hat. unfold two_pow_64 in Hat.
  unfold e_hi, e_lo, e_sz in *.
  assert (Ez : bv_unsigned (adr rho t (o + i)) = bv_unsigned (rho t) + o + i).
  { rewrite adr_unsigned_z; lia. }
  split; [|exact Ez].
  assert (Ea : adr rho t (o + i) = Z_to_bv 64 (bv_unsigned (rho t) + o + i)).
  { apply bv_eq. rewrite Ez. symmetry. apply br_lit_small. lia. }
  change (CXS.Mr A argH E CS m (ms_mem ms)) with (mrestrict (CXS.hid A argH E CS m) (ms_mem ms)).
  unfold mrestrict.
  assert (Hh : CXS.hid A argH E CS m (adr rho t (o + i)) = false).
  { rewrite Ea. exact (br_hid_false_z t o len Hv (bv_unsigned (rho t) + o + i) ltac:(lia)). }
  rewrite Hh.
  destruct HDI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr).
  apply (proj2 (Hfr t Ht) rg _ Hg). unfold in_ival. rewrite Ez.
  pose proof (i63_range (rg_lo rg)). lia.
Qed.

Definition resid_ok : Prop :=
  Forall (AX2S.kentry_ok segs E (CXS.Mr A argH E CS m (ms_mem ms))) (resid_kn BD 0 (AX2.s_know (CAP.a_ss CS))).
Hypothesis Hresid : resid_ok.

Lemma br_kentry k : kentry_check IM A BD keep KF F L k = true ->
  AX2S.kentry_ok segs E (CXS.Mr A argH E CS m (ms_mem ms)) k.
Proof.
  destruct chk_parts as (_ & _ & _ & HTL & _). intros Hkn.
  change (CXS.Mr A argH E CS m (ms_mem ms)) with (mrestrict (CXS.hid A argH E CS m) (ms_mem ms)).
  destruct k as [a w v | a n0 | a n0 k0 | lo0 hi0 | e m0 | e lo0 hi0 | a n0 | a1 n1 a2 n2 | a n0 c0 | a n0];
    cbn [kentry_check] in Hkn; try discriminate.
  - apply orb_prop in Hkn as [Hkn|Hkn].
    + exact (kword_sound segs IM rho xv xb VT M TL XT TEQ (ms_mem ms) br_rho0 br_mem HTL HXT HTEQ _ _ br_visb_sound a w v Hkn).
    + exact (kword_slots_sound segs IM rho xv xb VT M TL XT TEQ (ms_mem ms) br_rho0 br_mem HTL HXT HTEQ _ _ br_visb_sound
               _ br_xslots_sound a w v Hkn).
  - exact (kzero_sound segs IM rho xv xb VT M TL XT (ms_mem ms) br_rho0 br_mem HTL HXT _ _ br_visb_sound
             _ (fun t o n1 Hq j Hj => or_intror (br_nosegb_sound t o n1 Hq j Hj)) _ br_xslots_sound a n0 Hkn).
  - exact (kalign_sound segs rho xv xb VT M TL XT br_rho0 br_regions HTL HXT e m0 Hkn _).
  - exact (krange_sound segs rho xv xb VT M TL XT br_rho0 br_regions HTL HXT _ br_tbnd_sound e lo0 hi0 Hkn _).
  - exact (kwr_sound segs IM rho xv xb VT M TL XT (ms_mem ms) br_rho0 br_mem HTL HXT _ _ br_visb_sound _ br_xwrb_sound a n0 Hkn).
  - exact (kdisj_sound segs rho xv xb VT M TL XT br_rho0 br_regions br_sep HTL HXT ts tc (alloc_top V) br_HAT
             _ br_in_entry_sound a1 n1 a2 n2 Hkn _).
  - exact (kunk_sound segs IM rho xv xb VT M TL XT (ms_mem ms) br_rho0 br_mem HTL HXT _ _ br_visb_sound
             _ (fun t o n1 Hq j Hj => or_intror (br_nosegb_sound t o n1 Hq j Hj)) _ br_xwrb_sound a n0 Hkn).
Qed.

Lemma br_know : AX2S.know_ok segs E (CXS.Mr A argH E CS m (ms_mem ms)) (CAP.kn CS).
Proof.
  destruct chk_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkn & _).
  unfold AX2S.know_ok, CAP.kn. pose proof Hresid as Hr. unfold resid_ok in Hr.
  revert Hkn Hr. generalize 0%nat. induction (AX2.s_know (CAP.a_ss CS)) as [|k r IH]; intros i Hkn Hr; [constructor|].
  cbn [kn_check resid_kn] in Hkn, Hr. apply andb_prop in Hkn as [Hk Hrest].
  destruct (mem_nat i (bd_resid BD)) eqn:Ei.
  - constructor; [exact (Forall_inv Hr) | exact (IH (Datatypes.S i) Hrest (Forall_inv_tail Hr))].
  - cbn [orb] in Hk. constructor; [exact (br_kentry k Hk) | exact (IH (Datatypes.S i) Hrest Hr)].
Qed.

(* [comment removed for export] *)
Lemma br_shape : ms = mkst (ms_regs ms) (Z_to_bv 64 (CAP.pc CS)) (ms_mem ms) (seg_rom segs).
Proof.
  destruct chk_parts as (Hresv & Hpc & _).
  destruct (DInvX_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as (Efr & Efc & Erom).
  pose proof (DInv_pc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDI) as Epc.
  pose proof (DInv_svc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDI) as Esvc.
  pose proof (DInv_resv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDI Hresv) as Eresv.
  unfold CAP.pc. rewrite Hpc. unfold mkst.
  destruct ms as [rg frg pcv svc resv fcsr mem rom]. cbn in *.
  rewrite Efr, Efc, Erom, Epc, Esvc, Eresv, Hfr0, Hfc0, Hrom0. reflexivity.
Qed.

(* [comment removed for export] *)
Hypothesis Hfds : CXS.fds_ok E (CAP.a_fd CS) m.
Hypothesis Hfs : m_fs m = FS0.
Hypothesis Htid : CAP.a_tidset CS = false -> m_tid m = None.
Hypothesis Hsinv : SINV E (ms_mem ms).

Theorem bridge_cs_ok : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS (ms_regs ms) (ms_mem ms) m.
Proof.
  destruct chk_parts as (_ & _ & Hlog & HTL & _ & _ & _ & Hspw & _ & _ & Hmaps & _ & Htot & Heag & Hlim
                           & Hvis & Hgh & Hab).
  destruct br_exact as [Emaps Ena].
  destruct (maps_check_sound _ _ Hmaps br_in_maps) as [Hmm Hkinds].
  pose proof br_inv as Hinv. destruct Hinv as [Hres Hlimit _ _ _ _ _ _ _ _ Hsz _ _ _ Hbrkmin _].
  assert (HallowA : CXS.allowA A E CS = []) by (unfold CXS.allowA; rewrite Hvis, Hgh; reflexivity).
  constructor.
  - exact br_regs.
  - exact Hlog.
  - exact br_know.
  - exact br_halt.
  - exact Hfds.
  - exact Hfs.
  - exact Htid.
  - rewrite Hres. exact HR0.
  - exact Hlimit.
  - rewrite Emaps. exact Hmm.
  - apply Forall_forall. intros mp Hmp Hhole. exfalso.
    pose proof (proj1 (Forall_forall _ _) Hkinds mp Hmp) as Hk. unfold CAP.is_hole in Hhole.
    destruct Hk as [Hk | [Hk _]]; rewrite Hk in Hhole; discriminate.
  - exact br_seps.
  - exact br_wf.
  - exact br_bounds.
  - rewrite (proj1 br_nolazy). constructor.
  - exact br_nasub.
  - apply Forall_forall. intros mp Hmp Hk'.
    pose proof (proj1 (Forall_forall _ _) Hkinds mp Hmp) as Hk.
    destruct Hk as [Hk | [Hk Hin]].
    + rewrite Hk in Hk'. destruct Hk'; discriminate.
    + rewrite Ena. exact Hin.
  - apply Forall_forall. intros mp Hmp Hk'.
    pose proof (proj1 (Forall_forall _ _) Hkinds mp Hmp) as Hk.
    destruct Hk as [Hk | [Hk _]]; rewrite Hk in Hk'; discriminate.
  - rewrite sum_sizes_live, live_bytes_app, Hres. lia.
  - exact I.
  - exact br_brk.
  - exact Hbrkmin.
  - pose proof br_eager. lia.
  - rewrite HallowA. cbn [A_bytes]. exact Hab.
  - rewrite HallowA. constructor.
    + rewrite (proj2 br_nolazy). constructor.
    + rewrite (proj2 br_nolazy). intros p0 [].
    + rewrite (proj2 br_nolazy). intros p0 [].
    + rewrite (proj2 br_nolazy). intros p0 [].
    + cbn [A_bytes]. pose proof br_eager. lia.   (* [comment removed for export] *)
  - intros a _ _ _ Hlz _. rewrite (proj1 br_nolazy) in Hlz. discriminate.
  - exact Hsinv.
  - split; [exact Hisp|].
    pose proof (aview_sound rho xv xb VT M TL XT br_regions br_rho0 HTL HXT _ ts tc Hspw) as Hs.
    unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. unfold CXS.uE. lia.
  - destruct br_alloc_top as [_ Hat]. unfold CEILz, TOPMAXz in Hat. unfold CAP.CEIL, CAP.TOPMAX. exact Hat.
Qed.

Theorem bridge_sound :
  ms = mkst (ms_regs ms) (Z_to_bv 64 (CAP.pc CS)) (ms_mem ms) (seg_rom segs)
  /\ CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS (ms_regs ms) (ms_mem ms) m.
Proof. split; [exact br_shape | exact bridge_cs_ok]. Qed.

End Sound.

(* [comment removed for export] *)
Lemma bridge_check_tl IM A Rb Lim BD keep KF F L CS :
  bridge_check IM A Rb Lim BD keep KF F L CS = true -> tl_ok (bd_vt BD) (f_mem F) (bd_tl BD) = true.
Proof.
  unfold bridge_check. intros H.
  do 15 (apply andb_prop in H; destruct H as [H _]).
  apply andb_prop in H. exact (proj2 H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tb_tags_lt (n : int) (TB : list (int * Z * Z)) : bool :=
  forallb (fun b => (fst (fst b) <? n)%uint63) TB.

Lemma tb_ok_ext rho rho' n TB :
  (forall t, to_Z t < to_Z n -> rho' t = rho t) -> tb_tags_lt n TB = true -> tb_ok rho TB -> tb_ok rho' TB.
Proof.
  intros Hag Hlt Hok. unfold tb_ok in *. rewrite Forall_forall in *. unfold tb_tags_lt in Hlt.
  rewrite forallb_forall in Hlt. intros [[t lo] hi'] Hin. specialize (Hok _ Hin). specialize (Hlt _ Hin).
  cbn [fst] in Hlt. apply Uint63.ltb_spec in Hlt. cbn beta iota in *. rewrite (Hag t Hlt). exact Hok.
Qed.

Definition teq_tags_lt (n : int) (TEQ : list teq) : bool :=
  forallb (fun q => (fst (fst q) <? n)%uint63 && forallb (fun kt => (snd kt <? n)%uint63) (snd q)) TEQ.

Lemma teq_sum_ext rho rho' n : (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  forall ts, forallb (fun kt => (snd kt <? n)%uint63) ts = true -> teq_sum rho' ts = teq_sum rho ts.
Proof.
  intros Hag. induction ts as [|[k t] r IH]; intros Hlt; [reflexivity|].
  cbn [forallb snd] in Hlt. apply andb_prop in Hlt as [H1 H2]. apply Uint63.ltb_spec in H1.
  cbn [teq_sum]. rewrite (Hag t H1), (IH H2). reflexivity.
Qed.

Lemma teq_ok_ext rho rho' n TEQ :
  (forall t, to_Z t < to_Z n -> rho' t = rho t) -> teq_tags_lt n TEQ = true -> teq_ok rho TEQ -> teq_ok rho' TEQ.
Proof.
  intros Hag Hlt Hok. unfold teq_ok in *. rewrite Forall_forall in *. unfold teq_tags_lt in Hlt.
  rewrite forallb_forall in Hlt. intros [[t c] ts] Hin. specialize (Hok _ Hin). specialize (Hlt _ Hin).
  cbn [fst snd] in Hlt. apply andb_prop in Hlt as [H1 H2]. apply Uint63.ltb_spec in H1.
  unfold teq_holds in *. rewrite (Hag t H1), (teq_sum_ext rho rho' n Hag ts H2). exact Hok.
Qed.
