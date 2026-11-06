(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxLazy FxCellFrame
  FxDrive FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O FxDrive3W FxDrive3K FxDrive3J.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 BackingAlgebra.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import
  BrEnv BrMem BrLedger BrMain BrRev BrRevLedger BrClass BrRevS BrDress BrGrow BrTrans BrHole Br3Root Br3Ops Br3Leaf Br3Know Br3Eq BrRa.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Export Br3Aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition shp_of (M : itrie region) : list (int * int) :=
  flat_map (fun tr : int * region => match rg_kind (snd tr) with RK_shadow p => [(fst tr, p)] | RK_plain => [] end) (ielements M).
Definition pb_of (M : itrie region) : list (int * (Z * Z * Z)) :=
  map (fun tr : int * region => (fst tr, (to_Z (rg_clo (snd tr)), to_Z (rg_chi (snd tr)), to_Z (rg_len (snd tr))))) (ielements M).

Lemma shp_of_sound rho (M : itrie region) : (forall t rg, iget t M = Some rg -> region_ok rho t rg) ->
  Forall (fun q => bv_unsigned (rho (fst q)) = bv_unsigned (rho (snd q)) / 8 + to_Z shadow_K) (shp_of M).
Proof.
  intros HM. unfold shp_of. apply Forall_forall. intros q Hq. apply in_flat_map in Hq as ([t rg] & Hin & Hq). cbn [fst snd] in Hq.
  destruct (rg_kind rg) as [|p] eqn:Ek; [destruct Hq|]. destruct Hq as [<-|[]]. cbn [fst snd].
  destruct (HM t rg (proj1 (ielements_spec M t rg) Hin)) as (_ & _ & _ & _ & _ & _ & Hk). rewrite Ek in Hk. cbn in Hk. exact (proj2 Hk).
Qed.

Lemma pb_of_sound rho (M : itrie region) : (forall t rg, iget t M = Some rg -> region_ok rho t rg) ->
  Forall (fun q : int * (Z * Z * Z) => let '(clo, chi, bnd) := snd q in
            clo <= bv_unsigned (rho (fst q)) <= chi /\ bv_unsigned (rho (fst q)) + bnd < 2 ^ 63) (pb_of M).
Proof.
  intros HM. unfold pb_of. apply Forall_forall. intros q Hq. apply in_map_iff in Hq as ([t rg] & <- & Hin). cbn [fst snd].
  destruct (HM t rg (proj1 (ielements_spec M t rg) Hin)) as (_ & _ & Hb & _ & _ & Hc & _). split; [exact Hc | exact Hb].
Qed.

Lemma xain_ext rho rho' (XA : list fent) z : (forall e, In e XA -> rho' (fent_tag e) = rho (fent_tag e)) -> xain rho' XA z = xain rho XA z.
Proof.
  intros H. unfold xain. induction XA as [|[[t o] l] r IH]; [reflexivity|]. cbn [existsb].
  pose proof (H (t, o, l) (or_introl eq_refl)) as Ht. cbn [fent_tag fst] in Ht. rewrite Ht. f_equal. apply IH. intros e He. apply H. right. exact He.
Qed.

(* [comment removed for export] *)
Definition sh_page_expr (v : nat) : AX2.expr :=
  AX2.EAlu ALU_ADD (AX2.EMd M_MUL (AX2.ELit 512) (AX2.EVar v)) (AX2.ELit 2147450880).
Definition sh_page_lin (v : nat) : AX2.lin := AX2.lin_of (sh_page_expr v).
Definition xts_of (SHP : list (int * int)) (XTn : list (int * nat)) : list (int * AX2.lin) :=
  flat_map (fun q : int * int =>
     match List.find (fun p : int * nat => (fst p =? snd q)%uint63) XTn with
     | Some p => [(fst q, sh_page_lin (snd p))]
     | None => []
     end) SHP.

Section LeafTabs.
Variable E : AX2.env.
Variable n : int.
Variable rho' : int -> word.
Variable M1 : itrie region.
Variable ops : list vop.
Variable m' : Model.
Variable ALL' : list fent.
Variable VT : vtab.
Hypothesis HM1 : forall t rg, iget t M1 = Some rg -> region_ok rho' t rg.
Hypothesis Hops : Forall (op_ok rho' m' ALL') ops.
Local Notation E1 := (env_of rho' (AX2.ev E) (AX2.eb E) VT).

Definition xtn_chk (XTn : list (int * nat)) : bool :=
  forallb (fun p : int * nat =>
     vdef_is_div (vt_get VT (snd p)) (fst p) 0 4096 0
     && (match iget (fst p) M1 with Some rg => (12 <=? to_Z (rg_align rg)) && (to_Z (rg_align rg) <=? 62) | None => false end
         || existsb (fun o : vop => match fst o with
                                    | OpGrant | OpLazy => (fent_tag (snd o) =? fst p)%uint63
                                    | _ => false
                                    end) ops)) XTn.

Lemma xtn_sound XTn : xtn_chk XTn = true ->
  Forall (fun p => AX2S.eqm (AX2S.lden E1 (snd p)) (bv_unsigned (rho' (fst p)))) (map (fun p => (fst p, page_lin (snd p))) XTn).
Proof.
  unfold xtn_chk. intros Hc. rewrite forallb_forall in Hc. apply Forall_forall. intros q Hq.
  apply in_map_iff in Hq as ([t v] & <- & Hin). cbn [fst snd]. pose proof (Hc _ Hin) as H1. cbn [fst snd] in H1.
  apply andb_prop in H1 as [Hdiv Hal]. unfold vdef_is_div in Hdiv.
  destruct (vt_get VT v) as [[|t' c dd mm|]|] eqn:Ev; try discriminate.
  apply andb_prop in Hdiv as [Hdiv D4]. apply andb_prop in Hdiv as [Hdiv D3]. apply andb_prop in Hdiv as [D1 D2].
  apply Uint63.eqb_spec in D1. apply Z.eqb_eq in D2, D3, D4. subst t' c dd mm.
  assert (Hal4 : bv_unsigned (rho' t) mod 4096 = 0).
  { apply orb_prop in Hal as [Hl|Hd].
    - destruct (iget t M1) as [rg|] eqn:Hg; [|discriminate]. apply andb_prop in Hl as [L1 L2]. apply Z.leb_le in L1, L2.
      destruct (HM1 t rg Hg) as (_ & _ & _ & _ & Hm & _).
      assert (Hd : (2 ^ to_Z (rg_align rg) | bv_unsigned (rho' t))) by (apply Z.mod_divide; [lia | exact Hm]).
      destruct Hd as [c Hc']. rewrite Hc'. replace (to_Z (rg_align rg)) with ((to_Z (rg_align rg) - 12) + 12) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite Z.mul_assoc. apply Z.mod_mul. lia.
    - apply existsb_exists in Hd as (o & Ho & Hk). pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok.
      unfold op_ok in Hok. cbv zeta in Hok.
      destruct (fst o); try discriminate; apply Uint63.eqb_spec in Hk; rewrite Hk in Hok; exact (proj1 Hok). }
  unfold page_lin. pose proof (AX2S.lin_of_sound E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v))) as [q1 Hq1].
  unfold AX2S.uE in Hq1. cbn [AX2.edenot] in Hq1. rewrite ev_env_of, Ev in Hq1. cbn [vden] in Hq1.
  destruct (AX2S.u_mul_eqm (Z_to_bv 64 4096) (Z_to_bv 64 (digit (bv_unsigned (rho' t) + 0) 4096 0))) as [q2 Hq2].
  rewrite Hq2 in Hq1. pose proof (br_u64 (rho' t)) as Hu.
  unfold digit in Hq1. cbn [Z.eqb] in Hq1. rewrite Z.add_0_r in Hq1.
  assert (Hdv : 0 <= bv_unsigned (rho' t) / 4096 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (br_lit_small 4096), (br_lit_small (bv_unsigned (rho' t) / 4096)) in Hq1 by lia.
  exists (q1 + q2). rewrite Hq1. clear - Hal4. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma xtn_xv XTn : xtn_chk XTn = true ->
  Forall (fun p : int * nat => bv_unsigned (AX2.ev E1 (snd p)) = bv_unsigned (rho' (fst p)) / 4096) XTn.
Proof.
  unfold xtn_chk. intros Hc. rewrite forallb_forall in Hc. apply Forall_forall. intros [t v] Hin.
  cbn [fst snd]. pose proof (Hc _ Hin) as H1. cbn [fst snd] in H1.
  apply andb_prop in H1 as [Hdiv _]. unfold vdef_is_div in Hdiv.
  destruct (vt_get VT v) as [[|t' c dd mm|]|] eqn:Ev; try discriminate.
  apply andb_prop in Hdiv as [Hdiv D4]. apply andb_prop in Hdiv as [Hdiv D3]. apply andb_prop in Hdiv as [D1 D2].
  apply Uint63.eqb_spec in D1. apply Z.eqb_eq in D2, D3, D4. subst t' c dd mm.
  rewrite ev_env_of, Ev. cbn [vden]. unfold digit. cbn [Z.eqb]. rewrite Z.add_0_r.
  pose proof (br_u64 (rho' t)) as Hu.
  apply br_lit_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Definition shp_chk (SHP : list (int * int)) : bool :=
  forallb (fun q : int * int =>
     match iget (fst q) M1 with
     | Some rg => match rg_kind rg with RK_shadow p => (p =? snd q)%uint63 | RK_plain => false end
     | None => false
     end
     || ((snd q =? fst q - 1)%uint63
         && existsb (fun o : vop => match fst o with OpShadow => (fent_tag (snd o) =? fst q)%uint63 | _ => false end) ops)) SHP.

Lemma shp_sound SHP : shp_chk SHP = true ->
  Forall (fun q => bv_unsigned (rho' (fst q)) = bv_unsigned (rho' (snd q)) / 8 + to_Z shadow_K) SHP.
Proof.
  unfold shp_chk. intros Hc. rewrite forallb_forall in Hc. apply Forall_forall. intros [ts tp] Hq.
  pose proof (Hc _ Hq) as H1. cbn [fst snd] in *. apply orb_prop in H1 as [Hl|Hd].
  - destruct (iget ts M1) as [rg|] eqn:Hg; [|discriminate].
    destruct (HM1 ts rg Hg) as (_ & _ & _ & _ & _ & _ & Hk).
    destruct (rg_kind rg) as [|p]; [discriminate|]. apply Uint63.eqb_spec in Hl. subst p. exact (proj2 Hk).
  - apply andb_prop in Hd as [Hp Hex]. apply Uint63.eqb_spec in Hp. subst tp.
    apply existsb_exists in Hex as (o & Ho & Hk). pose proof (proj1 (Forall_forall _ _) Hops o Ho) as Hok.
    unfold op_ok in Hok. cbv zeta in Hok. destruct (fst o); try discriminate.
    apply Uint63.eqb_spec in Hk. rewrite Hk in Hok. exact (proj1 (proj2 Hok)).
Qed.

Lemma xts_sound SHP XTn : xtn_chk XTn = true -> shp_chk SHP = true ->
  Forall (fun p => AX2S.eqm (AX2S.lden E1 (snd p)) (bv_unsigned (rho' (fst p)))) (xts_of SHP XTn).
Proof.
  intros Hx Hs. pose proof (shp_sound SHP Hs) as Hsh. pose proof (xtn_xv XTn Hx) as Hxv. pose proof (xtn_sound XTn Hx) as Hxs.
  unfold xts_of. apply Forall_forall. intros q Hq. apply in_flat_map in Hq as ([ts tp] & Hin & Hq). cbn [fst snd] in Hq.
  destruct (List.find (fun p : int * nat => (fst p =? tp)%uint63) XTn) as [[t v]|] eqn:Hf; [|destruct Hq].
  destruct Hq as [<-|[]]. cbn [fst snd]. apply find_some in Hf as [Hv Ht]. cbn [fst] in Ht. apply Uint63.eqb_spec in Ht. subst t.
  pose proof (proj1 (Forall_forall _ _) Hsh _ Hin) as Esh. cbn [fst snd] in Esh.
  pose proof (proj1 (Forall_forall _ _) Hxv _ Hv) as Ev. cbn [fst snd] in Ev.
  pose proof (proj1 (Forall_forall _ _) Hxs _ (in_map (fun p => (fst p, page_lin (snd p))) _ _ Hv)) as Epl. cbn [fst snd] in Epl.
  (* [comment removed for export] *)
  pose proof (br_u64 (rho' tp)) as Hu.
  assert (Hal4 : bv_unsigned (rho' tp) mod 4096 = 0).
  { unfold page_lin in Epl. pose proof (AX2S.lin_of_sound E1 (AX2.EMd M_MUL (AX2.ELit 4096) (AX2.EVar v))) as [q1 Hq1].
    destruct Epl as [q0 Hq0]. unfold AX2S.uE in Hq1. cbn [AX2.edenot] in Hq1.
    destruct (AX2S.u_mul_eqm (Z_to_bv 64 4096) (AX2.ev E1 v)) as [q2 Hq2]. rewrite Hq2, Ev in Hq1.
    rewrite (br_lit_small 4096) in Hq1 by lia.
    assert (Hdv : 0 <= bv_unsigned (rho' tp) / 4096) by (apply Z.div_pos; lia).
    assert (E4 : 4096 * (bv_unsigned (rho' tp) / 4096) = bv_unsigned (rho' tp)).
    { apply br_eqm_small; [exists (q0 - q1 - q2); lia | | exact Hu]. clear - Hu Hdv. Z.div_mod_to_equations. lia. }
    clear - E4. Z.div_mod_to_equations. lia. }
  unfold sh_page_lin, sh_page_expr.
  pose proof (AX2S.lin_of_sound E1 (AX2.EAlu ALU_ADD (AX2.EMd M_MUL (AX2.ELit 512) (AX2.EVar v)) (AX2.ELit 2147450880))) as [q1 Hq1].
  unfold AX2S.uE in Hq1. cbn [AX2.edenot] in Hq1.
  destruct (AX2S.u_add_eqm (mul_div M_MUL (Z_to_bv 64 512) (AX2.ev E1 v)) (Z_to_bv 64 2147450880)) as [q2 Hq2].
  destruct (AX2S.u_mul_eqm (Z_to_bv 64 512) (AX2.ev E1 v)) as [q3 Hq3].
  rewrite Hq2, Hq3, Ev in Hq1. rewrite (br_lit_small 512), (br_lit_small 2147450880) in Hq1 by lia.
  change (to_Z shadow_K) with 2147450880 in Esh.
  exists (q1 + q2 + q3). rewrite Hq1, Esh. clear - Hal4. Z.div_mod_to_equations. lia.
Qed.

End LeafTabs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Leaf3.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

(* [comment removed for export] *)
Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).
Variable classes : list (int * rclass).
Variable CS : CAP.acs.
Variable d : sdesc.
Variable bs : list ditem.
Variable L3 : fledger3.
Variable W : Z.
Variable E : AX2.env.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
(* [comment removed for export] *)
Hypothesis HTT : tt_wf TT = true.
Hypothesis HRn0 : Rn segs IM n (rho_of TT E) (state_of d)
                     (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).
Hypothesis Hdlt : Forall (ditem_lt n) bs.
Hypothesis Hdok : Forall (ditem_ok (rho_of TT E)) bs.
Hypothesis Hroot : root3_chk segs A Lim TT n classes CS d bs L3 W = true.
(* [comment removed for export] *)
Variable XA : list fent.
Hypothesis HcwX : forall x, claimed_wr IM (rho_of TT E) (f_mem (state_of d)) x ->
                    CXS.hid A argH E CS m x = false \/ xain (rho_of TT E) XA (bv_unsigned x) = true.

Local Notation rho := (rho_of TT E).
Local Notation V := (m_vmmaps m).
Local Notation R0 := (segments_reserved segs).
Local Notation F0 := (dress (state_of d) bs).
Local Notation M0 := (f_mem (state_of d)).
Local Notation ms0 := (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).
Local Notation A0 := (map (denA rho) XA ++ CXS.allowA A E CS).
Local Notation D3 := (DInv3 cfg segs IM R0 Lim [] FULL (fun _ _ => True) [] bvmap_empty (Z_to_bv 32 0) (PropExec.seg_rom segs)
                            (fun x => argH E x = true) (Z_to_bv 64 W) (vm_noaccess V) (m_vm_lazy m) (vm_brk V) A0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable ra : ra_t.
Hypothesis Era : ra = AX2.ranges_apart (CAP.kn CS).
Variable n' : int.
Variable rho' : int -> word.
Variable F' : fstate.
Variable L' : fledger3.
Variable ms' : machine_state.
Variable m' : Model.
Hypothesis HD' : D3 n' rho' F' L' ms' m'.
Hypothesis Hext : pext IM n rho F0 L3 ms0 m n' rho' F' L' ms' m'.
Variable END : CAP.acs.
Variable ax : LeafAux.

Local Notation VT := (la_vt ax).
Local Notation M1 := (f_mem F').
Local Notation E1 := (env_of rho' (AX2.ev E) (AX2.eb E) VT).
Local Notation V' := (m_vmmaps m').
Local Notation nfresh := (length (fl_all L') - length (fl_all L3))%nat.
Local Notation fresh := (firstn nfresh (fl_all L')).
Local Notation XT1 := (xt_of TT ++ map (fun p => (fst p, page_lin (snd p))) (la_xtn ax) ++ xts_of (la_shp ax) (la_xtn ax)).

Definition fents_eqb (x y : list fent) : bool := CAP.list_eqb fent_eqb x y.
Lemma fents_eqb_eq : forall x y, fents_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] Hc; cbn in Hc; try discriminate; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. rewrite (fent_eqb_eq _ _ H1), (IH y H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition commits : list vop := List.filter is_commit (fl_ops L').

Definition creg_okZ (M : itrie region) (t : int) (o nn : Z) : bool :=
  match iget t M with
  | Some rg => (to_Z (rg_lo rg) <=? o) && (o + nn <=? to_Z (rg_len rg))
  | None => false
  end.
Definition creg_ok (M : itrie region) (c : fent) : bool := let '(t, off, len) := c in creg_okZ M t (to_Z off) (to_Z len).

Definition commit_regs_chkx (Mr Md : itrie region) : bool :=
  forallb (fun o : vop => (to_Z (fent_tag (snd o)) <? to_Z n) && creg_ok Mr (snd o) && creg_ok Md (snd o)
                          && match cls classes (fent_tag (snd o)) with Some c => class_neq c RCSpan | None => false end) commits.
Definition commit_regs_chk : bool := commit_regs_chkx M0 (f_mem F0).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition leaf3a_chk : bool :=
  CAP.fresh_ok nx0 CS
  && forallb (fun p => Nat.leb (CAP.nxt CS) (fst p)) VT
  && forallb (fun p => CAP.expr_vars_lt (CAP.nxt CS) (snd p)) TT
  && forallb (fun p => to_Z (fst p) <? to_Z n) TT
  && fents_eqb (skipn nfresh (fl_all L')) (fl_all L3)
  && ops3_chk n (fl_ops L')
  && xtn_chk M1 (fl_ops L') VT (la_xtn ax)
  && shp_chk M1 (fl_ops L') (la_shp ax)
  && model3_chk segs A Lim CS n (fl_all L') (fl_ops L') (fl_S (fl3 L')) (fl_E L') fresh END XT1 (fl_lazy L') (fl_ord L') (fl_allow L')
                (la_shp ax ++ shp_of M1) XA (pb_of M1) M1 (fl_ex L') TT
  && commit3_chk n (fl_all L') (fl_ops L') END (fl_ord L')
  && commit_regs_chk
  && forallb (fun e => to_Z (fent_tag e) <? to_Z n) XA.

(* [comment removed for export] *)
Definition in_fresh (t : int) (o nn : Z) : bool :=
  (0 <=? o) && (0 <=? nn)
  && existsb (fun e : fent => let '(t', off, len) := e in (t' =? t)%uint63 && (off =? 0)%uint63 && (o + nn <=? to_Z len)) fresh.

(* [comment removed for export] *)
Definition in_commit (t : int) (o nn : Z) : bool :=
  (0 <=? nn)
  && existsb (fun c : vop => let '(t', off, len) := snd c in (t' =? t)%uint63 && (to_Z off <=? o) && (o + nn <=? to_Z off + to_Z len)) commits.

(* [comment removed for export] *)
Definition in_xa (t : int) (o nn : Z) : bool :=
  (0 <=? nn)
  && existsb (fun e : fent => let '(t', off, len) := e in (t' =? t)%uint63 && (to_Z off <=? o) && (o + nn <=? to_Z off + to_Z len)) XA.

(* [comment removed for export] *)
Definition in_fresh_sh (t : int) (o nn : Z) : bool :=
  (0 <=? o) && (0 <=? nn)
  && existsb (fun q : int * int =>
       (fst q =? t)%uint63
       && existsb (fun e : fent => let '(t', off, len) := e in (t' =? snd q)%uint63 && (off =? 0)%uint63 && (8 * (o + nn) <=? to_Z len)) fresh)
       (la_shp ax).

Definition visb3 (cov : list (int * Z * Z)) (t : int) (o nn : Z) : bool :=
  if (to_Z t <? to_Z n) then (if vis_pre cov t o nn then true else if in_commit t o nn then true else in_xa t o nn)
  else (if in_fresh t o nn then true else in_fresh_sh t o nn).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cmf3_viewx (XTv : list (int * AX2.lin)) (Mr : itrie region) (a : AX2.saddr) (nn : Z) : bool :=
  match aview [] Mr [] XTv a with
  | Some (tf, o) =>
      (0 <=? nn) && creg_okZ Mr tf o nn && (0 <=? o) && (o + nn <? 2 ^ 62) && (to_Z tf <? to_Z n)
      && forallb (fun c : vop => let '(t, off, len) := snd c in
                    if (tf =? t)%uint63 then (o + nn <=? to_Z off) || (to_Z off + to_Z len <=? o) else true) commits
  | None => false
  end.

(* [comment removed for export] *)
Definition commit_tags : list int :=
  fold_right (fun (c : vop) acc => let t := fent_tag (snd c) in if existsb (fun t' => (t' =? t)%uint63) acc then acc else t :: acc) [] commits.

Lemma commit_tags_in c : In c commits -> In (fent_tag (snd c)) commit_tags.
Proof.
  unfold commit_tags. induction commits as [|c0 r IH]; intros Hin; [destruct Hin|].
  cbn [fold_right]. set (acc := fold_right _ [] r) in *. cbv zeta.
  destruct (existsb (fun t' => (t' =? fent_tag (snd c0))%uint63) acc) eqn:Eex.
  - destruct Hin as [<-|Hin]; [|exact (IH Hin)].
    apply existsb_exists in Eex as (t' & Ht' & Eq). apply Uint63.eqb_spec in Eq. subst t'. exact Ht'.
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH Hin)].
Qed.

Definition cmf3_apartx (Mr : itrie region) (a : AX2.saddr) (nn : Z) : bool :=
  (0 <=? nn)
  && match AX2.base_range (CAP.kn CS) (AX2.a_base a) with
     | Some (blo, bhi) => (0 <=? blo + AX2.a_off a) && (bhi + AX2.a_off a + nn <? 2 ^ 64)      (* [comment removed for export] *)
     | None => false
     end
  && forallb (fun t : int =>
       match iget t Mr with
       | Some rg => (0 <=? to_Z (rg_lo rg)) && (to_Z (rg_lo rg) <=? to_Z (rg_len rg))
                    && ra (AX2.a_base a) (AX2.a_off a) nn (tte TT t) (to_Z (rg_lo rg))
                                        (to_Z (rg_len rg) - to_Z (rg_lo rg))
       | None => false
       end) commit_tags.

Definition cmf3_view : AX2.saddr -> Z -> bool := cmf3_viewx (xt_of TT) M0.
Definition cmf3_apart : AX2.saddr -> Z -> bool := cmf3_apartx M0.

Definition cmf3x (XTv : list (int * AX2.lin)) (Mr : itrie region) (a : AX2.saddr) (nn : Z) : bool :=
  match commits with
  | [] => true
  | _ => if cmf3_viewx XTv Mr a nn then true else cmf3_apartx Mr a nn       (* [comment removed for export] *)
  end.
Definition cmf3 : AX2.saddr -> Z -> bool := cmf3x (xt_of TT) M0.

(* [comment removed for export] *)
Definition cnosegx (Md : itrie region) (t : int) (o nn : Z) : bool :=
  match iget t Md, cls classes t with
  | Some rg, Some c => (to_Z (rg_lo rg) <=? o) && (0 <=? nn) && (o + nn <=? to_Z (rg_len rg)) && class_neq c RCHull
  | _, _ => false
  end.
Definition cnoseg : int -> Z -> Z -> bool := cnosegx (f_mem F0).

(* [comment removed for export] *)
Definition ovb3x (Md : itrie region) (t : int) (o nn : Z) : bool :=
  if (to_Z t <? to_Z n) then (if cnosegx Md t o nn then true else noseg_chk A TT (CAP.kn CS) ra t o nn)
  else (if in_fresh t o nn then true else in_fresh_sh t o nn).
Definition ovb3 : int -> Z -> Z -> bool := ovb3x (f_mem F0).

(* [comment removed for export] *)
Definition pre_old : list Z :=
  (* [comment removed for export] *)
  map (old0_chk IM A TT (CAP.kn CS) d ra (CAP.kset_mem (CAP.kset_of (CAP.kn CS))) (xt_of TT) M0 (span_nclbR CS TT classes (f_mem F0) ra)) (CAP.kn END).

Definition leaf3b_chk (pre : list Z) : bool :=
  let XTv := xt_of TT in
  let Mr := M0 in
  let Md := f_mem F0 in
  let cov := root_cov (CAP.kn CS) Mr XTv in
  let nc := span_nclbR CS TT classes Md ra in
  (AX2.s_pc (CAP.a_ss END) =? to_Z (f_pc F'))
  && match f_resv F' with None => true | Some _ => false end
  && forallb (fun i => val_match VT [] XT1 [] (nth i (AX2.s_regs (CAP.a_ss END)) (AX2.ELit 0)) (FxState.rget F' (of_Z (Z.of_nat i)))) (seq 1 31)
  && cells_small_fast M1
  && forallb (know3_entry_chk2 IM A (CAP.kn CS) M1 VT (CAP.kset_mem (CAP.kset_of (CAP.kn CS))) XTv Mr n XT1 (cmf3x XTv Mr) (visb3 cov) (ovb3x Md)
                               (pure3_chk A CS (fl_all L') (fl_ops L') XT1 (la_xtn ax))) (combine (CAP.kn END) pre)
  && forallb (kvars_chk IM A TT (CAP.kn CS) d M1 (CAP.nxt CS) ra (CAP.kset_mem (CAP.kset_of (CAP.kn CS))) XTv Mr n (cmf3x XTv Mr) nc) (CAP.kn END)
  && match AX2.s_log (CAP.a_ss END) with [] => true | _ => false end.

Lemma leaf3a_parts : leaf3a_chk = true ->
  CAP.fresh_ok nx0 CS = true /\ forallb (fun p => Nat.leb (CAP.nxt CS) (fst p)) VT = true
  /\ forallb (fun p => CAP.expr_vars_lt (CAP.nxt CS) (snd p)) TT = true
  /\ forallb (fun p => to_Z (fst p) <? to_Z n) TT = true
  /\ skipn nfresh (fl_all L') = fl_all L3
  /\ ops3_chk n (fl_ops L') = true /\ xtn_chk M1 (fl_ops L') VT (la_xtn ax) = true /\ shp_chk M1 (fl_ops L') (la_shp ax) = true
  /\ model3_chk segs A Lim CS n (fl_all L') (fl_ops L') (fl_S (fl3 L')) (fl_E L') fresh END XT1 (fl_lazy L') (fl_ord L') (fl_allow L')
                (la_shp ax ++ shp_of M1) XA (pb_of M1) M1 (fl_ex L') TT = true
  /\ commit3_chk n (fl_all L') (fl_ops L') END (fl_ord L') = true /\ commit_regs_chk = true
  /\ forallb (fun e => to_Z (fent_tag e) <? to_Z n) XA = true.
Proof.
  unfold leaf3a_chk. intros Hc.
  apply andb_prop in Hc as [Hc H12]. apply andb_prop in Hc as [Hc H11]. apply andb_prop in Hc as [Hc H10].
  apply andb_prop in Hc as [Hc H9]. apply andb_prop in Hc as [Hc H8]. apply andb_prop in Hc as [Hc H7].
  apply andb_prop in Hc as [Hc H6]. apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4].
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2]. apply fents_eqb_eq in H5. tauto.
Qed.

Lemma leaf3_agree : forallb (fun p => Nat.leb (CAP.nxt CS) (fst p)) VT = true -> AxSymRun3.env_agree (CAP.nxt CS) E E1.
Proof. intros HVT. split; [|reflexivity]. intros x Hx. rewrite ev_env_of, (vt_get_new VT _ HVT x Hx). reflexivity. Qed.

Theorem leaf3_cs_ok :
  leaf3a_chk = true -> leaf3b_chk pre_old = true ->
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END (ms_regs ms') (ms_mem ms') m'
  /\ ms' = PropExec.mkst (ms_regs ms') (Z_to_bv 64 (AX2.s_pc (CAP.a_ss END))) (ms_mem ms') (PropExec.seg_rom segs)
  /\ m_fs m' = m_fs m /\ AxSymRun3.env_agree (CAP.nxt CS) E E1.
Proof.
  intros Hchk Hchkb.
  destruct (leaf3a_parts Hchk) as (Hfresh & HVT & HTv & HTn & Hskip & Hopc & Hxtn & Hshp & Hmodel & Hcommit & Hcregs & HXAt).
  destruct (root3_parts segs A Lim TT n classes CS d bs L3 W Hroot) as (Hnf & Hres & Hmaps3 & Htags0 & Eops0 & Eallow0 & Hshz & Hregs3).
  pose proof (shz_zones A CS TT _ L3 Hshz) as Hzones.
  (* [comment removed for export] *)
  pose proof (leaf3_agree HVT) as Hag.
  pose proof Hfresh as Hfresh0. unfold CAP.fresh_ok in Hfresh. cbv zeta in Hfresh.
  apply andb_prop in Hfresh as [Hf Hle]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _].
  apply andb_prop in Hf as [Hf Fgh]. apply andb_prop in Hf as [Hf Fvis]. apply Nat.leb_le in Hle.
  assert (Fallow : CAP.pairs_vars_lt (CAP.nxt CS) (CAP.a_vis CS ++ CAP.a_ghost CS) = true)
    by (unfold CAP.pairs_vars_lt in *; rewrite forallb_app, Fvis, Fgh; reflexivity).
  pose proof (CXS.cs_ok_agree segs A nx0 Lim NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E E1 CS R FULL m Hag Hfresh0 HCS) as HCS1.
  (* [comment removed for export] *)
  assert (Hlxs : CxOpt.ledger_exact E (CAP.a_maps CS) /\ CxOpt.ledger_exact E1 (CAP.a_maps CS)).
  { pose proof Hroot as Hc. unfold root3_chk in Hc. do 7 (apply andb_prop in Hc as [Hc _]). apply andb_prop in Hc as [Hnf0 Hled0].
    split; [exact (led_lx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCS Hnf0 Hled0) | exact (led_lx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCS1 Hnf0 Hled0)]. }
  destruct Hlxs as [Hlx Hlx1].
  pose proof (CXS.hid_agree A nx0 argH argH_agree (CAP.nxt CS) E E1 CS m Hag Hle Fallow) as Ehid.
  pose proof (CXS.allowA_agree A (CAP.nxt CS) E E1 CS Hag Fallow) as EA.
  (* [comment removed for export] *)
  pose proof (rb3_maps segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT L3 Hmaps3) as Hmaps0.
  assert (HR0 : FxRel.R segs IM rho (state_of d) ms0) by (apply HRn0; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0) as Hmem0. cbn [ms_mem PropExec.mkst] in Hmem0.
  (* [comment removed for export] *)
  destruct HD' as (HDI & Hlp & Hsp & Hx).
  destruct HDI as (HRn' & Hr0' & Hhalt' & _ & Hli & _ & _ & _ & _ & _ & _).
  rewrite erase_halted in Hhalt'. rewrite erase_vmmaps in Hli.
  destruct Hli as [li1 _ li3 li4 li5 li6 li7 li8 li9 li10 li11 _ _ _ _ _].
  cbn [erase_vm vm_reserved vm_maps vm_init_sp] in li1, li3, li4, li5, li6, li7, li8, li9, li10, li11.
  assert (Eat : alloc_top (erase_vm (Z_to_bv 64 W) V') = alloc_top V') by reflexivity. rewrite Eat in li7.
  destruct Hlp as [lp_pi _ lp_pw lp_mat _ _ lp_lim lp_maps lp_na lp_lz _ _ _ lp_E _ lp_wfna lp_wflz lp_opsR lp_ord lp_opsF].
  destruct Hsp as [HShZ _ Hspok Hexcov]. destruct Hx as (Hfr0 & Hfc0 & Hrom0 & Hhi & Hbrk).
  destruct Hext as [(Hnn & Hrho & Hsame & Hisp & Hsbrk & _) Hmfr].
  destruct Hmfr as (new & Enew & _ & HfrA & _ & _). rewrite Eops0 in Enew. cbn [app] in Enew. subst new.
  assert (HR1 : FxRel.R segs IM rho' F' ms') by (apply HRn'; split; [exact Hr0' | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR1) as Hmem1.
  assert (HM1 : forall t rg, iget t M1 = Some rg -> region_ok rho' t rg) by (intros t rg Hg; exact (proj1 (proj1 Hmem1 t rg Hg))).
  assert (HALL : fl_all L' = fresh ++ fl_all L3) by (rewrite <- Hskip at 2; symmetry; apply firstn_skipn).
  (* [comment removed for export] *)
  assert (HXT : Forall (fun p => AX2S.eqm (AX2S.lden E1 (snd p)) (bv_unsigned (rho' (fst p)))) XT1).
  { apply Forall_app. split;
      [|apply Forall_app; split; [exact (xtn_sound E rho' M1 (fl_ops L') m' (fl_all L') VT HM1 lp_opsF _ Hxtn)
                                 | exact (xts_sound E rho' M1 (fl_ops L') m' (fl_all L') VT HM1 lp_opsF _ _ Hxtn Hshp)]].
    unfold xt_of. apply Forall_forall. intros q Hq. apply in_map_iff in Hq as ([t e] & <- & Hin). cbn [fst snd].
    destruct (tt_get_In TT t e HTT Hin) as [Hg Hne].
    rewrite forallb_forall in HTv, HTn. pose proof (HTv (t, e) Hin) as Hve. pose proof (HTn (t, e) Hin) as Htn.
    cbn [fst snd] in Hve, Htn. apply Z.ltb_lt in Htn. rewrite (Hrho t Htn).
    assert (Er : rho t = AX2.edenot E1 e).
    { unfold rho_of. destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; contradiction|].
      rewrite Hg. exact (CXS.edenot_agree' (CAP.nxt CS) E E1 e Hag Hve). }
    rewrite Er. apply AX2S.lin_of_sound. }
  assert (Hrho_tt : forall t, rho t = AX2.edenot E1 (tte TT t)).
  { intros t. rewrite (rho_tte E TT t). apply (CXS.edenot_agree' (CAP.nxt CS) E E1 _ Hag).
    unfold tte. destruct (t =? 0)%uint63; [reflexivity|]. destruct (tt_get TT t) as [e|] eqn:Hg; [|reflexivity].
    rewrite forallb_forall in HTv. apply (HTv (t, e)). clear - Hg. induction TT as [|[t' e'] r IH]; [discriminate|].
    cbn [tt_get] in Hg. destruct (t' =? t)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; injection Hg as <-; subst t'; left; reflexivity | right; exact (IH Hg)]. }
  (* [comment removed for export] *)
  pose proof (CXS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH ISP argH_high E CS m) as Hnoseg.
  pose proof (fun a => rb_hull A argH ISP HULL_ok argH_high CS E m a) as Hhull.
  assert (HXArho : forall e, In e XA -> rho' (fent_tag e) = rho (fent_tag e)).
  { intros e He. rewrite forallb_forall in HXAt. pose proof (HXAt e He) as Ht. apply Z.ltb_lt in Ht. exact (Hrho _ Ht). }
  assert (Hcw : forall x, claimed_wr IM rho (f_mem F0) x -> CXS.hid A argH E1 CS m x = false \/ xain rho' XA (bv_unsigned x) = true).
  { intros x Hx. rewrite Ehid, (xain_ext rho rho' XA _ HXArho).
    apply HcwX. exact (claimed_wr_same IM rho _ _ x (dress_same bs M0) Hx). }
  assert (Hhi' : forall x : word, argH E1 x = true -> ms_mem ms' x = FULL x).
  { intros x Hx. rewrite <- (argH_agree E E1 x (CXS.env_agree_le nx0 (CAP.nxt CS) E E1 Hag Hle)) in Hx.
    exact (proj2 (proj2 (Hhi x Hx))). }
  assert (Hpi' : LazyCfg.page_inv (map (denA rho') (fl_allow L') ++ map (denA rho') XA ++ CXS.allowA A E1 CS) m').
  { rewrite EA. replace (map (denA rho') XA) with (map (denA rho) XA); [exact lp_pi|].
    apply map_ext_in. intros [[t o] l] He. unfold denA. pose proof (HXArho _ He) as Ht. cbn [fent_tag fst] in Ht. rewrite Ht. reflexivity. }
  (* [comment removed for export] *)
  unfold leaf3b_chk in Hchkb. cbv zeta in Hchkb.
  apply andb_prop in Hchkb as [Hb Hlogb]. apply andb_prop in Hb as [Hb Hkv]. apply andb_prop in Hb as [Hb Hkn'].
  apply andb_prop in Hb as [Hb Hsmall]. apply cells_small_fast_ok in Hsmall. apply andb_prop in Hb as [Hb Hregs']. apply andb_prop in Hb as [Hpc Hresv].
  apply Z.eqb_eq in Hpc.
  assert (Hlog : AX2.s_log (CAP.a_ss END) = []) by (destruct (AX2.s_log (CAP.a_ss END)); [reflexivity | discriminate]).
  pose proof Hmodel as Hz0. unfold model3_chk in Hz0. apply andb_prop in Hz0 as [Hal0 Hz0]. apply andb_prop in Hal0 as [_ Hal0].
  assert (HXAc : forallb (xa_ent_chk END XT1 (la_shp ax ++ shp_of M1) (pb_of M1)) XA = true).
  { unfold allow3_chk in Hal0. apply andb_prop in Hal0 as [Hal0 _]. apply andb_prop in Hal0 as [_ Hxa]. exact Hxa. }
  unfold zero3_chk in Hz0.
  apply andb_prop in Hz0 as [Hz0 Hcal].
  apply andb_prop in Hz0 as [Hz0 _]. apply andb_prop in Hz0 as [Hz0 _]. apply andb_prop in Hz0 as [Hz0 Hfv].
  apply andb_prop in Hz0 as [Hz0 _]. apply andb_prop in Hz0 as [Hz0 _]. apply andb_prop in Hz0 as [Hak Hav].
  assert (Hfacts' : vm_reserved V' = R0
            /\ sp_window_lo <= bv_unsigned (vm_init_sp V') <= sp_window_hi
            /\ Forall (fun p => 0 < e_sz p) (vm_maps V')
            /\ Forall (fun p => e_lo p mod page_size = 0 /\ e_sz p mod page_size = 0) (vm_maps V')
            /\ Forall (fun p => 0 < e_lo p /\ e_hi p <= alloc_top V') (vm_maps V')
            /\ Forall (fun p => Forall (e_disj p) R0) (vm_maps V')
            /\ pw_disj (vm_maps V') /\ Z.of_nat (length (vm_maps V')) <= fl_c (fl3 L') /\ live_bytes (vm_maps V') <= fl_S (fl3 L'))
    by (repeat split; assumption).
  set (H := CXS.hid A argH E CS m). set (H' := CXS.hid A argH E1 END m').
  assert (Hsub : forall a, H' a = true -> H a = true).
  { intros a Ha. unfold H. rewrite <- Ehid.
    exact (leaf_hid_mono segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 n rho (fl_all L3) Hmaps0 Htags0 rho' m' (fl_all L') (fl_ops L')
             Hrho lp_maps lp_na lp_lz Hisp lp_opsF Hopc fresh HALL END Hak a Ha). }
  assert (Hord1 : Forall (fun o : int * int * Z => bv_unsigned (rho' (fst (fst o))) + snd o <= bv_unsigned (rho' (snd (fst o)))) (fl_ord L')).
  { eapply Forall_impl; [|exact lp_ord]. intros o (_ & _ & Ho). exact Ho. }
  set (CMp := fun x : word => touched rho' commits (bv_unsigned x)).
  assert (Htsplit : forall z, touched rho' (fl_ops L') z ->
            touched rho' (List.filter (fun o => negb (is_commit o)) (fl_ops L')) z \/ touched rho' commits z).
  { intros z (o & Ho & Hz). destruct (is_commit o) eqn:Ecm.
    - right. exists o. split; [apply filter_In; split; [exact Ho | exact Ecm] | exact Hz].
    - left. exists o. split; [apply filter_In; split; [exact Ho | rewrite Ecm; reflexivity] | exact Hz]. }
  assert (Hunt : forall x : word, H x = false -> ~ touched rho' (List.filter (fun o => negb (is_commit o)) (fl_ops L')) (bv_unsigned x)).
  { intros x Hx. unfold H in Hx. rewrite <- Ehid in Hx. unfold CXS.hid in Hx. apply orb_false_iff in Hx as [_ Hv]. apply negb_false_iff in Hv.
    exact (leaf_untouched segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 Hlx1 Hres n rho (fl_all L3) Hmaps0 Htags0 rho' m' (fl_all L') (fl_ops L')
             (fl_c (fl3 L')) (fl_S (fl3 L')) Hrho lp_maps Hfacts' Hisp lp_opsF lp_opsR Hopc fresh HALL Hav x Hv). }   (* [comment removed for export] *)
  assert (Hfrv : forall e, In e fresh -> forall x : word, e_lo (den rho' e) <= bv_unsigned x < e_hi (den rho' e) -> H' x = false).
  { intros e He x Hx.
    exact (leaf_fresh_visible segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 n rho (fl_all L3) Hmaps0 Htags0 rho' m' (fl_all L') (fl_ops L')
             (fl_c (fl3 L')) (fl_S (fl3 L')) Hrho lp_maps lp_na Hfacts' Hisp fresh HALL END XT1 Hr0' HXT argH_high Hfv e He x Hx). }
  assert (HM0 : forall t rg, iget t M0 = Some rg -> region_ok rho t rg) by (intros t rg Hg; exact (proj1 (proj1 Hmem0 t rg Hg))).
  (* [comment removed for export] *)
  assert (Hcin : forall c, In c commits -> In c (fl_ops L') /\ is_commit c = true) by (intros c Hc; apply filter_In in Hc; exact Hc).
  assert (Hcden : forall c t off len, In c commits -> snd c = (t, off, len) ->
            to_Z t < to_Z n /\ rho' t = rho t
            /\ e_lo (den rho' (snd c)) = bv_unsigned (rho t) + to_Z off
            /\ e_hi (den rho' (snd c)) = bv_unsigned (rho t) + to_Z off + to_Z len
            /\ exists rg, iget t M0 = Some rg /\ to_Z (rg_lo rg) <= to_Z off /\ to_Z off + to_Z len <= to_Z (rg_len rg)).
  { intros c t off len Hc Esc. unfold commit_regs_chk, commit_regs_chkx in Hcregs. rewrite forallb_forall in Hcregs. pose proof (Hcregs c Hc) as H1.
    rewrite Esc in H1. cbn [fent_tag fst snd] in H1.
    apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [Ht Hcr]. apply Z.ltb_lt in Ht.
    unfold creg_ok, creg_okZ in Hcr. destruct (iget t M0) as [rg|] eqn:Hg; [|discriminate].
    apply andb_prop in Hcr as [C1 C2]. apply Z.leb_le in C1, C2.
    destruct (HM0 t rg Hg) as (_ & _ & Hb63 & _). pose proof (br_u64 (rho t)) as Hu.
    pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen. pose proof (i63_range (rg_lo rg)) as Hl0.
    split; [exact Ht|]. split; [exact (Hrho t Ht)|].
    assert (Elo : e_lo (den rho' (t, off, len)) = bv_unsigned (rho t) + to_Z off).
    { unfold e_lo. cbn [den fst]. rewrite (adr_unsigned rho' t (to_Z off)) by (rewrite ?(Hrho t Ht); lia). rewrite (Hrho t Ht). reflexivity. }
    rewrite Esc. split; [exact Elo|]. split; [unfold e_hi; rewrite Elo, e_sz_den; reflexivity|].
    exists rg. split; [reflexivity|]. split; [exact C1 | exact C2]. }
  assert (Hcmf3 : forall a0 nn nn', cmf3 a0 nn = true -> nn' <= nn ->
            forall x, AX2S.estart E a0 <= x < AX2S.estart E a0 + nn' -> ~ CMp (Z_to_bv 64 x)).
  { intros a0 nn nn' Hc Hle0 x Hx (c & Hcc & Hz). unfold cmf3, cmf3x in Hc. fold cmf3_view cmf3_apart in Hc.
    destruct commits as [|c0 cs] eqn:Ecs; [destruct Hcc|]. rewrite <- Ecs in *.
    destruct (cmf3_view a0 nn) eqn:Hview.
    2:{ (* [comment removed for export] *)
      unfold cmf3_apart, cmf3_apartx in Hc. apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [Hnn0 Hbr]. apply Z.leb_le in Hnn0.
      destruct (AX2.base_range (CAP.kn CS) (AX2.a_base a0)) as [[blo bhi]|] eqn:Ebr; [|discriminate].
      apply andb_prop in Hbr as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
      destruct (AX2S.base_range_sound segs E _ (CAP.kn CS) _ blo bhi (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Ebr) as [Hb1 Hb2].
      rewrite forallb_forall in Hall. pose proof (Hall _ (commit_tags_in c Hcc)) as Hcr.
      destruct (snd c) as [[t off] len] eqn:Esc. cbn [fent_tag fst] in Hcr.
      destruct (Hcden c t off len Hcc Esc) as (Ht & _ & Elo & Ehi & rg & Hg & G1 & G2). rewrite Esc in Elo, Ehi.
      rewrite Hg in Hcr. apply andb_prop in Hcr as [Hcr Hra]. rewrite Era in Hra. apply andb_prop in Hcr as [R1 R2]. apply Z.leb_le in R1, R2.
      pose proof (AX2S.ranges_apart_sound segs E _ (CAP.kn CS) _ _ _ _ _ _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hra) as D1.
      unfold AX2S.estart in D1, Hx. cbn [AX2.a_base AX2.a_off] in D1. rewrite <- (rho_tte E TT t) in D1.
      assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply br_lit_small; lia).
      unfold CMp, touched in Hz. rewrite Ux, Elo, Ehi in Hz. lia. }
    clear Hc. rename Hview into Hc. unfold cmf3_view, cmf3_viewx in Hc.
    destruct (aview [] M0 [] (xt_of TT) a0) as [[tf o]|] eqn:Haview; [|discriminate].
    apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [Hc Htf]. apply andb_prop in Hc as [Hc H62].
    apply andb_prop in Hc as [Hc Ho0]. apply andb_prop in Hc as [Hnn0 Hcr].
    apply Z.leb_le in Hnn0, Ho0. apply Z.ltb_lt in H62, Htf.
    unfold creg_okZ in Hcr. destruct (iget tf M0) as [rgf|] eqn:Hgf; [|discriminate].
    apply andb_prop in Hcr as [F1 F2]. apply Z.leb_le in F1, F2.
    pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M0 [] (xt_of TT) HM0 (rho_of_0 TT E) eq_refl (xt_of_ok TT E HTT) a0 tf o Haview) as Hs.
    rewrite env_eta in Hs.
    destruct (HM0 tf rgf Hgf) as (_ & _ & Hb63f & _). pose proof (br_u64 (rho tf)) as Huf.
    assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply br_lit_small; lia).
    rewrite Ux in Hz.
    destruct (snd c) as [[t off] len] eqn:Esc.
    destruct (Hcden c t off len Hcc Esc) as (Ht & _ & Elo & Ehi & rg & Hg & G1 & G2). rewrite Esc in Elo, Ehi. rewrite Elo, Ehi in Hz.
    rewrite forallb_forall in Hall. pose proof (Hall c Hcc) as Hcc1. rewrite Esc in Hcc1.
    destruct (tf =? t)%uint63 eqn:Et.
    - apply Uint63.eqb_spec in Et. subst tf. apply orb_prop in Hcc1 as [Q|Q]; apply Z.leb_le in Q; lia.
    - assert (Hne : tf <> t) by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
      pose proof (proj2 Hmem0 tf t rgf rg Hne Hgf Hg) as Hsep. lia. }
  assert (HshK : CAP.shadow_off A = to_Z shadow_K).
  { pose proof Hav as Hav'. unfold avis3_chk in Hav'. apply andb_prop in Hav' as [_ HK]. apply Z.eqb_eq in HK. exact HK. }
  assert (HSHP : Forall (fun q => bv_unsigned (rho' (fst q)) = bv_unsigned (rho' (snd q)) / 8 + to_Z shadow_K) (la_shp ax ++ shp_of M1)).
  { apply Forall_app. split; [exact (shp_sound rho' M1 (fl_ops L') m' (fl_all L') HM1 lp_opsF _ Hshp) | exact (shp_of_sound rho' M1 HM1)]. }
  (* [comment removed for export] *)
  assert (Hinfr : forall t o nn, in_fresh t o nn = true -> forall j, 0 <= j < nn ->
             exists e, In e fresh /\ e_lo (den rho' e) <= bv_unsigned (adr rho' t (o + j)) < e_hi (den rho' e)).
  { intros t o nn Hc j Hj. unfold in_fresh in Hc. apply andb_prop in Hc as [Hc Hex]. apply andb_prop in Hc as [Ho Hn0].
    apply Z.leb_le in Ho, Hn0. apply existsb_exists in Hex as ([[t' off] len] & He & Hec).
    apply andb_prop in Hec as [Hec Hl]. apply andb_prop in Hec as [Ht Hoff]. apply Uint63.eqb_spec in Ht, Hoff. subst t' off.
    apply Z.leb_le in Hl. exists (t, 0%uint63, len). split; [exact He|].
    destruct (den0 rho' t len) as [Dlo Dhi]. rewrite Dlo, Dhi.
    assert (Hin' : In (den rho' (t, 0%uint63, len)) (vm_maps V')).
    { rewrite lp_maps, HALL. apply in_map. apply in_or_app. left. exact He. }
    pose proof (proj1 (Forall_forall _ _) li7 _ Hin') as [_ Hhi7]. rewrite Dhi in Hhi7.
    pose proof (alloc_top_lt V') as Hat. unfold two_pow_64 in Hat.
    rewrite (adr_unsigned rho' t (o + j)) by lia. lia. }
  (* [comment removed for export] *)
  assert (Hinfsh : forall t o nn, in_fresh_sh t o nn = true -> forall j, 0 <= j < nn ->
             exists tp len, In (tp, 0%uint63, len) fresh /\ In (t, tp) (la_shp ax) /\ 8 * (o + j) + 8 <= to_Z len
                            /\ bv_unsigned (adr rho' t (o + j)) = bv_unsigned (rho' t) + (o + j)
                            /\ CAP.img_hi A <= bv_unsigned (adr rho' t (o + j))).
  { intros t o nn Hc j Hj. unfold in_fresh_sh in Hc. apply andb_prop in Hc as [Hc Hex]. apply andb_prop in Hc as [Ho Hn0].
    apply Z.leb_le in Ho, Hn0. apply existsb_exists in Hex as ([ts tp] & Hq & Hqc). cbn [fst snd] in Hqc.
    apply andb_prop in Hqc as [Hts Hex2]. apply Uint63.eqb_spec in Hts. subst ts.
    apply existsb_exists in Hex2 as ([[t' off] len] & He & Hec). apply andb_prop in Hec as [Hec Hl]. apply andb_prop in Hec as [Ht' Hoff].
    apply Uint63.eqb_spec in Ht', Hoff. subst t' off. apply Z.leb_le in Hl.
    pose proof (proj1 (Forall_forall _ _) HSHP (t, tp) (in_or_app _ _ _ (or_introl Hq))) as Esh. cbn [fst snd] in Esh.
    pose proof (br_u64 (rho' tp)) as Hup. pose proof (i63_range len) as Hlen. change (to_Z shadow_K) with 2147450880 in Esh.
    assert (Hq8 : 0 <= bv_unsigned (rho' tp) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Ea : bv_unsigned (adr rho' t (o + j)) = bv_unsigned (rho' t) + (o + j)) by (apply adr_unsigned; lia).
    exists tp, len. split; [exact He|]. split; [exact Hq|]. split; [lia|]. split; [exact Ea|].
    rewrite Ea, Esh. pose proof Hav as Hav'. unfold avis3_chk in Hav'.
    do 3 (apply andb_prop in Hav' as [Hav' _]). apply andb_prop in Hav' as [_ Hih]. apply Z.leb_le in Hih. unfold span_lo in Hih. lia. }
  assert (Hvisb : forall t o nn, visb3 (root_cov (CAP.kn CS) M0 (xt_of TT)) t o nn = true ->
             forall j, 0 <= j < nn -> H' (adr rho' t (o + j)) = false).
  { intros t o nn Hv j Hj. unfold visb3 in Hv. destruct (to_Z t <? to_Z n) eqn:Etn.
    - apply Z.ltb_lt in Etn.
      destruct (vis_pre (root_cov (CAP.kn CS) M0 (xt_of TT)) t o nn) eqn:Evp.
      + unfold adr. rewrite (Hrho t Etn).
        pose proof (vis_root_sound segs E TT (CAP.kn CS) H FULL M0 HTT Hnoseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) (xt_of TT) eq_refl HM0
                      t o nn (vis_pre_root (CAP.kn CS) M0 (xt_of TT) t o nn Evp) j Hj) as Hh. unfold adr in Hh.
        destruct (H' (bv_add (rho t) (Z_to_bv 64 (o + j)))) eqn:Eh'; [|reflexivity]. rewrite (Hsub _ Eh') in Hh. discriminate.
      + destruct (in_commit t o nn) eqn:Eic.
        2:{ (* [comment removed for export] *)
          apply (xa_visible segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 Hlx1 n rho (fl_all L3) Hmaps0 Htags0 rho' m' (fl_all L') (fl_ops L')
                   (fl_c (fl3 L')) (fl_S (fl3 L')) Hrho lp_maps lp_na Hfacts' Hisp fresh HALL END XT1 Hr0' HXT
                   (la_shp ax ++ shp_of M1) HSHP HshK XA (pb_of M1) (pb_of_sound rho' M1 HM1) argH_high Hzones HXAc).
          unfold in_xa in Hv. apply andb_prop in Hv as [Hnn0 Hex]. apply Z.leb_le in Hnn0.
          apply existsb_exists in Hex as ([[t' off] len] & He & Hec). apply andb_prop in Hec as [Hec X2]. apply andb_prop in Hec as [Ht' X1].
          apply Uint63.eqb_spec in Ht'. subst t'. apply Z.leb_le in X1, X2.
          pose proof (i63_range off) as Hoff. pose proof (i63_range len) as Hlen. pose proof (br_u64 (rho' t)) as Hu.
          assert (Hnw : bv_unsigned (rho' t) + to_Z off + to_Z len < 2 ^ 63).
          { rewrite forallb_forall in HXAc. pose proof (HXAc _ He) as Hck. unfold xa_ent_chk in Hck.
            apply existsb_exists in Hck as (p & Hp & Hpq).
            destruct (xa_q_sound A E1 rho' m' XT1 Hr0' HXT (la_shp ax ++ shp_of M1) HSHP HshK (pb_of M1) (pb_of_sound rho' M1 HM1)
                        t (to_Z off) (to_Z len) p ltac:(lia) ltac:(lia) Hpq) as (_ & S2 & _).
            unfold CXS.sh_hi in S2. rewrite HshK in S2. change (to_Z shadow_K) with 2147450880 in S2.
            pose proof (br_u64 (AX2.edenot E1 (fst p))) as Hp1. pose proof (br_u64 (AX2.edenot E1 (snd p))) as Hp2. unfold CXS.uE in S2.
            clear - S2 Hp1 Hp2. Z.div_mod_to_equations. lia. }
          unfold xain. apply existsb_exists. exists (t, off, len). split; [exact He|].
          rewrite (adr_unsigned rho' t (o + j)) by lia. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        unfold in_commit in Eic. apply andb_prop in Eic as [_ Hex]. apply existsb_exists in Hex as (c & Hcc & Hcx).
        destruct (snd c) as [[t' off] len] eqn:Esc. apply andb_prop in Hcx as [Hcx X2]. apply andb_prop in Hcx as [Ht' X1].
        apply Uint63.eqb_spec in Ht'. subst t'. apply Z.leb_le in X1, X2.
        destruct (Hcden c t off len Hcc Esc) as (_ & Er & Elo & Ehi & rg & Hg & G1 & G2).
        destruct (HM0 t rg Hg) as (_ & _ & Hb63 & _). pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range off) as Hoff.
        destruct (Hcin c Hcc) as [Hcops Hcm].
        apply (commit_visible segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 n rho' m' (fl_all L') (fl_ops L') (fl_c (fl3 L')) (fl_S (fl3 L'))
                 lp_maps lp_na lp_lz Hfacts' Hisp lp_opsF Hopc END (fl_ord L') Hord1 Hcommit M1 argH_high HM1 c _ Hcal Hcops Hcm).
        rewrite Elo, Ehi. rewrite (adr_unsigned rho' t (o + j)) by (rewrite ?Er; lia). rewrite Er. lia.
    - destruct (in_fresh t o nn) eqn:Eif; [destruct (Hinfr t o nn Eif j Hj) as (e & He & Hx); exact (Hfrv e He _ Hx)|].
      destruct (Hinfsh t o nn Hv j Hj) as (tp & len & Hfr & Hsp & Hd8 & Ex & _).
      exact (leaf_fresh_shadow_visible segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 Hlx1 n rho (fl_all L3) Hmaps0 Htags0 rho' m' (fl_all L') (fl_ops L')
               (fl_c (fl3 L')) (fl_S (fl3 L')) Hrho lp_maps lp_na Hfacts' Hisp fresh HALL END XT1 Hr0' HXT
               (la_shp ax ++ shp_of M1) HSHP HshK argH_high Hzones Hav Hfv tp len t Hfr (in_or_app _ _ _ (or_introl Hsp))
               (adr rho' t (o + j)) (o + j) ltac:(unfold in_fresh_sh in Hv; apply andb_prop in Hv as [Hv _]; apply andb_prop in Hv as [Ho _]; apply Z.leb_le in Ho; lia) Hd8 Ex). }
  assert (Hovb : forall t o nn, ovb3 t o nn = true -> forall j, 0 <= j < nn ->
             ms_mem ms' (adr rho' t (o + j)) <> None \/ find_segment segs (bv_unsigned (adr rho' t (o + j))) 1 = None).
  { intros t o nn Hv j Hj. right. unfold ovb3, ovb3x in Hv. fold cnoseg in Hv. destruct (to_Z t <? to_Z n) eqn:Etn.
    - apply Z.ltb_lt in Etn. unfold adr. rewrite (Hrho t Etn).
      destruct (cnoseg t o nn) eqn:Ecn;
        [|exact (noseg_chk_sound segs A SEGS_in_hull E TT (CAP.kn CS) H FULL (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) ra Era t o nn Hv j Hj)].
      unfold cnoseg, cnosegx in Ecn. destruct (iget t (f_mem F0)) as [rg|] eqn:Hg; [|discriminate].
      destruct (cls classes t) as [c|] eqn:Hcl; [|discriminate].
      apply andb_prop in Ecn as [Ecn Hneq]. apply andb_prop in Ecn as [Ecn Hhi0]. apply andb_prop in Ecn as [Hlo0 Hn0].
      apply Z.leb_le in Hlo0, Hn0, Hhi0.
      pose proof (Rn_dress segs IM n rho (state_of d) ms0 bs HRn0 Hdlt Hdok) as HRn0d.
      assert (HR0d : FxRel.R segs IM rho F0 ms0) by (apply HRn0d; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
      pose proof (R_mem _ _ _ _ _ HR0d) as Hmem0d. cbn [ms_mem PropExec.mkst] in Hmem0d.
      destruct (proj1 (proj1 Hmem0d t rg Hg)) as (_ & _ & Hb63 & _).
      destruct (reg3_get A CS TT classes (f_mem F0) t rg Hregs3 Hg) as (c' & Hcls' & Hclc & _ & _).
      rewrite Hcl in Hcls'. injection Hcls' as <-.
      pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range (rg_lo rg)) as Hl0.
      apply SEGS_in_hull. fold (adr rho t (o + j)). rewrite (adr_unsigned rho t (o + j)) by lia.
      destruct (CXS.in_hull A (bv_unsigned (rho t) + (o + j))) eqn:Eh; [|reflexivity]. exfalso.
      unfold CXS.in_hull in Eh. apply andb_prop in Eh as [Eh1 Eh2]. apply Z.leb_le in Eh1. apply Z.ltb_lt in Eh2.
      apply (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx HULL_ok c RCHull (bv_unsigned (rho t) + (o + j)) Hneq).
      + apply (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT t _ _ c Hclc Hb63). lia.
      + cbn [class_sem]. lia.
    - destruct (in_fresh t o nn) eqn:Eif.
      2:{ destruct (Hinfsh t o nn Hv j Hj) as (tp & len & _ & _ & _ & _ & Hih).
          apply SEGS_in_hull. unfold CXS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. exact Hih. }
      destruct (Hinfr t o nn Eif j Hj) as (e & He & Hx).
      assert (Hin' : In (den rho' e) (vm_maps V')) by (rewrite lp_maps, HALL; apply in_map; apply in_or_app; left; exact He).
      pose proof (proj1 (Forall_forall _ _) (leaf_bounds segs A Hres m' (fl_c (fl3 L')) (fl_S (fl3 L')) Hfacts') _ Hin') as (_ & _ & _ & Hh & _).
      apply SEGS_in_hull. unfold CXS.in_hull. unfold e_hi, e_lo, e_sz in Hx.
      apply andb_false_iff. destruct Hh as [Hh|Hh]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
  assert (Hknow : AX2S.know_ok segs E1 (CXS.Mr A argH E1 END m' (ms_mem ms')) (CAP.kn END)).
  { refine (know3_sound2 segs IM A E TT (CAP.kn CS) H FULL (ms_mem ms') d M1 VT (CAP.nxt CS) HTT HIM HWR Hnoseg
             (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) ra Era (CAP.kset_mem (CAP.kset_of (CAP.kn CS))) (CAP.kset_mem_of' (CAP.kn CS)) Hhull (xt_of TT) eq_refl M0 eq_refl rho' Hr0' n Hrho XT1 HXT Hmem0 Hmem1 CMp _ _ cmf3 Hcmf3
             HVT Hsmall H' Hsub (visb3 (root_cov (CAP.kn CS) M0 (xt_of TT))) Hvisb ovb3 Hovb
             (pure3_chk A CS (fl_all L') (fl_ops L') XT1 (la_xtn ax)) _ (f_mem F0) _ (span_nclbR CS TT classes (f_mem F0) ra) _
             (CAP.kn END) Hkn' Hkv).
    - intros x Hx Hncm Hnc. apply (HfrA x); [intros Ht; destruct (Htsplit _ Ht) as [Ht1|Ht1]; [exact (Hunt x Hx Ht1) | exact (Hncm Ht1)]|].
      left. intros Hcl. apply Hnc. exact (claimed_wr_same IM rho _ _ x (dress_same bs M0) Hcl).
    - intros x Hx Hncm Hne. apply (HfrA x); [intros Ht; destruct (Htsplit _ Ht) as [Ht1|Ht1]; [exact (Hunt x Hx Ht1) | exact (Hncm Ht1)]|].
      right. exact Hne.
    - intros K HK.
      exact (pure3_sound segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 Hres rho' m' (fl_all L') (fl_ops L') (fl_c (fl3 L')) (fl_S (fl3 L'))
               lp_maps Hfacts' Hisp lp_opsF XT1 Hr0' HXT (la_xtn ax)
               (xtn_xv E rho' M1 (fl_ops L') VT (la_xtn ax) Hxtn) K _ HK).
    - intros x Hx Hncm Hnc. apply (HfrA x); [intros Ht; destruct (Htsplit _ Ht) as [Ht1|Ht1]; [exact (Hunt x Hx Ht1) | exact (Hncm Ht1)]|].
      left. exact Hnc.
    - intros a0 nn Hc x Hx. rewrite (span_nclbR_eq CS TT classes (f_mem F0) ra a0 nn Era) in Hc.
      pose proof (Rn_dress segs IM n rho (state_of d) ms0 bs HRn0 Hdlt Hdok) as HRn0d.
      assert (HR0d : FxRel.R segs IM rho F0 ms0) by (apply HRn0d; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
      pose proof (R_mem _ _ _ _ _ HR0d) as Hmem0d. cbn [ms_mem PropExec.mkst] in Hmem0d.
      split; [exact (span_nclb_sound segs A Lim SINV argH ISP FS0 HULL_ok E CS R FULL m HCS Hlx TT classes (f_mem F0) IM FULL a0 nn
                        Hregs3 Hmem0d Hc x Hx)|].
      intros (c & Hcc & Hz).
      pose proof (span_nclb_span segs A Lim SINV argH ISP FS0 E CS R FULL m HCS TT classes (f_mem F0) a0 nn Hc x Hx) as Hxs.
      assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply br_lit_small; unfold span_lo, span_hi in Hxs; lia).
      rewrite Ux in Hz. destruct (snd c) as [[t off] len] eqn:Esc.
      destruct (Hcden c t off len Hcc Esc) as (_ & _ & Elo & Ehi & _). rewrite Esc in Elo, Ehi. rewrite Elo, Ehi in Hz.
      unfold commit_regs_chk, commit_regs_chkx in Hcregs. rewrite forallb_forall in Hcregs. pose proof (Hcregs c Hcc) as H1.
      rewrite Esc in H1. cbn [fent_tag fst snd] in H1. apply andb_prop in H1 as [H1 Hcl]. apply andb_prop in H1 as [_ Hcr].
      unfold creg_ok, creg_okZ in Hcr. destruct (iget t (f_mem F0)) as [rgd|] eqn:Hgd; [|discriminate].
      apply andb_prop in Hcr as [D1 D2]. apply Z.leb_le in D1, D2.
      destruct (cls classes t) as [cc|] eqn:Ecl; [|discriminate].
      apply (span_region_apart segs A Lim SINV argH ISP FS0 HULL_ok E CS R FULL m HCS Hlx TT classes (f_mem F0)
               (fun t1 rg1 Hg1 => proj1 (proj1 Hmem0d t1 rg1 Hg1)) t rgd cc x Hregs3 Hgd Ecl Hcl); [lia | exact Hxs]. }
  destruct HR1 as [R1pc R1regs R1svc R1resv R1mem].
  assert (Hregs : AX2S.regs_ok E1 (AX2.s_regs (CAP.a_ss END)) (ms_regs ms')).
  { unfold AX2S.regs_ok. intros rr. unfold getr, AX2.sr_get.
    destruct (bv_eqb rr 0) eqn:Er; [reflexivity|].
    pose proof (R1regs rr) as Hreg. unfold Sem.rget in Hreg. change (is_x0 rr) with (bv_eqb rr 0) in Hreg.
    rewrite Er in Hreg. change (c_regs (core_of ms')) with (ms_regs ms') in Hreg. rewrite Hreg.
    rewrite forallb_forall in Hregs'.
    pose proof (bv_unsigned_in_range _ rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    assert (Hrn0 : bv_unsigned rr <> 0) by (intros E0; unfold bv_eqb in Er; rewrite E0 in Er; discriminate).
    specialize (Hregs' (AX2.ridx rr)). unfold AX2.ridx in *. rewrite Z2Nat.id in Hregs' by lia.
    symmetry.
    apply (val_match_sound rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT1 [] HM1 Hr0' eq_refl HXT (Forall_nil _)).
    apply Hregs'. apply in_seq. lia. }
  split; [|split; [|split]].
  - refine (leaf_cs_ok segs A Lim SINV argH ISP FS0 E1 CS R FULL m HCS1 Hlx1 Hres n rho (fl_all L3) Hmaps0 Htags0 rho' m'
            (fl_all L') (fl_ops L') (fl_c (fl3 L')) (fl_S (fl3 L')) (fl_E L') Hrho lp_maps lp_na lp_lz Hfacts' lp_wfna lp_wflz Hsame Hisp Hsbrk Hbrk
            Hhalt' lp_lim lp_E lp_opsF lp_opsR Hopc fresh HALL END XT1 Hr0' HXT (fl_lazy L') lp_pw _ (fl_ord L') Hord1 Hcommit _ (fl_allow L') (la_shp ax ++ shp_of M1)
            HSHP HshK XA (pb_of M1) (pb_of_sound rho' M1 HM1) Hpi' lp_mat IM (f_mem F0) M1 (ms_mem ms') (fl_ex L') TT
            SEGS_in_hull argH_high Hrho_tt HfrA Hcw HShZ HM1 Hspok Hexcov SINV_frame Hhi' (ms_regs ms') Hmodel Hregs Hlog Hknow).
    + unfold model3_chk in Hmodel. do 4 (apply andb_prop in Hmodel as [Hmodel _]). exact Hmodel.
    + unfold model3_chk in Hmodel. do 3 (apply andb_prop in Hmodel as [Hmodel _]). apply andb_prop in Hmodel as [_ Hs]. exact Hs.
  - apply ms_eta; try reflexivity.
    + exact Hfr0.
    + rewrite R1pc, Hpc. reflexivity.
    + exact R1svc.
    + rewrite R1resv. destruct (f_resv F'); [discriminate | reflexivity].
    + exact Hfc0.
    + exact Hrom0.
  - destruct Hsame as (_ & _ & Hfsys & _). unfold m_fs. rewrite Hfsys. reflexivity.
  - exact Hag.
Qed.

End Leaf3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive hooksel : Set := HK6 | HK7 (W kw rounds : nat).
Definition xpc_of (IM : fimage) (code : itrie finstr) (xask : fstate -> option (int * int)) (h : hooksel)
    : fstate -> fledger3 -> int -> option dres3 :=
  match h with
  | HK6 => xpc_builtin6 IM code
  | HK7 W kw rounds => xpc_builtin7 IM code xask W kw rounds
  end.

Section Trans3.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).
Variable classes : list (int * rclass).
Variable CS : CAP.acs.
Variable d : sdesc.
Variable bs : list ditem.
Variable L3 : fledger3.
Variable W : Z.
Variables Rb Rc : Z.
Variable shp : int -> bool.
Variable xask : fstate -> option (int * int).
Variable bp : int.
Variable k fuel : nat.
Variable END : CAP.acs.
Variable aux : fstate -> fledger3 -> int -> LeafAux.
Variable XA : list fent.             (* [comment removed for export] *)
Variable hk : hooksel.               (* [comment removed for export] *)

Local Notation R0 := (segments_reserved segs).
Local Notation F0 := (dress (state_of d) bs).

(* [comment removed for export] *)
Definition strip_res (L : fledger3) : fledger3 :=
  FL3 (fl3 L) (fl_all L) (fl_ops L) (fl_lazy L) (fl_allow L) (fl_Ab L) (fl_E L) (fl_ex L) (fl_ord L) [].

Definition leafx_chk (ra : ra_t) (pre : list Z) (F' : fstate) (L' : fledger3) (n' : int) : bool :=
  leaf3a_chk segs A Lim nx0 TT n classes CS d bs L3 XA F' L' END (aux F' (strip_res L') n')
  && leaf3b_chk IM A TT n classes CS d bs L3 XA ra F' L' END (aux F' (strip_res L') n') pre.

Lemma leafx_strip ra pre F' L' n' : leafx_chk ra pre F' (strip_res L') n' = leafx_chk ra pre F' L' n'.
Proof. destruct L'. reflexivity. Qed.

Definition lkey_ok (ra : ra_t) (pre : list Z) (key : lkey) : Prop := leafx_chk ra pre (fst (fst key)) (snd (fst key)) (snd key) = true.

Fixpoint tree3x_chk (ra : ra_t) (pre : list Z) (t : dtree3) (seen : list lkey) : option (list lkey) :=
  match t with
  | D3Leaf F' L' n' r =>
      match r with
      | SBreak =>
          let key : lkey := (F', strip_res L', n') in
          if existsb (lkey_eqb key) seen then Some seen
          else if leafx_chk ra pre F' (strip_res L') n' then Some (key :: seen) else None
      | _ => None
      end
  | D3Fork a b => match tree3x_chk ra pre a seen with Some s1 => tree3x_chk ra pre b s1 | None => None end
  end.

Lemma tree3x_leaf ra pre : forall t seen seen', tree3x_chk ra pre t seen = Some seen' -> Forall (lkey_ok ra pre) seen ->
  Forall (lkey_ok ra pre) seen'
  /\ forall F' L' n' r, leaf_in3 (F', L', n', r) t ->
       leaf3a_chk segs A Lim nx0 TT n classes CS d bs L3 XA F' L' END (aux F' (strip_res L') n') = true
       /\ leaf3b_chk IM A TT n classes CS d bs L3 XA ra F' L' END (aux F' (strip_res L') n') pre = true.
Proof.
  induction t as [F1 L1 n1 r1 | a IHa b IHb]; intros seen seen' Hc Hs; cbn [tree3x_chk leaf_in3] in *.
  - destruct r1; try discriminate Hc. cbv zeta in Hc.
    assert (Hok : leafx_chk ra pre F1 L1 n1 = true /\ Forall (lkey_ok ra pre) seen').
    { destruct (existsb (lkey_eqb (F1, strip_res L1, n1)) seen) eqn:Ex.
      - injection Hc as <-. split; [|exact Hs]. apply existsb_exists in Ex as (key & Hin & Heq). apply lkey_eqb_ok in Heq.
        rewrite Forall_forall in Hs. pose proof (Hs key Hin) as Hk. unfold lkey_ok in Hk. rewrite <- Heq in Hk. cbn [fst snd] in Hk.
        rewrite leafx_strip in Hk. exact Hk.
      - destruct (leafx_chk ra pre F1 (strip_res L1) n1) eqn:El; [|discriminate Hc]. injection Hc as <-.
        split; [rewrite <- leafx_strip; exact El|]. constructor; [|exact Hs]. unfold lkey_ok. cbn [fst snd]. exact El. }
    destruct Hok as [Hl Hs']. split; [exact Hs'|]. intros F' L' n' r Hin. injection Hin as -> -> -> ->.
    unfold leafx_chk in Hl. apply andb_prop in Hl. exact Hl.
  - destruct (tree3x_chk ra pre a seen) as [s1|] eqn:Ea; [|discriminate Hc].
    destruct (IHa _ _ Ea Hs) as [Hs1 Hla]. destruct (IHb _ _ Hc Hs1) as [Hs2 Hlb]. split; [exact Hs2|].
    intros F' L' n' r [Hin|Hin]; [exact (Hla _ _ _ _ Hin) | exact (Hlb _ _ _ _ Hin)].
Qed.

(* [comment removed for export] *)
Definition rest3x_chk : bool :=
  root3_chk segs A Lim TT n classes CS d bs L3 W
  && xa_root_chk CS L3 XA
  && (live_bytes R0 <=? Rb) && (Z.of_nat (length R0) <=? Rc)
  && (let ra := ra_fast (CAP.kn CS) in                   (* [comment removed for export] *)
      let pre := pre_old IM A TT classes CS d bs ra END in
      match tree3x_chk ra pre (drive3 IM code Rb Rc Lim [] shp (fun _ _ _ => None) xask (xpc_of IM code xask hk) bp k fuel F0 L3 n) [] with
      | Some _ => true | None => false end).

Theorem fx_transform3_genX E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tt_wf TT = true ->
  Rn segs IM n (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) ->
  Forall (ditem_lt n) bs -> Forall (ditem_ok (rho_of TT E)) bs ->
  LZ IM (rho_of TT E) (m_vm_lazy m) (map (denA (rho_of TT E)) XA ++ CXS.allowA A E CS) (f_mem (state_of d)) ->
  (forall x, claimed_wr IM (rho_of TT E) (f_mem (state_of d)) x ->
             CXS.hid A argH E CS m x = false \/ xain (rho_of TT E) XA (bv_unsigned x) = true) ->
  rest3x_chk = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof.
  intros HCS HTT HRn0 Hdlt Hdok HLZX HcwX Hchk Hk HK. unfold rest3x_chk in Hchk.
  apply andb_prop in Hchk as [Hc Htree]. apply andb_prop in Hc as [Hc HRc]. apply andb_prop in Hc as [Hc HRb].
  apply andb_prop in Hc as [Hroot Hxa].
  apply Z.leb_le in HRb, HRc.
  pose proof (rb_DInv3_genX cfg segs IM A Lim SINV argH ISP FS0 HULL_ok argH_high TT n classes CS d bs L3 W
                E R FULL m HCS HTT HRn0 Hdlt Hdok Hroot XA Hxa HLZX) as HD0.
  unfold CXS.cfg_of.
  refine (drive3_universal cfg segs IM code Hcode Halloc R0 Rb Rc Lim HRb HRc [] FULL (fun _ _ => True) []
            (fun _ _ _ _ H => H) (fun _ _ _ _ H => H) bvmap_empty (Z_to_bv 32 0) (PropExec.seg_rom segs) (fun x => argH E x = true)
            (Z_to_bv 64 W) _ _ _ (map (denA (rho_of TT E)) XA ++ CXS.allowA A E CS) shp (fun _ _ _ => None) xask (xpc_of IM code xask hk) _ _ bp k Hk fuel n _ F0 L3 _ m T HD0 _).
  - intros n1 rho1 F1 L1 ms1 m1 res Hn. discriminate Hn.
  - intros n1 rho1 F1 L1 ms1 m1 res Hx HD1. destruct hk as [|Wj kwj rj]; cbn [xpc_of] in Hx.
    + exact (xpc_builtin6_sound cfg segs IM code Hcode R0 Lim [] FULL (fun _ _ => True) [] (fun _ _ _ _ H => H) bvmap_empty (Z_to_bv 32 0)
               (PropExec.seg_rom segs) (fun x => argH E x = true) (Z_to_bv 64 W) _ _ _ (map (denA (rho_of TT E)) XA ++ CXS.allowA A E CS) n1 rho1 F1 L1 ms1 m1 res Hx HD1).
    + exact (xpc_builtin7_sound cfg segs IM code Hcode R0 Lim [] FULL (fun _ _ => True) [] (fun _ _ _ _ H => H) bvmap_empty (Z_to_bv 32 0)
               (PropExec.seg_rom segs) (fun x => argH E x = true) (Z_to_bv 64 W) _ _ _ (map (denA (rho_of TT E)) XA ++ CXS.allowA A E CS)
               xask Wj kwj rj n1 rho1 F1 L1 ms1 m1 res Hx HD1).
  - intros F' L' n' r Hin rho' ms' m' HD' Hext _.
    cbv zeta in Htree.
    destruct (tree3x_chk (ra_fast (CAP.kn CS)) (pre_old IM A TT classes CS d bs (ra_fast (CAP.kn CS)) END)
                (drive3 IM code Rb Rc Lim [] shp (fun _ _ _ => None) xask (xpc_of IM code xask hk) bp k fuel F0 L3 n) []) as [seen'|] eqn:Etree;
      [|discriminate Htree].
    destruct (proj2 (tree3x_leaf _ _ _ _ _ Etree (Forall_nil _)) F' L' n' r Hin) as [Ha Hb].
    destruct (leaf3_cs_ok cfg segs IM HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high nx0 NX0_spw argH_agree SINV_agree SINV_frame
                TT n classes CS d bs L3 W E R FULL m HCS HTT HRn0 Hdlt Hdok Hroot XA HcwX (ra_fast (CAP.kn CS)) (ra_fast_eq _) n' rho' F' L' ms' m' HD' Hext END (aux F' (strip_res L') n') Ha Hb)
      as (HCS' & Ems & Hfs & Hag).
    rewrite Ems. exact (HK _ _ _ _ Hag HCS' Hfs).
Qed.

End Trans3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tree3_chk segs IM A Lim nx0 TT n classes CS d bs L3 END aux (pre : list Z) (t : dtree3) : bool :=
  match tree3x_chk segs IM A Lim nx0 TT n classes CS d bs L3 END aux [] (ra_fast (CAP.kn CS)) pre t [] with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition rest3h_chk (hk : hooksel) segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux : bool :=
  side_chkP A TT (CAP.kn CS) d        (* [comment removed for export] *)
  && rest3x_chk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux [] hk.

Definition trans3h_chk (hk : hooksel) segs IM code A Lim nx0 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux : bool :=
  rb_check IM A TT n shapes cuts classes CS d
  && forallb (dress_chk TT (CAP.kn CS) n) bs
  && rest3h_chk hk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux.

Definition rest3_chk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux : bool :=
  rest3h_chk HK6 segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux.

Definition trans3_chk segs IM code A Lim nx0 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux : bool :=
  trans3h_chk HK6 segs IM code A Lim nx0 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux.

Section Trans3C.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Theorem fx_transform3h_gen hk TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tt_wf TT = true ->
  Rn segs IM n (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) ->
  Forall (ditem_lt n) bs -> Forall (ditem_ok (rho_of TT E)) bs ->
  rest3h_chk hk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof.
  intros HCS HTT HRn0 Hdlt Hdok Hchk Hk HK. unfold rest3h_chk in Hchk. apply andb_prop in Hchk as [Hside Hrest]. apply side_chkP_ok in Hside.
  assert (HR0 : FxRel.R segs IM (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)))
    by (apply HRn0; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0) as Hmem0. cbn [ms_mem PropExec.mkst] in Hmem0.
  pose proof (CXS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH ISP argH_high E CS m) as Hnoseg.
  pose proof (fun a => rb_hull A argH ISP HULL_ok argH_high CS E m a) as Hhull.
  pose proof (CXS.lazy_cover_cs segs A Lim (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                HULL_ok SINV argH ISP FS0 0%nat E CS R FULL m HCS) as Hcover.
  apply (fx_transform3_genX cfg segs IM code Hcode Halloc HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high nx0 NX0_spw
           argH_agree SINV_agree SINV_frame TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux [] hk E R FULL m T HCS HTT HRn0 Hdlt Hdok);
    [ | | exact Hrest | exact Hk | exact HK].
  - exact (side_LZ segs IM A E TT (CAP.kn CS) _ FULL d _ _ HTT Hnoseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hhull Hcover Hmem0 Hside).
  - intros x Hx. left.
    exact (side_cw segs IM A E TT (CAP.kn CS) _ FULL d HTT Hnoseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) Hhull Hmem0 Hside x Hx).
Qed.

Theorem fx_transform3_gen TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  tt_wf TT = true ->
  Rn segs IM n (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)) ->
  Forall (ditem_lt n) bs -> Forall (ditem_ok (rho_of TT E)) bs ->
  rest3_chk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof. exact (fx_transform3h_gen HK6 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T). Qed.

Theorem fx_transform3h hk TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  trans3h_chk hk segs IM code A Lim nx0 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof.
  intros HCS Hchk Hk HK. unfold trans3h_chk in Hchk.
  apply andb_prop in Hchk as [Hc Hrest]. apply andb_prop in Hc as [Hrb Hdress].
  pose proof (rb_parts IM A TT n shapes cuts classes CS d Hrb) as (HTT & _).
  pose proof (rb_Rn segs IM HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS d E R FULL m HCS Hrb) as HRn0.
  destruct (dress_chk_all segs E TT (CAP.kn CS) _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) n bs Hdress) as [Hdlt Hdok].
  exact (fx_transform3h_gen hk TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T HCS HTT HRn0 Hdlt Hdok Hrest Hk HK).
Qed.

Theorem fx_transform3 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  trans3_chk segs IM code A Lim nx0 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof. exact (fx_transform3h HK6 TT n shapes cuts classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux E R FULL m T). Qed.

End Trans3C.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hole3.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Theorem fx_hole3h_chk hk TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux :
  trans3h_chk hk segs IM code A Lim nx0 TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux = true ->
  (k <= 61)%nat ->
  fx_hole cfg segs A Lim SINV argH ISP FS0 START END.
Proof.
  intros Hchk Hk E R FULL m T HCS HK.
  exact (fx_transform3h cfg segs IM code Hcode Halloc HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high nx0 NX0_spw
           argH_agree SINV_agree SINV_frame hk TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux
           E R FULL m T HCS Hchk Hk HK).
Qed.

Theorem fx_hole3_chk TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux :
  trans3_chk segs IM code A Lim nx0 TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux = true ->
  (k <= 61)%nat ->
  fx_hole cfg segs A Lim SINV argH ISP FS0 START END.
Proof. exact (fx_hole3h_chk HK6 TT n shapes cuts classes START d bs L3 W Rb Rc shp xask bp k fuel END aux). Qed.
End Hole3.
