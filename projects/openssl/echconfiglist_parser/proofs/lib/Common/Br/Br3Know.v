(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxLazy FxCellFrame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrKset.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import CXI.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv BrMem BrPart BrRev BrRevLedger BrClass BrRevS BrDress BrGrow BrTrans Br3Fill BrRa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing).
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint iallF_aux {T : Type} (f : int -> T -> bool) (k : nat) (sh p : int) (t : itrie T) : bool :=
  match k with
  | O => match iget 0%uint63 t with Some v => f p v | None => true end
  | S k' =>
      match t with
      | IEmpty => true
      | ILeaf key v => if (((key << sh) >> sh) =? key)%uint63 then f (p + (key << sh))%uint63 v else true
      | INode l r => if iallF_aux f k' (sh + 1)%uint63 p l then iallF_aux f k' (sh + 1)%uint63 (p + (1 << sh))%uint63 r else false
      end
  end.
Definition iallF {T : Type} (f : int -> T -> bool) (t : itrie T) : bool := iallF_aux f ifuel 0%uint63 0%uint63 t.

Lemma iallF_aux_spec {T : Type} (f : int -> T -> bool) : forall k sh p (t : itrie T) acc,
  forallb (fun kv => f (fst kv) (snd kv)) (ielements_aux k sh p t acc)
  = (iallF_aux f k sh p t && forallb (fun kv => f (fst kv) (snd kv)) acc)%bool.
Proof.
  induction k as [|k IH]; intros sh p t acc; cbn [ielements_aux iallF_aux].
  - destruct (iget 0%uint63 t) as [v|]; [reflexivity | reflexivity].
  - destruct t as [|key v|l r]; [reflexivity| |].
    + destruct (((key << sh) >> sh) =? key)%uint63; reflexivity.
    + rewrite IH, IH. destruct (iallF_aux f k (sh + 1)%uint63 p l); [reflexivity|]. cbn [andb]. reflexivity.
Qed.

#[local] Transparent ielements.
Lemma iallF_spec {T : Type} (f : int -> T -> bool) (t : itrie T) :
  iallF f t = forallb (fun kv => f (fst kv) (snd kv)) (ielements t).
Proof. unfold iallF, ielements. rewrite iallF_aux_spec. cbn [forallb]. rewrite andb_true_r. reflexivity. Qed.
#[local] Opaque ielements.

Definition cells_small_fast (M : itrie region) : bool :=
  iallF (fun _ rg =>
    iallF (fun pn p =>
      (to_Z pn <? 2 ^ 50) && (to_Z (rg_lo rg) <=? to_Z pn * 4096)
      && (let full := (to_Z pn * 4096 + 4096 <=? to_Z (rg_len rg)) in
          iallF (fun ci _ => if (ci <? 512)%uint63 then (if full then true else (to_Z pn * 4096 + to_Z ci * 8 + 8 <=? to_Z (rg_len rg))) else false)
               (pg_cells p))) (rg_pages rg)) M.

Lemma cells_small_fast_ok M : cells_small_fast M = true -> cells_small M = true.
Proof.
  unfold cells_small_fast, cells_small. rewrite iallF_spec. intros H. rewrite forallb_forall in H. apply forallb_forall.
  intros tr Htr. pose proof (H tr Htr) as H1. cbn beta in H1. rewrite iallF_spec in H1. rewrite forallb_forall in H1.
  apply forallb_forall. intros pp Hpp. pose proof (H1 pp Hpp) as H2. cbn beta in H2.
  apply andb_prop in H2 as [H2 H3]. rewrite H2. cbn [andb]. cbv zeta in H3. rewrite iallF_spec in H3. rewrite forallb_forall in H3.
  apply forallb_forall. intros cc Hcc. pose proof (H3 cc Hcc) as H4. cbn beta in H4.
  destruct (fst cc <? 512)%uint63 eqn:E5; [|discriminate]. apply Uint63.ltb_spec in E5. change (to_Z 512) with 512 in E5.
  apply andb_true_iff. split; [apply Z.ltb_lt; exact E5|].
  destruct (to_Z (fst pp) * 4096 + 4096 <=? to_Z (rg_len (snd tr))) eqn:Efull; [|exact H4].
  apply Z.leb_le in Efull. apply Z.leb_le. pose proof (i63_range (fst cc)). lia.
Qed.

Section Know3.
Variable segs : list Segment.
Variable IM : fimage.
Variable A : APC.atable.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn0 : list AX2.kentry.
Variable H : word -> bool.
Variables FULL FULL' : word -> option byte.
Variable d : sdesc.
Variable M1 : itrie region.
Variable VT : vtab.
Variable nx : nat.
Hypothesis HTT : tt_wf TT = true.
Hypothesis HIM : image_ok segs IM.                    (* [comment removed for export] *)
Hypothesis HWR : image_wr_ok IM.
Hypothesis Hnoseg : forall x, H x = true -> find_segment segs (bv_unsigned x) 1 = None.
Hypothesis Hkn0 : AX2S.know_ok segs E (mrestrict H FULL) kn0.
Variable ra : ra_t.                                   (* [comment removed for export] *)
Hypothesis Era : ra = AX2.ranges_apart kn0.
Variable km : AX2.kentry -> bool.                     (* [comment removed for export] *)
Hypothesis Ekm : forall K, km K = existsb (APC.kentry_eqb K) kn0.
Hypothesis Hhull : forall a, APC.img_lo A <= a < APC.img_hi A -> H (Z_to_bv 64 a) = false.

Local Notation rho := (rho_of TT E).
Variable XTv : list (int * AX2.lin).
Hypothesis EXT : XTv = xt_of TT.
Variable M0 : itrie region.
Hypothesis EM0 : M0 = f_mem (state_of d).
(* [comment removed for export] *)
Variable rho' : int -> word.
Hypothesis Hrho0' : rho' 0%uint63 = Z_to_bv 64 0.
Variable nroot : int.                    (* [comment removed for export] *)
Hypothesis Hrho_lt : forall t, to_Z t < to_Z nroot -> rho' t = rho t.
Local Notation E' := (env_of rho' (AX2.ev E) (AX2.eb E) VT).
Variable XT' : list (int * AX2.lin).
Hypothesis HXT' : xt_ok rho' (AX2.ev E) (AX2.eb E) VT XT'.
Hypothesis Hmem0 : mem_ok segs IM rho M0 FULL.
Hypothesis Hmem1 : mem_ok segs IM rho' M1 FULL'.
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable CM : word -> Prop.
Hypothesis Hfr : forall x, H x = false -> ~ CM x -> ~ claimed_wr IM rho M0 x -> FULL' x = FULL x.
Hypothesis Hcf : forall x, H x = false -> ~ CM x -> ~ cell_expl rho' M1 x -> FULL' x = FULL x.
Variable cmf : AX2.saddr -> Z -> bool.
Hypothesis Hcmf : forall a nn nn', cmf a nn = true -> nn' <= nn ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + nn' -> ~ CM (Z_to_bv 64 x).
Hypothesis HVT : forallb (fun p => Nat.leb nx (fst p)) VT = true.
Hypothesis Hkv : APC.kn_vars_lt nx kn0 = true.
Hypothesis Hsmall : cells_small M1 = true.
(* [comment removed for export] *)
Variable H' : word -> bool.
Hypothesis Hsub : forall a, H' a = true -> H a = true.
Variable visb' : int -> Z -> Z -> bool.
Hypothesis Hvisb' : forall t o n, visb' t o n = true -> forall j, 0 <= j < n -> H' (adr rho' t (o + j)) = false.
Variable ovb' : int -> Z -> Z -> bool.
Hypothesis Hovb' : forall t o n, ovb' t o n = true -> forall j, 0 <= j < n ->
  FULL' (adr rho' t (o + j)) <> None \/ find_segment segs (bv_unsigned (adr rho' t (o + j))) 1 = None.
Variable pure_ok : AX2.kentry -> bool.
Hypothesis Hpure : forall K, pure_ok K = true -> AX2S.kentry_ok segs E' (mrestrict H' FULL') K.

Lemma know3_agree : AxSymRun3.env_agree nx E E'.
Proof. split; [|reflexivity]. intros x Hx. rewrite ev_env_of, (vt_get_new VT nx HVT x Hx). reflexivity. Qed.

(* [comment removed for export] *)
Lemma kimg_chk_sound3 lo hi :
  kimg_chk M1 lo hi = true -> forall i, lo <= i < hi -> ~ cell_expl rho' M1 (Z_to_bv 64 i).
Proof.
  unfold kimg_chk. intros Hc i Hi (t & rg & pn & p & ci & Hg & Hp & Hce & j & Hj & Ex).
  destruct (iget 0%uint63 M1) as [rg0|] eqn:Hg0; [|discriminate].
  apply andb_prop in Hc as [Hc Hpages]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo0 Hlo].
  apply Z.leb_le in Hlo0, Hlo, Hhi.
  destruct (cells_small_spec M1 Hsmall t rg pn p ci Hg Hp Hce) as (Hpn & Hci & Hplo & Hphi).
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0.
  destruct (proj1 Hmem1 t rg Hg) as [Hreg _].
  destruct Hreg as (_ & Hlen62 & Hnw & _).
  destruct (proj1 Hmem1 0%uint63 rg0 Hg0) as [(_ & Hlen0 & _) _].
  pose proof (br_u64 (rho' t)) as Hu. pose proof (i63_range (rg_lo rg)) as Hrl.
  assert (Ux : bv_unsigned (adr rho' t (to_Z pn * 4096 + to_Z ci * 8 + j))
               = bv_unsigned (rho' t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (apply adr_unsigned; lia).
  assert (Ei : i = bv_unsigned (rho' t) + (to_Z pn * 4096 + to_Z ci * 8 + j)).
  { rewrite <- Ux, <- Ex. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    symmetry. apply Z.mod_small. lia. }
  destruct (t =? 0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. rewrite Hg0 in Hg. injection Hg as <-.
    rewrite Hrho0' in Ei. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Ei.
    rewrite forallb_forall in Hpages.
    pose proof (Hpages (pn, p) (proj2 (ielements_spec (rg_pages rg0) pn p) Hp)) as Hoff. cbn [fst snd] in Hoff.
    unfold cells_off in Hoff. rewrite forallb_forall in Hoff.
    destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|contradiction].
    pose proof (Hoff (ci, c) (proj2 (ielements_spec (pg_cells p) ci c) Ec)) as Hd. cbn [fst] in Hd. cbv zeta in Hd.
    apply orb_prop in Hd as [Hd|Hd]; [apply Z.leb_le in Hd | apply Z.leb_le in Hd]; lia.
  - assert (Hne : 0%uint63 <> t) by (intros <-; rewrite Uint63.eqb_refl in Et; discriminate).
    pose proof (proj2 Hmem1 0%uint63 t rg0 rg Hne Hg0 Hg) as Hsep.
    rewrite Hrho0' in Hsep. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hsep. lia.
Qed.

(* [comment removed for export] *)
Definition cellfree_chk (t : int) (lo hi : Z) : bool :=
  match iget t M1 with
  | Some rg0 =>
      (0 <=? lo) && (to_Z (rg_lo rg0) <=? lo) && (hi <=? to_Z (rg_len rg0))
      && pages_off2 (rg_pages rg0) lo hi
  | None => false
  end.

Lemma cellfree_sound t0 lo hi :
  cellfree_chk t0 lo hi = true -> forall i, lo <= i < hi -> ~ cell_expl rho' M1 (adr rho' t0 i).
Proof.
  unfold cellfree_chk. intros Hc i Hi (t & rg & pn & p & ci & Hg & Hp & Hce & j & Hj & Ex).
  destruct (iget t0 M1) as [rg0|] eqn:Hg0; [|discriminate].
  apply andb_prop in Hc as [Hc Hpages]. apply (pages_off2_all M1 Hsmall _ rg0 _ _ Hg0) in Hpages.
  apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo0 Hlo].
  apply Z.leb_le in Hlo0, Hlo, Hhi.
  destruct (cells_small_spec M1 Hsmall t rg pn p ci Hg Hp Hce) as (Hpn & Hci & Hplo & Hphi).
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0.
  destruct (proj1 Hmem1 t rg Hg) as [Hreg _].
  destruct Hreg as (_ & Hlen62 & Hnw & _).
  destruct (proj1 Hmem1 t0 rg0 Hg0) as [(_ & Hlen0 & Hnw0 & _) _].
  pose proof (br_u64 (rho' t)) as Hu. pose proof (br_u64 (rho' t0)) as Hu0.
  pose proof (i63_range (rg_lo rg)) as Hrl. pose proof (i63_range (rg_lo rg0)) as Hrl0.
  assert (Ux : bv_unsigned (adr rho' t (to_Z pn * 4096 + to_Z ci * 8 + j))
               = bv_unsigned (rho' t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (apply adr_unsigned; lia).
  assert (Ui : bv_unsigned (adr rho' t0 i) = bv_unsigned (rho' t0) + i) by (apply adr_unsigned; lia).
  assert (Ei : bv_unsigned (rho' t0) + i = bv_unsigned (rho' t) + (to_Z pn * 4096 + to_Z ci * 8 + j)) by (rewrite <- Ux, <- Ui, Ex; reflexivity).
  destruct (t =? t0)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t. rewrite Hg0 in Hg. injection Hg as <-.
    rewrite forallb_forall in Hpages.
    pose proof (Hpages (pn, p) (proj2 (ielements_spec (rg_pages rg0) pn p) Hp)) as Hoff. cbn [fst snd] in Hoff.
    unfold cells_off in Hoff. rewrite forallb_forall in Hoff.
    destruct (iget ci (pg_cells p)) as [c|] eqn:Ec; [|contradiction].
    pose proof (Hoff (ci, c) (proj2 (ielements_spec (pg_cells p) ci c) Ec)) as Hd. cbn [fst] in Hd. cbv zeta in Hd.
    apply orb_prop in Hd as [Hd|Hd]; [apply Z.leb_le in Hd | apply Z.leb_le in Hd]; lia.
  - assert (Hne : t0 <> t) by (intros <-; rewrite Uint63.eqb_refl in Et; discriminate).
    pose proof (proj2 Hmem1 t0 t rg0 rg Hne Hg0 Hg) as Hsep. lia.
Qed.

(* [comment removed for export] *)
Definition vfchk (a : AX2.saddr) (nn : Z) : bool :=
  (nn <=? 0)
  || match aview [] M0 [] XTv a with
     | Some (t, o) => (to_Z t <? to_Z nroot) && (0 <=? o) && (o + nn <? 2 ^ 62) && cellfree_chk t o (o + nn)
     | None => false
     end.

Definition carried_cf (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => vfchk a (Z.of_nat w)
  | AX2.KZero a nn | AX2.KBlob a nn _ | AX2.KFill a nn _ | AX2.KUnk a nn | AX2.KWr a nn =>
      match len_hi kn0 nn with Some h => vfchk a h | None => false end
  | _ => false
  end.

Lemma vfchk_sound a nn nn' :
  vfchk a nn = true -> nn' <= nn ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + nn' -> ~ cell_expl rho' M1 (Z_to_bv 64 x).
Proof.
  unfold vfchk. intros Hc Hn x Hx. apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
  destruct (aview [] M0 [] XTv a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hc as [Hc Hcf0]. apply andb_prop in Hc as [Hc H62]. apply andb_prop in Hc as [Ht Ho].
  apply Z.ltb_lt in Ht, H62. apply Z.leb_le in Ho.
  assert (HM0r : forall t rg, iget t M0 = Some rg -> region_ok rho t rg) by (intros t1 rg1 Hg1; exact (proj1 (proj1 Hmem0 t1 rg1 Hg1))).
  assert (HXTv0 : xt_ok rho (AX2.ev E) (AX2.eb E) [] XTv) by (rewrite EXT; exact (xt_of_ok TT E HTT)).
  pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M0 [] XTv HM0r (rho_of_0 TT E) eq_refl HXTv0 a t o Hav) as Hs.
  rewrite env_eta in Hs.
  replace (Z_to_bv 64 x) with (adr rho' t (o + (x - AX2S.estart E a))).
  - apply (cellfree_sound t o (o + nn) Hcf0). lia.
  - unfold adr. rewrite (Hrho_lt t Ht). apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma carried_cf_sound K :
  carried_cf K = true -> AX2S.kentry_ok segs E (mrestrict H FULL) K ->
  forall x, kentry_bytes E K x -> ~ cell_expl rho' M1 (Z_to_bv 64 x).
Proof.
  intros Hc HK x Hx.
  destruct K as [a w v | a nn | a nn j | lo hi | e m0 | e lo hi | a nn | a1 n1 a2 n2 | a nn c | a nn];
    cbn [carried_cf kentry_bytes] in *; try discriminate; try contradiction.
  - exact (vfchk_sound a (Z.of_nat w) (Z.of_nat w) Hc (Z.le_refl _) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (vfchk_sound a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (vfchk_sound a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (vfchk_sound a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (vfchk_sound a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (vfchk_sound a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
Qed.

(* [comment removed for export] *)
Variable M0d : itrie region.
Hypothesis Hfr2 : forall x, H x = false -> ~ CM x -> ~ claimed_wr IM rho M0d x -> FULL' x = FULL x.
Variable nclb : AX2.saddr -> AX2.expr -> bool.
Hypothesis Hnclb : forall a nn, nclb a nn = true ->
  forall x, AX2S.estart E a <= x < AX2S.estart E a + AX2S.elenZ E nn ->
    ~ claimed_wr IM rho M0d (Z_to_bv 64 x) /\ ~ CM (Z_to_bv 64 x).

Definition carried_nc (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => Nat.leb w 8 &&& nclb a (AX2.ELit (Z.of_nat w))
  | AX2.KZero a nn | AX2.KBlob a nn _ | AX2.KFill a nn _ | AX2.KUnk a nn | AX2.KWr a nn => nclb a nn
  | _ => false
  end.

Lemma carried_nc_sound K :
  carried_nc K = true -> forall x, kentry_bytes E K x -> ~ claimed_wr IM rho M0d (Z_to_bv 64 x) /\ ~ CM (Z_to_bv 64 x).
Proof.
  intros Hc x Hx.
  destruct K as [a w v | a nn | a nn j | lo hi | e m0 | e lo hi | a nn | a1 n1 a2 n2 | a nn c | a nn];
    cbn [carried_nc kentry_bytes] in *; try discriminate; try contradiction; try exact (Hnclb _ _ Hc x Hx).
  destruct (Nat.leb w 8) eqn:Ew; [|discriminate]. apply Nat.leb_le in Ew.
  apply (Hnclb a _ Hc x). unfold AX2S.elenZ. cbn [AX2.edenot]. rewrite br_lit_small by lia. exact Hx.
Qed.

(* [comment removed for export] *)
Definition in_hull_img (K : AX2.kentry) : bool :=
  match K with AX2.KImg lo hi => (APC.img_lo A <=? lo) && (hi <=? APC.img_hi A) | _ => true end.

(* [comment removed for export] *)
Definition cmfK (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w _ => cmf a (Z.of_nat w)
  | AX2.KZero a nn | AX2.KBlob a nn _ | AX2.KFill a nn _ | AX2.KUnk a nn | AX2.KWr a nn =>
      match len_hi kn0 nn with Some h => cmf a h | None => false end
  | AX2.KImg lo hi => cmf (AX2.SA (AX2.ELit 0) lo) (hi - lo)
  | _ => false
  end.

Lemma cmfK_sound K : cmfK K = true -> forall x, kentry_bytes E K x -> ~ CM (Z_to_bv 64 x).
Proof.
  intros Hc x Hx.
  destruct K as [a w v | a nn | a nn j | lo hi | e m0 | e lo hi | a nn | a1 n1 a2 n2 | a nn c | a nn];
    cbn [cmfK kentry_bytes] in *; try discriminate; try contradiction.
  - exact (Hcmf a (Z.of_nat w) (Z.of_nat w) Hc (Z.le_refl _) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (Hcmf a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (Hcmf a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - apply (Hcmf _ _ (hi - lo) Hc (Z.le_refl _) x). unfold AX2S.estart. cbn [AX2.a_base AX2.a_off AX2.edenot].
    change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (Hcmf a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (Hcmf a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
  - destruct (len_hi kn0 nn) as [h|] eqn:Hl; [|discriminate].
    exact (Hcmf a h _ Hc (len_hi_sound segs E kn0 H FULL Hkn0 nn h Hl) x Hx).
Qed.

Definition kimgK (K : AX2.kentry) : bool := match K with AX2.KImg lo hi => kimg_fast M1 lo hi | _ => false end.

(* [comment removed for export] *)
Definition frame_alt (K : AX2.kentry) : bool := carried_chk IM TT kn0 d ra XTv M0 K ||| kimgK K ||| carried_cf K.

Lemma frame_alt_same K : frame_alt K = true -> AX2S.kentry_ok segs E (mrestrict H FULL) K ->
  forall x, kentry_bytes E K x -> H (Z_to_bv 64 x) = false -> ~ CM (Z_to_bv 64 x) -> FULL' (Z_to_bv 64 x) = FULL (Z_to_bv 64 x).
Proof.
  unfold frame_alt. intros Hc Hok x Hx Ehx Hncm.
  destruct (carried_chk IM TT kn0 d ra XTv M0 K) eqn:Hcar.
  - apply (Hfr _ Ehx Hncm). exact (carried_sound segs IM E TT kn0 H FULL d HTT Hkn0 ra Era XTv EXT M0 EM0 Hmem0 K Hcar Hok x Hx).
  - destruct (kimgK K) eqn:Hki.
    + destruct K as [ | | | lo hi | | | | | | ]; try discriminate. cbn [kimgK] in Hki. cbn [kentry_bytes] in Hx.
      exact (Hcf _ Ehx Hncm (kimg_chk_sound3 _ _ (kimg_fast_ok M1 Hsmall _ _ Hki) x Hx)).
    + exact (Hcf _ Ehx Hncm (carried_cf_sound K Hc Hok x Hx)).
Qed.

Definition imgsub (K : AX2.kentry) : bool :=
  match K with
  | AX2.KImg lo hi =>
      existsb (fun K0 => match K0 with AX2.KImg lo0 hi0 => (lo0 <=? lo) && (hi <=? hi0) | _ => false end) kn0
      &&& kimg_fast M1 lo hi
  | _ => false
  end.

Definition old_chk (K : AX2.kentry) : bool :=
  in_hull_img K
  &&& ((km K &&& (is_pure K ||| (frame_alt K &&& cmfK K) ||| carried_nc K))
       ||| (imgsub K &&& cmfK K)).

Lemma kvars_in3 : forall l K, APC.kn_vars_lt nx l = true -> In K l -> APC.kn_vars_lt nx [K] = true.
Proof.
  induction l as [|K0 r IH]; intros K Hv Hin; [destruct Hin|].
  cbn [APC.kn_vars_lt] in Hv. apply andb_prop in Hv as [H0 Hr]. destruct Hin as [->|Hin].
  - cbn [APC.kn_vars_lt]. rewrite H0. reflexivity.
  - exact (IH K Hr Hin).
Qed.

Lemma img_hidden_false i : APC.img_lo A <= i < APC.img_hi A -> H (Z_to_bv 64 i) = false.
Proof. apply Hhull. Qed.

Lemma old_sound_H K : old_chk K = true -> AX2S.kentry_ok segs E (mrestrict H FULL') K.
Proof.
  unfold old_chk. rewrite (Ekm K). intros Hc.
  destruct (in_hull_img K); [|discriminate].
  destruct (existsb (APC.kentry_eqb K) kn0) eqn:Hin.
  - apply existsb_exists in Hin as (K0 & HK0 & Heq). apply APS.kentry_eqb_eq in Heq. subst K0.
    pose proof (proj1 (Forall_forall _ _) Hkn0 K HK0) as Hok.
    destruct (is_pure K) eqn:Hp; [destruct K; try discriminate; exact Hok|].
    destruct (frame_alt K) eqn:Hfa.
    + destruct (cmfK K) eqn:Hcm.
      * apply (kentry_ok_ext segs E (mrestrict H FULL) (mrestrict H FULL') K); [|exact Hok].
        intros x Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)) eqn:Ehx; [reflexivity|].
        exact (frame_alt_same K Hfa Hok x Hx Ehx (cmfK_sound K Hcm x Hx)).
      * destruct (carried_nc K) eqn:Hnc; [|destruct (imgsub K); discriminate Hc].
        apply (kentry_ok_ext segs E (mrestrict H FULL) (mrestrict H FULL') K); [|exact Hok].
        intros x Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)) eqn:Ehx; [reflexivity|].
        destruct (carried_nc_sound K Hnc x Hx) as [N1 N2]. exact (Hfr2 _ Ehx N2 N1).
    + destruct (carried_nc K) eqn:Hnc.
      * apply (kentry_ok_ext segs E (mrestrict H FULL) (mrestrict H FULL') K); [|exact Hok].
        intros x Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)) eqn:Ehx; [reflexivity|].
        destruct (carried_nc_sound K Hnc x Hx) as [N1 N2]. exact (Hfr2 _ Ehx N2 N1).
      * (* [comment removed for export] *)
        destruct (imgsub K) eqn:His; [|discriminate Hc]. destruct (cmfK K) eqn:Hcm; [|discriminate Hc].
        destruct K as [ | | | lo hi | | | | | | ]; try discriminate. cbn [imgsub] in His.
        destruct (existsb _ kn0) eqn:Hsubr in His; [|discriminate]. 
        cbn [AX2S.kentry_ok] in *. destruct Hok as (Hk1 & Hk2 & Hk3). split; [exact Hk1|]. split; [exact Hk2|].
        intros i Hi. specialize (Hk3 i Hi). unfold mrestrict in *.
        destruct (H (Z_to_bv 64 i)) eqn:Ehx; [reflexivity|].
        rewrite (Hcf _ Ehx (cmfK_sound _ Hcm i Hi) (kimg_chk_sound3 _ _ (kimg_fast_ok M1 Hsmall _ _ His) i Hi)). exact Hk3.
  - destruct (imgsub K) eqn:His; [|discriminate Hc]. destruct (cmfK K) eqn:Hcm; [|discriminate Hc].
    destruct K as [ | | | lo hi | | | | | | ]; try discriminate. cbn [imgsub] in His.
    destruct (existsb (fun K0 => match K0 with AX2.KImg lo0 hi0 => (lo0 <=? lo) && (hi <=? hi0) | _ => false end) kn0) eqn:Hsubr; [|discriminate].
    apply existsb_exists in Hsubr as (K0 & HK0 & Hs).
    destruct K0 as [ | | | lo0 hi0 | | | | | | ]; try discriminate.
    apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1, Hs2.
    pose proof (proj1 (Forall_forall _ _) Hkn0 _ HK0) as Hok. cbn [AX2S.kentry_ok] in *.
    destruct Hok as (Hk1 & Hk2 & Hk3). split; [lia|]. split; [lia|].
    intros i Hi. specialize (Hk3 i ltac:(lia)). unfold mrestrict in *.
    destruct (H (Z_to_bv 64 i)) eqn:Ehx; [reflexivity|].
    rewrite (Hcf _ Ehx (cmfK_sound _ Hcm i Hi) (kimg_chk_sound3 _ _ (kimg_fast_ok M1 Hsmall _ _ His) i Hi)). exact Hk3.
Qed.

(* [comment removed for export] *)
Definition new_chk3 (K : AX2.kentry) : bool :=
  match K with
  | AX2.KWord a w v => kword_ok IM VT M1 [] XT' [] visb' a w v || kword_slots_ok IM VT M1 [] XT' [] visb' (slotsP IM M1) a w v   (* [comment removed for export] *)
  | AX2.KWr a n => kwr_ok IM VT M1 [] XT' visb' (xwr2 IM M1) a n      (* [comment removed for export] *)
  | AX2.KUnk a n => kunk_ok IM VT M1 [] XT' visb' ovb' (xwr2 IM M1) a n
  | AX2.KZero a n => if kzero_ok IM VT M1 [] XT' visb' ovb' (slotsP IM M1) a n then true
                     else kzero_okP IM VT M1 [] XT' visb' ovb' (slotsP IM M1) a n      (* [comment removed for export] *)
  | AX2.KFill a n c => kfill_ok IM VT M1 [] XT' visb' ovb' a n c      (* [comment removed for export] *)
  | _ => false
  end.

Lemma new_sound3 K : new_chk3 K = true -> AX2S.kentry_ok segs E' (mrestrict H' FULL') K.
Proof.
  intros Hc. destruct K as [a w v | a n | | | | | a n | | a n c | a n]; cbn [new_chk3] in Hc; try discriminate.
  + apply orb_prop in Hc as [Hc|Hc].
    * exact (kword_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' [] FULL' Hrho0' Hmem1 eq_refl HXT'
               (Forall_nil _) H' visb' Hvisb' a w v Hc).
    * apply (kword_slots_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' [] FULL' Hrho0' Hmem1 eq_refl HXT'
               (Forall_nil _) H' visb' Hvisb' (slotsP IM M1)); [exact (slotsP_sound segs IM rho' M1 FULL' Hrho0' Hmem1) | exact Hc].
  + destruct (kzero_ok IM VT M1 [] XT' visb' ovb' (slotsP IM M1) a n) eqn:Ekz.
    * apply (kzero_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' FULL' Hrho0' Hmem1 eq_refl HXT'
               H' visb' Hvisb' ovb' Hovb' (slotsP IM M1)); [exact (slotsP_sound segs IM rho' M1 FULL' Hrho0' Hmem1) | exact Ekz].
    * apply (kzeroP_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' FULL' Hrho0' Hmem1 eq_refl HXT'
               H' visb' Hvisb' ovb' Hovb' (slotsP IM M1)); [exact (slotsP_sound segs IM rho' M1 FULL' Hrho0' Hmem1) | exact Hc].
  + apply (kwr_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' FULL' Hrho0' Hmem1 eq_refl HXT'
             H' visb' Hvisb' (xwr2 IM M1)); [exact (xwr2_sound segs IM rho' M1 FULL' Hrho0' Hmem1 HIM HWR) | exact Hc].
  + exact (kfill_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' FULL' Hrho0' Hmem1 eq_refl HXT'
             H' visb' Hvisb' ovb' Hovb' a n c Hc).
  + apply (kunk_sound segs IM rho' (AX2.ev E) (AX2.eb E) VT M1 [] XT' FULL' Hrho0' Hmem1 eq_refl HXT'
             H' visb' Hvisb' ovb' Hovb' (xwr2 IM M1)); [exact (xwr2_sound segs IM rho' M1 FULL' Hrho0' Hmem1 HIM HWR) | exact Hc].
Qed.

(* [comment removed for export] *)
Definition know3_entry_chk (K : AX2.kentry) : bool := old_chk K ||| new_chk3 K ||| pure_ok K.

Lemma old_sound K : old_chk K = true -> existsb (APC.kentry_eqb K) kn0 = true \/ (match K with AX2.KImg _ _ => True | _ => False end) ->
  APC.kn_vars_lt nx [K] = true -> AX2S.kentry_ok segs E' (mrestrict H' FULL') K.
Proof.
  intros Hc _ Hv. pose proof (old_sound_H K Hc) as Hok.
  assert (Hl : AX2S.know_ok segs E (mrestrict H FULL') [K]) by (constructor; [exact Hok | constructor]).
  pose proof (APS.know_ok_agree' segs nx E E' (mrestrict H FULL') [K] know3_agree Hv Hl) as Hk.
  assert (Hki : APS.kimg_in_hull A [K]).
  { constructor; [|constructor]. unfold old_chk in Hc. apply andb_prop in Hc as [Hih _].
    destruct K; try exact I. cbn [in_hull_img] in Hih. apply andb_prop in Hih as [I1 I2]. apply Z.leb_le in I1, I2. tauto. }
  assert (Hhl : forall a : word, APS.in_hull A (bv_unsigned a) = true -> H a = false).
  { intros a Ha. unfold APS.in_hull in Ha. apply andb_prop in Ha as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
    rewrite <- (Z_to_bv_bv_unsigned _ a). apply Hhull. lia. }
  exact (Forall_inv (APS.know_ok_unhide segs A E' H H' FULL' [K] Hnoseg Hki Hsub Hhl Hk)).
Qed.

(* [comment removed for export] *)
Definition old0_chk (K : AX2.kentry) : Z :=
  if in_hull_img K &&& km K
  then (if is_pure K ||| carried_nc K then 1 else if carried_chk IM TT kn0 d ra XTv M0 K then 2 else 0)
  else 0.

Lemma old0_1 K : old0_chk K = 1 -> old_chk K = true.
Proof.
  unfold old0_chk, old_chk. destruct (in_hull_img K); [|discriminate].
  destruct (km K); [|discriminate].
  destruct (is_pure K); [reflexivity|]. destruct (carried_nc K).
  - intros _. destruct (frame_alt K); [destruct (cmfK K)|]; reflexivity.
  - destruct (carried_chk IM TT kn0 d ra XTv M0 K); discriminate.
Qed.

Lemma old0_2 K : old0_chk K = 2 -> cmfK K = true -> old_chk K = true.
Proof.
  unfold old0_chk, old_chk, frame_alt. destruct (in_hull_img K); [|discriminate].
  destruct (km K); [|discriminate].
  destruct (is_pure K); [reflexivity|]. destruct (carried_nc K); [discriminate|].
  destruct (carried_chk IM TT kn0 d ra XTv M0 K); [|discriminate]. intros _ ->. reflexivity.
Qed.

(* [comment removed for export] *)
Definition old1_chk (K : AX2.kentry) : bool :=
  in_hull_img K
  &&& ((km K &&& ((kimgK K ||| carried_cf K) &&& cmfK K)) ||| (imgsub K &&& cmfK K)).

Lemma old1_old K : old1_chk K = true -> old_chk K = true.
Proof.
  unfold old1_chk, old_chk, frame_alt. destruct (in_hull_img K); [|discriminate].
  destruct (km K); [|intros Hq; exact Hq].
  destruct (is_pure K); [reflexivity|].
  destruct (carried_chk IM TT kn0 d ra XTv M0 K); destruct (kimgK K); destruct (carried_cf K); destruct (cmfK K);
    destruct (carried_nc K); destruct (imgsub K); try reflexivity; intros Hq; discriminate Hq.
Qed.

Definition know3_entry_chk2 (Kb : AX2.kentry * Z) : bool :=
  (snd Kb =? 1) ||| ((snd Kb =? 2) &&& cmfK (fst Kb)) ||| old1_chk (fst Kb) ||| new_chk3 (fst Kb) ||| pure_ok (fst Kb).

Definition kvars_chk (K : AX2.kentry) : bool := APC.kn_vars_lt nx [K] ||| negb (old_chk K).

Theorem know3_sound kn' :
  forallb know3_entry_chk kn' = true -> forallb kvars_chk kn' = true ->
  AX2S.know_ok segs E' (mrestrict H' FULL') kn'.
Proof.
  intros Hc Hv. rewrite forallb_forall in Hc, Hv. apply Forall_forall. intros K HK.
  pose proof (Hc K HK) as H1. pose proof (Hv K HK) as H2. unfold know3_entry_chk in H1. unfold kvars_chk in H2.
  destruct (old_chk K) eqn:Eo.
  - assert (H2' : APC.kn_vars_lt nx [K] = true) by (destruct (APC.kn_vars_lt nx [K]); [reflexivity | discriminate H2]).
    apply (old_sound K Eo); [|exact H2'].
    destruct K; try (right; exact I); left; unfold old_chk in Eo; cbn [in_hull_img] in Eo; rewrite Ekm in Eo;
      (destruct (existsb _ kn0); [reflexivity | discriminate Eo]).
  - destruct (new_chk3 K) eqn:En; [exact (new_sound3 K En) | exact (Hpure K H1)].
Qed.

Lemma in_combine_map {T U : Type} (f : T -> U) : forall (l : list T) x, In x l -> In (x, f x) (combine l (map f l)).
Proof. induction l as [|y l IH]; intros x Hx; [destruct Hx|]. cbn [map combine]. destruct Hx as [->|Hx]; [left; reflexivity | right; exact (IH x Hx)]. Qed.

Theorem know3_sound2 kn' :
  forallb know3_entry_chk2 (combine kn' (map old0_chk kn')) = true -> forallb kvars_chk kn' = true ->
  AX2S.know_ok segs E' (mrestrict H' FULL') kn'.
Proof.
  intros Hc Hv. apply know3_sound; [|exact Hv]. rewrite forallb_forall in Hc. apply forallb_forall. intros K HK.
  pose proof (Hc _ (in_combine_map old0_chk kn' K HK)) as H1. unfold know3_entry_chk2 in H1. cbn [fst snd] in H1.
  unfold know3_entry_chk.
  destruct (old0_chk K =? 1) eqn:E01; [apply Z.eqb_eq in E01; rewrite (old0_1 K E01); reflexivity|].
  destruct (old0_chk K =? 2) eqn:E02.
  - apply Z.eqb_eq in E02. destruct (cmfK K) eqn:Ecm; [rewrite (old0_2 K E02 Ecm); reflexivity|].
    destruct (old1_chk K) eqn:E1; [rewrite (old1_old K E1); reflexivity|].
    destruct (old_chk K); [reflexivity | exact H1].
  - destruct (old1_chk K) eqn:E1; [rewrite (old1_old K E1); reflexivity|].
    destruct (old_chk K); [reflexivity | exact H1].
Qed.

End Know3.
