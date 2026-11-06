(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2U Require Import
  I2Inv I2NodeLib I2NodeMem I2NodeM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fseg_disj (s s' : fseg) : bool :=
  ((to_Z (sg_base s) + to_Z (sg_size s) <=? to_Z (sg_base s'))%Z || (to_Z (sg_base s') + to_Z (sg_size s') <=? to_Z (sg_base s))%Z).
Fixpoint fsegs_disjoint_b (l : fimage) : bool :=
  match l with
  | [] => true
  | s :: r => forallb (fseg_disj s) r && fsegs_disjoint_b r
  end.

Lemma find_seg_range : forall l a sg, find_seg l a = Some sg ->
  In sg l /\ to_Z (sg_base sg) <= to_Z a < to_Z (sg_base sg) + to_Z (sg_size sg).
Proof.
  intros l a sg H. destruct (find_seg_spec _ _ _ H) as (Hin & H1 & H2). split; [exact Hin|].
  apply Uint63.leb_spec in H1. apply Uint63.ltb_spec in H2. rewrite Uint63.add_spec in H2.
  pose proof (i63_range (sg_base sg)). pose proof (i63_range (sg_size sg)). pose proof (i63_range a).
  pose proof (Z.mod_le (to_Z (sg_base sg) + to_Z (sg_size sg)) wB ltac:(slia) ltac:(change wB with (2 ^ 63); slia)). slia.
Qed.

Lemma find_seg_im_ro : forall l a sg, fsegs_disjoint_b l = true ->
  find_seg (im_ro l) a = Some sg -> find_seg l a = Some sg.
Proof.
  induction l as [|s r IH]; intros a sg Hd H; [exact H|].
  cbn [fsegs_disjoint_b] in Hd. apply andb_true_iff in Hd as [Hs Hr].
  unfold im_ro in H. cbn [List.filter] in H. change (List.filter (fun sg : fseg => negb (sg_wr sg)) r) with (im_ro r) in H.
  cbn [find_seg].
  destruct (sg_wr s); cbn [negb] in H.
  - (* [comment removed for export] *)
    pose proof (IH a sg Hr H) as Hf. destruct (find_seg_range _ _ _ Hf) as [Hin Hrange].
    destruct ((sg_base s <=? a)%uint63 && (a <? sg_base s + sg_size s)%uint63) eqn:E; [|exact Hf].
    exfalso. apply andb_true_iff in E as [E1 E2]. apply Uint63.leb_spec in E1. apply Uint63.ltb_spec in E2.
    rewrite Uint63.add_spec in E2.
    pose proof (i63_range (sg_base s)). pose proof (i63_range (sg_size s)). pose proof (i63_range a).
    pose proof (Z.mod_le (to_Z (sg_base s) + to_Z (sg_size s)) wB ltac:(slia) ltac:(change wB with (2 ^ 63); slia)).
    rewrite forallb_forall in Hs. specialize (Hs sg Hin). unfold fseg_disj in Hs. apply orb_true_iff in Hs.
    destruct Hs as [Hs|Hs]; apply Z.leb_le in Hs; slia.
  - cbn [find_seg] in H. destruct ((sg_base s <=? a)%uint63 && (a <? sg_base s + sg_size s)%uint63); [exact H|].
    exact (IH a sg Hr H).
Qed.

Section ImRo.
  Variable segs : list Segment.
  Variable IMX : fimage.
  Variable rho : int -> word.
  Hypothesis Hdisj : fsegs_disjoint_b IMX = true.

  Definition no_img_pages (M : itrie region) : Prop :=
    (forall rg0, iget 0%uint63 M = Some rg0 -> rg_dflt rg0 = None)
    /\ (forall t rg pn p, iget t M = Some rg -> iget pn (rg_pages rg) = Some p -> pg_kind p <> PKImage).

  Lemma image_cell_im_ro : forall a v, image_cell (im_ro IMX) a = Some v -> image_cell IMX a = Some v.
  Proof.
    intros a v H. unfold image_cell in *. destruct (find_seg (im_ro IMX) a) as [sg|] eqn:E; [|discriminate].
    rewrite (find_seg_im_ro _ _ _ Hdisj E). exact H.
  Qed.

  Lemma cell_at_im_ro : forall p pn ci v, cell_at (im_ro IMX) p pn ci = Some v -> cell_at IMX p pn ci = Some v.
  Proof.
    intros p pn ci v H. unfold cell_at in *. destruct (iget ci (pg_cells p)) as [c|]; [exact H|].
    destruct (pg_kind p); try exact H. apply image_cell_im_ro. exact H.
  Qed.

  Lemma page_ok_im_ro : forall m t pn L p, page_ok segs IMX rho m t pn L p -> page_ok segs (im_ro IMX) rho m t pn L p.
  Proof.
    intros m t pn L p (Hw & Hc & Hs & Hcut). split; [exact Hw|]. split; [|split; [exact Hs|]].
    - intros ci v Hci Hcell. apply (Hc ci v Hci). apply cell_at_im_ro. exact Hcell.
    - intros ci Hci Hb. destruct (cell_at (im_ro IMX) p pn ci) as [v|] eqn:E; [|reflexivity].
      pose proof (Hcut ci Hci Hb) as Hn. pose proof (cell_at_im_ro _ _ _ _ E). congruence.
  Qed.

  Lemma mem_ok_im_ro : forall M m, no_img_pages M -> mem_ok segs IMX rho M m -> mem_ok segs (im_ro IMX) rho M m.
  Proof.
    intros M m [Hd0 Hk] [Hregs Hsep]. split; [|exact Hsep].
    intros t rg Ht. destruct (Hregs t rg Ht) as [Hro Hpages]. split; [exact Hro|].
    intros pn p Hpn Hp.
    assert (HpX : page_at IMX rg t pn = Some p).
    { unfold page_at in Hp |- *. destruct (iget pn (rg_pages rg)) as [p0|] eqn:Ep; [exact Hp|].
      destruct (t =? 0)%uint63 eqn:Et.
      - destruct (find_seg (im_ro IMX) (pn << 12)%uint63) as [sg|] eqn:Ef.
        + rewrite (find_seg_im_ro _ _ _ Hdisj Ef). exact Hp.
        + apply Uint63.eqb_spec in Et. subst t. rewrite (Hd0 rg Ht) in Hp. discriminate.
      - exact Hp. }
    destruct (Hpages pn p Hpn HpX) as (Hok & Hb). split; [apply page_ok_im_ro; exact Hok | exact Hb].
  Qed.

  Lemma R_im_ro : forall F ms, no_img_pages (f_mem F) -> R segs IMX rho F ms -> R segs (im_ro IMX) rho F ms.
  Proof.
    intros F ms Hn [Hpc Hregs Hsvc Hresv Hmem]. constructor; try assumption. apply mem_ok_im_ro; assumption.
  Qed.
End ImRo.

Lemma Rn_im_ro : forall segs IMX n rho F ms, fsegs_disjoint_b IMX = true -> no_img_pages (f_mem F) ->
  Rn segs IMX n rho F ms -> Rn segs (im_ro IMX) n rho F ms.
Proof. intros segs IMX n rho F ms Hd Hn HR rho' Hag. apply R_im_ro; [exact Hd | exact Hn | exact (HR rho' Hag)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shape.
  Variable K : i2consts.
  Variable IMX : fimage.
  Open Scope uint63_scope.

  Definition tag_is_blk (blk : list (int * int)) (t : int) : bool := existsb (fun tn => fst tn =? t) blk.

  Definition region0_shape_ok (rg : region) : bool :=
    (rg_lo rg =? 65536) && (rg_len rg =? 3506176)
    && match rg_dflt rg with None => true | Some _ => false end
    && iall (fun pn p => seg_wr_page IMX pn && match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg).

  Definition region1_shape_ok (rg : region) : bool :=
    (rg_lo rg =? 0) && (rg_len rg =? c_stack K) && match rg_dflt rg with Some PKUnk => true | _ => false end
    && iall (fun pn p => match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg).

  Definition blk_shape_ok (n : int) (rg : region) : bool :=
    (rg_lo rg =? 0) && (rg_len rg =? n) && match rg_dflt rg with Some PKUnk => true | _ => false end
    && iall (fun pn p => match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg) && (1 <=? n).

  Definition cells_inb_b (M : itrie region) : bool :=
    iall (fun t rg => iall (fun pn p => iall (fun ci c =>
            (to_Z pn * 4096 + to_Z ci * 8 + 8 <=? to_Z (rg_len rg))%Z && (ci <? 512)) (pg_cells p)) (rg_pages rg)) M.

  Fixpoint nodupb (l : list int) : bool :=
    match l with [] => true | x :: r => negb (existsb (Uint63.eqb x) r) && nodupb r end.

  Definition start_shape_ok (st : i2st) : bool :=
    let M := f_mem (i_F st) in
    fsegs_disjoint_b IMX
    && match iget 0 M with Some rg => region0_shape_ok rg | None => false end
    && match iget 1 M with Some rg => region1_shape_ok rg | None => false end
    && forallb (fun tn : int * int => match iget (fst tn) M with Some rg => blk_shape_ok (snd tn) rg | None => false end
                                      && (2 <=? fst tn) && (fst tn <? i_n st)) (i_blk st)
    && iall (fun t _ => (t =? 0) || (t =? 1) || tag_is_blk (i_blk st) t) M
    && cells_inb_b M
    && nodupb (map fst (i_blk st))
    && (c_tra K <? i_n st) && (2 <=? c_tra K).
End Shape.

Lemma nodupb_spec : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|x r IH]; intros H; [constructor|]. cbn in H. apply andb_true_iff in H as [H1 H2].
  constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (existsb (Uint63.eqb x) r = true); [|congruence]. apply existsb_exists. exists x. split; [exact Hin | apply Uint63.eqb_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Start.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable IMX : fimage.
  Variable K : i2consts.
  Let IM := im_ro IMX.
  Hypothesis HK : K_ok K = true.
  Hypothesis HHx : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HHx.

  Theorem i2_start : forall (st0 : i2st) (G0 : list gblk) (rho0 : int -> word)
      (x : Z -> word) (Fr : bvmap 5 word) (pc : int) (fc : bv 32) (m : mem) (mo : Model)
      (s : PState) (LB : list block) (lo B : Z),
    start_shape_ok K IMX st0 = true ->
    start_ok K st0 = true ->
    i_blk st0 = map (fun g => (g_tag g, g_size g)) G0 ->
    List.NoDup (map g_id G0) ->
    Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) LB /\ rho0 (g_tag g) = wa (g_addr g)
                     /\ stk usegs m (g_addr g) (g_addr g + to_Z (g_size g))) G0 ->
    Rn usegs IMX (i_n st0) rho0 (i_F st0)
       (MS (mkRl (map x [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]))
           Fr (Z_to_bv 64 (to_Z (f_pc (i_F st0)))) fc None m (seg_rom usegs)) ->
    rho0 0%uint63 = Z_to_bv 64 0 ->
    rho0 1%uint63 = wa (bv_unsigned (x 2) - to_Z (c_stack K)) ->
    hs_RHEAP H s LB m -> hs_KREL H s mo ->
    lb_bytes LB + to_Z (c_cost K) <= hs_LIVE_MAX H -> Z.of_nat (length LB) + to_Z (c_cnt K) <= hs_LIVE_CNT_MAX H ->
    lb_big LB + to_Z (c_big K) <= hs_LIVE_BIG_MAX H ->
    hs_rauxv_ok H m B -> bv_unsigned (x 2) <= B -> B < 2 ^ 64 ->
    stk usegs m lo (bv_unsigned (x 2)) -> hceil <= lo -> lo <= bv_unsigned (x 2) - to_Z (c_stack K) -> bv_unsigned (x 2) mod 16 = 0 ->
    rw_cells usegs m (errA K) [C4 (x 0)] -> mem_inv usegs m ->
    I2R H IMX K (I2E (bv_unsigned (x 2)) lo B mo Fr fc m LB (i_n st0) rho0 G0) st0 rho0
        (MS (mkRl (map x [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]))
            Fr (Z_to_bv 64 (to_Z (f_pc (i_F st0)))) fc None m (seg_rom usegs)) mo.
  Proof.
    intros st0 G0 rho0 x Fr pc fc m mo s LB lo B Hshape Hstart HG Hnd HG0 HRn Hr0 Hr1 Hheap Hkrel Hcst Hcnt Hbg Haux HB HB64 Hstk Hhl Hlo Hsp16 Herr Hinv.
    (* [comment removed for export] *)
    unfold start_shape_ok in Hshape. cbv zeta in Hshape. rewrite !andb_true_iff in Hshape.
    destruct Hshape as [[[[[[[[Hdisj Hr0s] Hr1s] Hblks] Hdom] Hinb] Hndt] Htra] Htra2].
    unfold start_ok in Hstart. rewrite !andb_true_iff in Hstart.
    destruct Hstart as [[[[[[[Hn2 Hn59] Hcost0] Hcnt0] Hbig0] Hblk2] Hep] Hrv].
    apply Uint63.leb_spec in Hn2. apply Uint63.ltb_spec in Hn59. change (to_Z 2%uint63) with 2 in Hn2.
    apply Uint63.eqb_spec in Hcost0. apply Uint63.eqb_spec in Hcnt0. apply Uint63.eqb_spec in Hbig0.
    apply Uint63.ltb_spec in Htra. apply Uint63.leb_spec in Htra2. change (to_Z 2%uint63) with 2 in Htra2.
    destruct (iget 0%uint63 (f_mem (i_F st0))) as [rg0|] eqn:E0; [|discriminate].
    destruct (iget 1%uint63 (f_mem (i_F st0))) as [rg1|] eqn:E1; [|discriminate].
    unfold region0_shape_ok in Hr0s. rewrite !andb_true_iff in Hr0s. destruct Hr0s as [[[Hlo0 Hlen0] Hd0] Hp0].
    apply Uint63.eqb_spec in Hlo0. apply Uint63.eqb_spec in Hlen0.
    destruct (rg_dflt rg0) eqn:Ed0; [discriminate|]. rewrite iall_spec in Hp0.
    unfold region1_shape_ok in Hr1s. rewrite !andb_true_iff in Hr1s. destruct Hr1s as [[[Hlo1 Hlen1] Hd1] Hp1].
    apply Uint63.eqb_spec in Hlo1. apply Uint63.eqb_spec in Hlen1.
    destruct (rg_dflt rg1) as [[| |]|] eqn:Ed1; try discriminate. rewrite iall_spec in Hp1.
    rewrite forallb_forall in Hblks. rewrite iall_spec in Hdom. unfold cells_inb_b in Hinb. rewrite iall_spec in Hinb.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ Hheap) as HndLB.
    (* [comment removed for export] *)
    assert (Hblk : forall g, In g G0 ->
              2 <= to_Z (g_tag g) < to_Z (i_n st0) /\ 1 <= to_Z (g_size g)
              /\ exists rg, iget (g_tag g) (f_mem (i_F st0)) = Some rg /\ rg_lo rg = 0%uint63 /\ rg_len rg = g_size g
                            /\ rg_dflt rg = Some PKUnk /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_kind p = PKUnk).
    { intros g Hg. specialize (Hblks (g_tag g, g_size g) ltac:(rewrite HG; apply in_map_iff; exists g; split; [reflexivity | exact Hg])).
      cbn [fst snd] in Hblks. rewrite !andb_true_iff in Hblks. destruct Hblks as [[Hsh Ht2] Htn].
      apply Uint63.leb_spec in Ht2. apply Uint63.ltb_spec in Htn. change (to_Z 2%uint63) with 2 in Ht2.
      destruct (iget (g_tag g) (f_mem (i_F st0))) as [rg|] eqn:Eg; [|discriminate].
      unfold blk_shape_ok in Hsh. rewrite !andb_true_iff in Hsh. destruct Hsh as [[[[Hl Hn] Hd] Hk] Hsz].
      apply Uint63.eqb_spec in Hl. apply Uint63.eqb_spec in Hn. apply Uint63.leb_spec in Hsz. change (to_Z 1%uint63) with 1 in Hsz.
      destruct (rg_dflt rg) as [[| |]|] eqn:Edg; try discriminate. rewrite iall_spec in Hk.
      split; [slia|]. split; [exact Hsz|]. exists rg. repeat (split; [first [reflexivity | assumption]|]).
      intros pn p Hp. specialize (Hk pn p Hp). destruct (pg_kind p); try discriminate. reflexivity. }
    exists s, LB, G0.
    constructor; cbn [q_sp0 q_lo q_B q_mo0 q_F q_fc q_m0 q_LB0 q_n0 q_rho0 q_G0 ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS].
    - (* [comment removed for export] *)
      apply Rn_im_ro; [exact Hdisj | | exact HRn]. split.
      + intros rg0' H0'. rewrite E0 in H0'. injection H0' as <-. exact Ed0.
      + intros t rg pn p Ht Hp. specialize (Hdom t rg Ht). rewrite !orb_true_iff in Hdom.
        destruct Hdom as [[Ht0 | Ht1] | Htb].
        * apply Uint63.eqb_spec in Ht0. subst t. rewrite E0 in Ht. injection Ht as <-.
          specialize (Hp0 pn p Hp). apply andb_true_iff in Hp0 as [_ Hkd]. destruct (pg_kind p); try discriminate.
        * apply Uint63.eqb_spec in Ht1. subst t. rewrite E1 in Ht. injection Ht as <-.
          specialize (Hp1 pn p Hp). destruct (pg_kind p); try discriminate.
        * unfold tag_is_blk in Htb. apply existsb_exists in Htb as ([t' n'] & Hin & Et). cbn [fst] in Et. apply Uint63.eqb_spec in Et. subst t'.
          rewrite HG in Hin. apply in_map_iff in Hin as (g & Eg & Hg). injection Eg as Etg En.
          destruct (Hblk g Hg) as (_ & _ & rg' & Hrg' & _ & _ & _ & Hk). rewrite Etg, Ht in Hrg'. injection Hrg' as <-.
          rewrite (Hk pn p Hp). discriminate.
    - apply canonR_mkR.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hr0.
    - exact Hr1.
    - apply agree_refl. exact Hr0.
    - change (to_Z two59) with (2 ^ 59) in Hn59. slia.
    - exact Hheap.
    - exact Hkrel.
    - apply (mpres_refl H HH).
    - exact HG.
    - apply Forall_forall. intros g Hg. destruct (proj1 (Forall_forall _ _) HG0 g Hg) as (Hin & Hrho & _).
      destruct (Hblk g Hg) as (Htg & Hsz & rg & Hrg & Hl & Hn & _ & _).
      split; [exact Hin|]. split; [exact Hrho|]. split; [exact Hsz|]. split; [exact Htg|]. exists rg. split; [exact Hrg | split; assumption].
    - exact Hnd.
    - rewrite HG, map_map in Hndt. cbn [fst] in Hndt. exact (nodupb_spec _ Hndt).
    - apply Forall_forall. intros g Hg. left. exact Hg.
    - apply Forall_forall. intros g Hg. exact (proj2 (proj2 (proj1 (Forall_forall _ _) HG0 g Hg))).
    - intros t rg Ht. specialize (Hdom t rg Ht). rewrite !orb_true_iff in Hdom. destruct Hdom as [[Ht0 | Ht1] | Htb].
      + left. apply Uint63.eqb_spec in Ht0. exact Ht0.
      + right. left. apply Uint63.eqb_spec in Ht1. exact Ht1.
      + right. right. unfold tag_is_blk in Htb. apply existsb_exists in Htb as ([t' n'] & Hin & Et). cbn [fst] in Et. apply Uint63.eqb_spec in Et. subst t'.
        rewrite HG in Hin. apply in_map_iff in Hin as (g & Eg & Hg). injection Eg as Etg En. rewrite <- Etg. apply in_map. exact Hg.
    - exists rg0. split; [exact E0|]. split; [rewrite Hlo0; reflexivity|]. split; [rewrite Hlen0; reflexivity|]. split; [exact Ed0|].
      intros pn p Hp. specialize (Hp0 pn p Hp). apply andb_true_iff in Hp0 as [Hw Hkd]. split; [exact Hw|]. destruct (pg_kind p); try discriminate. reflexivity.
    - exists rg1. split; [exact E1|]. split; [exact Hlo1|]. split; [exact Hlen1 | exact Ed1].
    - exists rg0. split; [exact E0|]. intros c u Hc. pose proof (ro_of_range K HK c u Hc) as Hr.
      rewrite Hlo0, Hlen0. change (to_Z 65536%uint63) with 65536. change (to_Z 3506176%uint63) with 3506176. slia.
    - intros t rg pn p ci c Ht Hp Hcc. specialize (Hinb t rg Ht). rewrite iall_spec in Hinb. specialize (Hinb pn p Hp). rewrite iall_spec in Hinb.
      specialize (Hinb ci c Hcc). apply andb_true_iff in Hinb as [H1 H2]. apply Z.leb_le in H1. apply Uint63.ltb_spec in H2. change (to_Z 512%uint63) with 512 in H2.
      split; [slia | split; [exact H2 | intros; exact H1]].
    - intros t rg Ht Ht0. specialize (Hdom t rg Ht). rewrite !orb_true_iff in Hdom. destruct Hdom as [[Ht0' | Ht1] | Htb].
      + apply Uint63.eqb_spec in Ht0'. congruence.
      + apply Uint63.eqb_spec in Ht1. subst t. rewrite E1 in Ht. injection Ht as <-. split; [exact Ed1|].
        intros pn p Hp. specialize (Hp1 pn p Hp). destruct (pg_kind p); try discriminate. reflexivity.
      + unfold tag_is_blk in Htb. apply existsb_exists in Htb as ([t' n'] & Hin & Et). cbn [fst] in Et. apply Uint63.eqb_spec in Et. subst t'.
        rewrite HG in Hin. apply in_map_iff in Hin as (g & Eg & Hg). injection Eg as Etg En.
        destruct (Hblk g Hg) as (_ & _ & rg' & Hrg' & _ & _ & Hd & Hk). rewrite Etg, Ht in Hrg'. injection Hrg' as <-. split; [exact Hd | exact Hk].
    - rewrite Hcost0. change (to_Z 0%uint63) with 0. pose proof (i63_range (c_cost K)). slia.
    - rewrite Hcnt0. change (to_Z 0%uint63) with 0. pose proof (i63_range (c_cnt K)). slia.
    - rewrite Hbig0. change (to_Z 0%uint63) with 0. pose proof (i63_range (c_big K)). slia.
    - exact Hstk.
    - repeat split; assumption.
    - exact Haux.
    - exact Hinv.
    - pose proof (stk_of_rw_cells usegs m (errA K) [C4 (x 0)] Herr) as Hs. cbn [cells_size csize] in Hs.
      replace (errA K + Z.of_nat 4) with (errA K + 4) in Hs by slia. exact Hs.
    - intros b Hb _. exact Hb.
    - intros b Hb. pose proof (HH_RHEAP_block_range H HH _ _ _ b Hheap Hb) as (R1 & R2 & R3 & R4 & R5). slia.
    - split; [|exact HndLB]. apply Forall_forall. intros g Hg. exact (proj1 (proj1 (Forall_forall _ _) HG0 g Hg)).
    - intros b Hb. left. exact Hb.
    - intros. reflexivity.
  Qed.
End Start.
