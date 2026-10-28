(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX CellsX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA I2Start.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeM I2ACert.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Section Shape.
  Variable A : i2aconsts.
  Let K := ka_K A.
  Variable IMX : fimage.
  Open Scope uint63_scope.

  Definition region0_shape_okA (rg : region) : bool :=
    (rg_lo rg =? 65536) && (to_Z (rg_len rg) =? AIMG_TOP)%Z
    && match rg_dflt rg with None => true | Some _ => false end
    && iall (fun pn p => seg_wr_page IMX pn && match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg).

  Definition region1_shape_okA (rg : region) : bool :=
    (rg_lo rg =? 0) && (rg_len rg =? c_stack K) && match rg_dflt rg with Some PKUnk => true | _ => false end
    && match rg_kind rg with RK_plain => true | _ => false end && (to_Z (rg_align rg) =? 5)%Z
    && iall (fun pn p => match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg).

  Definition blk_shape_okA (n : int) (rg : region) : bool :=
    (rg_lo rg =? 0) && (rg_len rg =? n) && match rg_dflt rg with Some PKUnk => true | _ => false end
    && match rg_kind rg with RK_plain => true | _ => false end && (3 <=? to_Z (rg_align rg))%Z
    && iall (fun pn p => match pg_kind p with PKUnk => true | _ => false end) (rg_pages rg) && (1 <=? n).

  (* [comment removed for export] *)
  Definition tags_apart_b (l : list int) : bool :=
    forallb (fun t => forallb (fun t' => (t =? t') || (to_Z t + 2 <=? to_Z t')%Z || (to_Z t' + 2 <=? to_Z t)%Z) l) l.

  Definition start_shape_okA (st : i2ast) : bool :=
    let M := f_mem (a_F st) in
    fsegs_disjoint_b IMX
    && match iget 0 M with Some rg => region0_shape_okA rg | None => false end
    && match iget 1 M with Some rg => region1_shape_okA rg | None => false end
    && forallb (fun tn : int * int => match iget (fst tn) M with Some rg => blk_shape_okA (snd tn) rg | None => false end
                                      && (4 <=? fst tn) && (fst tn + 1 <? a_n st) && (fst tn <? kind_lim)) (a_blk st)
    && iall (fun t _ => (t =? 0) || (t =? 1) || tag_is_blk (a_blk st) t) M
    && cells_inb_b M
    && nodupb (map fst (a_blk st)) && tags_apart_b (map fst (a_blk st))
    && (c_tra K <? a_n st) && (ka_ts0 A <? a_n st) && (4 <=? a_n st) && (a_n st <? I2ACert.b60)
    && match a_ff st with [] => true | _ => false end
    && (a_cost st =? 0) && (a_cnt st =? 0)
    && (1 <=? c_stack K) && (c_stack K <=? 32768).
End Shape.

Lemma nodup_map_inj {T U} (f : T -> U) (l : list T) a b :
  List.NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  induction l as [|y l IH]; intros ND Ha Hb E; [destruct Ha|].
  cbn [map] in ND. inversion ND as [|y' l' Hy Hl]; subst.
  destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb]; [reflexivity | | | exact (IH Hl Ha Hb E)].
  - exfalso. apply Hy. rewrite E. apply in_map. exact Hb.
  - exfalso. apply Hy. rewrite <- E. apply in_map. exact Ha.
Qed.

(* [comment removed for export] *)
Section Start.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Let K := ka_K A.
  Let IM := im_ro IMX.
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Definition L31 := I2ACert.L31.

  Theorem i2a_start : forall (st0 : i2ast) (G0 : list gblk) (rho0 : int -> word)
      (x : Z -> word) (Fr : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
      (s : as_St H) (LB : list block) (LF : list fframe) (lo B : Z) (CH : list (Z * Z)),
    let sp := bv_unsigned (x 2) in
    let ms := MS (mkRl (map x L31)) Fr (Z_to_bv 64 (to_Z (f_pc (a_F st0)))) fc None m (seg_rom asegs) in
    start_shape_okA A IMX st0 = true ->
    a_cs st0 = [] ->
    a_blk st0 = map (fun g => (g_tag g, g_size g)) G0 ->
    List.NoDup (map g_id G0) ->
    Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) LB /\ rho0 (g_tag g) = wa (g_addr g)
                     /\ stk asegs m (g_addr g) (g_addr g + to_Z (g_size g))) G0 ->
    Rn asegs IMX (a_n st0) rho0 (a_F st0) ms ->
    rho0 0%uint63 = Z_to_bv 64 0 -> rho0 1%uint63 = wa (sp - to_Z (c_stack K)) ->
    rho0 2%uint63 = wa (sh (sp - to_Z (c_stack K))) -> rho0 3%uint63 = Z_to_bv 64 0 ->
    as_VIS H s msF = ms -> as_AKREL H s (mkCfg msF mo) ->
    as_RHEAP H s LB m -> as_RFS H LF m -> ACONST m -> stack0 m lo sp ->
    as_chain H m (bv_unsigned (rho0 (ka_ts0 A))) CH -> (forall fp ra, In (fp, ra) CH -> sp + 16 <= fp) ->
    pf_ok (as_TR H) (map (fun e : int * list int => (to_Z (fst e), map to_Z (snd e))) (ka_pfo A)) (bv_unsigned (rho0 (c_tra K))) CH ->
    csum H (ka_costs A) <= as_AL H s ->
    lb_bytes LB + to_Z (c_cost K) <= as_LIVE_MAX H -> Z.of_nat (length LB) + to_Z (c_cnt K) <= as_LIVE_CNT_MAX H ->
    (length LF + Z.to_nat (to_Z (ka_fsmax A)) <= AFS_MAXLIVE)%nat ->
    as_rauxv_ok H m B -> sp <= B -> sp < 2 ^ 64 ->
    stk asegs m lo sp -> aceil <= lo -> lo <= sp - to_Z (c_stack K) -> sp mod 16 = 0 -> (sp - to_Z (c_stack K)) mod 32 = 0 ->
    rw_cells asegs m (errA A) [C4 (x 0)] -> mem_inv asegs m ->
    I2RA H IMX A (I2AE sp lo B sp mo Fr fc m LB LF (a_n st0) rho0 G0 (bv_unsigned (rho0 (ka_ts0 A))) CH (as_AL H s) (ka_costs A))
         (a_start A st0) rho0 msF mo.
  Proof.
    intros st0 G0 rho0 x Fr fc msF m mo s LB LF lo B CH sp ms Hshape Hcs HG Hnd HG0 HRn Hr0 Hr1 Hr2 Hr3
           Hvis Hakrel Hheap Hrfs Hac Hst0 Hchain HCH Hpfo HAL Hcst Hcnt Hlf Haux HB HB64 Hstk Hhl Hlo Hsp16 Hsp32 Herr Hinv.
    unfold K in *. set (cs := to_Z (c_stack (ka_K A))) in *.
    (* [comment removed for export] *)
    unfold start_shape_okA in Hshape. cbv zeta in Hshape. rewrite !andb_true_iff in Hshape.
    destruct Hshape as [[[[[[[[[[[[[[[[Hdisj Hr0s] Hr1s] Hblks] Hdom] Hinb] Hndt] Hapart] Htra] Hts0] Hn4] Hn60] Hff] Hcost0] Hcnt0] Hcs1] Hcs2].
    apply Uint63.ltb_spec in Htra. apply Uint63.ltb_spec in Hts0. apply Uint63.leb_spec in Hn4. apply Uint63.ltb_spec in Hn60.
    change (to_Z 4%uint63) with 4 in Hn4. change (to_Z I2ACert.b60) with (2 ^ 60) in Hn60.
    apply Uint63.eqb_spec in Hcost0. apply Uint63.eqb_spec in Hcnt0.
    apply Uint63.leb_spec in Hcs1. apply Uint63.leb_spec in Hcs2. change (to_Z 1%uint63) with 1 in Hcs1. change (to_Z 32768%uint63) with 32768 in Hcs2.
    destruct (a_ff st0) as [|ff0 ffr] eqn:Eff; [|discriminate].
    destruct (iget 0%uint63 (f_mem (a_F st0))) as [rg0|] eqn:E0; [|discriminate].
    destruct (iget 1%uint63 (f_mem (a_F st0))) as [rg1|] eqn:E1; [|discriminate].
    unfold region0_shape_okA in Hr0s. rewrite !andb_true_iff in Hr0s. destruct Hr0s as [[[Hlo0 Hlen0] Hd0] Hp0].
    apply Uint63.eqb_spec in Hlo0. apply Z.eqb_eq in Hlen0.
    destruct (rg_dflt rg0) eqn:Ed0; [discriminate|]. rewrite iall_spec in Hp0.
    unfold region1_shape_okA in Hr1s. rewrite !andb_true_iff in Hr1s. destruct Hr1s as [[[[[Hlo1 Hlen1] Hd1] Hk1] Ha1] Hp1].
    apply Uint63.eqb_spec in Hlo1. apply Uint63.eqb_spec in Hlen1. apply Z.eqb_eq in Ha1.
    destruct (rg_dflt rg1) as [[| |]|] eqn:Ed1; try discriminate. destruct (rg_kind rg1) eqn:Ekd1; [|discriminate]. rewrite iall_spec in Hp1.
    rewrite forallb_forall in Hblks. rewrite iall_spec in Hdom. unfold cells_inb_b in Hinb. rewrite iall_spec in Hinb.
    (* [comment removed for export] *)
    assert (Hblk : forall g, In g G0 ->
              4 <= to_Z (g_tag g) /\ to_Z (g_tag g) + 1 < to_Z (a_n st0) /\ 1 <= to_Z (g_size g)
              /\ exists rg, iget (g_tag g) (f_mem (a_F st0)) = Some rg /\ rg_lo rg = 0%uint63 /\ rg_len rg = g_size g
                            /\ rg_dflt rg = Some PKUnk /\ rg_kind rg = RK_plain /\ 3 <= to_Z (rg_align rg)
                            /\ forall pn p, iget pn (rg_pages rg) = Some p -> pg_kind p = PKUnk).
    { intros g Hg. specialize (Hblks (g_tag g, g_size g) ltac:(rewrite HG; apply in_map_iff; exists g; split; [reflexivity | exact Hg])).
      cbn [fst snd] in Hblks. rewrite !andb_true_iff in Hblks. destruct Hblks as [[[Hsh Ht4] Htn] Hkl].
      apply Uint63.leb_spec in Ht4. apply Uint63.ltb_spec in Htn. apply Uint63.ltb_spec in Hkl. change (to_Z 4%uint63) with 4 in Ht4.
      change (to_Z kind_lim) with (2 ^ 60) in Hkl.
      pose proof (i63_range (g_tag g)). pose proof (i63_range (a_n st0)).
      rewrite to_Z_add_small in Htn by (change (to_Z 1%uint63) with 1; slia). change (to_Z 1%uint63) with 1 in Htn.
      destruct (iget (g_tag g) (f_mem (a_F st0))) as [rg|] eqn:Eg; [|discriminate].
      unfold blk_shape_okA in Hsh. rewrite !andb_true_iff in Hsh. destruct Hsh as [[[[[[Hl Hn] Hd] Hkd] Hal] Hk] Hsz].
      apply Uint63.eqb_spec in Hl. apply Uint63.eqb_spec in Hn. apply Z.leb_le in Hal. apply Uint63.leb_spec in Hsz. change (to_Z 1%uint63) with 1 in Hsz.
      destruct (rg_dflt rg) as [[| |]|] eqn:Edg; try discriminate. destruct (rg_kind rg) eqn:Ekg; [|discriminate]. rewrite iall_spec in Hk.
      split; [exact Ht4|]. split; [exact Htn|]. split; [exact Hsz|]. exists rg. repeat (split; [first [reflexivity | assumption]|]).
      intros pn p Hp. specialize (Hk pn p Hp). destruct (pg_kind p); try discriminate. reflexivity. }
    pose proof (i63_range (a_n st0)) as Hnr. pose proof (i63_range (c_stack (ka_K A))) as Hcsr. fold cs in Hcsr.
    pose proof aceil_facts as ACF.
    assert (HndLB : List.NoDup (map blk_id LB)) by exact (ah_nodup H HH _ _ _ Hheap).
    assert (Hgblk : forall g, In g G0 -> ablock_range H (g_addr g) (to_Z (g_size g))).
    { intros g Hg. destruct (proj1 (Forall_forall _ _) HG0 g Hg) as [Hin _].
      exact (ah_blocks H HH _ _ _ _ Hheap Hin). }
    (* [comment removed for export] *)
    assert (Htags : forall t, In t (map g_tag G0) -> exists g, In g G0 /\ g_tag g = t).
    { intros t Ht. apply in_map_iff in Ht as (g & <- & Hg). exists g. auto. }
    assert (Hapart2 : forall g g', In g G0 -> In g' G0 -> g <> g' -> to_Z (g_tag g) + 2 <= to_Z (g_tag g') \/ to_Z (g_tag g') + 2 <= to_Z (g_tag g)).
    { intros g g' Hg Hg' Hne. unfold tags_apart_b in Hapart. rewrite forallb_forall in Hapart.
      specialize (Hapart (g_tag g) ltac:(rewrite HG, map_map; cbn [fst]; apply in_map; exact Hg)). rewrite forallb_forall in Hapart.
      specialize (Hapart (g_tag g') ltac:(rewrite HG, map_map; cbn [fst]; apply in_map; exact Hg')).
      rewrite !orb_true_iff in Hapart. destruct Hapart as [[E|L]|R]; [| apply Z.leb_le in L; slia | apply Z.leb_le in R; slia].
      exfalso. apply Uint63.eqb_spec in E.
      rewrite HG, map_map in Hndt. cbn [fst] in Hndt. pose proof (nodupb_spec _ Hndt) as ND.
      exact (Hne (nodup_map_inj g_tag G0 g g' ND Hg Hg' E)). }
    (* [comment removed for export] *)
    set (M := f_mem (a_F st0)) in *.
    set (M' := iset 3%uint63 (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A)) (iset 2%uint63 (sh_region false 1%uint63 (c_stack (ka_K A))) M)).
    assert (EF' : a_F (a_start A st0) = FS (f_pc (a_F st0)) (f_regs (a_F st0)) M' (f_resv (a_F st0))) by reflexivity.
    assert (HM'0 : iget 0%uint63 M' = Some rg0) by (unfold M'; rewrite !iget_iset; exact E0).
    assert (HM'1 : iget 1%uint63 M' = Some rg1) by (unfold M'; rewrite !iget_iset; exact E1).
    assert (HM'2 : iget 2%uint63 M' = Some (sh_region false 1%uint63 (c_stack (ka_K A)))) by (unfold M'; rewrite !iget_iset; reflexivity).
    assert (HM'3 : iget 3%uint63 M' = Some (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))) by (unfold M'; rewrite !iget_iset; reflexivity).
    assert (HM'old : forall t, (t =? 2)%uint63 = false -> (t =? 3)%uint63 = false -> iget t M' = iget t M).
    { intros t H2 H3. unfold M'. rewrite !iget_iset, H2, H3. reflexivity. }
    assert (Hiv : forall t rg, iget t M' = Some rg ->
              (t = 2%uint63 /\ rg = sh_region false 1%uint63 (c_stack (ka_K A)))
              \/ (t = 3%uint63 /\ rg = abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))
              \/ ((t =? 2)%uint63 = false /\ (t =? 3)%uint63 = false /\ iget t M = Some rg)).
    { intros t rg Ht. unfold M' in Ht. rewrite !iget_iset in Ht.
      destruct (t =? 3)%uint63 eqn:Et3; [apply Uint63.eqb_spec in Et3; subst; injection Ht as <-; right; left; auto|].
      destruct (t =? 2)%uint63 eqn:Et2; [apply Uint63.eqb_spec in Et2; subst; injection Ht as <-; left; auto|].
      right. right. auto. }
    assert (Hdom' : forall t rg, iget t M = Some rg -> t = 0%uint63 \/ t = 1%uint63 \/ In t (map g_tag G0)).
    { intros t rg Ht. specialize (Hdom t rg Ht). rewrite !orb_true_iff in Hdom. destruct Hdom as [[Ht0|Ht1]|Htb].
      - left. apply Uint63.eqb_spec in Ht0. exact Ht0.
      - right. left. apply Uint63.eqb_spec in Ht1. exact Ht1.
      - right. right. unfold tag_is_blk in Htb. apply existsb_exists in Htb as ([t' n'] & Hin & Et). cbn [fst] in Et. apply Uint63.eqb_spec in Et. subst t'.
        rewrite HG in Hin. apply in_map_iff in Hin as (g & Eg & Hg). injection Eg as Etg En. rewrite <- Etg. apply in_map. exact Hg. }
    assert (HM2 : iget 2%uint63 M = None).
    { destruct (iget 2%uint63 M) as [rg|] eqn:E2; [|reflexivity]. exfalso.
      destruct (Hdom' _ _ E2) as [E|[E|Hin]]; [discriminate E | discriminate E |].
      destruct (Htags _ Hin) as (g & Hg & Etg). destruct (Hblk g Hg) as (H4 & _). rewrite Etg in H4. change (to_Z 2%uint63) with 2 in H4. slia. }
    assert (HM3 : iget 3%uint63 M = None).
    { destruct (iget 3%uint63 M) as [rg|] eqn:E3; [|reflexivity]. exfalso.
      destruct (Hdom' _ _ E3) as [E|[E|Hin]]; [discriminate E | discriminate E |].
      destruct (Htags _ Hin) as (g & Hg & Etg). destruct (Hblk g Hg) as (H4 & _). rewrite Etg in H4. change (to_Z 3%uint63) with 3 in H4. slia. }
    (* [comment removed for export] *)
    destruct (HK_parts A HK) as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[Hslo Hslen] Hscells].
    apply Z.eqb_eq in Hslo. apply Z.eqb_eq in Hslen. rewrite forallb_forall in Hscells.
    assert (Hcs8 : cs mod 8 = 0).
    { subst cs. destruct (HK_err A HK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H16 & _). clear - H16. Z.div_mod_to_equations. slia. }
    assert (Hspcs : 0 <= sp - cs /\ sp < 2 ^ 64) by (clear - Hlo Hhl ACF HB HB64; slia).
    exists s, LB, G0, [], [], ms.
    constructor; rewrite ?EF'; cbn [q_sp0 q_lo q_B q_shi q_mo0 q_F q_fc q_m0 q_LB0 q_LF0 q_n0 q_rho0 q_G0 q_s0 q_CH0 q_AL0 q_cs
                                      a_start a_F a_n a_blk a_ff a_cost a_cnt a_cs f_mem f_pc ms_regs ms_mem ms_fregs ms_fcsr ms_rom MS LF_of map app].
    - (* [comment removed for export] *) exact Hvis.
    - (* [comment removed for export] *)
      intros rho' Hag.
      assert (HR : R asegs IM rho' (a_F st0) ms).
      { apply (R_im_ro asegs IMX rho' Hdisj); [| exact (HRn rho' Hag)]. split.
        + intros rg0' H0'. fold M in H0'. rewrite E0 in H0'. injection H0' as <-. exact Ed0.
        + intros t rg pn p Ht Hp. fold M in Ht. destruct (Hdom' t rg Ht) as [-> | [-> | Htb]].
          * rewrite E0 in Ht. injection Ht as <-. specialize (Hp0 pn p Hp). apply andb_true_iff in Hp0 as [_ Hkd]. destruct (pg_kind p); try discriminate.
          * rewrite E1 in Ht. injection Ht as <-. specialize (Hp1 pn p Hp). destruct (pg_kind p); try discriminate.
          * destruct (Htags _ Htb) as (g & Hg & Etg). destruct (Hblk g Hg) as (_ & _ & _ & rg' & Hrg' & _ & _ & _ & _ & _ & Hk).
            rewrite Etg, Ht in Hrg'. injection Hrg' as <-. rewrite (Hk pn p Hp). discriminate. }
      destruct Hag as [Hr0' Hag]. 
      assert (E0' : rho' 0%uint63 = Z_to_bv 64 0) by exact Hr0'.
      assert (E1' : rho' 1%uint63 = wa (sp - cs)) by (rewrite (Hag 1%uint63) by (change (to_Z 1%uint63) with 1; slia); exact Hr1).
      assert (E2' : rho' 2%uint63 = wa (sh (sp - cs))) by (rewrite (Hag 2%uint63) by (change (to_Z 2%uint63) with 2; slia); exact Hr2).
      assert (E3' : rho' 3%uint63 = Z_to_bv 64 0) by (rewrite (Hag 3%uint63) by (change (to_Z 3%uint63) with 3; slia); exact Hr3).
      destruct HR as [Rpc Rregs Rsvc Rresv Rmem]. constructor; cbn [f_pc f_regs f_mem f_resv]; [exact Rpc | exact Rregs | exact Rsvc | exact Rresv |].
      apply mem_ok_parts.
      + intros t rg Ht. unfold M' in Ht. rewrite !iget_iset in Ht.
        destruct (t =? 3)%uint63 eqn:Et3.
        { apply Uint63.eqb_spec in Et3. subst t. injection Ht as <-. exact (abs_part_of_ACONST IMX A HK HSH0 rho' m E0' E3' Hac Hinv). }
        destruct (t =? 2)%uint63 eqn:Et2.
        { apply Uint63.eqb_spec in Et2. subst t. injection Ht as <-.
          apply (stack_sh_region_part IM rho' E0' m lo sp sp (c_stack (ka_K A)) E1' E2' Hst0); fold cs.
          - clear - Hlo. slia. - slia. - clear - Hsp32. Z.div_mod_to_equations. slia. - exact Hcs8. - clear - Hcs1 Hcs2. slia. }
        exact (mem_part_of _ _ _ _ _ _ _ Rmem Ht).
      + (* [comment removed for export] *)
        destruct Rmem as [_ Hsep].
        (* [comment removed for export] *)
        assert (Hold : forall t rg, iget t M = Some rg ->
                  (bv_unsigned (rho' t) + to_Z (rg_lo rg) = AIMG_LO /\ bv_unsigned (rho' t) + to_Z (rg_len rg) = AIMG_TOP)
                  \/ (bv_unsigned (rho' t) + to_Z (rg_lo rg) = sp - cs /\ bv_unsigned (rho' t) + to_Z (rg_len rg) = sp)
                  \/ (exists g, In g G0 /\ bv_unsigned (rho' t) + to_Z (rg_lo rg) = g_addr g /\ bv_unsigned (rho' t) + to_Z (rg_len rg) = g_addr g + to_Z (g_size g))).
        { intros t rg Ht. destruct (Hdom' t rg Ht) as [-> | [-> | Htb]].
          - left. rewrite E0 in Ht. injection Ht as <-. rewrite E0', Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Hlo0, Hlen0.
            unfold AIMG_LO. change (to_Z 65536%uint63) with 65536. slia.
          - right. left. rewrite E1 in Ht. injection Ht as <-. rewrite E1', Hlo1, Hlen1. change (to_Z 0%uint63) with 0. fold cs.
            rewrite wa_unsigned by slia. slia.
          - right. right. destruct (Htags _ Htb) as (g & Hg & Etg). exists g. split; [exact Hg|]. subst t.
            destruct (Hblk g Hg) as (H4 & Htn & _ & rg' & Hrg' & Hlo' & Hlen' & _). rewrite Ht in Hrg'. injection Hrg' as <-.
            rewrite Hlo', Hlen'. change (to_Z 0%uint63) with 0.
            rewrite (Hag (g_tag g)) by slia. rewrite (proj1 (proj2 (proj1 (Forall_forall _ _) HG0 g Hg))).
            pose proof (Hgblk g Hg) as (R1 & R2 & R3 & R4 & R5 & _). pose proof (i63_range (g_size g)). rewrite wa_unsigned by slia. slia. }
        assert (SR2 : bv_unsigned (rho' 2%uint63) = sh (sp - cs) /\ to_Z (rg_lo (sh_region false 1%uint63 (c_stack (ka_K A)))) = 0
                      /\ to_Z (rg_len (sh_region false 1%uint63 (c_stack (ka_K A)))) = nsh cs).
        { unfold sh_region. cbn [rg_lo rg_len]. rewrite E2', (nsh_eq (c_stack (ka_K A))) by slia. fold cs. change (to_Z 0%uint63) with 0.
          split; [| split; [reflexivity | reflexivity]].
          apply wa_unsigned. unfold sh. rewrite ASHADOW_BASE_val. clear - Hspcs Hcsr. Z.div_mod_to_equations. slia. }
        assert (SR3 : bv_unsigned (rho' 3%uint63) = 0 /\ to_Z (rg_lo (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))) = sh AIMG_LO
                      /\ to_Z (rg_len (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A))) = sh AIMG_TOP).
        { unfold abs_region. cbn [rg_lo rg_len]. rewrite E3', Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. auto. }
        assert (SHF : sh AIMG_TOP <= sh (sp - cs) /\ sh (sp - cs) + nsh cs <= sh sp /\ sh sp <= AHI_LO /\ AIMG_TOP <= sh AIMG_LO /\ sh AIMG_LO <= sh AIMG_TOP
                      /\ 0 <= nsh cs /\ AHI_LO <= aceil /\ ALOWSH_LO < sh AIMG_LO).
        { pose proof (stack0_bounds _ _ _ Hst0) as [SB1 SB2]. unfold sh, nsh, AIMG_LO, AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *. rewrite ASHADOW_BASE_val.
          clear - SB1 SB2 ACF Hlo Hhl Hcs8 Hsp32 Hcsr Hcs1. Z.div_mod_to_equations. slia. }
        assert (Hblkapp : forall g, In g G0 -> (g_addr g + to_Z (g_size g) <= ALOWSH_LO \/ AHI_LO <= g_addr g) /\ AIMG_TOP <= g_addr g /\ g_addr g + to_Z (g_size g) <= aceil).
        { intros g Hg. pose proof (Hgblk g Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold aapp, aapp_lo, aapp_hi in R7. slia. }
        intros t t' rg rg' Hne Ht Ht'.
        destruct (Hiv t rg Ht) as [[-> ->] | [[-> ->] | (T2 & T3 & HtM)]]; destruct (Hiv t' rg' Ht') as [[-> ->] | [[-> ->] | (T2' & T3' & HtM')]];
          try (exfalso; exact (Hne eq_refl)).
        * (* [comment removed for export] *) destruct SR2 as (-> & -> & ->). destruct SR3 as (-> & -> & ->). right. slia.
        * (* [comment removed for export] *) destruct SR2 as (-> & -> & ->).
          destruct (Hold t' rg' HtM') as [[L1 L2] | [[L1 L2] | (g & Hg & L1 & L2)]]; [right; slia | left; slia |].
          destruct (Hblkapp g Hg) as [[Lo|Hi] [B1 B2]]; [right; slia | left; slia].
        * (* [comment removed for export] *) destruct SR2 as (-> & -> & ->). destruct SR3 as (-> & -> & ->). left. slia.
        * (* [comment removed for export] *) destruct SR3 as (-> & -> & ->).
          destruct (Hold t' rg' HtM') as [[L1 L2] | [[L1 L2] | (g & Hg & L1 & L2)]]; [right; slia | left; slia |].
          destruct (Hblkapp g Hg) as [[Lo|Hi] [B1 B2]]; [right; slia | left; slia].
        * (* [comment removed for export] *) destruct SR2 as (-> & -> & ->).
          destruct (Hold t rg HtM) as [[L1 L2] | [[L1 L2] | (g & Hg & L1 & L2)]]; [left; slia | right; slia |].
          destruct (Hblkapp g Hg) as [[Lo|Hi] [B1 B2]]; [left; slia | right; slia].
        * (* [comment removed for export] *) destruct SR3 as (-> & -> & ->).
          destruct (Hold t rg HtM) as [[L1 L2] | [[L1 L2] | (g & Hg & L1 & L2)]]; [left; slia | right; slia |].
          destruct (Hblkapp g Hg) as [[Lo|Hi] [B1 B2]]; [left; slia | right; slia].
        * (* [comment removed for export] *) exact (Hsep t t' rg rg' Hne HtM HtM').
    - (* [comment removed for export] *) exists (map x L31). reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hr0.
    - exact Hr1.
    - exact Hr2.
    - exact Hr3.
    - apply agree_refl. exact Hr0.
    - slia.
    - exact Hakrel.
    - apply (ah_mpres_refl H HH).
    - exact Hheap.
    - exact Hrfs.
    - exact Hac.
    - exact Hst0.
    - exact Hchain.
    - exact HCH.
    - split; [reflexivity | split; [exact Hts0 | exact Htra]].
    - exact Hpfo.
    - exists []. split; [reflexivity|]. cbn [csum fold_right]. slia.
    - exact HAL.
    - (* [comment removed for export] *) exact HG.
    - apply Forall_forall. intros g Hg. destruct (proj1 (Forall_forall _ _) HG0 g Hg) as (Hin & Hrho & Hstkg).
      destruct (Hblk g Hg) as (H4 & Htn & Hsz & rg & Hrg & Hl & Hn & Hd & Hkd & Hal & Hk).
      pose proof (i63_range (g_tag g)).
      assert (T2 : (g_tag g =? 2)%uint63 = false) by (apply Uint63.eqb_false_spec; intros E; apply (f_equal to_Z) in E; change (to_Z 2%uint63) with 2 in E; slia).
      assert (T3 : (g_tag g =? 3)%uint63 = false) by (apply Uint63.eqb_false_spec; intros E; apply (f_equal to_Z) in E; change (to_Z 3%uint63) with 3 in E; slia).
      split; [exact Hin|]. split; [exact Hrho|]. split; [exact Hsz|]. split; [exact H4|]. split; [exact Htn|]. split.
      + exists rg. rewrite (HM'old _ T2 T3). split; [exact Hrg|]. split; [exact Hl|]. split; [exact Hn|]. split; [exact Hkd|]. split; [exact Hal| exact Hd].
      + intros rg' Hrg'. exfalso.
        assert (T2' : (g_tag g + 1 =? 2)%uint63 = false).
        { apply Uint63.eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite to_Z_add_small in E by (change (to_Z 1%uint63) with 1; slia).
          change (to_Z 2%uint63) with 2 in E. change (to_Z 1%uint63) with 1 in E. slia. }
        assert (T3' : (g_tag g + 1 =? 3)%uint63 = false).
        { apply Uint63.eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite to_Z_add_small in E by (change (to_Z 1%uint63) with 1; slia).
          change (to_Z 3%uint63) with 3 in E. change (to_Z 1%uint63) with 1 in E. slia. }
        rewrite (HM'old _ T2' T3') in Hrg'. destruct (Hdom' _ _ Hrg') as [E|[E|Hin']].
        * apply (f_equal to_Z) in E. rewrite to_Z_add_small in E by (change (to_Z 1%uint63) with 1; slia). change (to_Z 0%uint63) with 0 in E. change (to_Z 1%uint63) with 1 in E. slia.
        * apply (f_equal to_Z) in E. rewrite to_Z_add_small in E by (change (to_Z 1%uint63) with 1; slia). change (to_Z 1%uint63) with 1 in E. slia.
        * destruct (Htags _ Hin') as (g' & Hg' & Etg').
          assert (Hne : g <> g') by (intros <-; apply (f_equal to_Z) in Etg'; rewrite to_Z_add_small in Etg' by (change (to_Z 1%uint63) with 1; slia); change (to_Z 1%uint63) with 1 in Etg'; slia).
          pose proof (Hapart2 g g' Hg Hg' Hne) as AP. apply (f_equal to_Z) in Etg'. rewrite to_Z_add_small in Etg' by (change (to_Z 1%uint63) with 1; slia).
          change (to_Z 1%uint63) with 1 in Etg'. slia.
    - exact Hnd.
    - rewrite HG, map_map in Hndt. cbn [fst] in Hndt. exact (nodupb_spec _ Hndt).
    - apply Forall_forall. intros g Hg. left. exact Hg.
    - apply Forall_forall. intros g Hg. exact (proj2 (proj2 (proj1 (Forall_forall _ _) HG0 g Hg))).
    - (* [comment removed for export] *) rewrite Eff. reflexivity.
    - constructor.
    - cbn [map app]. exact (ah_RFS_nodup H HH _ _ Hrfs).
    - constructor.
    - split; [| split]; [intros g g' Hg Hg' Hne; exact (Hapart2 g g' Hg Hg' Hne) | intros g f _ [] | intros f f' [] ].
    - cbn [length]. slia.
    - constructor.
    - (* [comment removed for export] *) intros t rg Ht. destruct (Hiv t rg Ht) as [[-> _] | [[-> _] | (_ & _ & HtM)]]; [tauto | tauto |].
      destruct (Hdom' t rg HtM) as [-> | [-> | Htb]]; tauto.
    - exists rg0. split; [exact HM'0|]. split; [rewrite Hlo0; reflexivity|]. split; [exact Hlen0|]. split; [exact Ed0|].
      intros pn p Hp. specialize (Hp0 pn p Hp). apply andb_true_iff in Hp0 as [Hw Hkd]. split; [exact Hw|]. destruct (pg_kind p); try discriminate. reflexivity.
    - exists rg1. split; [exact HM'1|]. split; [exact Hlo1|]. split; [exact Hlen1|]. split; [exact Ed1|]. split; [exact Ekd1 | exact Ha1].
    - exact HM'2.
    - exact HM'3.
    - (* [comment removed for export] *) exists rg0. split; [exact HM'0|]. intros c u Hc. pose proof (ro_of_range A HK c u Hc) as Hr.
      rewrite Hlo0, Hlen0. unfold AIMG_LO in Hr. change (to_Z 65536%uint63) with 65536. slia.
    - (* [comment removed for export] *) intros t rg pn p ci c Ht Hp Hcc.
      destruct (Hiv t rg Ht) as [[-> ->] | [[-> ->] | (_ & _ & HtM)]].
      + unfold sh_region in Hp |- *. cbn [rg_pages rg_len] in Hp |- *. rewrite iget_iset, iget_iempty in Hp.
        destruct (pn =? 0)%uint63 eqn:Epn; [|discriminate]. apply Uint63.eqb_spec in Epn. subst pn. injection Hp as <-. cbn [pg_cells] in Hcc.
        pose proof (i63_range ci). destruct (sh_cells_inv (c_stack (ka_K A)) ci c ltac:(slia) Hcc) as [Hcilt ->].
        rewrite (nsh_eq (c_stack (ka_K A))) by slia. change (to_Z 0%uint63) with 0. fold cs.
        split; [Z.div_mod_to_equations; slia|]. split; [Z.div_mod_to_equations; slia|].
        intros v Ev. unfold sh_cell in Ev. destruct (((ci + 1) * 8 <=? c_stack (ka_K A) >> 3))%uint63 eqn:Ecv; [|discriminate].
        apply (proj1 (leb8_spec ci (c_stack (ka_K A)) ltac:(slia) ltac:(slia))) in Ecv. fold cs in Ecv. Z.div_mod_to_equations. slia.
      + unfold abs_region in Hp |- *. cbn [rg_pages rg_len] in Hp |- *. rewrite Hslen.
        destruct (abs_pages_inv _ _ _ _ _ Hp Hcc) as (a & Hin & Ha & Hb). pose proof (i63_range a). pose proof (i63_range pn). pose proof (i63_range ci).
        specialize (Hscells (a, c) Hin). cbn [fst snd] in Hscells. rewrite !andb_true_iff in Hscells. destruct Hscells as [[[H8 Hlo8] Hhi8] _].
        apply Z.leb_le in Hhi8. apply (f_equal to_Z) in Ha. rewrite to_Z_lsr12 in Ha. apply (f_equal to_Z) in Hb. rewrite to_Z_lsr3, to_Z_land4095 in Hb.
        apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8. change (to_Z 0%uint63) with 0 in H8.
        assert (Ea : to_Z a = to_Z pn * 4096 + to_Z ci * 8) by (rewrite <- Ha, <- Hb; Z.div_mod_to_equations; slia).
        split; [slia|]. split; [rewrite <- Hb; Z.div_mod_to_equations; slia | intros; slia].
      + specialize (Hinb t rg HtM). rewrite iall_spec in Hinb. specialize (Hinb pn p Hp). rewrite iall_spec in Hinb.
        specialize (Hinb ci c Hcc). apply andb_true_iff in Hinb as [H1 H2]. apply Z.leb_le in H1. apply Uint63.ltb_spec in H2. change (to_Z 512%uint63) with 512 in H2.
        split; [slia | split; [exact H2 | intros; exact H1]].
    - (* [comment removed for export] *) intros t rg Ht Ht0. destruct (Hiv t rg Ht) as [[-> ->] | [[-> ->] | (_ & _ & HtM)]].
      + split; [right; reflexivity|]. intros pn p Hp. unfold sh_region in Hp. cbn [rg_pages] in Hp. rewrite iget_iset, iget_iempty in Hp.
        destruct (pn =? 0)%uint63; [|discriminate]. injection Hp as <-. reflexivity.
      + split; [right; reflexivity|]. intros pn p Hp. unfold abs_region in Hp. cbn [rg_pages] in Hp. exact (proj2 (abs_pages_shape _ _ _ Hp)).
      + destruct (Hdom' t rg HtM) as [-> | [-> | Htb]]; [exfalso; exact (Ht0 eq_refl) | |].
        * rewrite E1 in HtM. injection HtM as <-. split; [left; exact Ed1|]. intros pn p Hp. specialize (Hp1 pn p Hp). destruct (pg_kind p); try discriminate. reflexivity.
        * destruct (Htags _ Htb) as (g & Hg & Etg). destruct (Hblk g Hg) as (_ & _ & _ & rg' & Hrg' & _ & _ & Hd & _ & _ & Hk).
          rewrite Etg, HtM in Hrg'. injection Hrg' as <-. split; [left; exact Hd | exact Hk].
    - (* [comment removed for export] *) rewrite Hcost0. change (to_Z 0%uint63) with 0. pose proof (i63_range (c_cost (ka_K A))). slia.
    - rewrite Hcnt0. change (to_Z 0%uint63) with 0. pose proof (i63_range (c_cnt (ka_K A))). slia.
    - exact Hstk.
    - fold cs. repeat split; slia.
    - exact Haux.
    - exact Hinv.
    - pose proof (stk_of_rw_cells asegs m (errA A) [C4 (x 0)] Herr) as Hs. cbn [cells_size csize] in Hs.
      replace (errA A + Z.of_nat 4) with (errA A + 4) in Hs by slia. exact Hs.
    - exact (HSH0 m Hac Hinv).
    - intros b Hb _. exact Hb.
    - intros b Hb. pose proof (ah_blocks H HH _ _ _ _ Hheap Hb) as (R1 & R2 & R3 & R4 & R5 & _). slia.
    - split; [| exact HndLB]. apply Forall_forall. intros g Hg. exact (proj1 (proj1 (Forall_forall _ _) HG0 g Hg)).
    - intros b Hb. left. exact Hb.
    - intros. reflexivity.
    - (* [comment removed for export] *) apply Forall_nil.
  Qed.
End Start.
