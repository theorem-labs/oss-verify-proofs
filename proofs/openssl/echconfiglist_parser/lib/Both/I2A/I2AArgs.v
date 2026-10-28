(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

Lemma dv_conc63 : forall rho n, rho 0%uint63 = Z_to_bv 64 0 -> dv rho (FV 0 (W64 0 n)) = Z_to_bv 64 (to_Z n).
Proof.
  intros rho n H0. rewrite (fk_dv_conc rho _ H0). unfold wbv. rewrite wZ_even_top by reflexivity. reflexivity.
Qed.

Lemma dv_tag_zero : forall rho t, to_Z t < 2 ^ 60 -> dv rho (FV t w_zero) = rho t.
Proof.
  intros rho t Ht. rewrite (fk_dv_plain rho (FV t w_zero) Ht). cbn [vtag vw]. rewrite wbv_w_zero.
  apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned w0) with 0. rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma wbytes8_le8 : forall w, wbytes8 w = le8 w.
Proof. intros w. unfold wbytes8. rewrite <- store_bytes_8. reflexivity. Qed.

Lemma list_eqb_eq : forall a b, list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Hb; cbn in Hb; try discriminate; [reflexivity|].
  apply andb_prop in Hb as [Hx Hr]. apply Uint63.eqb_spec in Hx. subst. f_equal. apply IH. exact Hr.
Qed.
Lemma inpf_In : forall pc0 ras l, inpf pc0 ras l = true -> In (pc0, ras) l.
Proof.
  intros pc0 ras l Hb. unfold inpf in Hb. apply existsb_exists in Hb as ([p r] & Hin & Hx). cbn [fst snd] in Hx.
  apply andb_prop in Hx as [Hp Hr]. apply Uint63.eqb_spec in Hp. apply list_eqb_eq in Hr. subst. exact Hin.
Qed.

Section Args.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cellv_bytes : forall Q st rho msF mo s LB G FF XS ms t rg Ab off v,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    iget t (f_mem (a_F st)) = Some rg -> bv_unsigned (rho t) = Ab -> Ab + to_Z (rg_len rg) < 2 ^ 64 ->
    cell_of (f_mem (a_F st)) t off = Some v -> to_Z off mod 8 = 0 ->
    bytes_at asegs (ms_mem ms) (Ab + to_Z off) (le8 (dv rho v)) /\ to_Z off + 8 <= to_Z (rg_len rg).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms t rg Ab off v X Ht HAb Hlen Hc Ho8.
    pose proof (r_Rn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X rho (agree_refl _ rho (r_rho0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X))) as HR.
    pose proof (bv_unsigned_in_range _ (rho t)) as Hrt. change (bv_modulus 64) with (2 ^ 64) in Hrt.
    unfold cell_of in Hc. rewrite Ht in Hc.
    destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p|] eqn:Ep; [|discriminate].
    destruct (iget ((off land 4095) >> 3)%uint63 (pg_cells p)) as [[v0| |sl]|] eqn:Eci; try discriminate. injection Hc as Ev. subst v0.
    pose proof (i63_range off) as Ho63. pose proof (i63_range (rg_len rg)).
    destruct (r_inb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X t rg _ _ _ _ Ht Ep Eci) as (Hinb & Hci512 & Hcv).
    specialize (Hcv v eq_refl). rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095 in Hinb, Hcv. rewrite to_Z_lsr3, to_Z_land4095 in Hci512.
    pose proof (off_decomp (to_Z off) ltac:(slia)) as Hdec.
    destruct (R_mem _ _ _ _ _ HR) as [Hregs _]. destruct (Hregs _ rg Ht) as [(_ & Hlen62 & _) Hpages].
    assert (Hpn : to_Z (off >> 12)%uint63 < 2 ^ 50) by (rewrite to_Z_lsr12; slia).
    destruct (Hpages _ _ Hpn (page_at_expl IMX _ _ _ _ Ep)) as ((_ & Hcells & _) & _).
    assert (Hcl : 0 <= to_Z ((off land 4095) >> 3)%uint63 < clim rg (off >> 12)%uint63).
    { rewrite to_Z_lsr3, to_Z_land4095. apply clim_intro; [pose proof (cell_index_range (to_Z off) ltac:(slia)); slia | rewrite to_Z_lsr12; slia]. }
    specialize (Hcells _ v Hcl ltac:(unfold cell_at; rewrite Eci; reflexivity)).
    split; [| slia].
    split; [slia|]. split; [rewrite length_le8; slia|]. intros i Hi. rewrite length_le8 in Hi.
    rewrite <- wbytes8_le8. rewrite <- (Hcells i Hi).
    change (mrd asegs (ms_mem ms) (wa (Ab + to_Z off + Z.of_nat i))) with (rview asegs (ms_mem ms) (wa (Ab + to_Z off + Z.of_nat i))). f_equal.
    rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. unfold adr, wa. apply bv_eq.
    rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite HAb. rewrite (Z.mod_small (to_Z off / 4096 * 4096 + to_Z off mod 4096 / 8 * 8 + Z.of_nat i)) by slia.
    rewrite !Z.mod_small by slia. slia.
  Qed.

  (* [comment removed for export] *)
  Lemma cell1v_cell_of : forall M off, cell1v M off = cell_of M 1%uint63 off.
  Proof. intros M off. reflexivity. Qed.

  Lemma rw_cells_2C8 : forall m a x y,
    bytes_at asegs m a (le8 x) -> bytes_at asegs m (a + 8) (le8 y) -> stk asegs m a (a + 16) ->
    rw_cells asegs m a [C8 x; C8 y].
  Proof.
    intros m a x y Bx By (S0 & S1 & SS). split.
    - split; [repeat constructor|]. cbn [cells_bytes cbytes app].
      destruct Bx as (B0 & B1 & Bi). destruct By as (_ & _ & Ci). rewrite length_le8 in Bi, Ci.
      split; [exact B0|]. split; [rewrite length_app, !length_le8; cbn; slia|].
      intros i Hi. rewrite length_app, !length_le8 in Hi.
      destruct (Nat.lt_ge_cases i 8) as [Hl|Hg].
      + rewrite nth_error_app1 by (rewrite length_le8; exact Hl). exact (Bi i Hl).
      + rewrite nth_error_app2 by (rewrite length_le8; exact Hg). rewrite length_le8.
        replace (a + Z.of_nat i) with (a + 8 + Z.of_nat (i - 8)) by slia. apply Ci. slia.
    - split; [slia|]. split; [cbn [cells_size csize Nat.add]; slia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      exact (proj1 (SS (a + i) ltac:(slia))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ra0_of (Q : i2aenv) : Z := bv_unsigned (q_rho0 Q (c_tra K)).

  Lemma chain_walk_sound : forall Q st rho msF mo s LB G FF XS ms fuel cur ras0 op ras,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    chain_walk fuel K (ka_ts0 A) (f_mem (a_F st)) (a_blk st) cur ras0 = Some (op, ras) ->
    exists tail CH, ras = ras0 ++ tail
      /\ as_chain H (ms_mem ms) (bv_unsigned (dv rho cur)) CH
      /\ map snd CH = map to_Z tail ++ (if op then ra0_of Q :: map snd (q_CH0 Q) else []).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms fuel. induction fuel as [|fuel IH]; intros cur ras0 op ras X Hw; [discriminate|].
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    destruct Xlo as (Hal & Hl2 & HB & Hsp16 & Hsp32 & HB64 & Hshi). acb. pose proof (i63_range (c_stack K)) as Hcs.
    destruct (HK_err A HK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ef3 & _ & Est16 & Est40). unfold AFS_STACK in Ef3.
    cbn [chain_walk] in Hw. destruct cur as [t [top off]].
    destruct (negb (top =? 0)%uint63) eqn:Etop; [discriminate|]. apply negb_false_iff in Etop. apply Uint63.eqb_spec in Etop. subst top.
    pose proof (i63_range off) as Hoff. pose proof (i63_range t) as Ht63.
    destruct (t =? 1)%uint63 eqn:Et1.
    - (* [comment removed for export] *)
      apply Uint63.eqb_spec in Et1. subst t.
      match type of Hw with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
      rewrite !andb_true_iff in Hg. destruct Hg as [[Ho16 Ho16'] Hocs].
      apply Uint63.eqb_spec in Ho16. apply (f_equal to_Z) in Ho16. rewrite (i63_land_ones off 15%uint63 4 eq_refl ltac:(slia)) in Ho16.
      change (2 ^ 4) with 16 in Ho16. change (to_Z 0%uint63) with 0 in Ho16.
      apply Uint63.leb_spec in Ho16'. change (to_Z 16%uint63) with 16 in Ho16'. apply Uint63.leb_spec in Hocs.
      destruct (cell1v (f_mem (a_F st)) (off - 16)) as [prev|] eqn:Hprev; [|discriminate].
      destruct (cell1v (f_mem (a_F st)) (off - 8)) as [rav|] eqn:Hrav; [|discriminate].
      rewrite cell1v_cell_of in Hprev, Hrav.
      destruct Xreg1 as (rg1 & Hrg1 & Hlo1 & Hlen1 & _).
      assert (Eo16 : to_Z (off - 16)%uint63 = to_Z off - 16) by (rewrite to_Z_sub_small; change (to_Z 16%uint63) with 16; slia).
      assert (Eo8 : to_Z (off - 8)%uint63 = to_Z off - 8) by (rewrite to_Z_sub_small; change (to_Z 8%uint63) with 8; slia).
      assert (Hr1u : bv_unsigned (rho 1%uint63) = q_sp0 Q - to_Z (c_stack K)) by (rewrite Xr1; apply wa_unsigned; slia).
      destruct (cellv_bytes _ _ _ _ _ _ _ _ _ _ _ _ rg1 (q_sp0 Q - to_Z (c_stack K)) _ _ X Hrg1 Hr1u ltac:(rewrite Hlen1; slia) Hprev ltac:(rewrite Eo16; Z.div_mod_to_equations; slia)) as [Bprev _].
      destruct (cellv_bytes _ _ _ _ _ _ _ _ _ _ _ _ rg1 (q_sp0 Q - to_Z (c_stack K)) _ _ X Hrg1 Hr1u ltac:(rewrite Hlen1; slia) Hrav ltac:(rewrite Eo8; Z.div_mod_to_equations; slia)) as [Brav _].
      rewrite Eo16 in Bprev. rewrite Eo8 in Brav.
      set (fp := q_sp0 Q - to_Z (c_stack K) + to_Z off).
      assert (Efp : bv_unsigned (dv rho (FV 1%uint63 (W64 0 off))) = fp).
      { rewrite (dv_adr rho 1%uint63 0%uint63 off) by first [cbn; slia | reflexivity]. subst fp. rewrite (adr_wa rho 1%uint63 _ _ Xr1); slia. }
      rewrite Efp.
      assert (Hstk16 : stk asegs (ms_mem ms) (fp - 16) (fp - 16 + 16)).
      { destruct Xstk as (S0 & S1 & SS). split; [slia|]. split; [slia|]. intros a Ha. apply SS. subst fp. slia. }
      destruct (off =? c_stack K)%uint63 eqn:Eocs.
      + (* [comment removed for export] *)
        apply Uint63.eqb_spec in Eocs. subst off.
        destruct (fval_eqb prev (FV (ka_ts0 A) w_zero) && fval_eqb rav (FV (c_tra K) w_zero)) eqn:Hev; [|discriminate].
        injection Hw as <- <-. apply andb_prop in Hev as [E1 E2]. apply fval_eqb_eq in E1. apply fval_eqb_eq in E2. subst prev rav.
        destruct Xs0v as (Es0 & Hts0 & Htra). destruct Xag as [_ Hagr].
        exists [], ((fp, ra0_of Q) :: q_CH0 Q). split; [rewrite app_nil_r; reflexivity|]. split.
        * apply (ah_chain_cons H HH _ (q_s0 Q)).
          -- replace fp with (q_sp0 Q) by (subst fp; slia). exact Xch.
          -- pose proof (bv_unsigned_in_range _ (q_rho0 Q (ka_ts0 A))). change (bv_modulus 64) with (2 ^ 64) in *. slia.
          -- unfold ra0_of. pose proof (bv_unsigned_in_range _ (q_rho0 Q (c_tra K))). change (bv_modulus 64) with (2 ^ 64) in *. slia.
          -- subst fp. replace (q_sp0 Q - to_Z (c_stack K) + to_Z (c_stack K)) with (q_sp0 Q) by slia. exact Hsp16.
          -- subst fp. slia.
          -- subst fp. slia.
          -- apply rw_cells_2C8.
             ++ rewrite (dv_tag_zero rho (ka_ts0 A)) in Bprev by slia. rewrite (Hagr (ka_ts0 A) Hts0) in Bprev.
                rewrite <- Es0, Z_to_bv_bv_unsigned. replace (fp - 16) with (q_sp0 Q - to_Z (c_stack K) + (to_Z (c_stack K) - 16)) by (subst fp; slia). exact Bprev.
             ++ unfold ra0_of. rewrite (dv_tag_zero rho (c_tra K)) in Brav by slia. rewrite (Hagr (c_tra K) Htra) in Brav.
                rewrite Z_to_bv_bv_unsigned. replace (fp - 16 + 8) with (q_sp0 Q - to_Z (c_stack K) + (to_Z (c_stack K) - 8)) by (subst fp; slia). exact Brav.
             ++ exact Hstk16.
        * cbn [map snd app]. reflexivity.
      + (* [comment removed for export] *)
        destruct rav as [tr [rtop ra]]. destruct prev as [tp [ptop poff]].
        match type of Hw with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
        rewrite !andb_true_iff in Hg. destruct Hg as [[Etr Ertop] Hout].
        apply Uint63.eqb_spec in Etr. apply Uint63.eqb_spec in Ertop. subst tr rtop.
        destruct (IH _ _ _ _ X Hw) as (tail & CH & Eras & Hch & Hmap).
        exists (ra :: tail), ((fp, to_Z ra) :: CH). split; [rewrite Eras, <- app_assoc; reflexivity|]. split.
        * apply (ah_chain_cons H HH _ (bv_unsigned (dv rho (FV tp (W64 ptop poff))))).
          -- exact Hch.
          -- pose proof (bv_unsigned_in_range _ (dv rho (FV tp (W64 ptop poff)))). change (bv_modulus 64) with (2 ^ 64) in *. slia.
          -- pose proof (i63_range ra). slia.
          -- subst fp. clear - Ho16 Hsp32 Hsp16 Hcs Hoff. Z.div_mod_to_equations. slia.
          -- subst fp. slia.
          -- subst fp. slia.
          -- apply rw_cells_2C8.
             ++ rewrite Z_to_bv_bv_unsigned. replace (fp - 16) with (q_sp0 Q - to_Z (c_stack K) + (to_Z off - 16)) by (subst fp; slia). exact Bprev.
             ++ rewrite (fk_dv_conc rho (W64 0 ra) Xr0) in Brav. unfold wbv in Brav. rewrite wZ_even_top in Brav by reflexivity.
                replace (fp - 16 + 8) with (q_sp0 Q - to_Z (c_stack K) + (to_Z off - 8)) by (subst fp; slia). exact Brav.
             ++ exact Hstk16.
        * cbn [map snd app]. rewrite Hmap. reflexivity.
    - destruct (t =? 0)%uint63 eqn:Et0.
      + (* [comment removed for export] *)
        apply Uint63.eqb_spec in Et0. subst t.
        destruct ((off <? two46) || negb ((off land 7) =? 0))%uint63 eqn:Hg; [|discriminate]. injection Hw as <- <-.
        exists [], []. split; [rewrite app_nil_r; reflexivity|]. split; [|reflexivity].
        apply (ah_chain_nil H HH). rewrite (fk_dv_conc rho _ Xr0). unfold wbv. rewrite wZ_even_top by reflexivity. rewrite Z_to_bv_unsigned.
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by slia.
        apply orb_prop in Hg as [Hg|Hg].
        * left. apply Uint63.ltb_spec in Hg. change (to_Z two46) with (2 ^ 46) in Hg. slia.
        * right. apply negb_true_iff in Hg. intros E. apply Uint63.eqb_false_spec in Hg. apply Hg. apply to_Z_inj. rewrite to_Z_land7. change (to_Z 0%uint63) with 0. exact E.
      + (* [comment removed for export] *)
        destruct (bsize_of t (a_blk st)) as [n|] eqn:Hbs; [|discriminate].
        destruct (off <=? n)%uint63 eqn:Hle; [|discriminate]. injection Hw as <- <-. apply Uint63.leb_spec in Hle.
        exists [], []. split; [rewrite app_nil_r; reflexivity|]. split; [|reflexivity].
        apply (ah_chain_nil H HH). left.
        rewrite XG in Hbs.
        assert (Hg : exists g, In g G /\ g_tag g = t /\ g_size g = n).
        { clear - Hbs. induction G as [|g G IH]; cbn [bsize_of map] in Hbs; [discriminate|].
          destruct (g_tag g =? t)%uint63 eqn:E.
          - apply Uint63.eqb_spec in E. injection Hbs as <-. exists g. split; [left; reflexivity | split; [exact E | reflexivity]].
          - destruct (IH Hbs) as (g' & Hin & E1 & E2). exists g'. split; [right; exact Hin | split; assumption]. }
        destruct Hg as (g & Hg & <- & <-).
        pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & Hrg & _ & Htg1 & Htg2 & _).
        pose proof (ablock_of_G H IMX A HHx _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite (dv_adr rho (g_tag g) 0%uint63 off) by first [cbn [vtag]; slia | reflexivity]. rewrite (adr_wa rho (g_tag g) (g_addr g) _ Hrg) by slia. slia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hpfc : Forall (fun e : int * list int => trace_ok (as_TR H) (to_Z (fst e)) (map to_Z (snd e))) (ka_pfc A).

  Lemma chain_okb_trace : forall Q st rho msF mo s LB G FF XS ms pc0 l,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> chain_okb A st pc0 l = true ->
    exists CH, as_chain H (ms_mem ms) (bv_unsigned (dv rho (FxState.rget (a_F st) 8))) CH
       /\ trace_ok (as_TR H) (to_Z pc0) (to_Z l :: map snd CH).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms pc0 l X Hb. unfold chain_okb in Hb.
    destruct (chain_walk 64 K (ka_ts0 A) (f_mem (a_F st)) (a_blk st) (FxState.rget (a_F st) 8) [l]) as [[op ras]|] eqn:Hw; [|discriminate].
    destruct (chain_walk_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hw) as (tail & CH & Eras & Hch & Hmap).
    exists CH. split; [exact Hch|].
    assert (Et : to_Z l :: map snd CH = map to_Z ras ++ (if op then ra0_of Q :: map snd (q_CH0 Q) else [])).
    { rewrite Eras, Hmap. cbn [map app]. reflexivity. }
    rewrite Et. destruct op.
    - apply inpf_In in Hb.
      pose proof (r_pfo _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PF. unfold ra0_of.
      apply (pf_ok_site (as_TR H) _ _ _ (to_Z pc0) (map to_Z ras) PF).
      apply in_map_iff. exists (pc0, ras). split; [reflexivity | exact Hb].
    - apply inpf_In in Hb. rewrite app_nil_r. exact (proj1 (Forall_forall _ _) Hpfc (pc0, ras) Hb).
  Qed.

  Lemma chain_anyb_chain : forall Q st rho msF mo s LB G FF XS ms l,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> chain_anyb A st l = true ->
    exists CH, as_chain H (ms_mem ms) (bv_unsigned (dv rho (FxState.rget (a_F st) 8))) CH.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms l X Hb. unfold chain_anyb in Hb.
    destruct (chain_walk 64 K (ka_ts0 A) (f_mem (a_F st)) (a_blk st) (FxState.rget (a_F st) 8) [l]) as [[op ras]|] eqn:Hw; [|discriminate].
    destruct (chain_walk_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hw) as (tail & CH & _ & Hch & _). exists CH. exact Hch.
  Qed.
End Args.
