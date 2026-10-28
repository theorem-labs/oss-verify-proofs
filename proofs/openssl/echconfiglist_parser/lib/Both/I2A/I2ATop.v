(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA I2Top.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeM I2ANodeF I2ANodeR I2ANodeSig I2ASound I2ACert I2AStart.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Definition xrA (rho : int -> word) (F : fstate) (k : Z) : word := dv rho (FxState.rget F (of_Z k)).
Definition xregsA (rho : int -> word) (F : fstate) : bvmap 5 word :=
  mkRl (map (xrA rho F) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]).

(* [comment removed for export] *)
Definition blk_ofA (G : list gblk) (idx : int) : option gblk := nth_error (rev G) (Z.to_nat (to_Z idx)).
Definition xval_semA (rho : int -> word) (G : list gblk) (w : word) (x : xval) : Prop :=
  match x with
  | XAny => True
  | XW c => w = wbv c
  | XV u => w = dv rho u
  | XNew idx off => exists g, blk_ofA G idx = Some g /\ w = bv_add (wa (g_addr g)) (Z_to_bv 64 (to_Z off))
  | XBytes _ _ => True     (* [comment removed for export] *)
  end.
Definition xregs_semA (rho : int -> word) (G : list gblk) (F : fstate) (l : list (int * xval)) : Prop :=
  Forall (fun rx : int * xval => xval_semA rho G (dv rho (FxState.rget F (fst rx))) (snd rx)) l.
(* [comment removed for export] *)
Definition xbytes_atA (m : mem) (a : Z) (mask : int) (wv : w64) : Prop :=
  forall j : int, In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63 -> mask_bit mask j = true ->
    mrd asegs m (wa (a + to_Z j)) = Some (Z_to_bv 8 (to_Z (w_byte j wv))).
Definition xcell_semA (rho : int -> word) (G : list gblk) (m : mem) (a : Z) (x : xval) : Prop :=
  match x with
  | XAny => True
  | XBytes mask wv => xbytes_atA m a mask wv
  | _ => exists w, bytes_at asegs m a (le8 w) /\ xval_semA rho G w x
  end.
Definition xcells_semA (rho : int -> word) (G : list gblk) (m : mem) (l : list (int * xval)) : Prop :=
  Forall (fun cx : int * xval => xcell_semA rho G m (to_Z (fst cx)) (snd cx)) l.
Definition xbcells_semA (rho : int -> word) (G : list gblk) (m : mem) (l : list (int * int * xval)) : Prop :=
  Forall (fun bx : int * int * xval => snd bx = XAny \/
            exists g, blk_ofA G (fst (fst bx)) = Some g /\ xcell_semA rho G m (g_addr g + to_Z (snd (fst bx))) (snd bx)) l.
(* [comment removed for export] *)
Definition errno_semA (K : i2consts) (m : mem) (x : word) : Prop :=
  forall j : nat, (j < 4)%nat -> mrd asegs m (wa (to_Z (c_errcell K) + to_Z (c_errbi K) + Z.of_nat j)) = nth_error (wbytes8 x) j.

Section Top.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Local Abbreviation K := (ka_K A).
  Variable code : itrie finstr.
  Let IM := im_ro IMX.
  Let RO := ro_of K.
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis Hcode : code_ok asegs code.
  Hypothesis HROC : ro_const A.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Hypothesis Hpfc : Forall (fun e : int * list int => trace_ok (as_TR H) (to_Z (fst e)) (map to_Z (snd e))) (ka_pfc A).
  Hypothesis NFSM : anode_fsmalloc_sig H IMX A.
  Hypothesis NFSF : anode_fsfree_sig H IMX A code.
  Hypothesis NSET : anode_memset_sig H IMX A.
  Hypothesis NCPY : anode_memcpy_sig H IMX A.
  Hypothesis NLEN : anode_strlen_sig H IMX A.
  Hypothesis NMAL : anode_memalign_sig H IMX A.
  Let HH : asan_rt_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma is_final_inv : forall F, is_final K code F = true ->
    exists imm link, iget (f_pc F) code = Some (FJalr 0 1 imm link) /\ wbv imm = Z_to_bv 64 0
      /\ FxState.rget F 1 = FV (c_tra K) w_zero /\ FxState.rget F 2 = FV 1 (W64 0 (c_stack K)) /\ f_resv F = None.
  Proof.
    intros F Hf. unfold is_final in Hf. destruct (iget (f_pc F) code) as [fi|]; [|discriminate].
    destruct fi; try discriminate.
    rewrite !andb_true_iff in Hf. destruct Hf as [[[[[Hrd Hrs] Himm] Hra] Hsp] Hrv].
    apply Uint63.eqb_spec in Hrd. apply Uint63.eqb_spec in Hrs. subst.
    apply w_eqb_true_bv in Himm. rewrite wbv_w_zero in Himm.
    apply fval_eqb_eq in Hra. apply fval_eqb_eq in Hsp. apply resv_none_inv in Hrv.
    exists imm, link. repeat split; assumption || reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma i2_final_step : forall rho F ms,
    rho 0%uint63 = Z_to_bv 64 0 -> to_Z (c_tra K) < 2 ^ 60 ->
    R asegs IM rho F ms -> canonR (ms_regs ms) -> is_final K code F = true ->
    evt asegs (fun ms' => ms' = MS (ms_regs ms) (ms_fregs ms) (ret_pc (rho (c_tra K))) (ms_fcsr ms) None (ms_mem ms) (ms_rom ms)) ms.
  Proof.
    intros rho F ms Hrho0 Htra HR Hcan Hf.
    destruct (is_final_inv F Hf) as (imm & link & Hi & Himm & Hra & Hsp & Hrv).
    destruct (code_entry asegs IM rho code Hcode F ms _ HR Hi) as (Hpc & w & Hfw & [[He E] | (He & i & Hd & Hc)]); [discriminate|].
    destruct i; cbn [compile] in Hc; try discriminate Hc;
      repeat match type of Hc with context [match ?x with _ => _ end] => destruct x; try discriminate Hc end.
    injection Hc as Erd Ers Eimm Elink.
    apply evt_step with (ms1 := MS (ms_regs ms) (ms_fregs ms) (ret_pc (rho (c_tra K))) (ms_fcsr ms) None (ms_mem ms) (ms_rom ms)); [|apply evt_done; reflexivity].
    split; [exact (R_svc _ _ _ _ _ HR)|].
    rewrite (step_decode asegs ms w _ Hfw He Hd). unfold exec. cbv zeta. rewrite interp_done.
    (* [comment removed for export] *)
    assert (Hrd0 : is_x0 rd = true).
    { unfold is_x0. unfold ireg in Erd. apply (f_equal to_Z) in Erd. rewrite Uint63.of_Z_spec in Erd.
      pose proof (bv_unsigned_in_range _ rd) as Hr. change (bv_modulus 5) with 32 in Hr. change (to_Z 0%uint63) with 0 in Erd.
      rewrite Z.mod_small in Erd by (change wB with (2 ^ 63); slia). apply Z.eqb_eq. exact Erd. }
    unfold Sem.rset. rewrite Hrd0.
    assert (Ers1 : Sem.rget (core_of ms) rs1 = rho (c_tra K)).
    { rewrite (R_regs _ _ _ _ _ HR rs1). rewrite Ers, Hra. apply dv_tag_zero. exact Htra. }
    assert (Eimm0 : sext 64 imm0 = Z_to_bv 64 0) by (rewrite <- (wbv_w_of_bv (sext 64 imm0)), Eimm; exact Himm).
    rewrite Ers1, Eimm0. unfold ms_of. cbn [core_of c_regs c_fregs c_pc c_fcsr c_resv with_pc].
    rewrite (R_resv _ _ _ _ _ HR), Hrv. cbn [option_map].
    assert (Eadd : (rho (c_tra K) + Z_to_bv 64 0)%bv = rho (c_tra K)).
    { apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
    rewrite Eadd. unfold ret_pc, w1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wbytes8_le8 : forall w, wbytes8 w = le8 w.
  Proof. intros w. unfold wbytes8. rewrite <- store_bytes_8. reflexivity. Qed.

  Lemma blk_of_map : forall (G : list gblk) idx t n,
    nth_error (rev (map (fun g => (g_tag g, g_size g)) G)) (Z.to_nat (to_Z idx)) = Some (t, n) ->
    exists g, blk_ofA G idx = Some g /\ g_tag g = t /\ g_size g = n.
  Proof.
    intros G idx t n Hn. unfold blk_ofA. rewrite <- map_rev in Hn.
    rewrite nth_error_map in Hn. destruct (nth_error (rev G) (Z.to_nat (to_Z idx))) as [g|]; [|discriminate].
    cbn in Hn. injection Hn as <- <-. exists g. repeat split; reflexivity.
  Qed.

  Lemma xval_ok_sem : forall Q st rho msF mo s LB G FF XS ms v x,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> xval_ok (st_of st) v x = true -> xval_semA rho G (dv rho v) x.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms v x X Hx. destruct x as [|w|u|idx off|mask wv]; cbn [xval_ok st_of i_F i_blk] in Hx; [| | | | exact I].
    - exact I.
    - apply fval_eqb_eq in Hx. subst v. cbn [xval_semA]. apply fk_dv_conc. exact (r_rho0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
    - apply fval_eqb_eq in Hx. subst v. reflexivity.
    - unfold blocks_old_first in Hx. cbn [st_of i_blk] in Hx. rewrite (r_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) in Hx.
      destruct (nth_error (rev (map (fun g : gblk => (g_tag g, g_size g)) G)) (Z.to_nat (to_Z idx))) as [[t n]|] eqn:En; [|discriminate].
      destruct (blk_of_map G idx t n En) as (g & Hg & <- & <-).
      apply fval_eqb_eq in Hx. subst v. cbn [xval_semA]. exists g. split; [exact Hg|].
      assert (Hin : In g G).
      { unfold blk_ofA in Hg. apply nth_error_In in Hg. apply in_rev in Hg. exact Hg. }
      pose proof (proj1 (Forall_forall _ _) (r_Gin _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) g Hin) as (_ & Hrg & _ & Htg & Htg2 & _).
      pose proof (r_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      rewrite (fk_dv_plain rho (FV (g_tag g) (W64 0 off))) by (cbn [vtag]; slia).
      cbn [vtag vw]. rewrite Hrg. unfold wbv. rewrite wZ_even_top by reflexivity. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma cell0_bytes : forall Q st rho msF mo s LB G FF XS ms c v,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    cell_of (f_mem (a_F st)) 0%uint63 c = Some v -> to_Z c mod 8 = 0 ->
    bytes_at asegs (ms_mem ms) (to_Z c) (le8 (dv rho v)).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms c v X Hc Hc8.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    pose proof (XRn rho (agree_refl _ rho Xr0)) as HR.
    unfold cell_of in Hc. destruct (iget 0%uint63 (f_mem (a_F st))) as [rg0|] eqn:E0; [|discriminate].
    destruct (iget (c >> 12)%uint63 (rg_pages rg0)) as [p|] eqn:Ep; [|discriminate].
    destruct (iget ((c land 4095) >> 3)%uint63 (pg_cells p)) as [[v0| |sl]|] eqn:Eci; try discriminate. injection Hc as Ev. subst v0.
    destruct Xreg0 as (rg0_ & E0_ & Hlo0 & Hlen0 & _). assert (rg0_ = rg0) by congruence. subst rg0_.
    pose proof (i63_range c) as Hc63.
    destruct (Xinb 0%uint63 rg0 _ _ _ _ E0 Ep Eci) as [Hinb Hci512]. rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095 in Hinb. rewrite to_Z_lsr3, to_Z_land4095 in Hci512.
    pose proof Hlen0 as Hlen0'. unfold AIMG_TOP in Hlen0'.
    destruct (R_mem _ _ _ _ _ HR) as [Hregs _]. destruct (Hregs 0%uint63 rg0 E0) as [_ Hpages].
    assert (Hpn : to_Z (c >> 12)%uint63 < 2 ^ 50) by (rewrite to_Z_lsr12; slia).
    assert (Hpa : page_at IM rg0 0%uint63 (c >> 12)%uint63 = Some p) by (unfold page_at; rewrite Ep; reflexivity).
    destruct (Hpages _ _ Hpn Hpa) as ((_ & Hcells & _) & _).
    assert (Hcl : 0 <= to_Z ((c land 4095) >> 3)%uint63 < clim rg0 (c >> 12)%uint63).
    { rewrite to_Z_lsr3, to_Z_land4095. apply clim_intro; [pose proof (cell_index_range (to_Z c) ltac:(slia)); slia | rewrite to_Z_lsr12; slia]. }
    specialize (Hcells _ v Hcl ltac:(unfold cell_at; rewrite Eci; reflexivity)).
    split; [slia|]. split; [rewrite length_le8; slia|]. intros i Hi. rewrite length_le8 in Hi.
    rewrite <- wbytes8_le8. rewrite <- (Hcells i Hi).
    change (mrd asegs (ms_mem ms) (wa (to_Z c + Z.of_nat i))) with (rview asegs (ms_mem ms) (wa (to_Z c + Z.of_nat i))). f_equal.
    rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. rewrite (adr_eq_wa rho 0%uint63 0); [| rewrite Xr0; reflexivity | slia | slia | slia].
    f_equal. pose proof (off_decomp (to_Z c) ltac:(slia)). slia.
  Qed.

  (* [comment removed for export] *)
  Lemma cellb_bytes : forall Q st rho msF mo s LB G FF XS ms g off v,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> In g G ->
    cell_of (f_mem (a_F st)) (g_tag g) off = Some v -> to_Z off mod 8 = 0 -> to_Z off + 8 <= to_Z (g_size g) ->
    bytes_at asegs (ms_mem ms) (g_addr g + to_Z off) (le8 (dv rho v)).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms g off v X Hg Hc Ho8 Hosz.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    pose proof (XRn rho (agree_refl _ rho Xr0)) as HR.
    pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (Hin & Hrg & Hsz & Htg & Htg2 & (rg & Hgg & Hlo & Hlen & _) & _).
    pose proof (ablock_of_G H IMX A HHx Q st rho msF mo s LB G FF XS ms g X Hg) as (R1 & R2 & R3 & R4 & R5 & _). pose proof aceil_facts.
    unfold cell_of in Hc. rewrite Hgg in Hc.
    destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p|] eqn:Ep; [|discriminate].
    destruct (iget ((off land 4095) >> 3)%uint63 (pg_cells p)) as [[v0| |sl]|] eqn:Eci; try discriminate. injection Hc as Ev. subst v0.
    pose proof (i63_range off) as Ho63. pose proof (i63_range (g_size g)).
    destruct (R_mem _ _ _ _ _ HR) as [Hregs _]. destruct (Hregs _ rg Hgg) as [_ Hpages].
    assert (Hpn : to_Z (off >> 12)%uint63 < 2 ^ 50) by (rewrite to_Z_lsr12; slia).
    assert (Hpa : page_at IM rg (g_tag g) (off >> 12)%uint63 = Some p) by (unfold page_at; rewrite Ep; reflexivity).
    destruct (Hpages _ _ Hpn Hpa) as ((_ & Hcells & _) & _).
    assert (Hcl : 0 <= to_Z ((off land 4095) >> 3)%uint63 < clim rg (off >> 12)%uint63).
    { rewrite to_Z_lsr3, to_Z_land4095. apply clim_intro; [pose proof (cell_index_range (to_Z off) ltac:(slia)); slia | rewrite to_Z_lsr12, Hlen].
      pose proof (off_decomp (to_Z off) ltac:(slia)). Z.div_mod_to_equations. nia. }
    specialize (Hcells _ v Hcl ltac:(unfold cell_at; rewrite Eci; reflexivity)).
    split; [slia|]. split; [rewrite length_le8; slia|]. intros i Hi. rewrite length_le8 in Hi.
    rewrite <- wbytes8_le8. rewrite <- (Hcells i Hi).
    change (mrd asegs (ms_mem ms) (wa (g_addr g + to_Z off + Z.of_nat i))) with (rview asegs (ms_mem ms) (wa (g_addr g + to_Z off + Z.of_nat i))). f_equal.
    rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. rewrite (adr_eq_wa rho (g_tag g) (g_addr g)); [| exact Hrg | slia | slia |].
    2:{ pose proof (off_decomp (to_Z off) ltac:(slia)). slia. }
    f_equal. pose proof (off_decomp (to_Z off) ltac:(slia)). slia.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_byte : forall Q st rho msF mo s LB G FF XS ms t rg pn p ci sl (j : int) b Ab,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    iget t (f_mem (a_F st)) = Some rg -> iget pn (rg_pages rg) = Some p -> iget ci (pg_cells p) = Some (CB sl) ->
    0 <= to_Z j < 8 -> sget j sl = SK b ->
    to_Z pn * 4096 + to_Z ci * 8 + to_Z j < to_Z (rg_len rg) ->
    rho t = wa Ab -> 0 <= Ab -> Ab + to_Z (rg_len rg) < 2 ^ 64 ->
    mrd asegs (ms_mem ms) (wa (Ab + (to_Z pn * 4096 + to_Z ci * 8 + to_Z j))) = Some (Z_to_bv 8 (to_Z b)).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms t rg pn p ci sl j b Ab X Ht Hp Hc Hj Hs Hlt HA HA0 HA64.
    pose proof X as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    pose proof (XRn rho (agree_refl _ rho Xr0)) as HR.
    pose proof (i63_range pn) as Hpn0. pose proof (i63_range ci) as Hci0. pose proof (i63_range (rg_len rg)) as Hlen0.
    destruct (Xinb t rg pn p ci _ Ht Hp Hc) as (Hst & Hci512 & _).
    destruct (R_mem _ _ _ _ _ HR) as [Hregs _]. destruct (Hregs t rg Ht) as [Hro Hpages]. pose proof (proj1 (proj2 Hro)) as Hlen62.
    assert (Hpn : to_Z pn < 2 ^ 50) by (clear -Hst Hlen62 Hpn0 Hci0; slia).
    assert (Hpa : page_at IM rg t pn = Some p) by (unfold page_at; rewrite Hp; reflexivity).
    destruct (Hpages _ _ Hpn Hpa) as ((_ & _ & Hslots & _) & _ & Hpnlt).
    assert (Hb : to_Z ci * 8 + to_Z j < blim rg pn) by (unfold blim; slia).
    destruct (Hslots ci sl ltac:(slia) ltac:(slia) Hc j Hj) as [Hin _]. specialize (Hin Hb). rewrite Hs in Hin. cbn [slot_ok] in Hin.
    rewrite (adr_eq_wa rho t Ab) in Hin; [| exact HA | exact HA0 | slia | slia].
    exact Hin.
  Qed.

  Lemma In8_range : forall j : int, In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63 -> 0 <= to_Z j < 8.
  Proof. intros j Hj. cbn in Hj. repeat (destruct Hj as [<-|Hj]; [cbn; slia|]). destruct Hj. Qed.

  (* [comment removed for export] *)
  Lemma xbytes_cell : forall Q st rho msF mo s LB G FF XS ms t rg off c mask wv Ab,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms ->
    iget t (f_mem (a_F st)) = Some rg -> cell_raw (f_mem (a_F st)) t off = Some c -> to_Z off mod 8 = 0 ->
    match c with CV v => xval_ok (st_of st) v (XBytes mask wv) = true | CB sl => slots_match mask wv sl = true | CU => False end ->
    (forall j : int, In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63 -> mask_bit mask j = true -> to_Z off + to_Z j < to_Z (rg_len rg)) ->
    rho t = wa Ab -> 0 <= Ab -> Ab + to_Z (rg_len rg) < 2 ^ 64 ->
    (forall v, c = CV v -> bytes_at asegs (ms_mem ms) (Ab + to_Z off) (le8 (dv rho v))) ->
    xbytes_atA (ms_mem ms) (Ab + to_Z off) mask wv.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms t rg off c mask wv Ab X Ht Hraw Ho8 Hm Hinb HA HA0 HA64 Hcv j Hj Hmj.
    pose proof (In8_range j Hj) as Hj8. pose proof (i63_range off) as Ho.
    unfold cell_raw in Hraw. rewrite Ht in Hraw.
    destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p|] eqn:Hp; [|discriminate].
    assert (Eoff : to_Z (off >> 12)%uint63 * 4096 + to_Z ((off land 4095) >> 3)%uint63 * 8 = to_Z off).
    { rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095. pose proof (off_decomp (to_Z off) ltac:(slia)). slia. }
    destruct c as [v| |sl].
    - (* [comment removed for export] *)
      specialize (Hcv v eq_refl). destruct v as [tv w']. cbn [xval_ok st_of i_F i_blk] in Hm. apply andb_true_iff in Hm as [Et Hbm].
      apply Uint63.eqb_spec in Et. subst tv.
      unfold I2Run.bytes_match in Hbm. rewrite forallb_forall in Hbm. specialize (Hbm j Hj). rewrite Hmj in Hbm. cbn [negb orb] in Hbm.
      apply Uint63.eqb_spec in Hbm.
      destruct Hcv as (_ & _ & Hb). rewrite length_le8 in Hb. specialize (Hb (Z.to_nat (to_Z j)) ltac:(slia)).
      rewrite Z2Nat.id in Hb by slia. rewrite Hb. rewrite <- wbytes8_le8, (fk_dv_conc rho w' (r_rho0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)), wbytes8_wbv.
      rewrite (w_bytes_nth_byte w' j) by slia. rewrite Hbm. reflexivity.
    - destruct Hm.
    - (* [comment removed for export] *)
      unfold slots_match in Hm. rewrite forallb_forall in Hm. specialize (Hm j Hj). rewrite Hmj in Hm. cbn [negb orb] in Hm.
      destruct (sget j sl) as [b| |] eqn:Es; try discriminate. apply Uint63.eqb_spec in Hm.
      rewrite <- Hm, byte_land255.
      rewrite <- Eoff. rewrite <- Z.add_assoc.
      replace (Ab + (to_Z (off >> 12)%uint63 * 4096 + to_Z ((off land 4095) >> 3)%uint63 * 8) + to_Z j)
        with (Ab + (to_Z (off >> 12)%uint63 * 4096 + to_Z ((off land 4095) >> 3)%uint63 * 8 + to_Z j)) by slia.
      apply (slot_byte Q st rho msF mo s LB G FF XS ms t rg _ p _ sl j b Ab X Ht Hp Hraw Hj8 Es); [rewrite Eoff; exact (Hinb j Hj Hmj) | exact HA | exact HA0 | exact HA64].
  Qed.

  Lemma export_sound : forall Q st rho msF mo s LB G FF XS ms X,
    I2RAX H IMX A Q st rho msF mo s LB G FF XS ms -> export_ok K (st_of st) X = true ->
    xregs_semA rho G (a_F st) (x_regs X) /\ xcells_semA rho G (ms_mem ms) (x_cells X) /\ xbcells_semA rho G (ms_mem ms) (x_bcells X)
    /\ map g_size (rev G) = x_sizes X
    /\ match x_errno X with None => True | Some t => to_Z t < 2 ^ 60 -> errno_semA K (ms_mem ms) (rho t) end.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms X HX Hx. unfold export_ok in Hx. rewrite !andb_true_iff in Hx.
    destruct Hx as [[[[[Hr Hc] Hb] Hn] Hs] He]. rewrite forallb_forall in Hr, Hc, Hb.
    pose proof HX as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    destruct Xreg0 as (rg0 & Hrg0 & Hlo0 & Hlen0 & _).
    split; [|split; [|split; [|split]]].
    - apply Forall_forall. intros [r x] Hin. cbn [fst snd]. exact (xval_ok_sem _ _ _ _ _ _ _ _ _ _ _ _ _ HX (Hr (r, x) Hin)).
    - apply Forall_forall. intros [c x] Hin. cbn [fst snd]. specialize (Hc (c, x) Hin). cbn [fst snd] in Hc.
      apply andb_true_iff in Hc as [Hc8 Hcx]. apply Uint63.eqb_spec in Hc8. apply (f_equal to_Z) in Hc8. rewrite to_Z_land7 in Hc8. change (to_Z 0%uint63) with 0 in Hc8.
      pose proof (i63_range c).
      destruct x as [|w|u|idx off|mask wv]; [exact I | | | |];
        [ (cbn [xcell_ok xcell_semA st_of i_F i_blk] in Hcx |- *; destruct (cell_of (f_mem (a_F st)) 0 c) as [v|] eqn:Ev; [|discriminate];
           exists (dv rho v); split; [exact (cell0_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ HX Ev Hc8) | exact (xval_ok_sem _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hcx)]) .. |].
      (* [comment removed for export] *)
      cbn [xcell_ok xcell_semA st_of i_F i_blk] in Hcx |- *.
      destruct (cell_raw (f_mem (a_F st)) 0 c) as [cr|] eqn:Hraw; [|discriminate].
      rewrite <- (Z.add_0_l (to_Z c)).
      apply (xbytes_cell Q st rho msF mo s LB G FF XS ms 0%uint63 rg0 c cr mask wv 0 HX Hrg0 Hraw Hc8).
      + destruct cr; [exact Hcx | discriminate | exact Hcx].
      + intros j Hj _. pose proof (In8_range j Hj).
        unfold cell_raw in Hraw. rewrite Hrg0 in Hraw. destruct (iget (c >> 12)%uint63 (rg_pages rg0)) as [p|] eqn:Hp; [|discriminate].
        destruct (Xinb 0%uint63 rg0 _ p _ cr Hrg0 Hp Hraw) as (Hst & _). rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095 in Hst. rewrite Hlen0 in Hst |- *.
        pose proof (off_decomp (to_Z c) ltac:(slia)). unfold AIMG_TOP in *. slia.
      + rewrite Xr0. reflexivity.
      + slia.
      + rewrite Hlen0. unfold AIMG_TOP. slia.
      + intros v ->. rewrite Z.add_0_l. apply (cell0_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ HX); [|exact Hc8].
        unfold cell_of. unfold cell_raw in Hraw. rewrite Hrg0 in Hraw |- *.
        destruct (iget (c >> 12)%uint63 (rg_pages rg0)) as [p|]; [|discriminate]. rewrite Hraw. reflexivity.
    - apply Forall_forall. intros [[idx off] x] Hin. cbn [fst snd]. specialize (Hb (idx, off, x) Hin). cbn [fst snd] in Hb.
      unfold blocks_old_first in Hb. cbn [st_of i_blk] in Hb. rewrite XG in Hb.
      destruct (nth_error (rev (map (fun g : gblk => (g_tag g, g_size g)) G)) (Z.to_nat (to_Z idx))) as [[t n]|] eqn:En; [|discriminate].
      destruct (blk_of_map G idx t n En) as (g & Hg & <- & <-).
      rewrite !andb_true_iff in Hb. destruct Hb as [[Ho8 Hon] Hcx].
      apply Uint63.eqb_spec in Ho8. apply (f_equal to_Z) in Ho8. rewrite to_Z_land7 in Ho8. change (to_Z 0%uint63) with 0 in Ho8.
      pose proof (i63_range off). pose proof (i63_range (g_size g)).
      assert (Hing : In g G) by (unfold blk_ofA in Hg; apply nth_error_In in Hg; apply in_rev in Hg; exact Hg).
      pose proof (proj1 (Forall_forall _ _) XGin g Hing) as (HinLB & Hrg & Hsz & Htg & Htg2 & (rg & Hgg & Hlog & Hleng & _) & _).
      pose proof (ablock_of_G H IMX A HHx Q st rho msF mo s LB G FF XS ms g HX Hing) as (R1 & R2 & R3 & R4 & R5 & _). pose proof aceil_facts.
      destruct x as [|w|u|idx' off'|mask wv]; [left; reflexivity | right | right | right | right]; exists g; (split; [exact Hg|]).
      1-3: cbn [xb_inb st_of i_F i_blk] in Hon; apply andb_true_iff in Hon as [H8n Hon];
        apply Uint63.leb_spec in H8n; change (to_Z 8%uint63) with 8 in H8n;
        apply Uint63.leb_spec in Hon; rewrite Uint63.sub_spec in Hon; change (to_Z 8%uint63) with 8 in Hon; change wB with (2 ^ 63) in Hon;
        rewrite Z.mod_small in Hon by slia;
        (cbn [xcell_ok xcell_semA st_of i_F i_blk] in Hcx |- *; destruct (cell_of (f_mem (a_F st)) (g_tag g) off) as [v|] eqn:Ev; [|discriminate];
         exists (dv rho v); split; [exact (cellb_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hing Ev Ho8 ltac:(slia)) | exact (xval_ok_sem _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hcx)]).
      (* [comment removed for export] *)
      cbn [xb_inb st_of i_F i_blk] in Hon. apply andb_true_iff in Hon as [Hon Hjn]. apply Uint63.ltb_spec in Hon. rewrite forallb_forall in Hjn.
      cbn [xcell_ok xcell_semA st_of i_F i_blk] in Hcx |- *.
      destruct (cell_raw (f_mem (a_F st)) (g_tag g) off) as [cr|] eqn:Hraw; [|discriminate].
      apply (xbytes_cell Q st rho msF mo s LB G FF XS ms (g_tag g) rg off cr mask wv (g_addr g) HX Hgg Hraw Ho8).
      + destruct cr; [exact Hcx | discriminate | exact Hcx].
      + intros j Hj Hmj. pose proof (In8_range j Hj). specialize (Hjn j Hj). rewrite Hmj in Hjn. cbn [negb orb] in Hjn.
        apply Uint63.ltb_spec in Hjn. rewrite Uint63.add_spec in Hjn. change wB with (2 ^ 63) in Hjn. rewrite Z.mod_small in Hjn by slia.
        rewrite Hleng. exact Hjn.
      + exact Hrg.
      + slia.
      + rewrite Hleng. slia.
      + intros v ->.
        assert (Ev : cell_of (f_mem (a_F st)) (g_tag g) off = Some v).
        { unfold cell_of. unfold cell_raw in Hraw. rewrite Hgg in Hraw |- *.
          destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p|]; [|discriminate]. rewrite Hraw. reflexivity. }
        (* [comment removed for export] *)
        unfold cell_raw in Hraw. rewrite Hgg in Hraw. destruct (iget (off >> 12)%uint63 (rg_pages rg)) as [p|] eqn:Hp; [|discriminate].
        destruct (Xinb (g_tag g) rg _ p _ (CV v) Hgg Hp Hraw) as (_ & _ & Hwhole). specialize (Hwhole v eq_refl).
        rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095, Hleng in Hwhole. pose proof (off_decomp (to_Z off) ltac:(slia)).
        exact (cellb_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hing Ev Ho8 ltac:(slia)).
    - unfold blocks_old_first in Hs. cbn [st_of i_blk] in Hs. rewrite (r_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX) in Hs. rewrite <- map_rev, map_map in Hs. cbn [snd] in Hs.
      clear -Hs. revert Hs. generalize (x_sizes X) as l.
      induction (rev G) as [|g r IH]; intros l Hs; destruct l as [|y l]; cbn [map list_int_eqb] in Hs |- *; try discriminate; [reflexivity|].
      apply andb_true_iff in Hs as [E1 E2]. apply Uint63.eqb_spec in E1. rewrite E1, (IH l E2). reflexivity.
    - (* [comment removed for export] *)
      destruct (x_errno X) as [te|]; [|exact I]. intros Hte j Hj.
      unfold errno_is in He. rewrite Hrg0 in He.
      destruct (iget (c_errcell K >> 12)%uint63 (rg_pages rg0)) as [p|] eqn:Hp; [|discriminate].
      destruct (iget ((c_errcell K land 4095) >> 3)%uint63 (pg_cells p)) as [[v| |sl]|] eqn:Hcr; try discriminate.
      rewrite !andb_true_iff in He. destruct He as [[[E0 E1] E2] E3].
      pose proof (HK_err A HK) as (Herrno & He8 & Hbi4 & _). unfold AERRNO, ATP in Herrno. pose proof (i63_range (c_errcell K)) as Hec0. pose proof (i63_range (c_errbi K)) as Heb0.
      assert (Hsl : forall (k : int) jj, errno_slot_is te jj (sget k sl) = true -> 0 <= to_Z k < 8 -> 0 <= to_Z jj < 4 ->
                mrd asegs (ms_mem ms) (wa (0 + (to_Z (c_errcell K >> 12)%uint63 * 4096 + to_Z ((c_errcell K land 4095) >> 3)%uint63 * 8 + to_Z k)))
                = nth_error (wbytes8 (rho te)) (Z.to_nat (to_Z jj))).
      { intros k jj Hk Hk8 Hjj. rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095.
        match goal with |- mrd ?sg ?mm ?aa = _ => change (mrd sg mm aa) with (rview sg mm aa) end.
        unfold errno_slot_is in Hk.
        destruct (sget k sl) as [b|[t' w'] j'|] eqn:Es; try discriminate.
        rewrite !andb_true_iff in Hk. destruct Hk as [[Ej Ew] Et]. apply Uint63.eqb_spec in Ej. subst j'.
        apply w_eqb_true_bv in Ew.
        pose proof (XRn rho (agree_refl _ rho Xr0)) as HR.
        destruct (R_mem _ _ _ _ _ HR) as [Hregs _]. destruct (Hregs 0%uint63 rg0 Hrg0) as [_ Hpages].
        assert (Hpn : to_Z (c_errcell K >> 12)%uint63 < 2 ^ 50) by (rewrite to_Z_lsr12; clear -Herrno Hec0 Heb0; slia).
        assert (Hpa : page_at IM rg0 0%uint63 (c_errcell K >> 12)%uint63 = Some p) by (unfold page_at; rewrite Hp; reflexivity).
        destruct (Hpages _ _ Hpn Hpa) as ((_ & _ & Hslots & _) & _ & Hpnlt).
        destruct (Xinb 0%uint63 rg0 _ p _ (CB sl) Hrg0 Hp Hcr) as (Hst & Hci512 & _).
        rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095, Hlen0 in Hst. rewrite to_Z_lsr3, to_Z_land4095 in Hci512. rewrite Hlen0 in Hpnlt.
        pose proof (off_decomp (to_Z (c_errcell K)) ltac:(slia)) as Hdec.
        assert (Hbl : to_Z (c_errcell K) mod 4096 / 8 * 8 + to_Z k < blim rg0 (c_errcell K >> 12)%uint63).
        { unfold blim. rewrite to_Z_lsr12, Hlen0. unfold AIMG_TOP in *. clear -Hst Hk8 Hpnlt Hec0. Z.div_mod_to_equations. slia. }
        destruct (Hslots ((c_errcell K land 4095) >> 3)%uint63 sl ltac:(rewrite to_Z_lsr3, to_Z_land4095; clear -Hec0; Z.div_mod_to_equations; slia)
                    ltac:(rewrite to_Z_lsr3, to_Z_land4095; clear -Hbl Hk8; slia) Hcr k Hk8) as [Hin _].
        rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095 in Hin. specialize (Hin Hbl). rewrite Es in Hin. cbn [slot_ok] in Hin.
        rewrite (adr_eq_wa rho 0%uint63 0) in Hin; [| rewrite Xr0; reflexivity | slia | slia | slia].
        rewrite Hin.
        assert (Eadd0 : bv_add (rho te) (wbv w_zero) = rho te).
        { rewrite wbv_w_zero. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
        apply orb_true_iff in Et as [Et|Et]; apply Uint63.eqb_spec in Et; subst t'.
        - rewrite (fk_dv_plain rho) by (cbn [vtag]; clear -Hte; slia). cbn [vtag vw]. rewrite Ew, Eadd0. reflexivity.
        - rewrite (fk_dv_ktag rho K_LO te) by (first [cbn; clear -Hte; slia | clear -Hte; slia]). rewrite fk_dvk_LO, Ew, Eadd0.
          exact (fk_bytes_sx32 (rho te) (Z.to_nat (to_Z jj)) ltac:(clear -Hjj; slia)). }
      set (jN := (of_Z (Z.of_nat j) : int)).
      assert (EjN : to_Z jN = Z.of_nat j) by (subst jN; rewrite Uint63.of_Z_spec; change wB with (2 ^ 63); apply Z.mod_small; slia).
      assert (Ek : to_Z (c_errbi K + jN)%uint63 = to_Z (c_errbi K) + Z.of_nat j).
      { rewrite Uint63.add_spec, EjN. change wB with (2 ^ 63). apply Z.mod_small. slia. }
      specialize (Hsl (c_errbi K + jN)%uint63 jN).
      rewrite to_Z_lsr12, to_Z_lsr3, to_Z_land4095, Ek, EjN, Nat2Z.id in Hsl.
      pose proof (off_decomp (to_Z (c_errcell K)) ltac:(slia)) as Hdec.
      replace (0 + (to_Z (c_errcell K) / 4096 * 4096 + to_Z (c_errcell K) mod 4096 / 8 * 8 + (to_Z (c_errbi K) + Z.of_nat j)))
        with (to_Z (c_errcell K) + to_Z (c_errbi K) + Z.of_nat j) in Hsl by slia.
      apply Hsl; [| slia | slia].
      destruct j as [|[|[|[|j]]]]; [ | | | | slia]; subst jN; cbn; [exact E0 | exact E1 | exact E2 | exact E3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ro_lookup_in : forall a l c, ro_lookup a l = Some c -> In (a, c) l.
  Proof.
    intros a l. induction l as [|[a' c'] l IH]; intros c Hl; cbn [ro_lookup] in Hl; [discriminate|].
    destruct (a' =? a)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst a'. injection Hl as <-. left. reflexivity.
    - right. exact (IH c Hl).
  Qed.

  Lemma xw_ok_cells0_in : forall F, xw_okA A F = true -> cells0_in A (f_mem F).
  Proof.
    intros F Hx rg0 pn p ci c H0 Hp Hc. unfold xw_okA in Hx. rewrite H0 in Hx. rewrite forallb_forall in Hx.
    specialize (Hx (pn, p) (proj2 (ielements_spec _ _ _) Hp)). cbn [fst snd] in Hx. apply andb_true_iff in Hx as [Hpn Hx].
    rewrite forallb_forall in Hx. specialize (Hx (ci, c) (proj2 (ielements_spec _ _ _) Hc)). cbn [fst snd] in Hx. apply andb_true_iff in Hx as [Hci Hx].
    apply Uint63.ltb_spec in Hpn. apply Uint63.ltb_spec in Hci. change (to_Z 4096%uint63) with 4096 in Hpn. change (to_Z 512%uint63) with 512 in Hci.
    pose proof (i63_range pn). pose proof (i63_range ci).
    assert (Ea : to_Z ((pn << 12) + (ci << 3))%uint63 = to_Z pn * 4096 + to_Z ci * 8).
    { rewrite Uint63.add_spec, !Uint63.lsl_spec. change (2 ^ to_Z 12%uint63) with 4096. change (2 ^ to_Z 3%uint63) with 8. change wB with (2 ^ 63).
      rewrite !Z.mod_small by slia. reflexivity. }
    cbv zeta. unfold cell0_ok in Hx. rewrite !orb_true_iff in Hx. destruct Hx as [[Hxw | He] | Hro].
    - left. apply existsb_exists in Hxw as (x & Hin & Ex). apply Uint63.eqb_spec in Ex. exists x. split; [exact Hin | rewrite Ex; exact Ea].
    - right. left. apply Uint63.eqb_spec in He. rewrite <- Ea, He. reflexivity.
    - right. right. destruct (ro_lookup ((pn << 12) + (ci << 3))%uint63 (c_ro K)) as [c'|] eqn:El; [|discriminate].
      rewrite <- Ea, of_to_Z. exists c'. exact (ro_lookup_in _ _ _ El).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition shad_all (st : i2ast) : bool :=
    forallb (fun tn : int * int => match iget (fst tn + 1)%uint63 (f_mem (a_F st)) with Some _ => true | None => false end) (a_blk st).
  (* [comment removed for export] *)
  Definition i2a_check2 (fuel : nat) (st0 : i2ast) (X : export) : bool :=
    start_ok K (st_of st0) && match a_ff st0 with [] => true | _ => false end &&
    match i2a_run IM A code fuel st0 with
    | ADone st' => xw_okA A (a_F st') && export_ok K (st_of st') X && match a_ff st' with [] => true | _ => false end
                   && match a_cs st' with [] => true | _ => false end && shad_all st'
    | ARej _ _ => false
    end.
  Lemma i2a_check2_split : forall fuel st0 X, i2a_check2 fuel st0 X = true ->
    i2a_check IM A code fuel st0 X = true
    /\ match i2a_run IM A code fuel st0 with ADone st' => shad_all st' = true | ARej _ _ => False end.
  Proof.
    intros fuel st0 X Hc. unfold i2a_check2 in Hc. unfold i2a_check.
    apply andb_true_iff in Hc as [Hpre Hc]. rewrite Hpre. cbn [andb].
    destruct (i2a_run IM A code fuel st0) as [st'|c stx]; [|discriminate].
    rewrite !andb_true_iff in Hc. destruct Hc as [[[[H1 H2] H3] H4] H5]. rewrite H1, H2, H3, H4. split; [reflexivity | exact H5].
  Qed.

  Definition i2a_post (Q : i2aenv) (X : export) : config -> Prop :=
    fun k => exists rho' st' (s' : as_St H) LB' G' XS' ms1,
      as_VIS H s' (cfg_ms k) = MS (ms_regs ms1) (q_F Q) (ret_pc (q_rho0 Q (c_tra K))) (q_fc Q) None (ms_mem ms1) (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H (q_mo0 Q) (cfg_model k)
      /\ (exists msF1 mo1, I2RAX H IMX A Q st' rho' msF1 mo1 s' LB' G' [] XS' ms1)
      /\ is_final K code (a_F st') = true /\ a_cs st' = []
      /\ xregs_semA rho' G' (a_F st') (x_regs X) /\ xcells_semA rho' G' (ms_mem ms1) (x_cells X)
      /\ xbcells_semA rho' G' (ms_mem ms1) (x_bcells X) /\ map g_size (rev G') = x_sizes X
      /\ match x_errno X with None => True | Some t => to_Z t < 2 ^ 60 -> errno_semA K (ms_mem ms1) (rho' t) end
      /\ Forall (fun g => addressable (ms_mem ms1) (g_addr g) (to_Z (g_size g))) G'.

  Theorem i2a_certificate : forall fuel (stb : i2ast) (X : export) (G0 : list gblk) (rho0 : int -> word)
      (x : Z -> word) (Fr : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
      (s : as_St H) (LB : list block) (LF : list fframe) (lo B : Z) (CH : list (Z * Z)),
    let sp := bv_unsigned (x 2) in
    let ms := MS (mkRl (map x L31)) Fr (Z_to_bv 64 (to_Z (f_pc (a_F stb)))) fc None m (seg_rom asegs) in
    i2a_check2 fuel (a_start A stb) X = true ->
    start_shape_okA A IMX stb = true ->
    a_cs stb = [] ->
    a_blk stb = map (fun g => (g_tag g, g_size g)) G0 ->
    List.NoDup (map g_id G0) ->
    Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) LB /\ rho0 (g_tag g) = wa (g_addr g)
                     /\ stk asegs m (g_addr g) (g_addr g + to_Z (g_size g))) G0 ->
    Rn asegs IMX (a_n stb) rho0 (a_F stb) ms ->
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
    as_SR H (i2a_post (I2AE sp lo B sp mo Fr fc m LB LF (a_n stb) rho0 G0 (bv_unsigned (rho0 (ka_ts0 A))) CH (as_AL H s) (ka_costs A)) X)
            (mkCfg msF mo).
  Proof.
    intros fuel stb X G0 rho0 x Fr fc msF m mo s LB LF lo B CH sp ms Hchk Hshape Hcs HG Hnd HG0 HRn Hr0 Hr1 Hr2 Hr3
           Hvis Hakrel Hheap Hrfs Hac Hst0 Hchain HCH Hpfo HAL Hcst Hcnt Hlf Haux HB HB64 Hstk Hhl Hlo Hsp16 Hsp32 Herr Hinv.
    apply i2a_check2_split in Hchk as [Hchk Hshad].
    unfold i2a_check in Hchk. apply andb_true_iff in Hchk as [Hpre Hchk]. apply andb_true_iff in Hpre as [Hstart Hff0].
    destruct (i2a_run IM A code fuel (a_start A stb)) as [st'|c stx] eqn:Hrun; [|discriminate].
    rewrite !andb_true_iff in Hchk. destruct Hchk as [[[Hxw Hexp] Hff'] Hcs'].
    destruct (a_ff st') as [|f0 fr] eqn:Eff'; [|discriminate]. destruct (a_cs st') as [|e0 er] eqn:Ecs'; [|discriminate].
    pose proof (i2a_start H IMX A HK HHx HSH0 stb G0 rho0 x Fr fc msF m mo s LB LF lo B CH Hshape Hcs HG Hnd HG0 HRn Hr0 Hr1 Hr2 Hr3
                  Hvis Hakrel Hheap Hrfs Hac Hst0 Hchain HCH Hpfo HAL Hcst Hcnt Hlf Haux HB HB64 Hstk Hhl Hlo Hsp16 Hsp32 Herr Hinv) as HI0.
    set (Q := I2AE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HI0 |- *.
    eapply (ah_seq H HH).
    { exact (i2a_run_sound H IMX A code HK HHx HIMX HWRX Hcode HROC HSH0 Hpfc NFSM NFSF NSET NCPY NLEN NMAL fuel Q (a_start A stb) st' rho0 msF mo
               Hrun (xw_ok_cells0_in _ Hxw) HI0). }
    intros [msF1 mo1] [rho' [(s' & LB' & G' & FF' & XS' & ms1 & X1) Hfin]]. cbn [cfg_ms cfg_model] in X1.
    pose proof X1 as X'.
    destruct X' as [Xvis XRn Xcan Xfr Xfc Xrom Xr0 Xr1 Xr2 Xr3 Xag Xn0 Xak Xmp Xheap Xrfs Xac Xst0 Xch XCH0 Xs0v Xpfo XAL XAL0
                    XG XGin XGnd XGtnd XGnew XGstk XFF XFFin XFFnd XFFtnd XTsep XFFlen XXS Xdom Xreg0 Xreg1 Xreg2 Xreg3 Xro Xinb Xkinds
                    Xcost Xcnt Xstk Xlo Xaux Xinv Xerr Xsh0 XLB0 XLB0h Xnamed XLBsub Xframe].
    assert (EFF : FF' = []) by (rewrite Eff' in XFF; destruct FF'; [reflexivity | discriminate XFF]). subst FF'.
    pose proof (XRn rho' (agree_refl _ rho' Xr0)) as HR.
    assert (Htra : to_Z (c_tra K) < 2 ^ 60) by (cbn [q_n0 Q] in Xn0, Xs0v; slia).
    eapply (ah_lift H HH _ _ s' msF1 ms1 mo1 Xak Xvis (i2_final_step rho' (a_F st') ms1 Xr0 Htra HR Xcan Hfin)).
    intros msF' mo' Hak' Hmp' Hvis'. apply (ah_done H HH).
    destruct (export_sound _ _ _ _ _ _ _ _ _ _ _ X X1 Hexp) as (S1 & S2 & S3 & S4 & S5).
    exists rho', st', s', LB', G', XS', ms1. cbn [cfg_ms cfg_model].
    assert (Etra : rho' (c_tra K) = rho0 (c_tra K)).
    { destruct Xag as [_ Hag]. apply Hag. cbn [q_n0 Q]. cbn [q_n0 Q] in Xs0v. slia. }
    rewrite Hvis', Etra, Xfr, Xfc, Xrom. cbn [q_F q_fc q_rho0 q_mo0 Q].
    split; [reflexivity|]. split; [exact Hak'|]. split; [exact (ah_mpres_trans H HH _ _ _ Xmp Hmp')|].
    split; [exists msF1, mo1; exact X1|]. split; [exact Hfin|]. split; [exact Ecs'|].
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
    (* [comment removed for export] *)
    unfold shad_all in Hshad. rewrite forallb_forall in Hshad. rewrite XG in Hshad.
    apply Forall_forall. intros g Hg.
    specialize (Hshad (g_tag g, g_size g) ltac:(apply in_map_iff; exists g; split; [reflexivity | exact Hg])). cbn [fst] in Hshad.
    pose proof (proj1 (Forall_forall _ _) XGin g Hg) as (_ & _ & _ & _ & _ & Hsh). destruct Hsh as [_ Hsh].
    destruct (iget (g_tag g + 1)%uint63 (f_mem (a_F st'))) as [rg'|] eqn:Erg; [|discriminate].
    exact (proj2 (proj2 (Hsh rg' eq_refl))).
  Qed.
End Top.
