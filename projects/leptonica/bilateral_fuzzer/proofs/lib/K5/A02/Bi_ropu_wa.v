(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit Cf_iface Cf_kit Km_setelem Km_iface Km_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_ropkit Bi_ropl_wa Bi_ropl_gk Bi_ropl_gdef Bi_ropu_iface Bi_ropu_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The exit steps of Bi_ropu_g1.v's proof, for this case's own proof. *)
Local Ltac ropu_ivt := lazymatch goal with DIN : In (?D, ?N) (rt_live _ _) |- _ =>
  cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists D, N; split; [exact DIN| lia]| exact I]] end.
Local Ltac ropu_pft Hx := lazymatch goal with PFS : forall a, _ -> _ <= a \/ a < _ |- _ =>
  pose proof (PFS _ Hx) as HS; destruct Hx as [_ HO]; cbn [outside] in HO |- *; repeat split; try exact I; lia end.
Local Ltac ropu_art RT AF := cps_stop; art_now RT AF ltac:(idtac; ropu_ivt);
  lazymatch goal with AG : agree_on ?PFv ?m0 ?mm, MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    is_var PFv; agf_munch AG MUx ltac:(fun Hx => ropu_pft Hx) | |- _ => idtac end.
Local Ltac ropu_frame24 := lazymatch goal with
  | FRx : rw_cells asegs ?mc (?u + -128) (CB 8 ?a :: C8 ?b :: C8 ?c :: ?rest) |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      change (CB 8 a :: C8 b :: C8 c :: rest) with ([CB 8 a; C8 b; C8 c] ++ rest) in FRx;
      apply rw_cells_merge_prefix in FRx; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FRx
  | FRx : rw_cells asegs ?mc (?u + -128) (CB 16 ?a :: C8 ?c :: ?rest) |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      change (CB 16 a :: C8 c :: rest) with ([CB 16 a; C8 c] ++ rest) in FRx;
      apply rw_cells_merge_prefix in FRx; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FRx
  | |- _ => idtac end.
Local Ltac ropu_exit RT AF := ropu_art RT AF; ropu_frame24;
  lazymatch goal with EX : forall (mf : mem) (Ff : bvmap 5 word) (fcf : bv 32) (jk : list byte), _ ,
      FRx : rw_cells asegs ?mc (_ + -128) (CB 24 _ :: _), A : ART RT _ ?mc, MIx : mem_inv asegs ?mc, STx : stk asegs ?mc _ (_ + -128),
      AGx : agree_on ?PFv ?m0 ?mc, WMx : wmono asegs ?m0 ?mc |- cps _ (ASTA _ _ _ (eq (MS _ ?Fc _ _ _ ?mc _))) _ =>
    is_var PFv;
    first [ lazymatch goal with FK1 : fs_agree ?F0 ?Fi, FK2 : fs_agree ?Fi Fc |- _ =>
              eapply EX; [exact (fs_agree_trans _ _ _ FK1 FK2)| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] end
          | lazymatch goal with FK1 : fs_agree ?F0 Fc |- _ =>
              eapply EX; [exact FK1| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] end
          | eapply EX; [apply fs_agree_refl| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] ] end.
(* The library statics lie outside the destination rows. *)
Local Ltac ropu_static DSS :=
  let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "HSB" in let H2 := fresh "HSL" in
  intros a Ha; pose proof (client_static_below a Ha) as H1; pose proof (client_static_lo a Ha) as H2;
  split; [right; left; exact Ha|]; cbn [outside]; split; [| exact I];
  clear - H1 H2 DSS; unfold parked, SEGTOP_A in *; lia.
(* The 4-byte load and store of a row's last, partly cleared word, at the address in the instruction's base register. *)
Local Ltac ropu_hl4 WR := next_instr ltac:(fun ins => lazymatch ins with
  | Load _ _ _ ?rs _ => reg_val rs ltac:(fun v => lazymatch v with Z_to_bv 64 ?A => hload4 WR A end) end).
Local Ltac ropu_hs4 WR := next_instr ltac:(fun ins => lazymatch ins with
  | Store _ ?rs _ _ => reg_val rs ltac:(fun v => lazymatch v with Z_to_bv 64 ?A => hstore4 WR A end) end).
(* The side goals of a step of the row loop (LOOPW, or its induction hypothesis IH). *)
Local Ltac ropu_wside dwq A MIx STx WMx FRx AGx :=
  lazymatch goal with
  | |- fs_agree _ _ =>
      first [ apply fs_agree_refl | eassumption
            | lazymatch goal with FK1 : fs_agree ?F0 ?Fi, FK2 : fs_agree ?Fi ?Fc |- fs_agree ?F0 ?Fc => exact (fs_agree_trans _ _ _ FK1 FK2) end ]
  | |- ART _ _ _ => exact A
  | |- mem_inv _ _ => exact MIx
  | |- stk _ _ _ _ => exact STx
  | |- wmono _ _ _ => exact WMx
  | |- rw_cells _ _ _ _ => exact FRx
  | |- agree_on _ _ _ => exact AGx
  | |- 1 <= _ -> _ =>
      first [ assumption
            | let Q := fresh "Q1" in intros Q; split; f_equal;
              rewrite ?(Z.mod_small (dwq + -1) 18446744073709551616) by lia; rewrite ?zext32x4 by lia; lia ]
  | |- _ => first [ lia | swrap32_fix; lia | unorm; first [ lia | swrap32_fix; lia ] ]
  end.
(* The next row of the loop: the induction hypothesis at row i + 1. *)
Local Ltac ropu_ih RT AF RBW i dwq :=
  unorm; ropu_art RT AF;
  lazymatch goal with IH : forall (i0 : Z) (mi0 : mem), _, A : ART RT _ ?mc, MIx : mem_inv asegs ?mc, STx : stk asegs ?mc _ (_ + -128),
                      FRx : rw_cells asegs ?mc (_ + -128) _, AGx : agree_on ?PFv ?m0 ?mc, WMx : wmono asegs ?m0 ?mc
                      |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    is_var PFv;
    pose proof (RBW (i + 1) ltac:(lia)) as IWn;
    eapply (IH (i + 1)); ropu_wside dwq A MIx STx WMx FRx AGx
  end.
(* A case to the row loop's head (0xaffd4), then the row loop. *)
Local Ltac ropu_wa_leaf RT AF LOOPW dh dwq :=
  uwalk [0xaffd4];
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0xaffd4) _ _ _ _) => idtac end;
  unorm;
  ropu_art RT AF;
  lazymatch goal with A : ART RT _ ?mc, MIx : mem_inv asegs ?mc, STx : stk asegs ?mc _ (_ + -128),
                      FRx : rw_cells asegs ?mc (_ + -128) _, AGx : agree_on ?PFv ?m0 ?mc, WMx : wmono asegs ?m0 ?mc
                      |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    is_var PFv;
    eapply (LOOPW (Z.to_nat dh) 0); ropu_wside dwq A MIx STx WMx FRx AGx
  end.

Section ROPUWA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
(* [comment removed for export] *)
Hypothesis TABR : In (167008, 132) ACC_LITS.
Hypothesis TABL : In (167200, 132) ACC_LITS.

Lemma ropu_clr_wa : rasteropUniLow_clr_case RT 0.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad dpixw dpixh dwpl dx dy dw dh FDO MST -> -> -> -> -> -> -> -> ARGS DX0 DY0 DW0 DH0 DXW DYH [DPW0 DPW1] [DPH0 DPH1]
    DWPL DWC DNHI CH ENV RES DXMOD.
  unfold lpost, keeps, keepsL in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as (SP0R0 & SP0R1).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP.
  assert (USP0 : 0 <= usp) by (unfold usp; apply bv_unsigned_in_range).
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof LH as LH0. pose proof SSP as SSP0. hide LH0. hide SSP0.
  set (dn := 4 * (dwpl * dpixh)) in *.
  assert (EDN : dn = 4 * (dwpl * dpixh)) by reflexivity.
  destruct CH as (DIN & D0 & D16 & DN0).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + dn)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [HH|HH]; [left; exact HH| right; lia]. }
  pose proof (af_live_range RT AF Σ m datad dn ART0 DIN) as (_ & CKR & CKS).
  pose proof (gp_live_hi RT GP Σ m datad dn ART0 DIN) as CKH.
  destruct (af_client_consts RT AF Σ m ART0) as (G0 & G5 & G6 & G7).
  pose proof (acc_live RT AF Σ m datad dn ART0 DIN) as ACC.
  unfold entry_st, e_rasteropUniLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return in *.
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, SHB in *.
  assert (DSS : parked (datad + dn <= 0x10000 \/ 0x662000 <= datad)) by exact CKS.
  assert (DSH : parked (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad)) by exact CKH.
  assert (D4 : datad mod 4 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (YD : 0 <= dy * dwpl < 2^24).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (dy * dwpl <= (dpixh - 1) * dwpl) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  assert (ACR : acc asegs m 167008 132) by exact (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABR).
  assert (ACL : acc asegs m 167200 132) by exact (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABL).
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* The x and y clipping (as rasteropLow's front): simplify each clamp right after the step that forms it. *)
  uwalk [0xafa18]. clipfix2. uwalk [0xafa24]. clipfix2. uwalk [0xafa38]. clipfix2. uwalk [0xafa3c]. clipfix2.
  uwalk [0xafa50]. clipfix2. uwalk [0xafa58]. clipfix2. uwalk [0xafa70]. clipfix2. uwalk [0xafa74]. clipfix2.
  do 4 (try (uwalk [0xafa88]; first [ at_pc 0xafa88 | progress clipfix2 ])).
  assert (L31 : forall x, 0 <= x -> Z.land (x * 8) 31 = 8 * (x mod 4))
    by (intros x Hx; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; change (2 ^ 5) with (4 * 8); rewrite Z.mul_mod_distr_r by lia; lia).
  pose proof (L31 dx DX0) as LDX. pose proof (L31 dw ltac:(lia)) as LDW.
  set (dxq := dx / 4) in *. set (dxm := dx mod 4) in *.
  assert (EDX : dx = 4 * dxq + dxm) by (unfold dxq, dxm; apply Z.div_mod; lia).
  assert (DXQ : 0 <= dxq) by (unfold dxq; apply Z.div_pos; lia).
  clearbody dxq dxm. subst dxm. rewrite Z.add_0_r in EDX.
  set (dwq := dw / 4) in *. set (dwr := dw mod 4) in *.
  assert (EDW : dw = 4 * dwq + dwr) by (unfold dwq, dwr; apply Z.div_mod; lia).
  assert (DWR0 : 0 <= dwr) by (unfold dwr; apply Z.mod_pos_bound; lia).
  assert (DWR1 : dwr < 4) by (unfold dwr; apply Z.mod_pos_bound; lia).
  assert (DWQ : 0 <= dwq) by (unfold dwq; apply Z.div_pos; lia).
  clearbody dwq dwr. subst dx dw.
  assert (RBW : forall i', 0 <= i' <= dh -> 0 <= dwpl * i' <= 0x1000000).
  { intros i' Hi'. split; [apply Z.mul_nonneg_nonneg; lia|].
    pose proof (Z.mul_le_mono_nonneg_l i' dpixh dwpl ltac:(lia) ltac:(lia)). lia. }
  (* The epilogue from 0xafe8c: reload the saved registers, release the frame, return. *)
  assert (EXIT : forall (mf : mem) (Ff : bvmap 5 word) (fcf : bv 32) (jk : list byte)
            (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
      fs_agree F Ff -> ART RT Σ mf -> mem_inv asegs mf -> stk asegs mf lo (usp + -128) -> wmono asegs m mf ->
      rw_cells asegs mf (usp + -128) [CB 24 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      agree_on PF m mf ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -128)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                                       Ff (Z_to_bv 64 0xafe8c) fcf None mf (seg_rom asegs)))) QF).
  { intros mf Ff fcf jk xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
      FKf ARTf MIf STf WMf FRf AGFf.
    cps_walk AF MST.
    pose proof (munch_refl [(usp - 128, usp)] mf) as MUf. pose proof (wmono_refl asegs mf) as WMf2.
    uwalk (@nil Z).
    cps_stop. apply cps_finish. intros c Hc. subst QF. cbv beta.
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
    do 2 eexists. unfold ret_stF, ret_st, rt_after.
    split; [split; [do 16 eexists; reflexivity| cbn [ms_fregs MS]; exact FKf]|].
    unfold hid in LH0, SSP0.
    split; [split; [split; [exact ARTf| split; [exact MIf| split; [exact WMf| assumption]]]| split]|].
    - apply (LIBH_agree RT GP PF m mf LH0 AGFf). ropu_static DSS.
    - apply (io_ssp_agree RT GP PF Σ m mf SSP0 ARTf AGFf). ropu_static DSS.
    - intros a Ha Ho. apply AGFf. split; assumption. }
  (* The row loop from 0xaffd4: per row, the full words by one __asan_memset and the last word's masked store;
     by induction on the rows left. *)
  assert (LOOPW : forall (k : nat) (i : Z) (mi : mem) (Fi : bvmap 5 word) (fci : bv 32) (jk : list byte) (mk : word)
            (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs11 xt4 xt5 xt6 : word) (lwb dw8 c0 rp iw pf2 : Z),
      Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> lwb = 8 * dwr -> dw8 = 32 * dwq + lwb -> c0 = i - dh ->
      rp = datad + dy * dwpl * 4 + dxq * 4 + 4 * (dwpl * i) -> iw = dwpl * i -> pf2 = datad + dy * dwpl * 4 + dxq * 4 ->
      (1 <= dwq -> xs1 = Z_to_bv 64 (4 * dwq) /\ xs11 = Z_to_bv 64 (pf2 + 4 * dwq)) ->
      fs_agree F Fi -> ART RT Σ mi -> mem_inv asegs mi -> stk asegs mi lo (usp + -128) -> wmono asegs m mi ->
      rw_cells asegs mi (usp + -128) [CB 8 jk; C8 mk; C8 (Z_to_bv 64 dwpl); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      agree_on PF m mi ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 c0) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                           xs2 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (dwpl * 4)) (Z_to_bv 64 dw8) (Z_to_bv 64 lwb) (Z_to_bv 64 rp)
                                           (Z_to_bv 64 32) (Z_to_bv 64 iw) (Z_to_bv 64 pf2) xs11 (Z_to_bv 64 dwpl) xt4 xt5 xt6)
                                       Fi (Z_to_bv 64 0xaffd4) fci None mi (seg_rom asegs)))) QF).
  { clear AGF.
    induction k as [|k IH]; intros i mi Fi fci jk mk xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs11 xt4 xt5 xt6
      lwb dw8 c0 rp iw pf2 HK HI HK1 ELWB EDW8 EC0 ERP EIW EPF2 XS FKi ARTi MIi STi WMi FRi AGFi; [lia|].
    pose proof (af_acc_live RT AF Σ mi datad dn ARTi DIN) as (WRD & ACCD).
    assert (RB : forall i', 0 <= i' < dh -> datad <= pf2 + 4 * (dwpl * i') /\ pf2 + 4 * (dwpl * i') + (4 * dwq + ((dwr + 3) / 4) * 4) <= datad + dn)
      by (apply (rows_fit' datad dn pf2 dwpl dh (4 * dwq + ((dwr + 3) / 4) * 4) dy dpixh); lia).
    destruct (RB i ltac:(lia)) as (RBi1 & RBi2).
    cps_walk AF MST.
    pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] mi) as MUl. pose proof (wmono_refl asegs mi) as WMl.
    assert (DWQ01 : dwq = 0 \/ 1 <= dwq) by lia.
    destruct DWQ01 as [DWQ0 | DWQ1].
    - (* no full word: only the last word, masked *)
      uwalk [0xaffb4]. ropu_hl4 WRD. uwalk [0xaffc0]. ropu_hs4 WRD.
      destruct k as [|k].
      + uwalk [0xafe8c]. ropu_exit RT AF.
      + uwalk [0xaffd4]. ropu_ih RT AF RBW i dwq.
    - destruct (XS DWQ1) as [EX1 EX11]. subst xs1 xs11.
      uwalk [0x66814].
      at_call RT AF ltac:(idtac; ropu_ivt) ltac:(fun Hx => ropu_pft Hx).
      pose proof (af_acc_live RT AF Σ mi datad dn ARTi DIN) as (WRD1 & ACCD1).
      eapply cps_seq.
      { pose proof (fk_asan_memset RT FKC) as MS0; unfold memset_icontractF in MS0;
        eapply MS0 with (lo := lo) (d := pf2 + 4 * (dwpl * i)) (n := 4 * dwq) (c := Z_to_bv 8 0); rt_side idtac.
        all: lazymatch goal with
             | |- @eq word _ _ => f_equal; lia
             | |- (0 <= _ <= _) => change (2^47) with 140737488355328; lia
             | |- (0 <= _ < _) => lia
             | |- checked_dst _ _ _ _ _ _ =>
                 unfold checked_dst; rewrite ?unsigned_lit by lia;
                 split; [intros _; split; [apply (acc_sub asegs _ datad dn); [exact ACCD1| lia| lia]
                                          | left; exists datad, dn; split; [exact DIN| lia]]|];
                 split; [intros i2 Hi2; right; right; left; exists datad, dn; split; [exact DIN| lia]
                        | apply (wr_at_sub _ datad dn); [exact WRD1| lia| lia| lia]]
             end. }
      after_call RT AF.
      fold_ag ltac:(fun Hx => destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split;
                    [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
      refresh RT AF.
      cps_walk AF MST.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
      assert (LWB : lwb = 0 \/ 0 < lwb) by lia.
      destruct LWB as [LWB0 | LWB1].
      + destruct k as [|k].
        * uwalk [0xafe8c]. ropu_exit RT AF.
        * uwalk [0xaffd4]. ropu_ih RT AF RBW i dwq.
      + uwalk [0xaffb4]. ropu_hl4 WRD1. uwalk [0xaffc0]. ropu_hs4 WRD1.
        destruct k as [|k].
        * uwalk [0xafe8c]. ropu_exit RT AF.
        * uwalk [0xaffd4]. ropu_ih RT AF RBW i dwq. }
  assert (DWR4 : (dwr = 0 /\ 1 <= dwq) \/ dwr = 1 \/ dwr = 2 \/ dwr = 3) by lia.
  destruct DWR4 as [[-> DWQ1] | [-> | [-> | ->]]]; ropu_wa_leaf RT AF LOOPW dh dwq.
Qed.
End ROPUWA.
