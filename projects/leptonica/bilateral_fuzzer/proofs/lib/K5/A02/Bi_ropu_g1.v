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


(* [comment removed for export] *)
Ltac ropu_ivt := lazymatch goal with DIN : In (?D, ?N) (rt_live _ _) |- _ =>
  cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists D, N; split; [exact DIN| lia]| exact I]] end.
Ltac ropu_pft Hx := lazymatch goal with PFS : forall a, _ -> _ <= a \/ a < _ |- _ =>
  pose proof (PFS _ Hx) as HS; destruct Hx as [_ HO]; cbn [outside] in HO |- *; repeat split; try exact I; lia end.
(* [comment removed for export] *)
Ltac ropu_art RT AF := cps_stop; art_now RT AF ltac:(idtac; ropu_ivt);
  lazymatch goal with AG : agree_on ?PFv ?m0 ?mm, MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    is_var PFv; agf_munch AG MUx ltac:(fun Hx => ropu_pft Hx) | |- _ => idtac end.
(* [comment removed for export] *)
Ltac ropu_frame24 := lazymatch goal with
  | FRx : rw_cells asegs ?mc (?u + -128) (CB 8 ?a :: C8 ?b :: C8 ?c :: ?rest) |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      change (CB 8 a :: C8 b :: C8 c :: rest) with ([CB 8 a; C8 b; C8 c] ++ rest) in FRx;
      apply rw_cells_merge_prefix in FRx; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FRx
  | FRx : rw_cells asegs ?mc (?u + -128) (CB 16 ?a :: C8 ?c :: ?rest) |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      change (CB 16 a :: C8 c :: rest) with ([CB 16 a; C8 c] ++ rest) in FRx;
      apply rw_cells_merge_prefix in FRx; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FRx
  | |- _ => idtac end.
(* [comment removed for export] *)
Ltac ropu_exit RT AF := ropu_art RT AF; ropu_frame24;
  lazymatch goal with EX : forall (mf : mem) (Ff : bvmap 5 word) (fcf : bv 32) (jk : list byte), _ ,
      FRx : rw_cells asegs ?mc (_ + -128) (CB 24 _ :: _), A : ART RT _ ?mc, MIx : mem_inv asegs ?mc, STx : stk asegs ?mc _ (_ + -128),
      AGx : agree_on ?PFv ?m0 ?mc, WMx : wmono asegs ?m0 ?mc |- cps _ (ASTA _ _ _ (eq (MS _ ?Fc _ _ _ ?mc _))) _ =>
    is_var PFv;
    first [ lazymatch goal with FK1 : fs_agree ?F0 ?Fi, FK2 : fs_agree ?Fi Fc |- _ =>
              eapply EX; [exact (fs_agree_trans _ _ _ FK1 FK2)| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] end
          | lazymatch goal with FK1 : fs_agree ?F0 Fc |- _ =>
              eapply EX; [exact FK1| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] end
          | eapply EX; [apply fs_agree_refl| exact A| exact MIx| exact STx| exact WMx| exact FRx| exact AGx] ] end.
(* [comment removed for export] *)
Ltac ropu_after MU' WM' DSH side :=
  lazymatch type of MU' with munch [(?D, ?D + ?dn)] ?m1 ?mf =>
    let OUT := fresh "OUT" in
    assert (OUT : D + dn <= 0x7fff8000 \/ 0x10007fff8000 <= D) by (clear - DSH; unfold parked in DSH; lia);
    rop_transport m1 mf MU' WM' OUT;
    loop_transport m1 mf MU' side;
    clear OUT; try clear MU' WM'; try clear m1 end.
(* [comment removed for export] *)
Ltac ropu_uf vD vN vdy vdh vdwpl vdph DSH side :=
  reg_val (Z_to_bv 5 13) ltac:(fun va3 => lazymatch va3 with Z_to_bv 64 ?vP =>
    let RD := fresh "RD" in let P4 := fresh "P4" in
    assert (RD : forall i', 0 <= i' < vdh -> vD <= vP + 4 * (vdwpl * i') /\ vP + 4 * (vdwpl * i') + 4 <= vD + vN)
      by (apply (rows_fit' vD vN vP vdwpl vdh 4 vdy vdph); lia);
    assert (P4 : vP mod 4 = 0) by (Z.div_mod_to_equations; lia);
    regfix (Z_to_bv 5 10) (vP + 4 * (vdwpl * 0)); regfix (Z_to_bv 5 13) (vP + 4 * (vdwpl * 0)); regfix (Z_to_bv 5 14) (vdh - 0);
    lazymatch goal with WRDc : wr_at asegs ?mm vD vN, ACCc : acc asegs ?mm vD vN, MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (uf_rows (Z.to_nat vdh) 0) with (DR := vD) (dn := vN) (P := vP) (dh := vdh) (dwpl := vdwpl);
      first [ exact RD | exact WRDc | exact ACCc | exact MIc | exact DSH | exact P4 | lia ]
    | cbv beta; intros ms' (f_a0 & f_a3 & f_a4 & f_a6 & f_a7 & mf1 & -> & MU1' & WM1' & MI1); ropu_after MU1' WM1' DSH side; clear RD P4;
      try replace (vdh - 0) with vdh by lia ] end end).
Ltac ropu_ul vD vN vdy vdh vdwpl vdph DSH side :=
  reg_val (Z_to_bv 5 21) ltac:(fun vs5 => lazymatch vs5 with Z_to_bv 64 ?vP =>
    let RD := fresh "RD" in let P4 := fresh "P4" in
    assert (RD : forall i', 0 <= i' < vdh -> vD <= vP + 4 * (vdwpl * i') /\ vP + 4 * (vdwpl * i') + 4 <= vD + vN)
      by (apply (rows_fit' vD vN vP vdwpl vdh 4 vdy vdph); lia);
    assert (P4 : vP mod 4 = 0) by (Z.div_mod_to_equations; lia);
    regfix (Z_to_bv 5 10) (vP + 4 * (vdwpl * 0)); regfix (Z_to_bv 5 21) (vP + 4 * (vdwpl * 0)); regfix (Z_to_bv 5 20) (vdh - 0);
    lazymatch goal with WRDc : wr_at asegs ?mm vD vN, ACCc : acc asegs ?mm vD vN, MIc : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ul_rows (Z.to_nat vdh) 0) with (DR := vD) (dn := vN) (P := vP) (dh := vdh) (dwpl := vdwpl);
      first [ exact RD | exact WRDc | exact ACCc | exact MIc | exact DSH | exact P4 | lia ]
    | cbv beta; intros ms' (l_a0 & l_a2 & l_a3 & l_s4 & l_s5 & mf3 & -> & MU3' & WM3' & MI3); ropu_after MU3' WM3' DSH side; clear RD P4;
      try replace (vdh - 0) with vdh by lia ] end end).
(* [comment removed for export] *)
Ltac ropu_tail RT AF vD vN vdy vdh vdwpl vdph DSH side :=
  uwalk [0xb02b0; 0xb003c]; unorm;
  first [ at_pc 0xb02b0; ropu_ul vD vN vdy vdh vdwpl vdph DSH side; uwalk [0xb003c] | at_pc 0xb003c ];
  ropu_exit RT AF.

(* An address a row loop did not write lies outside the destination rows (DSS, CKR, LOW, LOR: the proof's facts). *)
Local Ltac ropu_side DSS CKR LOW LOR Hx :=
  split; [| exact I];
  clear - Hx DSS CKR LOW LOR; unfold parked in DSS;
  unfold LSTK, RT_STACK, STACK_WIN, SEGTOP_A, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address,
    g_GOT_detect_uar, g_detect_stack_use_after_return in *;
  lia.
(* The library statics lie outside the destination rows. *)
Local Ltac ropu_static DSS :=
  let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "HSB" in let H2 := fresh "HSL" in
  intros a Ha; pose proof (client_static_below a Ha) as H1; pose proof (client_static_lo a Ha) as H2;
  split; [right; left; exact Ha|]; cbn [outside]; split; [| exact I];
  clear - H1 H2 DSS; unfold parked, SEGTOP_A in *; lia.
(* The continuation after the full-word rows: open it and start its walk. *)
Local Ltac ropu_cont RT AF S datad dn DIN MST usp :=
  let mf := fresh "mf9" in let Ff := fresh "Ff9" in let fcf := fresh "fcf9" in let jk := fresh "jk9" in
  intros mf Ff fcf jk ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?;
  let FK := fresh "FK9" in let A := fresh "ART9" in let MIx := fresh "MI9" in let STx := fresh "ST9" in
  let WMx := fresh "WM9c" in let FRx := fresh "FR9" in let AGx := fresh "AGF9" in
  intros FK A MIx STx WMx FRx AGx;
  let WRx := fresh "WRD9" in let ACx := fresh "ACC9" in
  pose proof (af_acc_live RT AF S mf datad dn A DIN) as (WRx & ACx);
  cps_walk AF MST;
  let MUx := fresh "MU9" in let WMy := fresh "WM9" in
  pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] mf) as MUx; pose proof (wmono_refl asegs mf) as WMy.
(* At the head of the full-word rows (0xb00e0): the row loop LOOPF; its continuation is left open. *)
Local Ltac ropu_loopf RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16 :=
  reg_val (Z_to_bv 5 23) ltac:(fun v7 => lazymatch v7 with Z_to_bv 64 ?nfv =>
  reg_val (Z_to_bv 5 9) ltac:(fun v1 => lazymatch v1 with Z_to_bv 64 ?Pv0 =>
    let Pv := lazymatch Pv0 with Z.land 18446744073709551615 ?X => X | _ => Pv0 end in
    ropu_art RT AF;
    lazymatch goal with A : ART RT _ ?mc, MIx : mem_inv asegs ?mc, STx : stk asegs ?mc _ (_ + -128),
                        FRx : rw_cells asegs ?mc (_ + -128) _, AGx : agree_on ?PFv ?m0 ?mc, WMx : wmono asegs ?m0 ?mc
                        |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      is_var PFv;
      eapply (LOOPF _ _ _ _ _ _ _ nfv Pv) with (k := Z.to_nat dh) (i := 0);
      lazymatch goal with
      | |- forall (mf : mem), _ => ropu_cont RT AF S datad dn DIN MST usp
      | |- fs_agree _ _ => apply fs_agree_refl
      | |- ART _ _ _ => exact A
      | |- mem_inv _ _ => exact MIx
      | |- stk _ _ _ _ => exact STx
      | |- wmono _ _ _ => exact WMx
      | |- rw_cells _ _ _ _ => exact FRx
      | |- agree_on _ _ _ => exact AGx
      | |- @eq word _ _ => first [ f_equal; lia | unorm; f_equal; lia ]
      | |- forall i', _ => apply (rows_fit' datad dn Pv dwpl dh (4 * nfv) dy dpixh); lia
      | |- _ mod _ = 0 => clear - D4 D16; Z.div_mod_to_equations; lia
      | |- @eq Z _ _ => first [ rewrite land_ones64 by lia; lia | lia | unorm; lia ]
      | |- _ => first [ lia | unorm; lia ]
      end
    end end) end).
(* Walk a case to its next stop, take the step that stop needs, and go on to the exit. *)
Local Ltac ropu_go RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16 DSH DSS CKR LOW LOR :=
  uwalk [0xafd5c; 0xb0100; 0xb00e0; 0xafe8c];
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0xafe8c) _ _ _ _) => ropu_exit RT AF
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0xafd5c) _ _ _ _) =>
      unorm;
      ropu_uf datad dn dy dh dwpl dpixh DSH ltac:(fun Hx => ropu_side DSS CKR LOW LOR Hx);
      ropu_go RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16 DSH DSS CKR LOW LOR
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0xb0100) _ _ _ _) =>
      unorm;
      ropu_ul datad dn dy dh dwpl dpixh DSH ltac:(fun Hx => ropu_side DSS CKR LOW LOR Hx);
      ropu_go RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16 DSH DSS CKR LOW LOR
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0xb00e0) _ _ _ _) =>
      unorm;
      ropu_loopf RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16;
      ropu_go RT AF LOOPF S datad dn DIN MST usp dwpl dh dy dpixh D4 D16 DSH DSS CKR LOW LOR
  end.

Section ROPUG.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (167008, 132) ACC_LITS.
Hypothesis TABL : In (167200, 132) ACC_LITS.

Lemma ropu_clr_g1 : rasteropUniLow_clr_case RT 1.
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
  pose proof (proj1 (af_acc_live RT AF Σ m datad dn ART0 DIN)) as WRD.
  assert (DWPLH : dwpl <= 0x1000000) by nia.
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
  clearbody dxq dxm. subst dxm.
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
  (* The full-word rows from 0xb00e0, one __asan_memset per row, by induction on the rows left. *)
  assert (LOOPF : forall (vs0 vs4 vs5 vs6 vs8 vs10 vs11 : word) (nf PFu : Z),
      1 <= nf -> vs0 = Z_to_bv 64 (4 * nf) -> PFu mod 4 = 0 ->
      (forall i', 0 <= i' < dh -> datad <= PFu + 4 * (dwpl * i') /\ PFu + 4 * (dwpl * i') + 4 * nf <= datad + dn) ->
      (forall (mf : mem) (Ff : bvmap 5 word) (fcf : bv 32) (jk : list byte)
              (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt5 xt6 : word),
         fs_agree F Ff -> ART RT Σ mf -> mem_inv asegs mf -> stk asegs mf lo (usp + -128) -> wmono asegs m mf ->
         rw_cells asegs mf (usp + -128) [CB 16 jk; C8 (Z_to_bv 64 dwpl); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
         agree_on PF m mf ->
         cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -128)) gp tp xt0 xt1 xt2 vs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                             (Z_to_bv 64 (dwpl * 4)) (Z_to_bv 64 0x7fff8000) vs4 vs5 vs6 (Z_to_bv 64 nf) vs8 xs9 vs10 vs11 xt3 xt4 xt5 xt6)
                                         Ff (Z_to_bv 64 0xafe88) fcf None mf (seg_rom asegs)))) QF) ->
      forall (k : nat) (i : Z) (mi : mem) (Fi : bvmap 5 word) (fci : bv 32) (jk : list byte)
             (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (c9 rp : Z),
      Z.of_nat k = dh - i -> 0 <= i -> (1 <= k)%nat -> c9 = dh - i -> rp = PFu + 4 * (dwpl * i) ->
      fs_agree F Fi -> ART RT Σ mi -> mem_inv asegs mi -> stk asegs mi lo (usp + -128) -> wmono asegs m mi ->
      rw_cells asegs mi (usp + -128) [CB 16 jk; C8 (Z_to_bv 64 dwpl); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      agree_on PF m mi ->
      cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -128)) gp tp xt0 xt1 xt2 vs0 (Z_to_bv 64 rp) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                           (Z_to_bv 64 (dwpl * 4)) (Z_to_bv 64 0x7fff8000) vs4 vs5 vs6 (Z_to_bv 64 nf) vs8 (Z_to_bv 64 c9) vs10 vs11 xt3 xt4 xt5 xt6)
                                       Fi (Z_to_bv 64 0xb00e0) fci None mi (seg_rom asegs)))) QF).
  { clear AGF.
    intros vs0 vs4 vs5 vs6 vs8 vs10 vs11 nf PFu NF1 EVS0 PF4 RBF CONT. subst vs0.
    induction k as [|k IH]; intros i mi Fi fci jk xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 c9 rp
      HK HI HK1 EC9 ERP FKi ARTi MIi STi WMi FRi AGFi; [lia|].
    pose proof (af_acc_live RT AF Σ mi datad dn ARTi DIN) as (WRDi & ACCi).
    destruct (RBF i ltac:(lia)) as (RBi1 & RBi2).
    cps_walk AF MST.
    pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] mi) as MUl. pose proof (wmono_refl asegs mi) as WMl.
    uwalk [0x66814].
    at_call RT AF ltac:(idtac; ropu_ivt) ltac:(fun Hx => ropu_pft Hx).
    eapply cps_seq.
    { pose proof (fk_asan_memset RT FKC) as MS0; unfold memset_icontractF in MS0;
      eapply MS0 with (lo := lo) (d := PFu + 4 * (dwpl * i)) (n := 4 * nf) (c := Z_to_bv 8 0); rt_side idtac.
      all: lazymatch goal with
           | |- @eq word _ _ => f_equal; lia
           | |- (0 <= _ <= _) => change (2^47) with 140737488355328; lia
           | |- (0 <= _ < _) => lia
           | |- checked_dst _ _ _ _ _ _ =>
               unfold checked_dst; rewrite ?unsigned_lit by lia;
               split; [intros _; split; [apply (acc_sub asegs _ datad dn); [exact ACCi| lia| lia]
                                        | left; exists datad, dn; split; [exact DIN| lia]]|];
               split; [intros i2 Hi2; right; right; left; exists datad, dn; split; [exact DIN| lia]
                      | apply (wr_at_sub _ datad dn); [exact WRDi| lia| lia| lia]]
           end. }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| lia]).
    refresh RT AF.
    cps_walk AF MST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(usp - 128, usp); (datad, datad + dn)] mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
    destruct k as [|k].
    - uwalk [0xafe88]. cps_stop.
      eapply CONT; first [ exact (fs_agree_trans _ _ _ FKi FK) | eassumption ].
    - uwalk [0xb00e0]. cps_stop.
      eapply (IH (i + 1)); first [ exact (fs_agree_trans _ _ _ FKi FK) | eassumption | lia ]. }
  assert (DWRC : dwr = 0 \/ dwr = 1 \/ dwr = 2 \/ dwr = 3) by lia.
  assert (DWQC : dwq = 0 \/ dwq = 1 \/ 2 <= dwq) by lia.
  destruct DWRC as [-> | [-> | [-> | ->]]]; destruct DWQC as [-> | [-> | DWQ2]];
    [exfalso; lia | ropu_go RT AF LOOPF Σ datad dn DIN MST usp dwpl dh dy dpixh D4 D16 DSH DSS CKR LOW LOR ..].
Qed.
End ROPUG.
