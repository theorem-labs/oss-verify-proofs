(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep AsanWMemcpyF1 AsanWMemcpyF2 AsanSMat AsanWMat AsanWMcM0 AsanWMcM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Set Default Proof Using "All".

Section MCFM.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HF : MCFCode segs e.

Section LoopM.
Variable model0 : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Let L : list word := range_pages src (Z.to_nat n) ++ range_pages dst (Z.to_nat n).
Hypothesis Hbud : (vm_backing_used model0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms' m', MCRc MCF_CLOB ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> matin model0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') K.

Let src_rdM := src_rdM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let sok_subM := sok_subM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let copied_stM := copied_stM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let len4M := len4M segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let len1M := len1M segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let fs_eqM := fs_eqM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let b16m := b16m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let tl60m := tl60m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.

Let mhaltF := mhaltF segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhaltF m' Hm) as Hh.

Local Ltac rdS Hf := cbn [msz_n]; eapply src_rdM; [exact Hf | lia | lia | lia].
Local Ltac inS := cbn [msz_n]; apply incl_appl; apply range_pages_incl; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                   rewrite ?Z2Nat.id by lia; lia.
Local Ltac inD := cbn [msz_n]; apply incl_appr; apply range_pages_incl; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                   rewrite ?Z2Nat.id by lia; lia.
Local Ltac okS Hf := cbn [msz_n]; eapply sok_subM; [exact Hf | lia | lia].
Local Ltac upd Hf c DT :=
  match goal with |- realizes_cfg _ _ (mkCfg (setx _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?data)) _) _ =>
    let Hf' := fresh "Hf" in
    pose proof (copied_stM m _ a data c Hf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(DT)) as Hf'; clear Hf; rename Hf' into Hf
  end.
Local Ltac ld F D Hf :=
  eapply (xs_ld_in segs cfg model0 _ L); [ exact Hh0 | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | memX
                                          | rdS Hf | inS | exact Hbud | pcX | resvX | ]; mnext.
Local Ltac st F D Hf c DT :=
  eapply (xs_st_in segs cfg model0 _ L); [ exact Hh0 | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | regX | memX
                                          | okS Hf | inD | exact Hbud | pcX | resvX | ]; mnext; upd Hf c DT.
Local Ltac dt1 := rewrite store1_load1 by (apply len1M; lia); apply fs_eqM; lia.
Local Ltac ai F D := wr wacc_OpImm F D valX.
Local Ltac regZ := rgn; rwregsX; first [ reflexivity | f_equal; lia ].
Local Ltac snapregs S2 E rs :=
  lazymatch rs with
  | cons ?r ?rest => let R := fresh "R" in eassert (R : rg S2 r = _) by (rewrite E; regX); snapregs S2 E rest
  | nil => idtac
  end.
Local Ltac snap S HS Hf rs :=
  match goal with |- realizes_cfg _ _ (mkCfg ?S' _) _ =>
    let S2 := fresh "S" in let E := fresh "E" in
    remember S' as S2 eqn:E;
    let HS2 := fresh "HS" in assert (HS2 : MCRc MCF_CLOB ms0 S2) by (rewrite E; mcf_chain HS);
    let Hv := fresh "Hsvc" in assert (Hv : ms_svc_pending S2 = None) by (rewrite E; reflexivity);
    let Hp := fresh "Hpc" in eassert (Hp : ms_pc_val S2 = _) by (rewrite E; rewrite pc_setx; reflexivity);
    let Hf2 := fresh "Hf" in
    lazymatch type of Hf with copied _ _ _ ?k' _ =>
      assert (Hf2 : copied (ms_mem S2) (ms_mem ms0) dst k' bs) by (rewrite E, mem_setx; exact Hf) end;
    snapregs S2 E rs;
    clear E; clear dependent S; rename S2 into S; rename HS2 into HS; rename Hf2 into Hf
  end.
Local Ltac bnorm Hb := unfold w0 in Hb;
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lia;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb;
  first [ apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb | apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Shift.
Variable c : nat.
Hypothesis Hc : (1 <= c <= 3)%nat.
Variable oL : Z.
Variables (sR : bv 5) (sL : bv 6).
Hypothesis HsR : bv_unsigned sR = (8 * Z.of_nat c)%Z.
Hypothesis HsL : bv_unsigned sL = (32 - 8 * Z.of_nat c)%Z.
Variables (w00 w14 w18 w20 w24 w2c w30 w38 : bv 32).
Hypothesis L00 : fetch_word segs (pcw e oL) = Some w00.
Hypothesis E00 : is_ecall w00 = false.
Hypothesis D00 : decode_any w00 = Some (ShiftImm32 ALU_SRL 16 14 sR, 4%Z).
Hypothesis L04 : fetch_word segs (pcw e (oL + 4)) = Some (Z_to_bv 32 0xff45a883).
Hypothesis L08 : fetch_word segs (pcw e (oL + 8)) = Some (Z_to_bv 32 0xff85a283).
Hypothesis L0c : fetch_word segs (pcw e (oL + 12)) = Some (Z_to_bv 32 0xffc5a303).
Hypothesis L10 : fetch_word segs (pcw e (oL + 16)) = Some (Z_to_bv 32 0x0005a703).
Hypothesis L14 : fetch_word segs (pcw e (oL + 20)) = Some w14.
Hypothesis E14 : is_ecall w14 = false.
Hypothesis D14 : decode_any w14 = Some (ShiftImm ALU_SLL 7 17 sL, 4%Z).
Hypothesis L18 : fetch_word segs (pcw e (oL + 24)) = Some w18.
Hypothesis E18 : is_ecall w18 = false.
Hypothesis D18 : decode_any w18 = Some (ShiftImm32 ALU_SRL 17 17 sR, 4%Z).
Hypothesis L1c : fetch_word segs (pcw e (oL + 28)) = Some (Z_to_bv 32 0x0103e833).
Hypothesis L20 : fetch_word segs (pcw e (oL + 32)) = Some w20.
Hypothesis E20 : is_ecall w20 = false.
Hypothesis D20 : decode_any w20 = Some (ShiftImm ALU_SLL 7 5 sL, 4%Z).
Hypothesis L24 : fetch_word segs (pcw e (oL + 36)) = Some w24.
Hypothesis E24 : is_ecall w24 = false.
Hypothesis D24 : decode_any w24 = Some (ShiftImm32 ALU_SRL 5 5 sR, 4%Z).
Hypothesis L28 : fetch_word segs (pcw e (oL + 40)) = Some (Z_to_bv 32 0x0113e8b3).
Hypothesis L2c : fetch_word segs (pcw e (oL + 44)) = Some w2c.
Hypothesis E2c : is_ecall w2c = false.
Hypothesis D2c : decode_any w2c = Some (ShiftImm ALU_SLL 7 6 sL, 4%Z).
Hypothesis L30 : fetch_word segs (pcw e (oL + 48)) = Some w30.
Hypothesis E30 : is_ecall w30 = false.
Hypothesis D30 : decode_any w30 = Some (ShiftImm32 ALU_SRL 6 6 sR, 4%Z).
Hypothesis L34 : fetch_word segs (pcw e (oL + 52)) = Some (Z_to_bv 32 0x0053e2b3).
Hypothesis L38 : fetch_word segs (pcw e (oL + 56)) = Some w38.
Hypothesis E38 : is_ecall w38 = false.
Hypothesis D38 : decode_any w38 = Some (ShiftImm ALU_SLL 7 14 sL, 4%Z).
Hypothesis L3c : fetch_word segs (pcw e (oL + 60)) = Some (Z_to_bv 32 0x0063e333).
Hypothesis L40 : fetch_word segs (pcw e (oL + 64)) = Some (Z_to_bv 32 0xff060613).
Hypothesis L44 : fetch_word segs (pcw e (oL + 68)) = Some (Z_to_bv 32 0x0106a023).
Hypothesis L48 : fetch_word segs (pcw e (oL + 72)) = Some (Z_to_bv 32 0x0116a223).
Hypothesis L4c : fetch_word segs (pcw e (oL + 76)) = Some (Z_to_bv 32 0x0056a423).
Hypothesis L50 : fetch_word segs (pcw e (oL + 80)) = Some (Z_to_bv 32 0x0066a623).
Hypothesis L54 : fetch_word segs (pcw e (oL + 84)) = Some (Z_to_bv 32 0x01068693).
Hypothesis L58 : fetch_word segs (pcw e (oL + 88)) = Some (Z_to_bv 32 0x01058593).
Hypothesis L5c : fetch_word segs (pcw e (oL + 92)) = Some (Z_to_bv 32 0xfac7e2e3).
(* [comment removed for export] *)
Hypothesis HX : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e (oL + 96) ->
  rg S 11 = Z_to_bv 64 (src + k - Z.of_nat c + 16) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (4 - Z.of_nat c <= n - k <= 19 - Z.of_nat c)%Z -> (Z.of_nat c <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.

Local Ltac valS := rgn; rwregsX; rewrite ?srlw_srliw, ?sll_slli, ?or_vor, ?lw_LWv; rewrite ?HsR, ?HsL; reflexivity.
Local Ltac sh F D := wr wacc_ShiftImm F D valS.
Local Ltac shw F D := wr wacc_ShiftImm32 F D valS.
Local Ltac orr F D := wr wacc_Op F D valS.
Local Ltac dtw := rewrite st4_w2le;
  rewrite (sw_merge' _ _ _ _ eq_refl) by first [ exact Hc | apply len4M; lia ];
  apply merge_subZ; lia.
Local Ltac sw F D Hf := st F D Hf 4%nat dtw.

Lemma shloopm : forall (d : nat) S k m, matin model0 m L -> (n - k < 16 * Z.of_nat d)%Z ->
  MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e oL ->
  rg S 11 = Z_to_bv 64 (src + k - Z.of_nat c + 16) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = LWv (firstn 4 (skipn (Z.to_nat (k - Z.of_nat c)) bs)) -> rg S 15 = Z_to_bv 64 (19 - Z.of_nat c) ->
  (20 - Z.of_nat c <= n - k)%Z -> (Z.of_nat c <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S k m Hm Hd HS Hpc H11 H13 H12 H14 H15 Hnk Hk Hf; [lia|].
  pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  shw L00 D00.
  ld L04 DW_ff45a883 Hf. ld L08 DW_ff85a283 Hf. ld L0c DW_ffc5a303 Hf. ld L10 DW_0005a703 Hf.
  sh L14 D14. shw L18 D18. orr L1c DW_0103e833.
  snap S HS Hf ([11; 12; 13; 15; 16; 17; 5; 6; 14] : list reg).
  sh L20 D20. shw L24 D24. orr L28 DW_0113e8b3.
  sh L2c D2c. shw L30 D30. orr L34 DW_0053e2b3.
  sh L38 D38. orr L3c DW_0063e333.
  ai L40 DW_ff060613.
  snap S HS Hf ([11; 12; 13; 15; 16; 17; 5; 6; 14] : list reg).
  sw L44 DW_0106a023 Hf. sw L48 DW_0116a223 Hf. sw L4c DW_0056a423 Hf. sw L50 DW_0066a623 Hf.
  ai L54 DW_01068693. ai L58 DW_01058593.
  snap S HS Hf ([11; 12; 13; 15; 14] : list reg).
  wb2 L5c DW_fac7e2e3; intros Hb; bnorm Hb.
  - apply (IH _ (k + 16)%Z _ Hm); [ lia | mcf_chain HS | reflexivity | regZ | regZ | regZ | | regZ | lia | lia | ].
    + rgn. rwregsX. rewrite lw_LWv. f_equal. apply fs_eqM. lia.
    + rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf.
  - apply (HX _ (k + 16)%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | ].
    rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf.
Qed.

End Shift.


(* [comment removed for export] *)
Lemma EP2m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e (0xa4 + 96) ->
  rg S 11 = Z_to_bv 64 (src + k - Z.of_nat 2 + 16) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (4 - Z.of_nat 2 <= n - k <= 19 - Z.of_nat 2)%Z -> (Z.of_nat 2 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  ai (FF_104 segs cfg e HF) DW_ff258593. ai (FF_108 segs cfg e HF) DW_01000713.
  wb2 (FF_10c segs cfg e HF) DW_f4e66ae3; intros Hb; bnorm Hb.
  - apply (tl60m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | rewrite c16s by lia; lia | exact Hf ].
  - wj (FF_110 segs cfg e HF) DW_19c0006f.
    apply (b16m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | exact Hf ].
Qed.

(* [comment removed for export] *)
Lemma EP1m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e (0x1ac + 96) ->
  rg S 11 = Z_to_bv 64 (src + k - Z.of_nat 1 + 16) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (4 - Z.of_nat 1 <= n - k <= 19 - Z.of_nat 1)%Z -> (Z.of_nat 1 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  ai (FF_20c segs cfg e HF) DW_ff158593. ai (FF_210 segs cfg e HF) DW_01000713.
  wb2 (FF_214 segs cfg e HF) DW_e4e666e3; intros Hb; bnorm Hb.
  - apply (tl60m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | rewrite c16s by lia; lia | exact Hf ].
  - wj (FF_218 segs cfg e HF) DW_0940006f.
    apply (b16m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | exact Hf ].
Qed.

(* [comment removed for export] *)
Lemma EP3m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e (0x240 + 96) ->
  rg S 11 = Z_to_bv 64 (src + k - Z.of_nat 3 + 16) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (4 - Z.of_nat 3 <= n - k <= 19 - Z.of_nat 3)%Z -> (Z.of_nat 3 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  ai (FF_2a0 segs cfg e HF) DW_ff358593. ai (FF_2a4 segs cfg e HF) DW_01000713.
  wb2 (FF_2a8 segs cfg e HF) DW_dae66ce3; intros Hb; bnorm Hb.
  - apply (tl60m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | rewrite c16s by lia; lia | exact Hf ].
  - 
    apply (b16m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | exact Hf ].
Qed.

Let SHL2 := shloopm 2%nat ltac:(lia) 0xa4 16 16 eq_refl eq_refl (Z_to_bv 32 0x0107581b) (Z_to_bv 32 0x01089393) (Z_to_bv 32 0x0108d89b) (Z_to_bv 32 0x01029393) (Z_to_bv 32 0x0102d29b) (Z_to_bv 32 0x01031393) (Z_to_bv 32 0x0103531b) (Z_to_bv 32 0x01071393)
  (FF_a4 segs cfg e HF) eq_refl DW_0107581b (FF_a8 segs cfg e HF) (FF_ac segs cfg e HF) (FF_b0 segs cfg e HF) (FF_b4 segs cfg e HF) (FF_b8 segs cfg e HF) eq_refl DW_01089393 (FF_bc segs cfg e HF) eq_refl DW_0108d89b (FF_c0 segs cfg e HF) (FF_c4 segs cfg e HF) eq_refl DW_01029393 (FF_c8 segs cfg e HF) eq_refl DW_0102d29b (FF_cc segs cfg e HF) (FF_d0 segs cfg e HF) eq_refl DW_01031393 (FF_d4 segs cfg e HF) eq_refl DW_0103531b (FF_d8 segs cfg e HF) (FF_dc segs cfg e HF) eq_refl DW_01071393 (FF_e0 segs cfg e HF) (FF_e4 segs cfg e HF) (FF_e8 segs cfg e HF) (FF_ec segs cfg e HF) (FF_f0 segs cfg e HF) (FF_f4 segs cfg e HF) (FF_f8 segs cfg e HF) (FF_fc segs cfg e HF) (FF_100 segs cfg e HF) EP2m.

Let SHL1 := shloopm 1%nat ltac:(lia) 0x1ac 8 24 eq_refl eq_refl (Z_to_bv 32 0x0087581b) (Z_to_bv 32 0x01889393) (Z_to_bv 32 0x0088d89b) (Z_to_bv 32 0x01829393) (Z_to_bv 32 0x0082d29b) (Z_to_bv 32 0x01831393) (Z_to_bv 32 0x0083531b) (Z_to_bv 32 0x01871393)
  (FF_1ac segs cfg e HF) eq_refl DW_0087581b (FF_1b0 segs cfg e HF) (FF_1b4 segs cfg e HF) (FF_1b8 segs cfg e HF) (FF_1bc segs cfg e HF) (FF_1c0 segs cfg e HF) eq_refl DW_01889393 (FF_1c4 segs cfg e HF) eq_refl DW_0088d89b (FF_1c8 segs cfg e HF) (FF_1cc segs cfg e HF) eq_refl DW_01829393 (FF_1d0 segs cfg e HF) eq_refl DW_0082d29b (FF_1d4 segs cfg e HF) (FF_1d8 segs cfg e HF) eq_refl DW_01831393 (FF_1dc segs cfg e HF) eq_refl DW_0083531b (FF_1e0 segs cfg e HF) (FF_1e4 segs cfg e HF) eq_refl DW_01871393 (FF_1e8 segs cfg e HF) (FF_1ec segs cfg e HF) (FF_1f0 segs cfg e HF) (FF_1f4 segs cfg e HF) (FF_1f8 segs cfg e HF) (FF_1fc segs cfg e HF) (FF_200 segs cfg e HF) (FF_204 segs cfg e HF) (FF_208 segs cfg e HF) EP1m.

Let SHL3 := shloopm 3%nat ltac:(lia) 0x240 24 8 eq_refl eq_refl (Z_to_bv 32 0x0187581b) (Z_to_bv 32 0x00889393) (Z_to_bv 32 0x0188d89b) (Z_to_bv 32 0x00829393) (Z_to_bv 32 0x0182d29b) (Z_to_bv 32 0x00831393) (Z_to_bv 32 0x0183531b) (Z_to_bv 32 0x00871393)
  (FF_240 segs cfg e HF) eq_refl DW_0187581b (FF_244 segs cfg e HF) (FF_248 segs cfg e HF) (FF_24c segs cfg e HF) (FF_250 segs cfg e HF) (FF_254 segs cfg e HF) eq_refl DW_00889393 (FF_258 segs cfg e HF) eq_refl DW_0188d89b (FF_25c segs cfg e HF) (FF_260 segs cfg e HF) eq_refl DW_00829393 (FF_264 segs cfg e HF) eq_refl DW_0182d29b (FF_268 segs cfg e HF) (FF_26c segs cfg e HF) eq_refl DW_00831393 (FF_270 segs cfg e HF) eq_refl DW_0183531b (FF_274 segs cfg e HF) (FF_278 segs cfg e HF) eq_refl DW_00871393 (FF_27c segs cfg e HF) (FF_280 segs cfg e HF) (FF_284 segs cfg e HF) (FF_288 segs cfg e HF) (FF_28c segs cfg e HF) (FF_290 segs cfg e HF) (FF_294 segs cfg e HF) (FF_298 segs cfg e HF) (FF_29c segs cfg e HF) EP3m.

Lemma fsfsZM : forall (j : Z) (q : nat) (k' : Z), (0 <= j)%Z -> k' = (j + Z.of_nat q)%Z -> (q < 4)%nat ->
  firstn 1 (skipn q (firstn 4 (skipn (Z.to_nat j) bs))) = firstn 1 (skipn (Z.to_nat k') bs).
Proof.
  intros j q k' Hj -> Hq. rewrite skipn_firstn_comm, firstn_firstn. replace (Nat.min 1 (4 - q)) with 1%nat by lia.
  rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma sb_srli8M : forall l, length l = 4%nat -> store_bytes SZ1 (v_srli (LWv l) 8) = firstn 1 (skipn 1 l).
Proof. intros l Hl. exact (sb_srli l 1 Hl ltac:(lia)). Qed.
Lemma sb_srli16M : forall l, length l = 4%nat -> store_bytes SZ1 (v_srli (LWv l) 16) = firstn 1 (skipn 2 l).
Proof. intros l Hl. exact (sb_srli l 2 Hl ltac:(lia)). Qed.

Local Ltac litu := repeat match goal with |- context [bv_unsigned ?b] => is_closed_term b;
                     let v := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with v end.
Local Ltac cpX Hf := rewrite ?mem_setx;
  lazymatch type of Hf with copied _ _ _ ?k1 _ =>
    lazymatch goal with |- copied _ _ _ ?k2 _ => replace k2 with k1 by lia; exact Hf end end.
Local Ltac valP := rgn; rwregsX; rewrite ?srl_srli, ?lw_LWv; litu; reflexivity.
Local Ltac dtb0 := rewrite sb_lw0 by (apply len4M; lia); rewrite <- (skipn_O (firstn 4 _)); apply fsfsZM; lia.
Local Ltac dtb8 := rewrite sb_srli8M by (apply len4M; lia); apply fsfsZM; lia.
Local Ltac dtb16 := rewrite sb_srli16M by (apply len4M; lia); apply fsfsZM; lia.

(* [comment removed for export] *)
Lemma PR2m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x88 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = LWv (firstn 4 (skipn (Z.to_nat (src + k - src)) bs)) ->
  (32 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 H14 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  wr wacc_ShiftImm (FF_88 segs cfg e HF) DW_00875793 valP.
  ai (FF_8c segs cfg e HF) DW_ffe60613.
  st (FF_90 segs cfg e HF) DW_00e68023 Hf 1%nat dtb0.
  st (FF_94 segs cfg e HF) DW_00f680a3 Hf 1%nat dtb8.
  ai (FF_98 segs cfg e HF) DW_00268693. ai (FF_9c segs cfg e HF) DW_01058593. ai (FF_a0 segs cfg e HF) DW_01100793.
  apply (SHL2 (Z.to_nat ((n - (k + 2)) / 16) + 1) _ (k + 2)%Z _ Hm).
  - pose proof (Z.div_mod (n - (k + 2)) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - (k + 2)) 16 ltac:(lia)).
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). lia.
  - mcf_chain HS.
  - reflexivity.
  - regZ.
  - regZ.
  - regZ.
  - rgn. rwregsX. f_equal. apply fs_eqM. lia.
  - regZ.
  - lia.
  - lia.
  - cpX Hf.
Qed.

Lemma PR1m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x198 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = LWv (firstn 4 (skipn (Z.to_nat (src + k - src)) bs)) ->
  (32 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 H14 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  st (FF_198 segs cfg e HF) DW_00e68023 Hf 1%nat dtb0.
  ai (FF_19c segs cfg e HF) DW_00168693. ai (FF_1a0 segs cfg e HF) DW_fff60613.
  ai (FF_1a4 segs cfg e HF) DW_01058593. ai (FF_1a8 segs cfg e HF) DW_01200793.
  apply (SHL1 (Z.to_nat ((n - (k + 1)) / 16) + 1) _ (k + 1)%Z _ Hm).
  - pose proof (Z.div_mod (n - (k + 1)) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - (k + 1)) 16 ltac:(lia)).
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). lia.
  - mcf_chain HS.
  - reflexivity.
  - regZ.
  - regZ.
  - regZ.
  - rgn. rwregsX. f_equal. apply fs_eqM. lia.
  - regZ.
  - lia.
  - lia.
  - cpX Hf.
Qed.

Lemma PR3m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x21c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = LWv (firstn 4 (skipn (Z.to_nat (src + k - src)) bs)) ->
  (32 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 H14 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  wr wacc_ShiftImm (FF_21c segs cfg e HF) DW_00875793 valP.
  wr wacc_ShiftImm (FF_220 segs cfg e HF) DW_01075813 valP.
  ai (FF_224 segs cfg e HF) DW_ffd60613.
  st (FF_228 segs cfg e HF) DW_00e68023 Hf 1%nat dtb0.
  st (FF_22c segs cfg e HF) DW_00f680a3 Hf 1%nat dtb8.
  st (FF_230 segs cfg e HF) DW_01068123 Hf 1%nat dtb16.
  ai (FF_234 segs cfg e HF) DW_00368693. ai (FF_238 segs cfg e HF) DW_01058593. ai (FF_23c segs cfg e HF) DW_01000793.
  apply (SHL3 (Z.to_nat ((n - (k + 3)) / 16) + 1) _ (k + 3)%Z _ Hm).
  - pose proof (Z.div_mod (n - (k + 3)) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - (k + 3)) 16 ltac:(lia)).
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). lia.
  - mcf_chain HS.
  - reflexivity.
  - regZ.
  - regZ.
  - regZ.
  - rgn. rwregsX. f_equal. apply fs_eqM. lia.
  - regZ.
  - lia.
  - lia.
  - cpX Hf.
Qed.

End LoopM.
End MCFM.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
