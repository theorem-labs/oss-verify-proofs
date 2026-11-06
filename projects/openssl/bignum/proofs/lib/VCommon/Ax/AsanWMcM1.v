(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep AsanWMemcpyF1 AsanSMat AsanWMat AsanWMcM0.
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

Let HC : MCCode segs e := mcf_al segs e HF.
Let T2 := t2m segs cfg e HC MCF_CLOB HCLF HCL1F model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok
             Hbud Hra HK.

Lemma mhaltF : forall m, matin model0 m L -> m_halted m = None.
Proof. intros m Hm. rewrite (matin_halted _ _ _ Hm). exact Hh0. Qed.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhaltF m' Hm) as Hh.

Lemma LbsM : length bs = Z.to_nat n.
Proof. exact (rdn_length _ _ _ _ _ Hbs). Qed.

Lemma src_rdM : forall m k' (a : Z) (c : nat), copied m (ms_mem ms0) dst k' bs -> (0 <= k' <= n)%Z ->
  (0 <= a - src)%Z -> (a - src + Z.of_nat c <= n)%Z ->
  rdn segs m (Z_to_bv 64 a) c = Some (firstn c (skipn (Z.to_nat (a - src)) bs)).
Proof.
  intros m k' a c Hc Hk' Ha Hac.
  assert (E : rdn segs m (Z_to_bv 64 a) c = rdn segs (ms_mem ms0) (Z_to_bv 64 a) c).
  { apply rdn_ext; [rewrite bvu_z by lia; lia|].
    intros x Hx. rewrite bvu_z in Hx by lia. apply (proj2 (Hc x)). lia. }
  rewrite E.
  pose proof (SeqExec.rdn_skipn segs (ms_mem ms0) (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat (a - src)) Hbs ltac:(lia)) as Hs.
  unfold nat_to_word in Hs. rewrite zw_add, Z2Nat.id in Hs by lia. replace (src + (a - src))%Z with a in Hs by lia.
  apply (SeqExec.rdn_firstn segs (ms_mem ms0) (Z.to_nat n - Z.to_nat (a - src))); [exact Hs | lia].
Qed.

Lemma sok_subM : forall m k' (a : Z) (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= a - dst)%Z -> (a - dst + Z.of_nat c <= n)%Z -> store_ok segs m (Z_to_bv 64 a) c = true.
Proof.
  intros m k' a c Hc Ha Hac.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (copied_grows _ _ _ _ _ Hc) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma copied_stM : forall m k' (a : Z) data (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= k')%Z -> (k' + Z.of_nat c <= n)%Z -> a = (dst + k')%Z -> data = firstn c (skipn (Z.to_nat k') bs) ->
  copied (write_to_mem m (Z_to_bv 64 a) data) (ms_mem ms0) dst (k' + Z.of_nat c) bs.
Proof.
  intros m k' a data c Hc Hk Hkc -> ->. apply copied_step; [lia | lia | rewrite LbsM; lia | lia | exact Hc].
Qed.

Lemma len4M : forall (j : Z), (0 <= j)%Z -> (j + 4 <= n)%Z -> length (firstn 4 (skipn (Z.to_nat j) bs)) = 4%nat.
Proof. intros j Hj Hjn. rewrite length_firstn, length_skipn, LbsM. lia. Qed.

Lemma len1M : forall (j : Z), (0 <= j)%Z -> (j + 1 <= n)%Z -> length (firstn 1 (skipn (Z.to_nat j) bs)) = 1%nat.
Proof. intros j Hj Hjn. rewrite length_firstn, length_skipn, LbsM. lia. Qed.

Lemma fs_eqM : forall (c : nat) (j j' : Z), j = j' -> firstn c (skipn (Z.to_nat j) bs) = firstn c (skipn (Z.to_nat j') bs).
Proof. intros c j j' ->. reflexivity. Qed.

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
Local Ltac sb F D Hf := st F D Hf 1%nat dt1.
Local Ltac ai F D := wr wacc_OpImm F D valX.
Local Ltac regZ := rgn; rwregsX; first [ reflexivity | f_equal; lia ].

Lemma b4m : forall S k r m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x394 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + 4 + r mod 4 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z.mod_pos_bound r 4 ltac:(lia)).
  ld (FF_394 segs cfg e HF) DW_0005c703 Hf. ld (FF_398 segs cfg e HF) DW_0015c783 Hf. ld (FF_39c segs cfg e HF) DW_0025c803 Hf. ld (FF_3a0 segs cfg e HF) DW_0035c883 Hf.
  ai (FF_3a4 segs cfg e HF) DW_00458593. ai (FF_3a8 segs cfg e HF) DW_00468293.
  sb (FF_3ac segs cfg e HF) DW_00e68023 Hf. sb (FF_3b0 segs cfg e HF) DW_00f680a3 Hf. sb (FF_3b4 segs cfg e HF) DW_01068123 Hf. sb (FF_3b8 segs cfg e HF) DW_011681a3 Hf.
  ai (FF_3bc segs cfg e HF) DW_00028693.
  apply (T2 _ (k + 4)%Z r _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
  - rewrite ?mem_setx. replace (k + 4)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.

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

Local Ltac valA := rgn; rwregsX; rewrite alu_andi_z by (lits; lia); lits; reflexivity.
Local Ltac bnorm Hb := unfold w0 in Hb;
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lia;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb;
  first [ apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb | apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb | idtac ].

Lemma tl68m : forall S k r m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x68 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z_land_range r 4 ltac:(lia) ltac:(lia)).
  wr wacc_OpImm (FF_68 segs cfg e HF) DW_00467713 valA.
  wb2 (FF_6c segs cfg e HF) DW_32071463; intros Hb; bnorm Hb.
  - destruct (c4_1 r Hr Hb) as [M1 M2].
    apply (b4m _ k r _ Hm); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
  - destruct (c4_0 r Hr Hb) as [M1 M2].
    wj (FF_70 segs cfg e HF) DW_3500006f.
    apply (T2 _ k r _ Hm); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
Qed.

Lemma b8m : forall S k r m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x340 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + 8 + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z.mod_pos_bound r 8 ltac:(lia)). pose proof (Z_land_range r 4 ltac:(lia) ltac:(lia)).
  ld (FF_340 segs cfg e HF) DW_0005c703 Hf. ld (FF_344 segs cfg e HF) DW_0015c783 Hf. ld (FF_348 segs cfg e HF) DW_0025c803 Hf. ld (FF_34c segs cfg e HF) DW_0035c883 Hf.
  ld (FF_350 segs cfg e HF) DW_0045c283 Hf. ld (FF_354 segs cfg e HF) DW_0055c303 Hf. ld (FF_358 segs cfg e HF) DW_0065c383 Hf. ld (FF_35c segs cfg e HF) DW_0075ce03 Hf.
  ai (FF_360 segs cfg e HF) DW_00858593.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28] : list reg).
  sb (FF_364 segs cfg e HF) DW_00e68023 Hf. sb (FF_368 segs cfg e HF) DW_00f680a3 Hf. sb (FF_36c segs cfg e HF) DW_01068123 Hf. sb (FF_370 segs cfg e HF) DW_011681a3 Hf.
  ai (FF_374 segs cfg e HF) DW_00868713.
  sb (FF_378 segs cfg e HF) DW_00568223 Hf. sb (FF_37c segs cfg e HF) DW_006682a3 Hf. sb (FF_380 segs cfg e HF) DW_00768323 Hf. sb (FF_384 segs cfg e HF) DW_01c683a3 Hf.
  ai (FF_388 segs cfg e HF) DW_00070693.
  snap S HS Hf ([11; 12; 13] : list reg).
  wr wacc_OpImm (FF_38c segs cfg e HF) DW_00467713 valA.
  wb2 (FF_390 segs cfg e HF) DW_02070863; intros Hb; bnorm Hb.
  - destruct (c4_0 r Hr Hb) as [M1 M2].
    apply (T2 _ (k + 8)%Z r _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
                                                 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
  - destruct (c4_1 r Hr Hb) as [M1 M2].
    apply (b4m _ (k + 8)%Z r _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
                                                 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.

Lemma tl60m : forall S k r m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x60 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 16 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z_land_range r 8 ltac:(lia) ltac:(lia)).
  wr wacc_OpImm (FF_60 segs cfg e HF) DW_00867713 valA.
  wb2 (FF_64 segs cfg e HF) DW_2c071e63; intros Hb; bnorm Hb.
  - destruct (c8_1 r Hr Hb) as [M1 M2].
    apply (b8m _ k r _ Hm); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
  - destruct (c8_0 r Hr Hb) as [M1 M2].
    apply (tl68m _ k r _ Hm); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
Qed.

Lemma b16m : forall S k r m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x2ac ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (16 <= r < 32)%Z -> (0 <= k)%Z -> (k + r = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k r m Hm HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (c16 r Hr). pose proof (Z_land_range r 8 ltac:(lia) ltac:(lia)).
  ld (FF_2ac segs cfg e HF) DW_0005c703 Hf. ld (FF_2b0 segs cfg e HF) DW_0015c783 Hf. ld (FF_2b4 segs cfg e HF) DW_0025c803 Hf. ld (FF_2b8 segs cfg e HF) DW_0035c883 Hf.
  ld (FF_2bc segs cfg e HF) DW_0045c283 Hf. ld (FF_2c0 segs cfg e HF) DW_0055c303 Hf. ld (FF_2c4 segs cfg e HF) DW_0065c383 Hf. ld (FF_2c8 segs cfg e HF) DW_0075ce03 Hf.
  sb (FF_2cc segs cfg e HF) DW_00e68023 Hf. sb (FF_2d0 segs cfg e HF) DW_00f680a3 Hf. sb (FF_2d4 segs cfg e HF) DW_01068123 Hf. sb (FF_2d8 segs cfg e HF) DW_011681a3 Hf.
  snap S HS Hf ([11; 12; 13; 5; 6; 7; 28] : list reg).
  ld (FF_2dc segs cfg e HF) DW_0085c703 Hf. ld (FF_2e0 segs cfg e HF) DW_0095c783 Hf. ld (FF_2e4 segs cfg e HF) DW_00a5c803 Hf. ld (FF_2e8 segs cfg e HF) DW_00b5c883 Hf.
  sb (FF_2ec segs cfg e HF) DW_00568223 Hf. sb (FF_2f0 segs cfg e HF) DW_006682a3 Hf. sb (FF_2f4 segs cfg e HF) DW_00768323 Hf. sb (FF_2f8 segs cfg e HF) DW_01c683a3 Hf.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17] : list reg).
  ld (FF_2fc segs cfg e HF) DW_00c5c283 Hf. ld (FF_300 segs cfg e HF) DW_00d5c303 Hf. ld (FF_304 segs cfg e HF) DW_00e5c383 Hf. ld (FF_308 segs cfg e HF) DW_00f5ce03 Hf.
  ai (FF_30c segs cfg e HF) DW_01058593.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28] : list reg).
  sb (FF_310 segs cfg e HF) DW_00e68423 Hf. sb (FF_314 segs cfg e HF) DW_00f684a3 Hf. sb (FF_318 segs cfg e HF) DW_01068523 Hf. sb (FF_31c segs cfg e HF) DW_011685a3 Hf.
  ai (FF_320 segs cfg e HF) DW_01068713.
  sb (FF_324 segs cfg e HF) DW_00568623 Hf. sb (FF_328 segs cfg e HF) DW_006686a3 Hf. sb (FF_32c segs cfg e HF) DW_00768723 Hf. sb (FF_330 segs cfg e HF) DW_01c687a3 Hf.
  ai (FF_334 segs cfg e HF) DW_00070693.
  snap S HS Hf ([11; 12; 13] : list reg).
  wr wacc_OpImm (FF_338 segs cfg e HF) DW_00867713 valA.
  wb2 (FF_33c segs cfg e HF) DW_d20706e3; intros Hb; bnorm Hb.
  - destruct (c8_0 r ltac:(lia) Hb) as [M1 M2].
    apply (tl68m _ (k + 16)%Z r _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
  - destruct (c8_1 r ltac:(lia) Hb) as [M1 M2].
    apply (b8m _ (k + 16)%Z r _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.
End LoopM. End MCFM.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
