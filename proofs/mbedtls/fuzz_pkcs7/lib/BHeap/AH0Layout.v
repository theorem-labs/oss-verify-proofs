(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanSound AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AH0Spec0 AH0Base.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Layout () : Init.string Init.list := ["Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PG"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_lla"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_ictx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_divec"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tmpv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_mus1"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_mus2"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_brk0pg"; "Layout.SB"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Spec0.BP"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_secv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dtls"; "Layout.TOP"; "Layout.SP"; "Layout.EXTRA"; "Layout.GSH"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"].


Section Layout.
  Context {hAR : arun}.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  (* [comment removed for export] *)
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.

  Definition SP : Z := 32768 * uv p v_s1 + 16 * uv p v_s2.
  Definition TOP : Z := 32768 * uv p v_s1 + 4096 * uv p v_tpg.
  Definition SB : Z := PG p v_prim - PG p v_pslack + 0x10000.
  Definition EXTRA : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AH0Layout ()) "(0.(1.$2.$2.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$6.)+10000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$7.)+38>000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$8.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$9.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$:.)+1000.)(;.(1.$2.$2.)))))))VFOG,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition GSH : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AH0Layout ()) "(3.(1.$2.$2.)(4.$2.$2.(<.VhAR,)(=.(>.+2.+2?.)(<.VhAR,)))(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$:.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$9.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$8.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$7.)+38>000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$6.)+10000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$?.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$10.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(11.(5.Vp,$10.)+1000.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$12.)+1000.)(3.(1.$2.$2.)(4.$2.$2.(5.Vp,$13.)+2000.)(3.(1.$2.$2.)(4.$2.$2.(11.$14.(>.+2.+25.))+1000.)(;.(1.$2.$2.))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  Definition bp_of : boot_params := ltac2:(CDefT.buildp (gd_tbl_AH0Layout ()) "(15.(5.Vp,$16.)$14.(5.Vp,$17.)(5.Vp,$18.)(5.Vp,$19.)(5.Vp,$1:.)(5.Vp,$1;.)(5.Vp,$1<.)(5.Vp,$1=.)$1>.$1?.VSTKHI,$20.VTF,$21.)")
(* [comment removed for export] *).

  Hypothesis HAC : ACEIL = STKPG p - 0x800000.
  Hypothesis STKHI_gt : SP < STKHI.
  Hypothesis STKHI_pg : STKHI mod 4096 = 0.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.
  Hypothesis STKHI_len : STKHI <= SP + 2 ^ 23.
  Hypothesis FOG_ok : ltac2:(CDefT.buildp (gd_tbl_AH0Layout ()) "(22.(1.$2.$2.)Lr,(1.$2.$2.)(23.(24.(25.$2.$2.R1.)(26.$2.$2.R1.))(23.(27.=(26.$2.$2.R1.))(23.(28.(11.(25.$2.$2.R1.)(26.$2.$2.R1.))(<.VhAR,))(23.(29.$2.(2:.(25.$2.$2.R1.)+1000.)=)(29.$2.(2:.(26.$2.$2.R1.)+1000.)=)))))VFOG,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="HCN"] Lemma vrange : forall v lo hi, existsb (nt_eqb (NRange lo (WVar v) hi)) CNSTS = true -> lo <= uv p v <= hi.
  Proof.
    intros v lo hi H. pose proof (me_cnst p HCN _ (In_CNSTS _ H)) as C. cbn [ninst cnst_ok winst] in C. unfold uv. exact C.
  Qed.
  #[using="HCN"] Lemma r_s1 : 0xffff0000 <= uv p v_s1 <= 0xffffffff. Proof. apply vrange. vm_compute. reflexivity. Qed.
  #[using="HCN"] Lemma r_s2 : 0 <= uv p v_s2 <= 2047. Proof. apply vrange. vm_compute. reflexivity. Qed.
  #[using="HCN"] Lemma r_tpg : 0 <= uv p v_tpg <= 8. Proof. apply vrange. vm_compute. reflexivity. Qed.
  #[using="HCN"] Lemma r_pslack : 0 <= uv p v_pslack <= 15. Proof. apply vrange. vm_compute. reflexivity. Qed.
  #[using="HCN"] Lemma r_prim : 0x10007fff8 <= uv p v_prim <= 0x7fdfff7ef. Proof. apply vrange. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="hAR HCN STKHI"] Lemma r_top : 0 <= 16 * uv p v_s2 - 4096 * uv p v_tpg + 3935 <= 4095.
  Proof.
    assert (H : existsb (nt_eqb (NRange 0 (WAlu ALU_ADD (WAlu ALU_ADD (WMd M_MUL (WLit 16) (WVar v_s2)) (WMd M_MUL (WLit (-0x1000)) (WVar v_tpg))) (WLit 3935)) 4095)) CNSTS = true)
      by (vm_compute; reflexivity).
    pose proof (me_cnst p HCN _ (In_CNSTS _ H)) as C. cbn [ninst cnst_ok] in C. rewrite zev_sound in C. cbn [zev] in C.
    pose proof r_s2. pose proof r_tpg.
    (* [comment removed for export] *)
    set (x := 16 * uv p v_s2 + -4096 * uv p v_tpg + 3935) in C.
    assert (Hx : -2 ^ 16 < x < 2 ^ 16) by (subst x; lia).
    destruct (Z_lt_le_dec x 0) as [Hneg|Hnn].
    - exfalso. replace (x mod 2 ^ 64) with (x + 2 ^ 64) in C by (symmetry; rewrite <- (Z_mod_plus_full x 1 (2 ^ 64)) || idtac; rewrite Z.mod_small; lia). lia.
    - rewrite Z.mod_small in C by lia. subst x. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR HCN STKHI"] Lemma r_sb : (4096 * uv p v_prim) mod 0x10000 = 4096 * uv p v_pslack.
  Proof.
    assert (H : existsb (nt_eqb (NRange 0 (WAlu ALU_ADD (WMd M_MUL (WLit (-0x1000)) (WVar v_pslack)) (WAlu ALU_AND (WMd M_MUL (WLit 0x1000) (WVar v_prim)) (WLit 0xffff))) 0)) CNSTS = true)
      by (vm_compute; reflexivity).
    pose proof (me_cnst p HCN _ (In_CNSTS _ H)) as C. cbn [ninst cnst_ok] in C. rewrite zev_sound in C. cbn [zev] in C.
    pose proof r_pslack as RS. pose proof r_prim as RP.
    rewrite (Z.mod_small (4096 * uv p v_prim)) in C by lia. rewrite (Z.mod_small 65535) in C by lia.
    change 65535 with (Z.ones 16) in C. rewrite Z.land_ones in C by lia. change (2 ^ 16) with 0x10000 in C.
    pose proof (Z.mod_pos_bound (4096 * uv p v_prim) 0x10000 ltac:(lia)) as MB.
    set (x := -4096 * uv p v_pslack + (4096 * uv p v_prim) mod 0x10000) in C.
    assert (Hx : -2 ^ 17 < x < 2 ^ 17) by (subst x; lia).
    destruct (Z_lt_le_dec x 0) as [Hneg|Hnn].
    - exfalso. replace (x mod 2 ^ 64) with (x + 2 ^ 64) in C by (symmetry; rewrite <- (Z_mod_plus_full x 1 (2 ^ 64)) || idtac; rewrite Z.mod_small; lia). lia.
    - rewrite Z.mod_small in C by lia. subst x. lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac pv := cbn; tauto.
  Local Ltac inC := apply In_CNSTS; vm_compute; reflexivity.

  #[using="HCN STKHI HAC FOG_ok"] Lemma extra_ok : ltac2:(CDefT.buildp (gd_tbl_AH0Layout ()) "(22.(1.$2.$2.)Lr,(1.$2.$2.)(23.(24.(25.$2.$2.R1.)(26.$2.$2.R1.))(23.(27.=(26.$2.$2.R1.))(23.(28.(11.(25.$2.$2.R1.)(26.$2.$2.R1.))(<.VhAR,))(23.(29.$2.(2:.(25.$2.$2.R1.)+1000.)=)(29.$2.(2:.(26.$2.$2.R1.)+1000.)=)))))$20.)")
(* [comment removed for export] *).
  Proof.
    pose proof r_s1 as S1. pose proof r_s2 as S2.
    assert (ONE : forall v len, In v PAGEVARS -> 0 < len < 2 ^ 64 -> len mod 4096 = 0 ->
              In (NDisj (AOff (W_STKPG) (-0x800000)) (WLit 0x800000000000) (AOff (WMd M_MUL (WLit 0x1000) (WVar v)) 0) (WLit len)) CNSTS ->
              In (NDisj (ALit 0x10000) (WLit 0x64f000) (AOff (WMd M_MUL (WLit 0x1000) (WVar v)) 0) (WLit len)) CNSTS ->
              In (NDisj (ALit 0x7fff7000) (WLit 0x100000001000) (AOff (WMd M_MUL (WLit 0x1000) (WVar v)) 0) (WLit len)) CNSTS ->
              lowhigh (PG p v) len /\ 0 < len /\ PG p v + len <= ACEIL /\ PG p v mod 4096 = 0 /\ len mod 4096 = 0).
    { intros v len Hv Hlen Hal I1 I2 I3. pose proof (PG_range p HCN v Hv) as G.
      pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v len Hv ltac:(lia) I1) as K.
      pose proof (page_hull_apart p HCN v len Hv ltac:(lia) I2) as HH.
      pose proof (page_band_apart p HCN v len Hv ltac:(lia) I3) as BB.
      unfold lowhigh, kHighMemBeg. rewrite HAC. repeat split; try lia. }
    unfold EXTRA. apply Forall_app. split; [|exact FOG_ok].
    constructor; [exact (ONE v_lla 0x10000 ltac:(pv) ltac:(lia) eq_refl ltac:(inC) ltac:(inC) ltac:(inC))|].
    constructor; [exact (ONE v_ictx 0x38e000 ltac:(pv) ltac:(lia) eq_refl ltac:(inC) ltac:(inC) ltac:(inC))|].
    constructor; [exact (ONE v_tvec 0x1000 ltac:(pv) ltac:(lia) eq_refl ltac:(inC) ltac:(inC) ltac:(inC))|].
    constructor; [exact (ONE v_gvec 0x1000 ltac:(pv) ltac:(lia) eq_refl ltac:(inC) ltac:(inC) ltac:(inC))|].
    constructor; [exact (ONE v_divec 0x1000 ltac:(pv) ltac:(lia) eq_refl ltac:(inC) ltac:(inC) ltac:(inC))|].
    constructor.
  Qed.

  #[using="HCN"] Lemma r_brk0pg : 1631 <= uv p v_brk0pg <= 0x4065f. Proof. apply vrange. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma gsh_ok : wf_gsh (L0_of bp_of).
  Proof.
    pose proof aceil_bounds as AB. pose proof r_brk0pg as BR.
    assert (PGR : forall v, In v PAGEVARS -> 0 <= PG p v /\ PG p v + 0x38e000 + 0x1000 <= 2 ^ 47).
    { intros v Hv. pose proof (proj1 (PG_range p HCN v Hv)). lia. }
    pose proof (PGR v_divec ltac:(pv)). pose proof (PGR v_gvec ltac:(pv)). pose proof (PGR v_tvec ltac:(pv)). pose proof (PGR v_ictx ltac:(pv)).
    pose proof (PGR v_lla ltac:(pv)). pose proof (PGR v_tmpv ltac:(pv)). pose proof (PGR v_mus1 ltac:(pv)). pose proof (PGR v_mus2 ltac:(pv)).
    pose proof r_prim as PR. pose proof r_pslack as PS.
    unfold wf_gsh. cbn [l_gsh L0_of bp_of bp_gsh]. unfold GSH. split.
    - repeat (apply Forall_cons; [cbn [fst snd]; unfold SB, PG in *; lia|]). apply Forall_nil.
    - unfold sum, npg_shadow. cbn [fold_right map snd].
      assert (D0 : (2 ^ 47 - ACEIL) / 32768 <= 65792) by (apply Z.div_le_upper_bound; lia).
      change (0x1000 / 32768) with 0. change (0x38e000 / 32768) with 113. change (0x10000 / 32768) with 2. change (0x2000 / 32768) with 0. lia.
  Qed.

  #[using="HCN HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len FOG_ok"] Theorem L0_wf : wf_L' (L0_of bp_of).
  Proof.
    pose proof r_s1 as S1. pose proof r_s2 as S2. pose proof r_tpg as TPG. pose proof r_pslack as PS. pose proof r_prim as PR.
    pose proof r_top as RT.
    assert (HSTK : STKPG p <= SP /\ SP < STKPG p + 4096).
    { unfold STKPG, SP. pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    pose proof (proj1 (PG_range p HCN v_prim ltac:(pv))) as Gprim. pose proof (proj1 (PG_range p HCN v_secv ltac:(pv))) as Gsecv.
    pose proof (proj1 (PG_range p HCN v_thr ltac:(pv))) as Gthr. pose proof (proj1 (PG_range p HCN v_treg ltac:(pv))) as Gtreg.
    pose proof (proj1 (PG_range p HCN v_fstk ltac:(pv))) as Gfstk. pose proof (proj1 (PG_range p HCN v_dtls ltac:(pv))) as Gdtls.
    pose proof (proj1 (PG_range p HCN v_dnodes ltac:(pv))) as Gdn. pose proof (proj1 (PG_range p HCN v_dstore ltac:(pv))) as Gds.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_prim 0x2000011000 ltac:(pv) ltac:(lia) ltac:(inC)) as Kprim.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_secv 0x800000 ltac:(pv) ltac:(lia) ltac:(inC)) as Ksecv.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_thr 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Kthr.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_treg 0x10000 ltac:(pv) ltac:(lia) ltac:(inC)) as Ktreg.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_fstk 0xb09000 ltac:(pv) ltac:(lia) ltac:(inC)) as Kfstk.
    pose proof (page_stack_apart p HCN (proj2 S1) (proj2 S2) v_dtls 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Kdtls.
    pose proof (page_hull_apart p HCN v_thr 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Hthr.
    pose proof (page_hull_apart p HCN v_treg 0x10000 ltac:(pv) ltac:(lia) ltac:(inC)) as Htreg.
    pose proof (page_hull_apart p HCN v_fstk 0xb09000 ltac:(pv) ltac:(lia) ltac:(inC)) as Hfstk.
    pose proof (page_hull_apart p HCN v_dtls 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Hdtls.
    pose proof (page_hull_apart p HCN v_secv 0x800000 ltac:(pv) ltac:(lia) ltac:(inC)) as Hsecv.
    pose proof (page_band_apart p HCN v_thr 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Bthr.
    pose proof (page_band_apart p HCN v_treg 0x10000 ltac:(pv) ltac:(lia) ltac:(inC)) as Btreg.
    pose proof (page_band_apart p HCN v_fstk 0xb09000 ltac:(pv) ltac:(lia) ltac:(inC)) as Bfstk.
    pose proof (page_band_apart p HCN v_dtls 0x1000 ltac:(pv) ltac:(lia) ltac:(inC)) as Bdtls.
    pose proof (page_band_apart p HCN v_secv 0x800000 ltac:(pv) ltac:(lia) ltac:(inC)) as Bsecv.
    pose proof extra_ok as EX.
    pose proof gsh_ok as GS.
    unfold wf_L', wf_L, wf_dtls, lowhigh, kHighMemBeg, kFakeBytes, space_end, kSpaceSize.
    cbn [L0_of bp_of l_b6 l_sb l_pa l_T l_ctx l_fs l_nb0 l_ss0 l_top l_s0 l_htop l_stk_lo l_stk_hi l_errno l_extra l_ctxlen
         bp_b6 bp_sb bp_pa bp_T bp_ctx bp_fs bp_nb0 bp_ss0 bp_dtls bp_top bp_sp0 bp_stkhi bp_extra bp_tf].
    unfold SB, TOP. fold SP. unfold SP in HSTK, STKHI_gt, STKHI_len |- *.
    (* [comment removed for export] *)
    assert (AL : forall k x, (x * k) mod k = 0) by (intros; apply Z_mod_mult).
    assert (ALPG : forall v, PG p v mod 4096 = 0) by (intros v; unfold PG; rewrite Z.mul_comm; apply Z_mod_mult).
    assert (ALSB : (PG p v_prim - PG p v_pslack + 65536) mod 2 ^ 16 = 0).
    { unfold PG. pose proof r_sb as RSB. rewrite <- RSB.
      rewrite Zplus_mod, Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
    assert (ALTOP : (32768 * uv p v_s1 + 4096 * uv p v_tpg) mod 4096 = 0).
    { replace (32768 * uv p v_s1 + 4096 * uv p v_tpg) with ((8 * uv p v_s1 + uv p v_tpg) * 4096) by lia. apply Z_mod_mult. }
    assert (AL16a : (32768 * uv p v_s1 + 16 * uv p v_s2 - 48) mod 16 = 0).
    { replace (32768 * uv p v_s1 + 16 * uv p v_s2 - 48) with ((2048 * uv p v_s1 + uv p v_s2 - 3) * 16) by lia. apply Z_mod_mult. }
    assert (AL16b : (32768 * uv p v_s1 + 16 * uv p v_s2 - 2 ^ 23) mod 16 = 0).
    { replace (32768 * uv p v_s1 + 16 * uv p v_s2 - 2 ^ 23) with ((2048 * uv p v_s1 + uv p v_s2 - 2 ^ 19) * 16) by lia. apply Z_mod_mult. }
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption
            | exact GS
            | apply ALPG
            | (* [comment removed for export] *)
              clear Hthr Htreg Hfstk Hdtls Hsecv Bthr Btreg Bfstk Bdtls Bsecv AL ALPG ALSB ALTOP AL16a AL16b EX GS; unfold PG in *; lia ].
  Qed.
End Layout.
