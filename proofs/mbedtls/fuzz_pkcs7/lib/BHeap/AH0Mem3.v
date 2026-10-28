(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX HMLib HM AH0Spec0 AH0Facts AH0Base AH0Layout AH0K AH0Rom AH0Mem1 AH0Mem2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotTop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Mem3 () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_rcase1"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_rcase2"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Rom.BSS_LO"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Rom.BSS_HI"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ct"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cinst"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CImg"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.length"].


Section Mem3.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Hypothesis HDEF : me_def p mem.
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  (* [comment removed for export] *)
  Hypothesis HR : ltac2:(CDefT.buildp (gd_tbl_AH0Mem3 ()) "(0.(1.(2.$3.VTF,+3.)(4.$5.(6.$7.Vmem,)(8.Vp,)))(1.(2.$3.VTF,+2.)(4.$5.(6.$7.Vmem,)(9.Vp,))))")
(* [comment removed for export] *).
  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.
  Let HF := HF mem p HCOM.
  Let NB := PG p v_dnodes.
  Let SS := PG p v_dstore.
  (* [comment removed for export] *)
  Hypothesis NB_ok : 0x65f000 <= NB /\ NB + 2 ^ 20 <= ACEIL.
  Hypothesis SS_ok : 0x65f000 <= SS /\ SS + 2 ^ 23 <= ACEIL.
  Hypothesis NBSS : NB + 2 ^ 20 <= SS \/ SS + 2 ^ 23 <= NB.
  Local Ltac pv := cbn; tauto.
  Local Ltac zdec := repeat match goal with |- _ /\ _ => split end;
    first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.eqb_eq; vm_compute; reflexivity ].
  Local Ltac orw :=
    lazymatch goal with |- rw_cells asegs ?m ?A ?cs =>
      lazymatch cs with context [p] => fail "orw: symbolic cell" | _ =>
      lazymatch A with context [p] => fail "orw: symbolic address" | _ =>
      apply (chk_rw_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end end end.
  Local Ltac znum := cbn [cells_size csize Nat.add Nat.mul length repeat Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.
  Local Ltac zrw L := apply L; [cbn; tauto | reflexivity | | | |]; znum.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section IMG.
    Variables lo hi : Z.
    Hypothesis IMG : AsanMainEntryKit.cell_ok ASEGS mem (CImg lo hi).
    #[using="IMG"] Lemma img_none : forall z, lo <= z < hi -> mem (Z_to_bv 64 z) = None.
    Proof. intros z Hz. exact (IMG z Hz). Qed.
    #[using="hAR p NB SS IMG"] Lemma img_zero_bytes : ltac2:(CDefT.buildp (gd_tbl_AH0Mem3 ()) "Pa,$3.Pk,$:.P,(;.Vlo,R2.)P,(;.(<.R3.(=.R2.))Vhi,)P,(;.$>.R4.)P,(;.(<.R5.(=.R4.))$?.)(10.$11.Vmem,R6.(12.(13.&8.)(14.&8.=)R5.))")
(* [comment removed for export] *).
    Proof.
      intros a k H1 H2 H3 H4. split; [unfold BSS_LO in *; lia|]. split; [rewrite repeat_length; unfold BSS_HI in *; lia|].
      intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat' by exact Hi.
      rewrite asegs_ASEGS. unfold mrd, wa. rewrite (img_none (a + Z.of_nat i)) by lia.
      exact (proj2 (bss_zero (a + Z.of_nat i) ltac:(lia))).
    Qed.
    #[using="hAR p NB SS IMG"] Lemma img_zero_wr : forall a n, lo <= a -> a + n <= hi -> BSS_LO <= a -> a + n <= BSS_HI -> wr_at asegs mem a n.
    Proof.
      intros a n H1 H2 H3 H4. split; [unfold BSS_LO in *; lia|]. split; [unfold BSS_HI in *; lia|].
      intros i Hi. rewrite asegs_ASEGS. pose proof (proj1 (bss_zero (a + i) ltac:(lia))) as W.
      unfold wa. unfold wview in W |- *. rewrite (img_none (a + i)) by lia. cbn beta in W. rewrite W. discriminate.
    Qed.
    #[using="hAR p NB SS IMG"] Lemma img_zero_rw : ltac2:(CDefT.buildp (gd_tbl_AH0Mem3 ()) "Pa,$3.Pcs,(15.$16.)P,(17.R1.)P,(2.(15.(13.&8.))(18.R2.)(12.(13.&8.)(14.&8.=)(19.R2.)))P,(;.Vlo,R4.)P,(;.(<.R5.(=.(19.R4.)))Vhi,)P,(;.$>.R6.)P,(;.(<.R7.(=.(19.R6.)))$?.)(1:.$11.Vmem,R8.R7.)")
(* [comment removed for export] *).
    Proof.
      intros a cs Hwf Hb H1 H2 H3 H4. split; [split; [exact Hwf | rewrite Hb; apply img_zero_bytes; lia] | apply img_zero_wr; lia].
    Qed.
  End IMG.

  (* [comment removed for export] *)
  #[using="hAR HCOM STKHI FOG HR HF NB SS NB_ok SS_ok NBSS"] Lemma rcase_facts : ltac2:(CDefT.buildp (gd_tbl_AH0Mem3 ()) "(1;.$3.LBK,$3.(1;.(15.$1<.)LLR,(15.$1<.)(1.(4.$5.(6.$7.Vmem,)(1=.$1<.$5.(1>.Vp,)R1.))(1.(6.$7.Vmem,(1?.+1=;8>8.R2.))(1.(6.$7.Vmem,(1?.(<.R2.+4.)+5>;8=8.))(1.(;.$20.R2.)(1.(;.(<.R2.+4.)+5>;8=8.)(1.(2.$3.(21.(22.R2.$20.)+4.)=)(1.(1:.$11.Vmem,R2.(23.$16.(24.(14.&40.+1.))(25.$16.)))(1.(1:.$11.Vmem,$26.(23.$16.(27.(14.&40.VTF,))(25.$16.)))(1;.(13.&40.)Lst,(13.&40.)(1:.$11.Vmem,(<.$26.+18.)(23.$16.(24.R1.)(25.$16.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    destruct HR as [[-> R]|[-> R]].
    - dexists 0x23f900, CELLS_rcase1. assert (HF1 : Forall (cell_ok ASEGS mem) (map (cinst p) CELLS_rcase1)) by exact R.
      split; [exact HF1|].
      split; [exact (proj1 (Forall_forall _ _) HF1 (CImg 0x1db8e8 0x23f900) ltac:(apply in_map_iff; exists (TImg 0x1db8e8 0x23f900); split; [reflexivity | cbn; tauto]))|].
      split; [exact (proj1 (Forall_forall _ _) HF1 (CImg 0x23f904 0x5eb8d8) ltac:(apply in_map_iff; exists (TImg 0x23f904 0x5eb8d8); split; [reflexivity | cbn; tauto]))|].
      split; [unfold A_DEP; lia|]. split; [lia|]. split; [reflexivity|].
      split; [split; [apply (chk_ro_cells mem p CELLS_rcase1 HF1 QLit 0x23f900 [C4 (Z_to_bv 64 1)]); [vm_compute; reflexivity | cbn; tauto | zdec | zdec]
                     | apply (chk_wr_at mem p CT_COMMON HF QLit 0x23f900 4); [vm_compute; reflexivity | zdec | zdec]]|].
      split; [split; [apply (chk_ro_cells mem p CELLS_rcase1 HF1 QLit A_SS [C8 (Z_to_bv 64 3)]); [vm_compute; reflexivity | cbn; tauto | zdec | zdec]
                     | apply (chk_wr_at mem p CT_COMMON HF QLit A_SS 8); [vm_compute; reflexivity | zdec | zdec]]|].
      destruct (chk_ex_C4 mem p CELLS_rcase1 HF1 QLit (A_SS + 24) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [st Hst]. exists st.
      split; [exact Hst | apply (chk_wr_at mem p CT_COMMON HF QLit (A_SS + 24) 4); [vm_compute; reflexivity | zdec | zdec]].
    - dexists 0x384a88, CELLS_rcase2. assert (HF2 : Forall (cell_ok ASEGS mem) (map (cinst p) CELLS_rcase2)) by exact R.
      split; [exact HF2|].
      split; [exact (proj1 (Forall_forall _ _) HF2 (CImg 0x1db8e8 0x384a88) ltac:(apply in_map_iff; exists (TImg 0x1db8e8 0x384a88); split; [reflexivity | cbn; tauto]))|].
      split; [exact (proj1 (Forall_forall _ _) HF2 (CImg 0x384a8c 0x5eb8d8) ltac:(apply in_map_iff; exists (TImg 0x384a8c 0x5eb8d8); split; [reflexivity | cbn; tauto]))|].
      split; [unfold A_DEP; lia|]. split; [lia|]. split; [reflexivity|].
      split; [split; [apply (chk_ro_cells mem p CELLS_rcase2 HF2 QLit 0x384a88 [C4 (Z_to_bv 64 1)]); [vm_compute; reflexivity | cbn; tauto | zdec | zdec]
                     | apply (chk_wr_at mem p CT_COMMON HF QLit 0x384a88 4); [vm_compute; reflexivity | zdec | zdec]]|].
      split; [split; [apply (chk_ro_cells mem p CELLS_rcase2 HF2 QLit A_SS [C8 (Z_to_bv 64 2)]); [vm_compute; reflexivity | cbn; tauto | zdec | zdec]
                     | apply (chk_wr_at mem p CT_COMMON HF QLit A_SS 8); [vm_compute; reflexivity | zdec | zdec]]|].
      destruct (chk_ex_C4 mem p CELLS_rcase2 HF2 QLit (A_SS + 24) ltac:(vm_compute; reflexivity) ltac:(zdec) ltac:(zdec)) as [st Hst]. exists st.
      split; [exact Hst | apply (chk_wr_at mem p CT_COMMON HF QLit (A_SS + 24) 4); [vm_compute; reflexivity | zdec | zdec]].
  Qed.

  (* [comment removed for export] *)
  #[using="hAR p HCOM TF HR HF NB SS NB_ok SS_ok NBSS"] Lemma map1_img : AsanMainEntryKit.cell_ok ASEGS mem (CImg 0x5eb8f0 0x62bdc0).
  Proof.
    exact (proj1 (Forall_forall _ _) HF (CImg 0x5eb8f0 0x62bdc0) ltac:(apply in_map_iff; exists (TImg 0x5eb8f0 0x62bdc0); split; [reflexivity | unfold CT_COMMON; rewrite !in_app_iff; left; cbn; tauto])).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR p NB SS"] Lemma def_ex_bytes : ltac2:(CDefT.buildp (gd_tbl_AH0Mem3 ()) "PA,$3.Pk,$:.P,Pa,(13.&40.)P,(1.(;.R3.(28.&40.R1.))(29.(28.&40.R1.)(<.R3.(=.R2.))))(2:.(2.(2;.(13.&8.))A1.Vmem,R2.(2<.(13.&8.))))P,(;.=R3.)P,(;.(<.R4.(=.R3.))(2=.+2.+40.))(1;.(15.(13.&8.))Lbs,(15.(13.&8.))(1.(2.$:.(2>.(13.&8.)R1.)R5.)(10.$11.Vmem,R6.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros A k H HA HB.
    exists (map (fun i => match mem (Z_to_bv 64 (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
    split; [rewrite length_map, length_seq; reflexivity|]. split; [exact HA|]. split; [rewrite length_map, length_seq; exact HB|].
    intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, (nth_error_nth' (seq 0 k) 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi.
    cbn [option_map Nat.add]. rewrite asegs_ASEGS. unfold mrd, wa.
    assert (U : bv_unsigned (Z_to_bv 64 (A + Z.of_nat i)) = A + Z.of_nat i) by (rewrite u_zbv; apply Z.mod_small; lia).
    pose proof (H (Z_to_bv 64 (A + Z.of_nat i)) ltac:(rewrite U; lia)) as D. destruct (mem (Z_to_bv 64 (A + Z.of_nat i))); [reflexivity | exfalso; exact (D eq_refl)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCN HCOM HDEF HR HF NB SS NB_ok SS_ok NBSS"] Theorem h0_hm_depot : hm_depot h0 mem.
  Proof.
    pose proof NB_ok as GN. pose proof SS_ok as GS. pose proof aceil_lt47 as A47.
    ddestruct rcase_facts as (BK & LR & HFR & IMG1 & IMG2 & BK1 & BK2 & BK4 & HBK & HSS & (st & Hst)).
    pose proof map1_img as IMG3.
    pose proof HDEF as D. unfold me_def in D. ddestruct D as (_ & _ & Ddstore & Ddnodes & _). revert Ddstore Ddnodes.
    rewrite ?(u_page p HCN v_dstore ltac:(pv)), ?(u_page p HCN v_dnodes ltac:(pv)). rewrite ?(u_wlit p) by lia. fold NB SS. intros Ddstore Ddnodes.
    unfold hm_depot. cbn [h_dep d_n d_nb s_total d_bl h0 h0_of bp bp_of bp_nb0 bp_ss0 bp_tf]. fold NB SS.
    unfold depot_inv.
    split; [orw|].
    split.
    { (* [comment removed for export] *)
      intros i Hi. destruct (Z.eq_dec (A_DEP + 4 * i) BK) as [E|NE].
      - exists 1. rewrite E. split; [exact HBK | lia].
      - exists 0. split; [| lia].
        assert (C : A_DEP + 4 * i + 4 <= BK \/ BK + 4 <= A_DEP + 4 * i).
        { pose proof (Z.div_mod (BK - A_DEP) 4 ltac:(lia)) as DM. rewrite BK4, Z.add_0_r in DM. lia. }
        destruct C as [C|C].
        + apply (img_zero_rw 0x1db8e8 BK IMG1); [cbn; tauto | reflexivity | | | |]; znum; unfold A_DEP, BSS_LO, BSS_HI in *; lia.
        + apply (img_zero_rw (BK + 4) 0x5eb8d8 IMG2); [cbn; tauto | reflexivity | | | |]; znum; unfold A_DEP, BSS_LO, BSS_HI in *; lia. }
    split.
    { (* [comment removed for export] *)
      split; [| split; [apply Forall_cons; [| apply Forall_nil]; split; [lia | split; [lia | exact (proj2 (PG_range p HCN v_dnodes ltac:(pv)))]] | cbn [length]; apply Nat2Z.inj_le; change (Z.of_nat (Init.Nat.of_num_uint _)) with 32768%Z; cbn; lia]].
      intros k Hk. unfold dmap1v, dblk. cbn [length]. change (Z.of_nat 1%nat) with 1.
      destruct (Z.eq_dec k 0) as [->|NZ].
      - cbn [Z.ltb]. change (Z.to_nat 0) with 0%nat. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r.
        me_word HF (ALit 0x5eb8e8) 8%nat X.
        split; [| apply (chk_wr_at mem p CT_COMMON HF QLit A_DEP_MAP1 8); [vm_compute; reflexivity | zdec | zdec]].
        pose proof (cword_ro_cells mem _ 8%nat _ [C8 (Z_to_bv 64 NB)] X ltac:(unfold NB; cbn [cells_bytes cbytes app]; rewrite app_nil_r, (w64_Page p HCN v_dnodes) by pv; reflexivity) ltac:(cbn; tauto) ltac:(rewrite u_zbv; zdec)) as R.
        rewrite u_zbv in R. exact R.
      - replace (k <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
        apply (img_zero_rw 0x5eb8f0 0x62bdc0 IMG3); [cbn; tauto | reflexivity | | | |]; znum; unfold A_DEP_MAP1, BSS_LO, BSS_HI in *; lia. }
    split.
    { (* [comment removed for export] *)
      intros s Hs. cbn [length] in Hs. change (Z.of_nat 1%nat) with 1 in Hs. unfold dnode, dblk. cbn [length].
      rewrite Z.div_small, Z.mod_small by lia. change (Z.to_nat 0) with 0%nat. cbn [nth].
      destruct (Z.eq_dec s 0) as [->|S0]; [| destruct (Z.eq_dec s 1) as [->|S1]].
      - dexists (Z_to_bv 64 0), (Z_to_bv 64 0), 0. split; [| lia]. rewrite Z.mul_0_r.
        zrw (zr_rw mem NB 0 16%nat (2 ^ 20) (NB_zero1 mem p HCN HCOM) (NB_wr mem p HCN HCOM)).
      - ddestruct (def_ex_bytes (NB + 16) 8 ltac:(intros a Ha; apply Ddnodes; lia) ltac:(lia) ltac:(lia)) as (bs & LEN & BS).
        dexists (le_bytes_to_word bs), (Z_to_bv 64 1), 0. split; [| lia]. rewrite Z.mul_1_r.
        split; [| change (Z.of_nat _) with 16; apply (zr_wr mem NB (2 ^ 20) (NB_wr mem p HCN HCOM)); lia].
        split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r, le8_le_bytes_to_word by exact LEN.
        apply bytes_at_app. split; [exact BS|]. rewrite LEN. change (Z.of_nat 8) with 8. replace (NB + 16 + 8) with (NB + 24) by lia.
        me_word HF ((#0x1000 * v_dnodes) .+ 24)%tm 4%nat X1. me_word HF ((#0x1000 * v_dnodes) .+ 28)%tm 4%nat X2.
        apply bytes_at_app. split.
        + pose proof (u_addi_Page p HCN v_dnodes 24 ltac:(pv) ltac:(lia)) as UA24.
          pose proof (cword_bytes_at mem _ 4%nat _ X1 ltac:(apply (le_by_eq _ _ _ UA24); lia)) as B1.
          replace (bv_unsigned (ABoot.PropExec.v_addi _ _)) with (PG p v_dnodes + 24) in B1 by (symmetry; exact UA24). exact B1.
        + match goal with |- bytes_at _ _ ?a _ => replace a with (NB + 28) by (change (Z.of_nat (length (le4 (Z_to_bv 64 0)))) with 4; lia) end. unfold NB.
          pose proof (u_addi_Page p HCN v_dnodes 28 ltac:(pv) ltac:(lia)) as UA28.
          pose proof (cword_bytes_at mem _ 4%nat _ X2 ltac:(apply (le_by_eq _ _ _ UA28); lia)) as B2.
          replace (bv_unsigned (ABoot.PropExec.v_addi _ _)) with (PG p v_dnodes + 28) in B2 by (symmetry; exact UA28). exact B2.
      - dexists (Z_to_bv 64 0), (Z_to_bv 64 0), 0. split; [| lia].
        zrw (zr_rw mem NB 32 (Z.to_nat 0xfffe0) (2 ^ 20) (NB_zero2 mem p HCN HCOM) (NB_wr mem p HCN HCOM)). }
    split; [unfold dwf; cbn [length]; change (Z.of_nat 1%nat) with 1; change (1 / 65536) with 0; lia|].
    split; [orw|].
    split.
    { exists (Z_to_bv 64 0x800000). change [C8 (Z_to_bv 64 TF); C8 (Z_to_bv 64 0x800000)] with ([C8 (Z_to_bv 64 TF)] ++ [C8 (Z_to_bv 64 0x800000)]).
      apply rw_cells_app2; [exact HSS | cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; orw]. }
    split.
    { (* [comment removed for export] *)
      split; [| split; [apply Forall_cons; [| apply Forall_nil]; split; [lia | split; [lia | exact (proj2 (PG_range p HCN v_dstore ltac:(pv)))]] | cbn [length]; apply Nat2Z.inj_le; change (Z.of_nat (Init.Nat.of_num_uint _)) with 4096%Z; cbn; lia]].
      intros j Hj. unfold sptr, sblk. cbn [length]. change (Z.of_nat 1%nat) with 1.
      destruct (Z.eq_dec j 0) as [->|NZ].
      - change (Z.to_nat 0) with 0%nat. cbn [nth]. replace (if 0 <? 1 then SS else 0) with SS by reflexivity. rewrite Z.mul_0_r, Z.add_0_r. exists st.
        change [C8 (Z_to_bv 64 SS); C4 st; C4 (Z_to_bv 64 0)] with ([C8 (Z_to_bv 64 SS)] ++ ([C4 st] ++ [C4 (Z_to_bv 64 0)])).
        apply rw_cells_app2; [| apply rw_cells_app2; cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; [exact Hst | orw]].
        me_word HF (ALit 0x1db8d8) 8%nat X.
        split; [| apply (chk_wr_at mem p CT_COMMON HF QLit (A_SS + 16) 8); [vm_compute; reflexivity | zdec | zdec]].
        pose proof (cword_ro_cells mem _ 8%nat _ [C8 (Z_to_bv 64 SS)] X ltac:(unfold SS; cbn [cells_bytes cbytes app]; rewrite app_nil_r, (w64_Page p HCN v_dstore) by pv; reflexivity) ltac:(cbn; tauto) ltac:(rewrite u_zbv; zdec)) as R.
        rewrite u_zbv in R. exact R.
      - replace (j <? 1) with false by (symmetry; apply Z.ltb_ge; lia). exists (Z_to_bv 64 0).
        apply (img_zero_rw 0x1db8e8 BK IMG1); [cbn; tauto | reflexivity | | | |]; znum; unfold A_SS, A_DEP, BSS_LO, BSS_HI in *; lia. }
    split.
    { (* [comment removed for export] *)
      intros j Hj. cbn [length] in Hj. change (Z.of_nat 1%nat) with 1 in Hj. unfold sblk. replace (Z.to_nat j) with 0%nat by lia. cbn [nth].
      split; [lia|]. split; [lia|]. intros a Ha.
      assert (U : bv_unsigned (wa a) = a) by (unfold wa; rewrite u_zbv; apply Z.mod_small; lia).
      pose proof (Ddstore (wa a) ltac:(rewrite U; lia)) as D. rewrite asegs_ASEGS. unfold wview, mrd.
      destruct (mem (wa a)) as [b|]; [split; [discriminate | exists b; reflexivity] | exfalso; exact (D eq_refl)]. }
    split; [destruct HR as [[-> _]|[-> _]]; lia|].
    split; [cbn [length]; change (Z.of_nat 1%nat) with 1; destruct HR as [[-> _]|[-> _]]; reflexivity|].
    (* [comment removed for export] *)
    unfold blocks_apart, dblk, sblk. cbn [length]. change (Z.of_nat 1%nat) with 1.
    split; [intros k1 k2 H1 H2 NE; lia|]. split; [intros j1 j2 H1 H2 NE; lia|].
    intros k j Hk Hj. replace (Z.to_nat k) with 0%nat by lia. replace (Z.to_nat j) with 0%nat by lia. cbn [nth]. exact NBSS.
  Qed.
End Mem3.
