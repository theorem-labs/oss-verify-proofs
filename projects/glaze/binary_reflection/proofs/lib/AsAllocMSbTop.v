(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocMSbM5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMES.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL3 : code_ato segs rb 0x4c204 al3_words.
  Hypothesis HAM2 : code_ato segs rb 0x4baf4 am2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variables (g_lsan gMAG : Z).
  Hypothesis HLSN : code_ato segs rb 0x9bf80 lsn_words.
  Hypothesis GLSN : gload segs rb 0x9bf80 10 g_lsan.
  Hypothesis GMAG : gload segs rb 0x4c238 10 gMAG.
  Hypothesis Gg : (AIMGLO <= g_lsan /\ g_lsan + 8 <= AIMGHI)%Z /\ (AIMGLO <= gMAG /\ gMAG + 8 <= AIMGHI)%Z.
  Let L67138 := AsAllocM5.L67138 segs rb HAL3.
  Let L6713c := AsAllocM5.L6713c segs rb HAL3.
  Let L67140 := AsAllocM5.L67140 segs rb HAL3.
  Let L67144 := AsAllocM5.L67144 segs rb HAL3.
  Let L67000 := AsAllocM5.L67000 segs rb HAL3.
  Let L6714c := AsAllocM5.L6714c segs rb HAL3.
  Let L67150 := AsAllocM5.L67150 segs rb HAL3.
  Let L67154 := AsAllocM5.L67154 segs rb HAL3.
  Let L67158 := AsAllocM5.L67158 segs rb HAL3.
  Let L6715c := AsAllocM5.L6715c segs rb HAL3.
  Let L67160 := AsAllocM5.L67160 segs rb HAL3.
  Let L67164 := AsAllocM5.L67164 segs rb HAL3.
  Let L67168 := AsAllocM5.L67168 segs rb HAL3.
  Let L67174 := AsAllocM5.L67174 segs rb HAL3.
  Let L67178 := AsAllocM5.L67178 segs rb HAL3.
  Let L6717c := AsAllocM5.L6717c segs rb HAL3.
  Let L67180 := AsAllocM5.L67180 segs rb HAL3.
  Let L67184 := AsAllocM5.L67184 segs rb HAL3.
  Let L67188 := AsAllocM5.L67188 segs rb HAL3.
  Let L6718c := AsAllocM5.L6718c segs rb HAL3.
  Let L67190 := AsAllocM5.L67190 segs rb HAL3.
  Let L67194 := AsAllocM5.L67194 segs rb HAL3.
  Let L67198 := AsAllocM5.L67198 segs rb HAL3.
  Let L6719c := AsAllocM5.L6719c segs rb HAL3.
  Let L671a0 := AsAllocM5.L671a0 segs rb HAL3.
  Let L671a4 := AsAllocM5.L671a4 segs rb HAL3.
  Let L671a8 := AsAllocM5.L671a8 segs rb HAL3.
  Let L671ac := AsAllocM5.L671ac segs rb HAL3.
  Let L671b0 := AsAllocM5.L671b0 segs rb HAL3.
  Let L671b4 := AsAllocM5.L671b4 segs rb HAL3.
  Let L671b8 := AsAllocM5.L671b8 segs rb HAL3.
  Let L671bc := AsAllocM5.L671bc segs rb HAL3.
  Let L671c0 := AsAllocM5.L671c0 segs rb HAL3.
  Let L671c4 := AsAllocM5.L671c4 segs rb HAL3.
  Let L671c8 := AsAllocM5.L671c8 segs rb HAL3.
  Let N66a28 := AsAllocM5.N66a28 segs rb HAM2.
  Let N66a2c := AsAllocM5.N66a2c segs rb HAM2.
  Let N66a30 := AsAllocM5.N66a30 segs rb HAM2.
  Let N66a34 := AsAllocM5.N66a34 segs rb HAM2.
  Let N66a38 := AsAllocM5.N66a38 segs rb HAM2.

  Variables (rom : word -> option byte) (sp m tp : word) (n off : Z) (h1 : byte).
  Hypothesis Hn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis Gm : (U m mod 4096 = 0)%Z /\ (8192 <= U m)%Z /\ (U m + sec_needed n + 4096 <= 2 ^ 47)%Z.   (* [comment removed for export] *)
  Hypothesis Gimg : (U m + sec_needed n <= AIMGLO \/ AIMGHI <= U m)%Z.
  Hypothesis Gsp : (2 ^ 32 <= U sp)%Z /\ (U sp + 144 <= 2 ^ 47)%Z.
  Hypothesis Goff : (0 <= off)%Z /\ (U tp + off + 4 <= 2 ^ 64)%Z.

  Lemma RETes : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using Gm n m RB. intros d Hd Hdr. pose proof RB as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.
  Lemma rz_facts_s : (16 <= rz n <= 2048)%Z /\ (rz n mod 16 = 0)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z.
  Proof using Gm Hn m rb.
    assert (E : rz n = 2048%Z) by (apply rz_sec; lia). split; [lia|]. split; [rewrite E; reflexivity|].
    assert (E7 : rz_log n = 7%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end). repeat (match goal with |- context [Z.leb n ?k] => destruct (Z.leb_spec n k) as [?|?]; [exfalso; lia|] end). reflexivity. }
    rewrite E, E7. split; intros X; discriminate X.
  Qed.

  (* [comment removed for export] *)
  Theorem amE3s : forall (M : word -> option byte) r0,
    getr r0 2 = sp -> getr r0 4 = tp -> getr r0 9 = Z_to_bv 64 n -> getr r0 18 = m -> getr r0 20 = at_ m (rz n) -> getr r0 21 = at_ m (rz n - 16) ->
    rdn segs M (Z_to_bv 64 g_lsan) 8 = Some (LE8 (Z_to_bv 64 off)) -> rdn segs M (at_ tp off) 4 = Some (LE4 0) ->
    rdn segs M (at_ m (rz n - 15)) 1 = Some [h1] ->
    store_ok segs M (at_ m (rz n - 16)) 16 = true -> store_ok segs M m 16 = true ->
    (rz_log n <> 0%Z -> rdn segs M (Z_to_bv 64 gMAG) 8 = Some (LE8 (Z_to_bv 64 MAGIC))) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c204) M rom) (mkst r (at_ rb 0x7cb90) (amE3_mem m n h1 M) rom)
      /\ getr r 1 = at_ rb 0x4c258 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x [1; 10; 11; 13]) r0 r.
  Proof using Goff Gsp Gimg Gm Hn L67188 L67184 L67180 L6717c L67178 L67174 L67168 L67164 L67160 L6715c L67158 L67154 L67150 L6714c L67000 L67144 L67140 L6713c L67138 Gg GMAG GLSN HLSN RB HAL3.
    intros M r0 R2 R4 R9 R18 R20 R21 Rgl Rtls Rh1 SOKh SOKm Rmag.
    pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htp. destruct Gm as (Gm1 & Gm2 & Gm3). destruct Goff as [Go1 Go2].
    destruct rz_facts_s as (Hrz2 & Hrz16 & Hrz0). pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb. pose proof (u8_range h1) as Hh1.
    (* [comment removed for export] *)
    destruct (lsan_run segs rb g_lsan HLSN GLSN M rom (regupd r0 1 (at_ rb 0x4c208)) (at_ rb 0x4c208) tp off Rgl Go1 Go2 Rtls
                (RETes 0x4c208 eq_refl ltac:(lia))) as (r1 & RUN1 & A10 & AG1).
    { apply getr_same. intros E; discriminate E. }
    { rewrite getr_other by (intros E; discriminate E). exact R4. }
    Ltac r1f AG1 r H := rewrite (AG1 r) by notin_list; gres; exact H.
    assert (B9 : getr r1 9 = Z_to_bv 64 n) by r1f AG1 (9:reg) R9.
    assert (B18 : getr r1 18 = m) by r1f AG1 (18:reg) R18.
    assert (B20 : getr r1 20 = at_ m (rz n)) by r1f AG1 (20:reg) R20.
    assert (B21 : getr r1 21 = at_ m (rz n - 16)) by r1f AG1 (21:reg) R21.
    set (M1 := wbytes M (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1))))]).
    set (M2 := wbytes M1 (at_ m (rz n - 16)) [Z_to_bv 8 2]).
    assert (SOK1 : store_ok segs M1 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOKh]).
    assert (SOKm2 : store_ok segs M2 m 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M2, M1 in G in change_no_check G' end); do 2 (eapply store_ok_mono; [apply wbytes_grows|]); exact SOKm).
    Ltac sok16 SOK := eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r0 (at_ rb 0x4c204) M rom) (mkst r2 (at_ rb 0x4c22c) M2 rom)
               /\ getr r2 11 = Z_to_bv 64 2 /\ (forall i : reg, In i [2; 4; 9; 18; 20; 21] -> getr r2 i = getr r1 i)
               /\ regs_agree (fun x => In x [1; 10; 11]) r0 r2).
    { wd_eexists. split.
      - an L67138 D_4c1fc.                                 (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        chain_step; [reflexivity
          | eapply step_lbu with (b := h1); [exact L6713c | reflexivity | exact D_4c200
            | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rh1; f_equal; f_equal; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67140 D_4c204. an L67144 D_4c208.             (* [comment removed for export] *)
        an L67000 D_4c20c. an L6714c D_4c210.             (* [comment removed for export] *)
        change (v_or (v_andi (Z_to_bv 64 (U h1)) 243) (Z_to_bv 64 0)) with (hb2w (Z_to_bv 64 (U h1))).
        an L67150 D_4c214.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))));
            [exact L67154 | reflexivity | exact D_4c218 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes M _ _) with M1.
        afence L67158 D_4c21c.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := at_ m (rz n - 16)) (b := Z_to_bv 8 2);
            [exact L6715c | reflexivity | exact D_4c220 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | reflexivity | sok16 SOK1]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes M1 _ _) with M2.
        wd_refl.
      - post; [|ra_chain]. intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi. }
    destruct W2 as (r2 & RUN2 & C11 & CK & AG2).
    assert (C18 : getr r2 18 = m) by (rewrite (CK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B18).
    assert (C21 : getr r2 21 = at_ m (rz n - 16)) by (rewrite (CK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B21).
    assert (C20 : getr r2 20 = at_ m (rz n)) by (rewrite (CK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B20).
    assert (C9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (CK 9) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact B9).
    (* [comment removed for export] *)
    destruct (Z.eqb_spec (rz_log n) 0) as [E0|E0].
    - assert (E16 : rz n = 16%Z) by (apply Hrz0; exact E0).
      wd_eexists. split.
      + eapply msteps_trans; [exact RUN2|].
        ab_tk L67160 D_4c224 ltac:(rewrite E16; condz).  (* [comment removed for export] *)
        an L67180 D_4c244. an L67184 D_4c248.             (* [comment removed for export] *)
        an L67188 D_4c24c.                                 (* [comment removed for export] *)
        replace (amE3_mem m n h1 M) with M2 by ((lazymatch goal with |- ?G => let G' := eval unfold amE3_mem in G in change_no_check G' end); rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
        wd_refl.
      + post. all: try (rewrite ?at_add_0_r; reflexivity). all: ra_chain.
    - assert (E16 : (32 <= rz n)%Z).
      { unfold rz in *. pose proof (rz_log_range n). assert (1 <= rz_log n)%Z by lia.
        replace 32%Z with (16 * 2 ^ 1)%Z by reflexivity. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
      specialize (Rmag E0).
      assert (Rmag2 : rdn segs M2 (Z_to_bv 64 gMAG) 8 = Some (LE8 (Z_to_bv 64 MAGIC))).
      { rewrite <- Rmag. (lazymatch goal with |- ?G => let G' := eval unfold M2, M1 in G in change_no_check G' end). apply rdn_ext; [wd_ulia_c | intros x Hx].
        rewrite !wbytes_outside; [reflexivity | ..]; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?at_u by lia; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      wd_eexists. split.
      + eapply msteps_trans; [exact RUN2|].
        ab_ft L67160 D_4c224 ltac:(condz).                (* [comment removed for export] *)
        an L67164 D_4c228.                                 (* [comment removed for export] *)
        ab_ft L67168 D_4c22c ltac:(condz).                (* [comment removed for export] *)
        eapply msteps_trans; [apply (GMAG _ M2 rom (Z_to_bv 64 MAGIC) Rmag2)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ m 8);
            [exact L67174 | reflexivity | exact D_4c238 | gres; rwH; imm_norm; rewrite ?at_addi; fold_at_vars; reflexivity | gres; rwH; reflexivity
            | do 2 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        afence L67178 D_4c23c.                             (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := m);
            [exact L6717c | reflexivity | exact D_4c240 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity
            | do 3 (eapply store_ok_mono; [apply wbytes_grows|]); eapply (store_ok_sub segs _ m _ 16); [lia | exact SOKm | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        an L67180 D_4c244. an L67184 D_4c248.             (* [comment removed for export] *)
        an L67188 D_4c24c.                                 (* [comment removed for export] *)
        replace (amE3_mem m n h1 M) with (wbytes (wbytes M2 (at_ m 8) (LE8 (at_ m (rz n - 16)))) m (LE8 (Z_to_bv 64 MAGIC)))
          by ((lazymatch goal with |- ?G => let G' := eval unfold amE3_mem in G in change_no_check G' end); rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        wd_refl.
      + post. all: try (rewrite ?at_add_0_r; reflexivity). all: ra_chain.
  Qed.
  (* [comment removed for export] *)
  Theorem amE4s : forall (M : word -> option byte) r0 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' : word),
    getr r0 2 = sp -> getr r0 20 = at_ m (rz n) ->
    (forall (k : Z) (v : word), In (k, v) (amE4_slots rb s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0') -> rdn segs M (at_ sp k) 8 = Some (LE8 v)) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c258) M rom) (mkst r (at_ rb 0x6e600) M rom)
      /\ getr r 10 = at_ m (rz n) /\ getr r 2 = at_ sp 144 /\ getr r 1 = at_ rb 0x6e600
      /\ getr r 8 = s0' /\ getr r 9 = s1 /\ getr r 18 = s2 /\ getr r 19 = s3 /\ getr r 20 = s4 /\ getr r 21 = s5
      /\ getr r 22 = s6 /\ getr r 23 = s7 /\ getr r 24 = s8 /\ getr r 25 = s9 /\ getr r 26 = s10 /\ getr r 27 = s11
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) r0 r.
  Proof using Goff Gsp Gimg Gm Hn off tp N66a38 N66a34 N66a30 N66a2c N66a28 L671c8 L671c4 L671c0 L671bc L671b8 L671b4 L671b0 L671ac L671a8 L671a4 L671a0 L6719c L67198 L67194 L67190 L6718c Gg gMAG g_lsan RB HAM2 HAL3.
    intros M r0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0' R2 R20 SL.
    pose proof (u64_range sp) as Hspr. destruct Gsp as [Gs1 Gs2]. pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). destruct rz_facts_s as (Hrz2 & Hrz16 & Hrz0). pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    unfold amE4_slots in SL.
    Ltac fld F D vv SL :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; fold_at_vars; rewrite ?at_addi; zlit_at; apply SL; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    pose proof (RETes 0x4baf4 eq_refl ltac:(lia)) as RT1. pose proof (RETes 0x6e600 eq_refl ltac:(lia)) as RT2.
    wd_eexists. split.
    - an L6718c D_4c250.                                   (* [comment removed for export] *)
      fld L67190 D_4c254 (at_ rb 0x4baf4) SL.              (* [comment removed for export] *)
      fld L67194 D_4c258 s0 SL. fld L67198 D_4c25c s1 SL. fld L6719c D_4c260 s2 SL. fld L671a0 D_4c264 s3 SL.
      fld L671a4 D_4c268 s4 SL. fld L671a8 D_4c26c s5 SL. fld L671ac D_4c270 s6 SL. fld L671b0 D_4c274 s7 SL.
      fld L671b4 D_4c278 s8 SL. fld L671b8 D_4c27c s9 SL. fld L671bc D_4c280 s10 SL. fld L671c0 D_4c284 s11 SL.
      an L671c4 D_4c288.                                   (* [comment removed for export] *)
      aret L671c8 D_4c28c (at_ rb 0x4baf4).                (* [comment removed for export] *)
      ab_ft N66a28 D_4baec ltac:(condz).                  (* [comment removed for export] *)
      fld N66a2c D_4baf0 (at_ rb 0x6e600) SL.              (* [comment removed for export] *)
      fld N66a30 D_4baf4 s0' SL.                           (* [comment removed for export] *)
      an N66a34 D_4baf8.                                   (* [comment removed for export] *)
      aret N66a38 D_4bafc (at_ rb 0x6e600).                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AMES.
End FPGen1.
End AsAllocMSbM5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSecPh.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section PH.
  Variables (M : word -> option byte) (FL MIDEND : Z).
  Hypothesis C_gsb : rdn ASEGS M (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sb : rdn ASEGS M (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn ASEGS M (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS M (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn ASEGS M (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn ASEGS M (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS M (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).

  Variables (addr size : Z) (ra fsp : word).
  Hypothesis Ha8 : addr mod 8 = 0.
  Hypothesis Hs8 : size mod 8 = 0.
  Hypothesis Hrng : (0x10007fff8000 <= addr /\ 8 <= size /\ addr + size <= 0x800000000000) \/ (0 <= addr /\ 8 <= size /\ addr + size <= 0x7fff7000).
  Hypothesis Hfsp : 2 ^ 32 + 64 <= U fsp /\ U fsp + 16 <= 2 ^ 47.
  Hypothesis Hstk : store_ok ASEGS M (at_ fsp (-64)) 64 = true.
  Hypothesis Hshw : store_ok ASEGS M (Z_to_bv 64 (0x7fff8000 + addr / 8)) (Z.to_nat (size / 8)) = true.
  Hypothesis Hret : ret_ok ra.

  Lemma ph_lits : 0 <= addr /\ addr + size <= 2 ^ 47 /\ 0 <= size.
  Proof using Hrng. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; lia. Qed.

  Ltac ph_common :=
    [> exact C_gsb | exact C_sb | exact C_gmb | exact C_mb | exact C_gme | exact C_me | exact C_ghe | exact C_he | exact C_grm
     | replace (word_to_le_bytes 8 (1005284 : word)) with (LE8 (Z_to_bv 64 0xf56e4)) by reflexivity; exact C_rm
     | vm_compute; discriminate
     | apply ret_ok_even; reflexivity
     | ..].

  Lemma mk_poisonH_fa : forall thr0,
    rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 1] ->
    poisonH ASEGS asan_poison_tab M (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) thr0.
  Proof using Hret Hshw Hstk Hfsp Hrng Hs8 Ha8 C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sb C_gsb.
    intros thr0 C_cpm. pose proof ph_lits as (L1 & L2 & L3). destruct Hfsp as [F1 F2]. pose proof (u64_range fsp) as Hf.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
    all: ph_common.
    - intros _. split; [exact C_cpm | vm_compute; discriminate].
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact Ha8.
    - rewrite u_Z2bv by lia. exact Hs8.
    - rewrite !u_Z2bv by lia. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; [left; lia | right; lia].
    - lia.
    - exact Hstk.
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia. replace (addr / 8 + 2147450880) with (0x7fff8000 + addr / 8) by lia. exact Hshw.
    - exact Hret.
  Qed.

  Lemma mk_poisonH_0 : forall CFL,
    rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CFL)) ->
    rdn ASEGS M (Z_to_bv 64 (CFL + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)) -> CFL = 0x1990a8 ->
    poisonH ASEGS asan_poison_tab M (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 0) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615.
  Proof using Hret Hshw Hstk Hfsp Hrng Hs8 Ha8 C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sb C_gsb.
    intros CFL C_gcf C_thr ECF. subst CFL. pose proof ph_lits as (L1 & L2 & L3). destruct Hfsp as [F1 F2]. pose proof (u64_range fsp) as Hf.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
    all: ph_common.
    - intros NZ. exfalso. apply NZ. reflexivity.
    - intros _. split; [exact C_gcf|]. split; [replace (Z_to_bv 64 (1675432 + 120)) with (Z_to_bv 64 (0x1990a8 + 120) : word) by (apply bv_eq; reflexivity); exact C_thr|].
      (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). rewrite u_Z2bv by lia. split; [apply Z.div_lt_upper_bound; lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact Ha8.
    - rewrite u_Z2bv by lia. exact Hs8.
    - rewrite !u_Z2bv by lia. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; [left; lia | right; lia].
    - lia.
    - exact Hstk.
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia. replace (addr / 8 + 2147450880) with (0x7fff8000 + addr / 8) by lia. exact Hshw.
    - exact Hret.
  Qed.
End PH.
End FPGen.
End AsAllocMSecPh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSbRun1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s AsAllocMSecPh OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma sb_shadow_arith2 : forall um n, um mod 4096 = 0 -> 0 <= um -> 64513 <= n ->
  forall k n8 nm re r8 asz a8, k = um / 8 -> n8 = n / 8 -> nm = n mod 8 -> re = sbre um n -> r8 = re / 8 -> asz = sbasz n -> a8 = asz / 8 ->
  (um = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
   /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
  /\ hideW (nm = 0 -> r8 = k + 256 + n8) /\ hideW (nm <> 0 -> r8 = k + 256 + n8 + 1)
  /\ ((um + asz) / 8 = k + a8 /\ (um + asz - re) / 8 = k + a8 - r8 /\ (um + asz - re) mod 8 = 0 /\ (um + 2048) / 8 = k + 256
      /\ (um + 2048) mod 8 = 0 /\ (um + 2048 + (n - nm)) / 8 = k + 256 + n8 /\ (n - nm) / 8 = n8 /\ (n - nm) mod 8 = 0 /\ um mod 8 = 0
      /\ re mod 8 = 0 /\ 2048 / 8 = 256).
Proof.
  intros um n Hum H0 Hn k n8 nm re r8 asz a8 -> -> -> -> -> -> ->. (lazymatch goal with |- ?G => let G' := eval unfold hideW, sbre, sbasz in G in change_no_check G' end). rewrite (rz_sec n) by lia.
  pose proof (sec_needed_bnd n ltac:(lia)) as Hs. set (sn := sec_needed n) in *. clearbody sn.
  Z.div_mod_to_equations; repeat split; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition sb_foot1 (s um n z : Z) : Prop :=
  (um + 2040 <= z < um + 2048) \/ (s - 2336 <= z < s - 2272) \/ (SB + um / 8 <= z < SB + (um + sbasz n) / 8).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]) end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr (regupd _ ?i _) ?i = _ => rewrite getr_same by (intros E; discriminate E) end
                          | match goal with |- getr (regupd _ ?j _) ?i = _ => rewrite getr_other by (intros E; discriminate E) end ]).

(* [comment removed for export] *)
Ltac slia0 B := clear - B; lia.
Ltac slia2 B X := clear - B X; lia.

Section RUNS1.
  Variables (M rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S m : word) (n id sbeg FL MIDEND : Z).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H8 : getr r0 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 id.
  Hypothesis H18 : getr r0 18 = m.
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis H21 : getr r0 21 = at_ m (rz n - 16).
  Hypothesis H22 : getr r0 22 = Z_to_bv 64 0x103f18.
  Hypothesis H24 : getr r0 24 = Z_to_bv 64 0.
  Hypothesis H25 : getr r0 25 = at_ m (rz n + n).
  (* [comment removed for export] *)
  Hypothesis GS : 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hid : 0 <= id < 2 ^ 32.
  Hypothesis Gm : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sbasz n <= U S - 3584 /\ U m + sbasz n + 4096 <= 2 ^ 47.
  Hypothesis Grng : hideW (U m + sbasz n <= 0x7fff7000 \/ 0x10007fff8000 <= U m - 4096).
  Hypothesis Gimg : hideW (U m + sbasz n <= AIMGLO \/ AIMGHI <= U m - 4096).
  Hypothesis Gsb : 0 <= sbeg /\ sbeg + 2 ^ 37 < 2 ^ 64.
  Hypothesis Dsb : U m < sbeg \/ sbeg + 2 ^ 37 <= U m.
  Hypothesis GFL : AIMGLO <= FL /\ FL + 4096 < AIMGHI.
  Hypothesis GME : 0 <= MIDEND < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_gcf : rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_thr64 : rdn ASEGS M (Z_to_bv 64 (0x1990a8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).
  Hypothesis C_gsb : rdn ASEGS M (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sb : rdn ASEGS M (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 SB)).
  Hypothesis C_cpm : rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gmb : rdn ASEGS M (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS M (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn ASEGS M (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_gfl : rdn ASEGS M (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_pp : rdn ASEGS M (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_grm : rdn ASEGS M (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS M (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  (* [comment removed for export] *)
  Hypothesis C_sbeg : rdn ASEGS M (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 sbeg)).
  Hypothesis C_pg : rdn ASEGS M (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_sz : rdn ASEGS M (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))).
  (* [comment removed for export] *)
  Hypothesis C_hdr : store_ok ASEGS M (at_ m (rz n - 16)) 16 = true.
  Hypothesis C_shw : store_ok ASEGS M (Z_to_bv 64 (SB + U m / 8)) (Z.to_nat (sbasz n / 8)) = true.

  Theorem run_sB1 :
    exists (r5 : bvmap 5 word) (M5 : word -> option byte),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x4bed0) M rom) (mkst r5 (Z_to_bv 64 0x4c070) M5 rom)
      /\ (forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r5 i = getr r0 i)
      /\ (forall x : word, ~ sb_foot1 (U S) (U m) n (U x) -> M5 x = M x)
      /\ mem_grows M M5
      /\ rdn ASEGS M5 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id)))
      /\ (forall x : word, SB + U m / 8 <= U x < SB + U m / 8 + 256 -> M5 x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + sbre (U m) n / 8 <= U x < SB + (U m + sbasz n) / 8 -> M5 x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + (U m + 2048) / 8 <= U x < SB + (U m + 2048) / 8 + n / 8 -> M5 x = Some (Z_to_bv 8 0))
      /\ (n mod 8 <> 0 -> M5 (Z_to_bv 64 (SB + (U m + 2048 + (n - n mod 8)) / 8)) = Some (Z_to_bv 8 (n mod 8))).
  Proof using C_shw C_hdr C_sz C_pg C_sbeg C_rm C_grm C_pp C_gfl C_he C_ghe C_me C_gme C_mb C_gmb C_cpm C_sb C_gsb C_thr64 C_gcf Hstk GME GFL Dsb Gsb Gimg Grng Gm Hid Gn GS H25 H24 H22 H21 H20 H18 H10 H9 H8 H2 MIDEND FL sbeg.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr.
    destruct GS as (GS1 & GS2). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    set (k := U m / 8) in *. set (n8 := n / 8) in *. set (nm := n mod 8) in *.
    set (re := sbre (U m) n) in *. set (asz := sbasz n) in *. set (r8 := re / 8) in *. set (a8 := asz / 8) in *.
    destruct (sb_shadow_arith2 (U m) n Gm1 ltac:(lia) ltac:(lia) k n8 nm re r8 asz a8 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (LIN & HZ & HNZ & IDS).
    destruct LIN as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    destruct IDS as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
    rewrite I1, I4, I6.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    assert (Gm' : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sec_needed n + 4096 <= 2 ^ 47) by (clear - Gm1 Gm2 Gm4 L10; lia).
    assert (Usp : U sp2 = U S - 2272) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (BASE : (U m = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
                    /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
                   /\ 64513 <= n <= 2 ^ 34 /\ 8192 <= U m /\ U m + asz <= U S - 3584 /\ U m + asz + 4096 <= 2 ^ 47
                   /\ 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U sp2 = U S - 2272 /\ 0 <= U S < 2 ^ 64 /\ 0 <= U m < 2 ^ 64 /\ rz n = 2048).
    { repeat split; first [assumption | apply L3 | apply L6 | apply L7 | apply Gn | apply HSr | apply Hmr]. }
    assert (RETA : forall d, d mod 2 = 0 -> 0 <= d < 2 ^ 24 -> ret_ok (at_ ARB d)).
    { clear. intros d Hd Hdr. pose proof ARB_ok as [E1 E2]. pose proof (u64_range ARB). apply ret_ok_at; [exact E1 | exact Hd | lia]. }
    (* [comment removed for export] *)
    assert (XF : forall (Mx : word -> option byte), (forall x : word, AIMGLO <= U x < AIMGHI -> Mx x = M x) ->
              forall (a : Z) (len : nat) bs, AIMGLO <= a -> a + Z.of_nat len <= AIMGHI ->
              rdn ASEGS M (Z_to_bv 64 a) len = Some bs -> rdn ASEGS Mx (Z_to_bv 64 a) len = Some bs).
    { clear. intros Mx IM a len bs Ha1 Ha2 Hr. eapply (rd_same ASEGS); [| | exact Hr]; [intros x Hx; apply IM; rewrite u_Z2bv in Hx by lia; lia | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]]. }
    assert (SOK64 : forall Mx : word -> option byte, mem_grows M Mx -> store_ok ASEGS Mx (at_ sp2 (-64)) 64 = true).
    { intros Mx GX. eapply store_ok_mono; [exact GX|]. rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end).
      eapply (store_ok_sub ASEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; slia0 BASE | exact Hstk | rewrite !at_u by slia0 BASE; slia0 BASE | rewrite !at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE]. }
    assert (SOKsh : forall (Mx : word -> option byte) (o len : Z), mem_grows M Mx -> 0 <= o -> 0 <= len -> o + len <= a8 ->
              store_ok ASEGS Mx (Z_to_bv 64 (0x7fff8000 + (k + o))) (Z.to_nat len) = true).
    { intros Mx o len GX Ho Hl Hol. eapply store_ok_mono; [exact GX|]. unfold SB in C_shw.
      assert (Ha8 : 0 <= a8 /\ 0 <= k /\ 2147450880 + k + a8 < 2 ^ 63) by slia0 BASE.
      eapply (store_ok_sub ASEGS M (Z_to_bv 64 (2147450880 + k)) _ (Z.to_nat a8)); [rewrite u_Z2bv by (clear - Ha8; lia); rewrite Z2Nat.id by (clear - Ha8; lia); clear - Ha8; lia | exact C_shw
        | rewrite !u_Z2bv by (clear - Ha8 Ho Hl Hol; lia); clear - Ha8 Ho Hl Hol; lia | rewrite !u_Z2bv by (clear - Ha8 Ho Hl Hol; lia); rewrite !Z2Nat.id by (clear - Ha8 Ho Hl Hol; lia); clear - Ha8 Ho Hl Hol; lia]. }
    Ltac ximg XF IM C := (eapply (XF _ IM); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact C]).
    Ltac mkph L XF IM C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm :=
      apply L; [ ximg XF IM C_gsb | unfold SB in C_sb; ximg XF IM C_sb | ximg XF IM C_gmb | ximg XF IM C_mb | ximg XF IM C_gme | ximg XF IM C_me
       | ximg XF IM C_ghe | ximg XF IM C_he | ximg XF IM C_grm | ximg XF IM C_rm | .. ].
    (* [comment removed for export] *)
    destruct (amD1s ASEGS ARB asan_HAL2 ARB_ok rom m n 0 Gn ltac:(lia) Gm' M r0 id sbeg Hid H10 H8 H9 H18 H20 H21 H22 H24 H25 C_hdr Gsb Dsb
                ltac:(unfold hideW in Gimg; slia2 BASE Gimg) C_sbeg C_pg C_sz)
      as (r1 & RUN1 & B1 & B10 & B11 & B12 & B8 & B22 & AG1).
    clear Dsb.
    set (M1 := amD_mem m n 0 M id) in *.
    assert (O1 : forall x : word, (U x < U m + 2040 \/ U m + 2048 <= U x) -> M1 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite length_N_to_le_bytes, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia2 BASE Hx]. }
    assert (G1 : mem_grows M M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end); apply wbytes_grows).
    assert (R1 : rdn ASEGS M1 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end). apply rdn_wbytes_hitw. rewrite at_u by slia0 BASE. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). slia0 BASE. }
    clearbody M1.
    assert (IMG1 : forall x : word, AIMGLO <= U x < AIMGHI -> M1 x = M x).
    { intros x Hx. apply O1. unfold hideW in Gimg. clear - Hx Gimg L7 Gn. lia. }
    (* [comment removed for export] *)
    assert (PH1 : poisonH ASEGS asan_poison_tab M1 (Z_to_bv 64 (U m)) (Z_to_bv 64 2048) (Z_to_bv 64 250) (at_ ARB 0x4bfa8) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { mkph (mk_poisonH_fa M1 MIDEND) XF IMG1 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I9.
      - reflexivity.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact G1.
      - rewrite I11. fold k. replace (2147450880 + k) with (2147450880 + (k + 0)) by lia. apply SOKsh; [exact G1 | lia | lia | slia0 BASE].
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG1 C_cpm. }
    rewrite Z_to_bv_bv_unsigned in PH1.
    destruct (asan_poison_shadow M1 rom m (Z_to_bv 64 2048) (Z_to_bv 64 250) (at_ ARB 0x4bfa8) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0 r1
                PH1 B1 ltac:(rchB) B10 B11 B12) as (r2 & RUN2 & AG2).
    clear PH1.
    match type of RUN2 with msteps _ _ (mkst _ _ ?MM _) => set (M2 := MM) in * end.
    destruct (psm_facts M1 sp2 (at_ ARB 0x4bfa8) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) (U m) 2048 250
                ltac:(slia0 BASE) ltac:(lia) ltac:(lia) ltac:(slia0 BASE)) as (O2 & N2 & G2).
    cbv zeta in O2, N2, G2. rewrite Z_to_bv_bv_unsigned in O2, N2, G2. change (psm M1 _ _ _ _ _ _ _ _ _ _ _) with M2 in O2, N2, G2.
    rewrite I11 in O2, N2. fold k in O2, N2. rewrite Usp in O2.
    clearbody M2.
    assert (GR2 : mem_grows M M2) by (eapply mem_grows_trans; [exact G1 | exact G2]).
    assert (FRo : forall x : word, AIMGLO <= U x < AIMGHI -> (U x < U S - 2272 - 56 \/ U S - 2272 <= U x) /\ (U x < 2147450880 + k \/ 2147450880 + k + a8 <= U x)).
    { intros x Hx. slia2 BASE Hx. }
    assert (IMG2 : forall x : word, AIMGLO <= U x < AIMGHI -> M2 x = M x).
    { intros x Hx. rewrite O2; [apply IMG1; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; exact X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    destruct (amD1b ASEGS ARB asan_HAL2 rom m n Gn Gm' M2 r2 ltac:(rchB) ltac:(rchB) ltac:(rchB)) as (r3 & RUN3 & C1 & C10 & C11 & C12 & AG3).
    fold re asz in C10, C11.
    assert (PH2 : poisonH ASEGS asan_poison_tab M2 (Z_to_bv 64 re) (Z_to_bv 64 (U m + asz - re)) (Z_to_bv 64 250) (at_ ARB 0x4bfbc) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { mkph (mk_poisonH_fa M2 MIDEND) XF IMG2 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I10.
      - exact I3.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact GR2.
      - rewrite I2. fold r8. replace (2147450880 + r8) with (2147450880 + (k + (r8 - k))) by lia. apply SOKsh; [exact GR2 | | |]; slia0 BASE.
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG2 C_cpm. }
    destruct (asan_poison_shadow M2 rom (Z_to_bv 64 re) (Z_to_bv 64 (U m + asz - re)) (Z_to_bv 64 250) (at_ ARB 0x4bfbc) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0 r3
                PH2 C1 ltac:(rchB) C10 C11 C12) as (r4 & RUN4 & AG4).
    clear PH2.
    match type of RUN4 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in * end.
    destruct (psm_facts M2 sp2 (at_ ARB 0x4bfbc) (getr r3 8) (getr r3 9) (getr r3 18) (getr r3 19) (getr r3 20) (getr r3 21) re (U m + asz - re) 250
                ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE)) as (O3 & N3 & G3).
    cbv zeta in O3, N3, G3. change (psm M2 _ _ _ _ _ _ _ _ _ _ _) with M3 in O3, N3, G3.
    rewrite I2 in O3, N3. fold r8 in O3, N3. rewrite Usp in O3.
    clearbody M3.
    assert (GR3 : mem_grows M M3) by (eapply mem_grows_trans; [exact GR2 | exact G3]).
    assert (IMG3 : forall x : word, AIMGLO <= U x < AIMGHI -> M3 x = M x).
    { intros x Hx. rewrite O3; [apply IMG2; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; slia2 BASE X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    destruct (amD1c ASEGS ARB asan_HAL2 rom m n Gn M3 r4 ltac:(rchB)) as (r5 & RUN5 & D22 & AG5).
    destruct (amD2s ASEGS ARB asan_HAL2 rom m n Gn Gm' M3 r5 ltac:(lia) D22 ltac:(rchB)) as (r6 & RUN6 & E1 & E10 & E11 & E12 & AG6).
    fold nm in D22, E11.
    assert (Ep : at_ m (rz n) = Z_to_bv 64 (U m + 2048)) by (rewrite Erz; reflexivity).
    assert (PH3 : poisonH ASEGS asan_poison_tab M3 (Z_to_bv 64 (U m + 2048)) (Z_to_bv 64 (n - nm)) (Z_to_bv 64 0) (at_ ARB 0x4bfdc) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615).
    { mkph (fun a b c d e f g h i j ad sz ra fsp h1 h2 h3 h4 h5 h6 h7 => mk_poisonH_0 M3 MIDEND a b c d e f g h i j ad sz ra fsp h1 h2 h3 h4 h5 h6 h7 0x1990a8) XF IMG3 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I5.
      - exact I8.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact GR3.
      - rewrite I4, I7. apply SOKsh; [exact GR3 | | |]; slia0 BASE.
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG3 C_gcf.
      - ximg XF IMG3 C_thr64.
      - reflexivity. }
    rewrite <- Ep in PH3.
    destruct (asan_poison_shadow M3 rom (at_ m (rz n)) (Z_to_bv 64 (n - nm)) (Z_to_bv 64 0) (at_ ARB 0x4bfdc) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615 r6
                PH3 E1 ltac:(rchB) E10 E11 E12) as (r7 & RUN7 & AG7).
    clear PH3.
    match type of RUN7 with msteps _ _ (mkst _ _ ?MM _) => set (M4 := MM) in * end.
    destruct (psm_facts M3 sp2 (at_ ARB 0x4bfdc) (getr r6 8) (getr r6 9) (getr r6 18) (getr r6 19) (getr r6 20) (getr r6 21) (U m + 2048) (n - nm) 0
                ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE)) as (O4 & N4 & G4).
    cbv zeta in O4, N4, G4. rewrite <- Ep in O4, N4, G4. change (psm M3 _ _ _ _ _ _ _ _ _ _ _) with M4 in O4, N4, G4.
    rewrite I4, I7 in O4, N4. rewrite Usp in O4.
    clearbody M4.
    assert (GR4 : mem_grows M M4) by (eapply mem_grows_trans; [exact GR3 | exact G4]).
    assert (IMG4 : forall x : word, AIMGLO <= U x < AIMGHI -> M4 x = M x).
    { intros x Hx. rewrite O4; [apply IMG3; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; slia2 BASE X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    assert (K7 : forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r7 i = getr r0 i).
    { intros i Hi. cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [rewrite (AG7 _) by notinB; rewrite (AG6 _) by notinB; rewrite (AG5 _) by notinB; rewrite (AG4 _) by notinB;
                                       rewrite (AG3 _) by notinB; rewrite (AG2 _) by notinB; rewrite (AG1 _) by notinB; reflexivity|]). destruct Hi. }
    assert (F22 : getr r7 22 = Z_to_bv 64 (n - nm)) by (rewrite (AG7 _) by notinB; rewrite (AG6 _) by notinB; exact D22).
    assert (W8 : exists (r8' : bvmap 5 word) (M5 : word -> option byte),
               msteps ASEGS (mkst r7 (at_ ARB 0x4bfdc) M4 rom) (mkst r8' (at_ ARB 0x4c070) M5 rom)
               /\ (forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r8' i = getr r7 i)
               /\ (forall x : word, (nm = 0 \/ U x <> 2147450880 + (k + 256 + n8)) -> M5 x = M4 x)
               /\ mem_grows M4 M5
               /\ (nm <> 0 -> M5 (Z_to_bv 64 (2147450880 + (k + 256 + n8))) = Some (Z_to_bv 8 nm) /\ r8 = k + 256 + n8 + 1)).
    { destruct (Z.eq_dec nm 0) as [Em|Em].
      - exists r7, M4. split; [| split; [intros; reflexivity | split; [intros; reflexivity | split; [apply mem_grows_refl | intros X; exfalso; exact (X Em)]]]].
        apply (amE1zs ASEGS ARB asan_HAL2 rom m n Gn M4 r7 Em); [rewrite (K7 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H9 | exact F22].
      - destruct (amE1s ASEGS ARB asan_HAL2 ARB_ok rom m n Gn Gm' 0xff270 (Z_to_bv 64 0x107578) SB
                    ltac:((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); split; [lia | fold k; slia0 BASE])
                    0x106ddc 0xff278 0xff280 0xff288 0xff268 (Z_to_bv 64 0x108268) (Z_to_bv 64 0x108270) (Z_to_bv 64 0x108260) (Z_to_bv 64 FL) (Z_to_bv 64 MIDEND)
                    asan_CPM asan_GCPM asan_GLSB2 asan_GLMB asan_GLME asan_GLHE asan_GLFL
                    ltac:(split; [repeat constructor; lia | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]]) M4 r7
                    ltac:(unfold hideW in Grng; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); slia2 BASE Grng) Em
                    ltac:(rewrite (K7 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H9) F22 ltac:(rewrite (K7 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H20))
          as (r8' & RUN8 & AG8).
        { ximg XF IMG4 C_cpm. } { ximg XF IMG4 C_gsb. } { ximg XF IMG4 C_sb. } { ximg XF IMG4 C_gmb. } { ximg XF IMG4 C_mb. }
        { ximg XF IMG4 C_gme. } { ximg XF IMG4 C_me. } { ximg XF IMG4 C_ghe. } { ximg XF IMG4 C_he. } { ximg XF IMG4 C_gfl. }
        { assert (UFL : U (Z_to_bv 64 FL) = FL) by (apply u_Z2bv; clear - GFL; lia).
          eapply (rd_same ASEGS); [| | exact C_pp]; [intros x Hx; apply IMG4; rewrite at_u in Hx by (rewrite UFL; clear - GFL; lia); rewrite UFL in Hx; cbn in Hx; clear - Hx GFL; lia
                                                     | rewrite at_u by (rewrite UFL; clear - GFL; lia); rewrite UFL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia]. }
        { rewrite Erz. fold nm. rewrite I6. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). replace (2147450880 + (k + 256 + n8)) with (2147450880 + (k + (256 + n8))) by lia.
          change 1%nat with (Z.to_nat 1). apply SOKsh; [exact GR4 | slia0 BASE | lia | unfold hideW in HNZ; specialize (HNZ Em); slia0 BASE]. }
        exists r8', (amE1_mem m n SB M4). split; [exact RUN8|].
        assert (EA : Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8) = Z_to_bv 64 (2147450880 + (k + 256 + n8)) :> word).
        { rewrite Erz. fold nm. rewrite I6. reflexivity. }
        split; [intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [rewrite (AG8 _) by notinB; reflexivity|]); destruct Hi|].
        (lazymatch goal with |- ?G => let G' := eval unfold amE1_mem in G in change_no_check G' end). rewrite EA. split; [| split; [apply wbytes_grows|]].
        + intros x [Hx|Hx]; [exfalso; exact (Em Hx)|]. apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; slia0 BASE | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
        + intros _. split; [| unfold hideW in HNZ; exact (HNZ Em)].
          rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; slia0 BASE | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
          rewrite Z.sub_diag. reflexivity. }
    destruct W8 as (r8' & M5 & RUN8 & K8 & O5 & G5 & N5).
    (* [comment removed for export] *)
    exists r8', M5.
    assert (C250 : cbyte (Z_to_bv 64 250) = Z_to_bv 8 250) by (apply bv_eq; reflexivity).
    assert (C0 : cbyte (Z_to_bv 64 0) = Z_to_bv 8 0) by (apply bv_eq; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - rewrite <- (ARB_lit 0x4bed0) by lia. rewrite <- (ARB_lit 0x4c070) by lia.
      rewrite (ARB_lit 0x6f610) in RUN1, RUN3, RUN6 by lia.
      replace (456208%bv : word) with (Z_to_bv 64 456208 : word) in RUN2, RUN4, RUN7 by (apply bv_eq; reflexivity).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. exact RUN8.
    - intros i Hi. rewrite (K8 i Hi). apply K7. exact Hi.
    - intros x NF. unfold sb_foot1, SB in NF. fold asz in NF. rewrite I1 in NF. fold k in NF.
      assert (Q1 : U x < U m + 2040 \/ U m + 2048 <= U x) by (clear - NF; lia).
      assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (clear - NF; lia).
      assert (Q3 : U x < 2147450880 + k \/ 2147450880 + (k + a8) <= U x) by (clear - NF; lia).
      rewrite O5 by (right; destruct Q3 as [Q3|Q3]; [slia2 BASE Q3 | clear - Q3 L6 L9 L2 L3 Gn; lia]).
      rewrite O4; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O3; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O2; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      apply O1. exact Q1.
    - eapply mem_grows_trans; [exact GR4 | exact G5].
    - eapply (rd_same ASEGS); [| | exact R1]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_u in Hx by slia0 BASE. rewrite Erz in Hx. cbn in Hx.
      assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      assert (Q3 : U x < 2147450880 + k \/ 2147450880 + (k + a8) <= U x).
      { unfold hideW in Grng. destruct Grng as [G|G]; [left | right]; clear - G Hx L1 L4 L7 L8 Gn Gm2 Gm4; lia. }
      rewrite O5 by (right; destruct Q3 as [Q3|Q3]; [slia2 BASE Q3 | slia2 BASE Q3]).
      rewrite O4; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O3; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O2; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      reflexivity.
    - intros x Hx. assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      rewrite O5 by (right; slia2 BASE Hx). rewrite O4; [| exact Q2 | left; slia2 BASE Hx]. rewrite O3; [| exact Q2 | left; slia2 BASE Hx].
      rewrite <- C250. apply N2. slia2 BASE Hx.
    - fold re r8 k. intros x Hx. assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      rewrite O5; [| destruct (Z.eq_dec nm 0) as [Em|Em]; [left; exact Em | right; unfold hideW in HNZ; specialize (HNZ Em); clear - Hx HNZ; lia]].
      rewrite O4; [| exact Q2 | right; slia2 BASE Hx].
      rewrite <- C250. apply N3. slia2 BASE Hx.
    - intros x Hx. rewrite O5 by (right; slia2 BASE Hx). rewrite <- C0. apply N4. slia2 BASE Hx.
    - intros Em. exact (proj1 (N5 Em)).
  Qed.
End RUNS1.
End FPGen.
End AsAllocMSbRun1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSbRun2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunB1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 AsAllocMSbM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition sb_foot2 (s um t z : Z) : Prop :=
  (s - 2304 <= z < s - 2272) \/ (t + 2800 <= z < t + 2824) \/ (t + 2904 <= z < t + 2912)
  \/ (um + 2048 <= z < um + 2048 + 4096) \/ (um + 2032 <= z < um + 2034) \/ (um <= z < um + 16).

(* [comment removed for export] *)
Ltac slia0 B := clear - B; lia.
Ltac slia2 B X := clear - B X; lia.

Section FPGen.
Context {fx : FPState}.

Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold ms_clob in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto) end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : ms_agree _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr (regupd _ ?i _) ?i = _ => rewrite getr_same by (intros E; discriminate E) end
                          | match goal with |- getr (regupd _ ?j _) ?i = _ => rewrite getr_other by (intros E; discriminate E) end ]).

Section RUNS2.
  Variables (M rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp m : word) (T tctx n FL TSDP : Z) (h1 : byte).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 n.
  Hypothesis H18 : getr r0 18 = m.
  Hypothesis H19 : getr r0 19 = Z_to_bv 64 (sec_needed n).
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis H21 : getr r0 21 = at_ m (rz n - 16).
  (* [comment removed for export] *)
  Hypothesis GS : 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Gm : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sbasz n <= U S - 3584 /\ U m + sbasz n + 4096 <= 2 ^ 47.
  Hypothesis Gimg : hideW (U m + sbasz n <= AIMGLO \/ AIMGHI <= U m - 4096).
  Hypothesis GT : 4096 <= T /\ T + 4096 <= U S - 3584.
  Hypothesis GTimg : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T).
  Hypothesis GmT : hideW (U m + sbasz n <= T \/ T + 4096 <= U m - 4096).
  Hypothesis Gctx : 1 <= tctx /\ tctx + 4096 <= U S - 3584.
  Hypothesis Gtp : AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI.
  Hypothesis Gtsdp : AIMGLO <= TSDP /\ TSDP + 8 <= AIMGHI.
  Hypothesis GFL : AIMGLO <= FL /\ FL + 4096 < AIMGHI.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_kif : rdn ASEGS M (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS M (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS M (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP)).
  Hypothesis C_tctx : rdn ASEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS M (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_gfl : rdn ASEGS M (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_mfs : rdn ASEGS M (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096).
  Hypothesis C_fill : rdn ASEGS M (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe).
  Hypothesis C_grm : rdn ASEGS M (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS M (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  Hypothesis C_glsn : rdn ASEGS M (Z_to_bv 64 0xffec8) 8 = Some (LE8 (Z_to_bv 64 0x10)).
  Hypothesis C_lsn : rdn ASEGS M (at_ tp 0x10) 4 = Some (LE4 0).
  Hypothesis C_magic : rdn ASEGS M (Z_to_bv 64 0x103b8) 8 = Some (LE8 (Z_to_bv 64 MAGIC)).
  Hypothesis C_hook : rdn ASEGS M (Z_to_bv 64 0x199040) 8 = Some (LE8 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Hypothesis C_Tdef : forall i, T + 2800 <= i < T + 2912 -> M (Z_to_bv 64 i) <> None.
  Hypothesis C_Tw : store_ok ASEGS M (at_ thr 2800) 112 = true.
  Hypothesis C_chunk : store_ok ASEGS M m (Z.to_nat 6144) = true.
  Hypothesis C_h1 : rdn ASEGS M (at_ m (rz n - 15)) 1 = Some [h1].
  Hypothesis C_fflag : rdn ASEGS M (at_ sp2 8) 8 = Some (LE8 (Z_to_bv 64 1)).

  Theorem run_sB2 :
    exists (r : bvmap 5 word) (M9 : word -> option byte),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x4c070) M rom) (mkst r (Z_to_bv 64 0x4c258) M9 rom)
      /\ getr r 2 = sp2 /\ getr r 20 = at_ m (rz n) /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ (forall x : word, ~ sb_foot2 (U S) (U m) T (U x) -> M9 x = M x)
      /\ mem_grows M M9
      /\ M9 (at_ m (rz n - 16)) = Some (Z_to_bv 8 2)
      /\ M9 (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))))
      /\ rdn ASEGS M9 m 8 = Some (LE8 (Z_to_bv 64 MAGIC))
      /\ rdn ASEGS M9 (at_ m 8) 8 = Some (LE8 (at_ m (rz n - 16))).
  Proof using C_fflag C_h1 C_chunk C_Tw C_Tdef C_hook C_magic C_lsn C_glsn C_rm C_grm C_fill C_mfs C_gfl C_thr C_tctx C_tsdp C_key C_kif Hstk GFL Gtsdp Gtp Gctx GmT GTimg GT Gimg Gm Gn GS H21 H20 H19 H18 H9 H4 H3 H2 TSDP FL tctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4). destruct GT as (GT1 & GT2). destruct Gctx as (Gc1 & Gc2). destruct Gtp as (Gtp1 & Gtp2).
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb. pose proof (sbasz_bnd n) as [Hasz _].
    assert (Uthr : U thr = T) by (apply u_Z2bv; lia).
    assert (Uctx : U ctxw = tctx) by (apply u_Z2bv; lia).
    assert (Usp : U sp2 = U S - 2272) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    set (asz := sbasz n) in *.
    assert (BASE : 64513 <= n <= 2 ^ 34 /\ 8192 <= U m /\ U m + asz <= U S - 3584 /\ U m + asz + 4096 <= 2 ^ 47
                   /\ 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U sp2 = U S - 2272 /\ 0 <= U S < 2 ^ 64 /\ 0 <= U m < 2 ^ 64 /\ rz n = 2048
                   /\ n + 4096 <= sec_needed n <= n + 4103 /\ sec_needed n <= asz <= sec_needed n + 4095 /\ 4096 <= T /\ T + 4096 <= U S - 3584 /\ U thr = T
                   /\ 1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ U ctxw = tctx /\ AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI).
    { repeat split; first [assumption | apply Gn | apply HSr | apply Hmr | apply Hsnb | apply Hasz]. }
    assert (Gm' : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sec_needed n + 4096 <= 2 ^ 47) by (split; [exact Gm1 | slia0 BASE]).
    assert (Gimg' : U m + sec_needed n <= AIMGLO \/ AIMGHI <= U m) by (unfold hideW in Gimg; slia2 BASE Gimg).
    assert (RETA : forall d, d mod 2 = 0 -> 0 <= d < 2 ^ 24 -> ret_ok (at_ ARB d)).
    { clear. intros d Hd Hdr. pose proof ARB_ok as [E1 E2]. pose proof (u64_range ARB). apply ret_ok_at; [exact E1 | exact Hd | lia]. }
    (* [comment removed for export] *)
    assert (XF : forall (Mx : word -> option byte), (forall x : word, AIMGLO <= U x < AIMGHI -> Mx x = M x) ->
              forall (a : word) (len : nat) bs, AIMGLO <= U a -> U a + Z.of_nat len <= AIMGHI ->
              rdn ASEGS M a len = Some bs -> rdn ASEGS Mx a len = Some bs).
    { clear. intros Mx IM a len bs Ha1 Ha2 Hr. eapply (rd_same ASEGS); [| | exact Hr]; [intros x Hx; apply IM; lia | lia]. }
    assert (SOKs : forall (Mx : word -> option byte) (o : Z) (len : nat), mem_grows M Mx -> -3584 <= o -> o + Z.of_nat len <= 0 ->
              store_ok ASEGS Mx (at_ S o) len = true).
    { intros Mx o len GX Ho Hl. eapply store_ok_mono; [exact GX|].
      eapply (store_ok_sub ASEGS M (at_ S (-3584)) _ 3584); [rewrite at_u by slia0 BASE; slia0 BASE | exact Hstk
        | rewrite !at_u by (clear - BASE Ho Hl; lia); clear - BASE Ho Hl; lia | rewrite !at_u by (clear - BASE Ho Hl; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE Ho Hl; lia]. }
    assert (SOKc : forall (Mx : word -> option byte) (o : Z) (len : nat), mem_grows M Mx -> 0 <= o -> o + Z.of_nat len <= 6144 ->
              store_ok ASEGS Mx (at_ m o) len = true).
    { intros Mx o len GX Ho Hl. eapply store_ok_mono; [exact GX|].
      eapply (store_ok_sub ASEGS M m _ (Z.to_nat 6144)); [slia0 BASE | exact C_chunk
        | rewrite ?at_u by (clear - BASE Ho Hl; lia); clear - BASE Ho Hl; lia | rewrite ?at_u by (clear - BASE Ho Hl; lia); rewrite ?Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE Ho Hl; lia]. }
    Ltac ximg XF IM C := (eapply (XF _ IM); [ | | exact C]).
    (* [comment removed for export] *)
    pose proof (jal_66fa4 r0 M rom) as RUNJ.
    assert (GH : gctH ASEGS asan_gct_tab M (at_ sp2 (-16)) tp (Z_to_bv 64 TSDP) ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - rewrite Uctx. slia0 BASE.
      - rewrite !at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). apply SOKs; [apply mem_grows_refl | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite at_at, at_u by slia0 BASE. slia0 BASE.
      - rewrite u_Z2bv by lia. rewrite at_at, at_u by slia0 BASE. slia0 BASE.
      - rewrite at_at, at_u by slia0 BASE. slia0 BASE.
      - rewrite u_Z2bv by lia. rewrite at_at, at_u by slia0 BASE. slia2 BASE Gtsdp.
      - rewrite Uctx. rewrite at_at, at_u by slia0 BASE. slia0 BASE. }
    destruct (gts_run ASEGS ARB asan_HGTS ARB_ok asan_gct_tab M rom (regupd r0 1 (at_ ARB 0x4c074)) (at_ ARB 0x4c074) sp2 tp (Z_to_bv 64 TSDP) ctxw thr
                asan_gct_tab_ok asan_GTRB GH) as (r4 & RUN4 & D10 & AG4).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). apply SOKs; [apply mem_grows_refl | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { slia0 BASE. } { rewrite Uthr. slia0 BASE. } { rewrite Uthr. slia0 BASE. }
    { apply RETA; [reflexivity | lia]. }
    { rchB. } { rchB. } { rchB. }
    clear GH.
    match type of RUN4 with msteps _ _ (mkst _ _ ?MM _) => set (M4 := MM) in * end.
    assert (O4 : forall x : word, (U x < U S - 2304 \/ U S - 2272 <= U x) -> M4 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite !wbytes_outside; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); slia2 BASE Hx. }
    assert (G4 : mem_grows M M4) by ((lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    clearbody M4.
    (* [comment removed for export] *)
    assert (T24 : forall o, 2800 <= o -> o + 8 <= 2912 -> exists w : word, rdn ASEGS M4 (at_ thr o) 8 = Some (LE8 w)).
    { intros o Ho1 Ho2. destruct (rdn_defined_ex ASEGS M4 (at_ thr o) 8) as (bs & Rb & Lb).
      - intros i Hi. rewrite at_u, Uthr in Hi by (rewrite Uthr; clear - BASE Ho1 Ho2; lia). apply G4. apply C_Tdef. cbn in Hi. clear - Hi Ho1 Ho2. lia.
      - rewrite at_u, Uthr by (rewrite Uthr; clear - BASE Ho1 Ho2; lia). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). clear - BASE Ho1 Ho2. lia.
      - exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite (word_to_le_bytes_of_bytes8 bs Lb). exact Rb. }
    destruct (T24 2800 ltac:(lia) ltac:(lia)) as [v0 Rv0]. destruct (T24 2808 ltac:(lia) ltac:(lia)) as [v8 Rv8].
    destruct (T24 2816 ltac:(lia) ltac:(lia)) as [v16 Rv16]. destruct (T24 2904 ltac:(lia) ltac:(lia)) as [v104 Rv104]. clear T24.
    destruct (amE2sa ASEGS ARB asan_HAL2 rom m n Gn Gm' thr ltac:(rewrite Uthr; slia0 BASE) M4 r4 v0 v8 v16 v104 D10 ltac:(rchB) ltac:(rchB) Rv0 Rv8 Rv16 Rv104
                ltac:(eapply store_ok_mono; [exact G4 | exact C_Tw]))
      as (r5 & w0 & w8 & w16 & w104 & RUN5 & AG5).
    set (M5 := amE2s_mem thr M4 w0 w8 w16 w104) in *.
    assert (O5 : forall x : word, (U x < T + 2800 \/ T + 2824 <= U x) -> (U x < T + 2904 \/ T + 2912 <= U x) -> M5 x = M4 x).
    { intros x Hx1 Hx2. (lazymatch goal with |- ?G => let G' := eval unfold M5, amE2s_mem in G in change_no_check G' end). rewrite !wbytes_outside; [reflexivity | ..];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by (rewrite Uthr; slia0 BASE); rewrite ?Uthr; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - BASE Hx1 Hx2; lia. }
    assert (G5 : mem_grows M M5).
    { eapply mem_grows_trans; [exact G4|]. (lazymatch goal with |- ?G => let G' := eval unfold M5, amE2s_mem in G in change_no_check G' end). do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    clearbody M5. clear Rv0 Rv8 Rv16 Rv104.
    assert (IMG5 : forall x : word, AIMGLO <= U x < AIMGHI -> M5 x = M x).
    { intros x Hx. unfold hideW in GTimg. rewrite O5 by (clear - BASE Hx GTimg; lia). apply O4. slia2 BASE Hx. }
    (* [comment removed for export] *)
    assert (MSOK : ret_ok (Z_to_bv 64 0xf56e4)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (UFL : U (Z_to_bv 64 FL) = FL) by (apply u_Z2bv; clear - GFL; lia).
    destruct (amE2sc ASEGS ARB asan_HAL2 rom m n Gn Gm'
                0x106ddc 0xff278 0xff280 0xff288 0xff268 (Z_to_bv 64 0x108268) (Z_to_bv 64 0x108270) (Z_to_bv 64 0x108260) (Z_to_bv 64 FL)
                ltac:(split; [repeat constructor; lia | rewrite UFL; rewrite !u_Z2bv by lia; clear - GFL; lia])
                sp2 ltac:(slia0 BASE) 0xff268 0xff290 (Z_to_bv 64 0x1011b0) (Z_to_bv 64 0xf56e4) 0xbe asan_GLFL3 asan_GLRMS ltac:(lia) MSOK
                M5 r5 ltac:(rchB) ltac:(rchB) ltac:(rchB))
      as (r7 & RUN7 & G1 & G10 & G11 & G12 & AG7).
    { eapply (rd_same ASEGS); [| | exact C_fflag]; [| rewrite at_at, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_at, at_u in Hx by slia0 BASE. cbn in Hx.
      rewrite O5 by (clear - BASE Hx; lia). apply O4. slia2 BASE Hx. }
    { ximg XF IMG5 C_gfl; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { ximg XF IMG5 C_mfs; [rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); clear - GFL; lia | rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia]. }
    { ximg XF IMG5 C_fill; [rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); clear - GFL; lia | rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia]. }
    { ximg XF IMG5 C_grm; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { ximg XF IMG5 C_rm; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    destruct (asan_memset M5 (at_ m (rz n)) (Z_to_bv 64 0xbe) (at_ ARB 0x4c204) 4096 rom r7 ltac:(lia) ltac:(rewrite at_u by slia0 BASE; slia0 BASE))
      as (r8 & RUN8 & I10 & MSA).
    { rewrite Erz. apply SOKc; [exact G5 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { apply RETA; [reflexivity | lia]. }
    { exact G10. } { exact G11. } { exact G12. } { exact G1. }
    unfold asan_memset_entry in RUN8. replace (1005284%bv : word) with (Z_to_bv 64 0xf56e4 : word) in RUN8 by (apply bv_eq; reflexivity).
    match type of RUN8 with msteps _ _ (mkst _ _ ?MM _) => set (M7 := MM) in * end.
    assert (O7 : forall x : word, (U x < U m + 2048 \/ U m + 2048 + 4096 <= U x) -> M7 x = M5 x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M7 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | |]; rewrite repeat_length, at_u by slia0 BASE; rewrite Erz; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia2 BASE Hx. }
    assert (G7 : mem_grows M M7) by (eapply mem_grows_trans; [exact G5 | (lazymatch goal with |- ?G => let G' := eval unfold M7 in G in change_no_check G' end); apply wbytes_grows]).
    clearbody M7.
    assert (IMG7 : forall x : word, AIMGLO <= U x < AIMGHI -> M7 x = M x).
    { intros x Hx. rewrite O7 by (clear - BASE Hx Gimg'; lia). apply IMG5. exact Hx. }
    (* [comment removed for export] *)
    destruct (amE3s ASEGS ARB asan_HAL3 ARB_ok 0xffec8 0x103b8 asan_HLSN asan_GLSN asan_GMAG ltac:(lia) rom sp2 m tp n 0x10 h1 Gn Gm' Gimg'
                ltac:(slia0 BASE) ltac:(slia0 BASE) M7 r8 ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB))
      as (r9 & RUN9 & J1 & J10 & J11 & AG9).
    { ximg XF IMG7 C_glsn; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { ximg XF IMG7 C_lsn; [rewrite at_u by slia0 BASE; slia0 BASE | rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE]. }
    { eapply (rd_same ASEGS); [| | exact C_h1]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_u in Hx by slia0 BASE. rewrite Erz in Hx. cbn in Hx. unfold hideW in GmT.
      rewrite O7 by slia2 BASE Hx. rewrite O5 by (clear - BASE Hx GmT; lia). apply O4. slia2 BASE Hx. }
    { rewrite Erz. apply SOKc; [exact G7 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite <- (at_0 m) at 1. apply SOKc; [exact G7 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { intros _. ximg XF IMG7 C_magic; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    set (M8 := amE3_mem m n h1 M7) in *.
    assert (E7 : (rz_log n =? 0) = false).
    { apply Z.eqb_neq. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end). repeat (match goal with |- context [Z.leb n ?q] => destruct (Z.leb_spec n q) as [?|?]; [exfalso; lia|] end). discriminate. }
    assert (M8eq : M8 = wbytes (wbytes (wbytes (wbytes M7 (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1))))]) (at_ m (rz n - 16)) [Z_to_bv 8 2])
                                (at_ m 8) (LE8 (at_ m (rz n - 16)))) m (LE8 (Z_to_bv 64 MAGIC))).
    { (lazymatch goal with |- ?G => let G' := eval unfold M8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite E7. reflexivity. }
    assert (O8 : forall x : word, (U x < U m + 2032 \/ U m + 2034 <= U x) -> (U x < U m \/ U m + 16 <= U x) -> M8 x = M7 x).
    { intros x Hx1 Hx2. rewrite M8eq. rewrite !wbytes_outside; [reflexivity | ..];
        wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by slia0 BASE; rewrite ?Erz; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - BASE Hx1 Hx2; lia. }
    assert (N8a : M8 (at_ m (rz n - 16)) = Some (Z_to_bv 8 2)).
    { rewrite M8eq. do 2 (rewrite wbytes_outside; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by slia0 BASE; rewrite ?Erz; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); slia0 BASE ..]). rewrite ?Erz. idtac.
      rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE ..]. rewrite Z.sub_diag. reflexivity. }
    assert (N8b : M8 (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))))).
    { rewrite M8eq. do 3 (rewrite wbytes_outside; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by slia0 BASE; rewrite ?Erz; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); slia0 BASE ..]). idtac.
      rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE ..]. rewrite Z.sub_diag. reflexivity. }
    assert (N8c : rdn ASEGS M8 m 8 = Some (LE8 (Z_to_bv 64 MAGIC))) by (rewrite M8eq; apply rdn_wbytes_hitw; slia0 BASE).
    assert (N8d : rdn ASEGS M8 (at_ m 8) 8 = Some (LE8 (at_ m (rz n - 16)))).
    { rewrite M8eq. eapply (rd_same ASEGS); [| | apply rdn_wbytes_hitw; rewrite at_u by slia0 BASE; slia0 BASE]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_u in Hx by slia0 BASE. cbn in Hx. apply wbytes_outside; [rewrite length_N_to_le_bytes; slia0 BASE | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia2 BASE Hx]. }
    assert (G8 : mem_grows M M8).
    { eapply mem_grows_trans; [exact G7|]. rewrite M8eq. do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    clearbody M8. clear M8eq.
    assert (IMG8 : forall x : word, AIMGLO <= U x < AIMGHI -> M8 x = M x).
    { intros x Hx. rewrite O8 by (clear - BASE Hx Gimg'; lia). apply IMG7. exact Hx. }
    (* [comment removed for export] *)
    destruct (rmh_run ASEGS ARB (Z_to_bv 64 0x199040) asan_HRMH asan_GRMH asan_HHK ARB_ok M8 rom r9 (at_ ARB 0x4c258) sp2)
      as (r10 & RUN10 & AG10).
    { ximg XF IMG8 C_hook; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { rewrite u_Z2bv by lia. lia. }
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). apply SOKs; [exact G8 | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { slia0 BASE. }
    { apply RETA; [reflexivity | lia]. }
    { exact J1. } { rchB. }
    match type of RUN10 with msteps _ _ (mkst _ _ ?MM _) => set (M9 := MM) in * end.
    assert (O9 : forall x : word, (U x < U S - 2304 \/ U S - 2272 <= U x) -> M9 x = M8 x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). rewrite !wbytes_outside; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); slia2 BASE Hx. }
    assert (G9 : mem_grows M M9) by (eapply mem_grows_trans; [exact G8|]; (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end); do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    clearbody M9.
    (* [comment removed for export] *)
    exists r10, M9.
    rewrite (ARB_lit 0x4c258) in RUN10 by lia. rewrite <- (ARB_lit 0x4c070) by lia.
    split; [| split; [rchB | split; [rchB | split; [rchB | split; [rchB|]]]]].
    { eapply msteps_trans; [exact RUNJ|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|]. exact RUN10. }
    split; [| split; [exact G9 | split; [| split; [| split]]]].
    - intros x NF. unfold sb_foot2 in NF.
      rewrite O9 by (clear - NF; lia). rewrite O8 by (clear - NF; lia). rewrite O7 by (clear - NF; lia). rewrite O5 by (clear - NF; lia). apply O4. clear - NF. lia.
    - rewrite O9 by (rewrite at_u by slia0 BASE; slia0 BASE). exact N8a.
    - rewrite O9 by (rewrite at_u by slia0 BASE; slia0 BASE). exact N8b.
    - eapply (rd_same ASEGS); [| | exact N8c]; [| slia0 BASE]. intros x Hx. apply O9. cbn in Hx. slia2 BASE Hx.
    - eapply (rd_same ASEGS); [| | exact N8d]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE]. intros x Hx. rewrite at_u in Hx by slia0 BASE. apply O9. cbn in Hx. slia2 BASE Hx.
  Qed.
End RUNS2.
End FPGen.
End AsAllocMSbRun2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMSbRun3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 AsAllocMSbM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]) end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, ~ In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by notinB end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end ]).

Section FPGen.
Context {fx : FPState}.

Section RUNS3.
  Variables (M rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp m : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI)%Z.
  Hypothesis Gm : (U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sec_needed n + 4096 <= 2 ^ 47)%Z.
  Hypothesis Gimg : (U m + sec_needed n <= AIMGLO \/ AIMGHI <= U m)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn ASEGS M (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS M (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn ASEGS M (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  (* [comment removed for export] *)
  Hypothesis C_slots4 : forall (k : Z) (v : word),
    In (k, v) (amE4_slots ARB S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81)) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S) ->
    rdn ASEGS M (at_ sp2 k) 8 = Some (LE8 v).
  Hypothesis C_slotsI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn ASEGS M (at_ S k) 8 = Some (LE8 v).

  Theorem run_sB3 :
    exists (r : bvmap 5 word),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x4c258) M rom) (mkst r (getr R 1) M rom)
      /\ getr r 10 = at_ m (rz n) /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using C_slotsI C_slots4 C_mcs C_fum C_gcf C_inited Hstk Gimg Gm Gtp GT Gn GS Hret H20 H4 H3 H2 x19 x18 T.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    (* [comment removed for export] *)
    destruct (amE4s ASEGS ARB asan_HAL3 asan_HAM2 ARB_ok 0xffec8 0x103b8 ltac:(lia) rom sp2 m tp n 0x10 Gn Gm Gimg
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) M r0 S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S H2 H20 C_slots4)
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & AG1).
    rewrite (ARB_lit 0x4c258) in RUN1 by lia.
    rewrite at_at in A2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in A2.
    (* [comment removed for export] *)
    assert (MH : mpH ASEGS asan_mp_tab M S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x1990a8) 34) with (Z_to_bv 64 0x1990ca : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub ASEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    destruct (mp_epi ASEGS asan_mp_tab asan_mp_tab_ok R M rom (getr R 1) S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) M r1 A2 C_slotsI)
      as (r2 & RUN2 & B10 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & BK).
    cbn [mt_rb asan_mp_tab] in RUN2. rewrite (ARB_lit 0x6e600) in RUN2 by lia. rewrite (ARB_lit 0x6e600) in A1 by lia.
    exists r2. split.
    { eapply msteps_trans; [exact RUN1|]. exact RUN2. }
    rewrite B10, A10.
    repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity;
      try rchB.
  Qed.
End RUNS3.
End FPGen.
End AsAllocMSbRun3.
Module AsAllocMSbRun.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 AsAllocMSbM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit AsAllocMSbRun1 AsAllocMSbRun2 AsAllocMSbRun3.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition sb_foot (s um t n z : Z) : Prop := sb_foot1 s um n z \/ sb_foot2 s um t z.

Section FPGen.
Context {fx : FPState}.

Section RUNS.
  Variables (M rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp m : word) (T tctx n id sbeg FL MIDEND TSDP : Z) (h1 : byte) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H8 : getr r0 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 id.
  Hypothesis H18 : getr r0 18 = m.
  Hypothesis H19 : getr r0 19 = Z_to_bv 64 (sec_needed n).
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis H21 : getr r0 21 = at_ m (rz n - 16).
  Hypothesis H22 : getr r0 22 = Z_to_bv 64 0x103f18.
  Hypothesis H24 : getr r0 24 = Z_to_bv 64 0.
  Hypothesis H25 : getr r0 25 = at_ m (rz n + n).
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hid : 0 <= id < 2 ^ 32.
  Hypothesis Gm : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sbasz n <= U S - 3584 /\ U m + sbasz n + 4096 <= 2 ^ 47.
  Hypothesis Grng : hideW (U m + sbasz n <= 0x7fff7000 \/ 0x10007fff8000 <= U m - 4096).
  Hypothesis Gimg : hideW (U m + sbasz n <= AIMGLO \/ AIMGHI <= U m - 4096).
  Hypothesis Gsb : 0 <= sbeg /\ sbeg + 2 ^ 37 < 2 ^ 64.
  Hypothesis Dsb : U m < sbeg \/ sbeg + 2 ^ 37 <= U m.
  Hypothesis GT : 4096 <= T /\ T + 4096 <= U S - 3584.
  Hypothesis GTimg : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T).
  Hypothesis GTband : hideW (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T).
  Hypothesis GmT : hideW (U m + sbasz n <= T \/ T + 4096 <= U m - 4096).
  Hypothesis Gctx : 1 <= tctx /\ tctx + 4096 <= U S - 3584.
  Hypothesis Gctxband : hideW (tctx + 0x10000 <= 0x7fff7000 \/ 0x10007fff8000 <= tctx).
  Hypothesis Gmctx : hideW (U m + sbasz n <= tctx \/ tctx + 4096 <= U m - 4096).
  Hypothesis Gtp : AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI.
  Hypothesis Gtsdp : AIMGLO <= TSDP /\ TSDP + 8 <= AIMGHI.
  Hypothesis GFL : AIMGLO <= FL /\ FL + 4096 < AIMGHI.
  Hypothesis GME : 0 <= MIDEND < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_inited : rdn ASEGS M (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS M (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn ASEGS M (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_thr64 : rdn ASEGS M (Z_to_bv 64 (0x1990a8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).
  Hypothesis C_kif : rdn ASEGS M (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS M (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS M (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP)).
  Hypothesis C_tctx : rdn ASEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS M (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_gsb : rdn ASEGS M (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sb : rdn ASEGS M (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 SB)).
  Hypothesis C_cpm : rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gmb : rdn ASEGS M (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS M (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn ASEGS M (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_gfl : rdn ASEGS M (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_pp : rdn ASEGS M (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mfs : rdn ASEGS M (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096).
  Hypothesis C_fill : rdn ASEGS M (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe).
  Hypothesis C_grm : rdn ASEGS M (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS M (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  Hypothesis C_glsn : rdn ASEGS M (Z_to_bv 64 0xffec8) 8 = Some (LE8 (Z_to_bv 64 0x10)).
  Hypothesis C_lsn : rdn ASEGS M (at_ tp 0x10) 4 = Some (LE4 0).
  Hypothesis C_magic : rdn ASEGS M (Z_to_bv 64 0x103b8) 8 = Some (LE8 (Z_to_bv 64 MAGIC)).
  Hypothesis C_hook : rdn ASEGS M (Z_to_bv 64 0x199040) 8 = Some (LE8 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Hypothesis C_sbeg : rdn ASEGS M (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 sbeg)).
  Hypothesis C_pg : rdn ASEGS M (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_sz : rdn ASEGS M (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))).
  (* [comment removed for export] *)
  Hypothesis C_Tdef : forall i, T + 2800 <= i < T + 2912 -> M (Z_to_bv 64 i) <> None.
  Hypothesis C_Tw : store_ok ASEGS M (at_ thr 2800) 112 = true.
  Hypothesis C_chunk : store_ok ASEGS M m (Z.to_nat 6144) = true.
  Hypothesis C_shw : store_ok ASEGS M (Z_to_bv 64 (SB + U m / 8)) (Z.to_nat (sbasz n / 8)) = true.
  Hypothesis C_h1 : rdn ASEGS M (at_ m (rz n - 15)) 1 = Some [h1].
  Hypothesis C_fflag : rdn ASEGS M (at_ sp2 8) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_slots4 : forall (k : Z) (v : word),
    In (k, v) (amE4_slots ARB S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81)) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S) ->
    rdn ASEGS M (at_ sp2 k) 8 = Some (LE8 v).
  Hypothesis C_slotsI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn ASEGS M (at_ S k) 8 = Some (LE8 v).

  Theorem run_sB :
    exists (r : bvmap 5 word) (Mf : word -> option byte),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x4bed0) M rom) (mkst r (getr R 1) Mf rom)
      /\ (getr r 10 = at_ m (rz n) /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
          /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
          /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
          /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27)
      /\ (forall x : word, ~ sb_foot (U S) (U m) T n (U x) -> Mf x = M x)
      /\ mem_grows M Mf
      /\ rdn ASEGS Mf (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id)))
      /\ (forall x : word, SB + U m / 8 <= U x < SB + U m / 8 + 256 -> Mf x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + sbre (U m) n / 8 <= U x < SB + (U m + sbasz n) / 8 -> Mf x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + (U m + 2048) / 8 <= U x < SB + (U m + 2048) / 8 + n / 8 -> Mf x = Some (Z_to_bv 8 0))
      /\ (n mod 8 <> 0 -> Mf (Z_to_bv 64 (SB + (U m + 2048 + (n - n mod 8)) / 8)) = Some (Z_to_bv 8 (n mod 8)))
      /\ Mf (at_ m (rz n - 16)) = Some (Z_to_bv 8 2)
      /\ Mf (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1)))))
      /\ rdn ASEGS Mf m 8 = Some (LE8 (Z_to_bv 64 MAGIC))
      /\ rdn ASEGS Mf (at_ m 8) 8 = Some (LE8 (at_ m (rz n - 16))).
  Proof using C_slotsI C_slots4 C_fflag C_h1 C_shw C_chunk C_Tw C_Tdef C_sz C_pg C_sbeg C_hook C_magic C_lsn C_glsn C_rm C_grm C_fill C_mfs C_pp C_gfl C_he C_ghe C_me C_gme C_mb C_gmb C_cpm C_sb C_gsb C_thr C_tctx C_tsdp C_key C_kif C_thr64 C_mcs C_fum C_gcf C_inited Hstk GME GFL Gtsdp Gtp Gmctx Gctxband Gctx GmT GTband GTimg GT Dsb Gsb Gimg Grng Gm Hid Gn GS Hret H25 H24 H22 H21 H20 H19 H18 H10 H9 H8 H4 H3 H2 x19 x18 TSDP MIDEND FL sbeg tctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4). destruct GT as (GT1 & GT2). destruct Gctx as (Gc1 & Gc2). destruct Gtp as (Gtp1 & Gtp2).
    set (k := U m / 8) in *. set (n8 := n / 8) in *. set (nm := n mod 8) in *.
    set (re := sbre (U m) n) in *. set (asz := sbasz n) in *. set (r8 := re / 8) in *. set (a8 := asz / 8) in *.
    destruct (sb_shadow_arith2 (U m) n Gm1 ltac:(lia) ltac:(lia) k n8 nm re r8 asz a8 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (LIN & HZ & HNZ & IDS).
    destruct IDS as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
    rewrite I1, I4, I6.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (Uthr : U thr = T) by (apply u_Z2bv; clear - GT1 GT2 HSr; lia).
    assert (Uctx : U ctxw = tctx) by (apply u_Z2bv; clear - Gc1 Gc2 HSr; lia).
    assert (Usp : U sp2 = U S - 2272) by (rewrite at_u by (clear - GS1 HSr; lia); clear; lia).
    assert (BASE : (U m = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
                    /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
                   /\ 64513 <= n <= 2 ^ 34 /\ 8192 <= U m /\ U m + asz <= U S - 3584 /\ U m + asz + 4096 <= 2 ^ 47
                   /\ 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U sp2 = U S - 2272 /\ 0 <= U S < 2 ^ 64 /\ 0 <= U m < 2 ^ 64 /\ rz n = 2048
                   /\ n + 4096 <= sec_needed n <= n + 4103 /\ 4096 <= T /\ T + 4096 <= U S - 3584 /\ U thr = T
                   /\ 1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ U ctxw = tctx /\ AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI).
    { split; [exact LIN|]. repeat split; first [assumption | apply Gn | apply HSr | apply Hmr | apply Hsnb]. }
    clear LIN.
    (* [comment removed for export] *)
    assert (NF1 : forall z, (AIMGLO <= z < AIMGHI) \/ (U S - 2272 <= z < U S) \/ (T <= z < T + 4096) \/ (tctx <= z < tctx + 4096)
                            \/ (U m - 4096 <= z < U m + 2040) \/ (U m + 2048 <= z < U m + asz) -> ~ sb_foot1 (U S) (U m) n z).
    { intros z Hz NF. unfold sb_foot1, SB in NF. fold asz in NF. rewrite I1 in NF. fold k in NF.
      unfold hideW in Gimg, GTband, Gctxband, Grng.
      destruct Hz as [Hz|[Hz|[Hz|[Hz|[Hz|Hz]]]]].
      - clear - BASE Hz NF Gimg. lia.
      - clear - BASE Hz NF. lia.
      - clear - BASE Hz NF GTband GmT. unfold hideW in GmT. lia.
      - clear - BASE Hz NF Gctxband Gmctx. unfold hideW in Gmctx. lia.
      - clear - BASE Hz NF Grng. lia.
      - clear - BASE Hz NF Grng. lia. }
    assert (NF2 : forall z, (AIMGLO <= z < AIMGHI) \/ (U S - 2272 <= z < U S) \/ (2147450880 + k <= z < 2147450880 + (k + a8))
                            \/ (U m + 2040 <= z < U m + 2048) \/ (U m - 4096 <= z < U m) -> ~ sb_foot2 (U S) (U m) T z).
    { intros z Hz NF. unfold sb_foot2 in NF. unfold hideW in Gimg, GTimg, GTband, Grng, GmT.
      destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
      - clear - BASE Hz NF Gimg GTimg. lia.
      - clear - BASE Hz NF. lia.
      - clear - BASE Hz NF GTband Grng. lia.
      - clear - BASE Hz NF GmT. lia.
      - clear - BASE Hz NF GmT. lia. }
    (* [comment removed for export] *)
    destruct (run_sB1 M rom r0 S m n id sbeg FL MIDEND H2 H8 H9 H10 H18 H20 H21 H22 H24 H25 (conj GS1 GS2) Gn Hid (conj Gm1 (conj Gm2 (conj Gm3 Gm4)))
                Grng Gimg Gsb Dsb GFL GME Hstk C_gcf C_thr64 C_gsb C_sb C_cpm C_gmb C_mb C_gme C_me C_ghe C_he C_gfl C_pp C_grm C_rm C_sbeg C_pg C_sz
                ltac:(eapply (store_ok_sub ASEGS M m _ (Z.to_nat 6144)); [slia0 BASE | exact C_chunk | rewrite at_u by slia0 BASE; slia0 BASE
                                                                          | rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE])
                C_shw)
      as (r5 & M5 & RUN1 & K5 & O5 & G5 & R5 & N5l & N5r & N5z & N5p).
    fold k re r8 asz nm n8 in N5l, N5r, N5z, N5p. rewrite I1 in N5r. rewrite I4 in N5z. rewrite I6 in N5p. unfold SB in N5l, N5r, N5z, N5p.
    clear Dsb.
    assert (XF1 : forall (a : word) (len : nat) bs, U a + Z.of_nat len <= 2 ^ 64 ->
              (forall z, U a <= z < U a + Z.of_nat len -> ~ sb_foot1 (U S) (U m) n z) -> rdn ASEGS M a len = Some bs -> rdn ASEGS M5 a len = Some bs).
    { intros a len bs Hnw Hz Hr. eapply (rd_same ASEGS); [| exact Hnw | exact Hr]. intros x Hx. apply O5. apply Hz. exact Hx. }
    Ltac x1img XF1 NF1 C := (eapply XF1; [ | intros z Hz; apply NF1; left | exact C]).
    assert (UFL : U (Z_to_bv 64 FL) = FL) by (apply u_Z2bv; clear - GFL; lia).
    (* [comment removed for export] *)
    destruct (run_sB2 M5 rom r5 R S tp m T tctx n FL TSDP h1
                ltac:(rewrite (K5 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H2) ltac:(rewrite (K5 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H3) ltac:(rewrite (K5 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H4)
                ltac:(rewrite (K5 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H9) ltac:(rewrite (K5 18%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H18) ltac:(rewrite (K5 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H19)
                ltac:(rewrite (K5 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H20) ltac:(rewrite (K5 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H21)
                (conj GS1 GS2) Gn (conj Gm1 (conj Gm2 (conj Gm3 Gm4))) Gimg (conj GT1 GT2) GTimg GmT (conj Gc1 Gc2) (conj Gtp1 Gtp2) Gtsdp GFL
                ltac:(eapply store_ok_mono; [exact G5 | exact Hstk]))
      as (r9 & M9 & RUN2 & Q2 & Q20 & Q3 & Q4 & O9 & G9 & N9a & N9b & N9c & N9d).
    { x1img XF1 NF1 C_kif; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_key; [rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
                            | rewrite at_u in Hz by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]); rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_tsdp; [rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite at_u in Hz by slia0 BASE; cbn in Hz; slia2 BASE Hz]. }
    { x1img XF1 NF1 C_tctx; [rewrite u_Z2bv by (clear - Gtsdp; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gtsdp; lia | rewrite u_Z2bv in Hz by (clear - Gtsdp; lia); cbn in Hz; clear - Hz Gtsdp; lia]. }
    { eapply XF1; [ | intros z Hz; apply NF1; right; right; right; left | exact C_thr];
        [rewrite at_u, Uctx by (rewrite Uctx; slia0 BASE); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite at_u, Uctx in Hz by (rewrite Uctx; slia0 BASE); cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_gfl; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_mfs; [rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia | rewrite at_u, UFL in Hz by (rewrite UFL; clear - GFL; lia); cbn in Hz; clear - Hz GFL; lia]. }
    { x1img XF1 NF1 C_fill; [rewrite at_u, UFL by (rewrite UFL; clear - GFL; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia | rewrite at_u, UFL in Hz by (rewrite UFL; clear - GFL; lia); cbn in Hz; clear - Hz GFL; lia]. }
    { x1img XF1 NF1 C_grm; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_rm; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_glsn; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_lsn; [rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite at_u in Hz by slia0 BASE; cbn in Hz; slia2 BASE Hz]. }
    { x1img XF1 NF1 C_magic; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x1img XF1 NF1 C_hook; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { intros i Hi. apply G5. apply C_Tdef. exact Hi. }
    { eapply store_ok_mono; [exact G5 | exact C_Tw]. }
    { eapply store_ok_mono; [exact G5 | exact C_chunk]. }
    { eapply XF1; [ | intros z Hz; apply NF1; right; right; right; right; left | exact C_h1];
        [rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite at_u in Hz by slia0 BASE; rewrite Erz in Hz; cbn in Hz; clear - Hz; lia]. }
    { eapply XF1; [ | intros z Hz; apply NF1; right; left | exact C_fflag];
        [rewrite at_at, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite at_at, at_u in Hz by slia0 BASE; cbn in Hz; clear - Hz; lia]. }
    (* [comment removed for export] *)
    assert (XF9 : forall (a : word) (len : nat) bs, U a + Z.of_nat len <= 2 ^ 64 ->
              (forall z, U a <= z < U a + Z.of_nat len -> ~ sb_foot1 (U S) (U m) n z /\ ~ sb_foot2 (U S) (U m) T z) ->
              rdn ASEGS M a len = Some bs -> rdn ASEGS M9 a len = Some bs).
    { intros a len bs Hnw Hz Hr. eapply (rd_same ASEGS); [| exact Hnw | exact Hr]. intros x Hx. destruct (Hz (U x) Hx) as [Z1 Z2]. rewrite (O9 x Z2). apply O5. exact Z1. }
    Ltac x9img XF9 NF1 NF2 C := (eapply XF9; [ | intros z Hz; split; [apply NF1; left | apply NF2; left] | exact C]).
    destruct (run_sB3 M9 rom r9 R S tp m T n x18 x19 Q2 Q3 Q4 Q20 Hret ltac:(split; [slia0 BASE | split; [exact GS2 | exact GS3]]) Gn (conj GT1 GT2) (conj Gtp1 Gtp2)
                ltac:(split; [exact Gm1 | slia0 BASE]) ltac:(unfold hideW in Gimg; slia2 BASE Gimg)
                ltac:(eapply store_ok_mono; [exact G9|]; eapply store_ok_mono; [exact G5 | exact Hstk]))
      as (rF & RUN3 & F).
    { x9img XF9 NF1 NF2 C_inited; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x9img XF9 NF1 NF2 C_gcf; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x9img XF9 NF1 NF2 C_fum; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { x9img XF9 NF1 NF2 C_mcs; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia | rewrite u_Z2bv in Hz by lia; cbn in Hz; clear - Hz; lia]. }
    { intros k0 v Hin. assert (Hk : 24 <= k0 /\ k0 + 8 <= 144).
      { clear - Hin. unfold amE4_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      eapply XF9; [ | intros z Hz; split; [apply NF1; right; left | apply NF2; right; left] | exact (C_slots4 k0 v Hin)];
        [rewrite at_at, at_u by (clear - BASE Hk; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE Hk; lia
        | rewrite at_at, at_u in Hz by (clear - BASE Hk; lia); cbn in Hz; clear - Hz Hk; lia
        | rewrite at_at, at_u in Hz by (clear - BASE Hk; lia); cbn in Hz; clear - Hz Hk; lia]. }
    { intros k0 v Hin. assert (Hk : -56 <= k0 /\ k0 + 8 <= 0).
      { clear - Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      eapply XF9; [ | intros z Hz; split; [apply NF1; right; left | apply NF2; right; left] | exact (C_slotsI k0 v Hin)];
        [rewrite at_u by (clear - BASE Hk; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE Hk; lia
        | rewrite at_u in Hz by (clear - BASE Hk; lia); cbn in Hz; clear - Hz Hk; lia
        | rewrite at_u in Hz by (clear - BASE Hk; lia); cbn in Hz; clear - Hz Hk; lia]. }
    (* [comment removed for export] *)
    exists rF, M9. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end).
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split; [exact F|].
    split; [intros x NF; rewrite O9 by (intros X; apply NF; right; exact X); apply O5; intros X; apply NF; left; exact X|].
    split; [eapply mem_grows_trans; [exact G5 | exact G9]|].
    split; [| split; [| split; [| split; [| split; [| split; [exact N9a | split; [exact N9b | split; [exact N9c | exact N9d]]]]]]]].
    - eapply (rd_same ASEGS); [| | exact R5]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_u in Hx by slia0 BASE. rewrite Erz in Hx. cbn in Hx. apply O9. apply NF2. right; right; right; left. clear - Hx. lia.
    - intros x Hx. rewrite O9 by (apply NF2; right; right; left; slia2 BASE Hx). apply N5l. exact Hx.
    - intros x Hx. rewrite O9 by (apply NF2; right; right; left; slia2 BASE Hx). apply N5r. exact Hx.
    - intros x Hx. rewrite O9 by (apply NF2; right; right; left; slia2 BASE Hx). apply N5z. exact Hx.
    - intros Em. rewrite O9; [exact (N5p Em)|]. apply NF2. right; right; left. rewrite u_Z2bv by slia0 BASE.
      unfold hideW in HNZ. specialize (HNZ Em). clear - BASE HNZ. lia.
  Qed.
End RUNS.
End FPGen.
End AsAllocMSbRun.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4.AsAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbM4 AsAllocMSbRun1 AsAllocMSbRun2 AsAllocMSbRun OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAllocMSbRepc.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma sbtop_arith : forall mp n, mp mod 4096 = 0 -> 0 <= mp -> 64513 <= n ->
  forall um k r8 a8, um = mp + 4096 -> k = um / 8 -> r8 = sbre um n / 8 -> a8 = sbasz n / 8 ->
  sec_map_size n = sbasz n + 4096 /\ sec_user_off n = 4096 + 2048
  /\ (mp + PG) / 8 = k /\ (mp + sec_user_off n) / 8 = k + 256 /\ (mp + sec_user_off n + n + 7) / 8 = r8
  /\ (mp + sec_map_size n) / 8 = k + a8 /\ mp / 8 = k - 512 /\ (mp + sec_map_size n + 7) / 8 = k + a8.
Proof.
  intros mp n Hmp H0 Hn um k r8 a8 -> -> -> ->. (lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, sec_user_off, RoundUp, PG, sbre, sbasz in G in change_no_check G' end). rewrite (rz_sec n) by lia.
  pose proof (sec_needed_bnd n ltac:(lia)) as Hs. set (sn := sec_needed n) in *. clearbody sn.
  Z.div_mod_to_equations; repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition shxl (um k r8 a8 z : Z) : Prop :=
  z = um + 2032 \/ (um <= z < um + 16) \/ (SB + k <= z < SB + k + 256) \/ (SB + r8 <= z < SB + k + a8).
Lemma sec_hx_lin : forall mp n, mp mod 4096 = 0 -> 0 <= mp -> 64513 <= n ->
  forall um k r8 a8, um = mp + 4096 -> k = um / 8 -> r8 = sbre um n / 8 -> a8 = sbasz n / 8 ->
  forall z, sec_hx mp n z <-> shxl um k r8 a8 z.
Proof.
  intros mp n Hmp H0 Hn um k r8 a8 Eum Ek Er Ea z.
  destruct (sbtop_arith mp n Hmp H0 Hn um k r8 a8 Eum Ek Er Ea) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
  (lazymatch goal with |- ?G => let G' := eval unfold sec_hx, shxl in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite E3, E4, E5, E6, E2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). subst um. clear. split; intros H; lia.
Qed.

(* [comment removed for export] *)
Definition sbfl (s um t k a8 z : Z) : Prop :=
  (um + 2040 <= z < um + 2048) \/ (s - 2336 <= z < s - 2272) \/ (SB + k <= z < SB + k + a8)
  \/ (t + 2800 <= z < t + 2824) \/ (t + 2904 <= z < t + 2912) \/ (um + 2048 <= z < um + 6144) \/ (um + 2032 <= z < um + 2034) \/ (um <= z < um + 16).
Lemma sbfl_dec : forall s um t k a8 z, sbfl s um t k a8 z \/ ~ sbfl s um t k a8 z.
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold sbfl in G in change_no_check G' end). lia. Qed.


(* [comment removed for export] *)
Lemma pin_byte : forall (Mf M0 : mem) (a : word) b, 0 <= b < 2 ^ 64 ->
  Mf a = Some (Z_to_bv 8 b) -> byteZ ASEGS M0 (U a) b -> M0 a <> None -> Mf a = M0 a.
Proof.
  intros Mf M0 a b Hb EF BZ D. unfold byteZ, cellN in BZ. rewrite Z_to_bv_bv_unsigned in BZ. rewrite (w2b1 b Hb) in BZ. cbn [rdn] in BZ.
  destruct (M0 a) as [y|]; [| exfalso; exact (D eq_refl)]. cbn in BZ. injection BZ as ->. exact EF.
Qed.

Section TOPSB.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis SCELL_pg : In (0x103f58, 8%nat, 0x1000) (bt_consts bt).      (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem malloc_partBs : forall HPf, partBs_stmt bt FXOK HPf.
  Proof using HTP SCELL_pg CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros HPf h fx R M mdl Lc FF B C K ret n sp st c' HLT HFX W0 BD HP0 HO CP HR10 Hn FPC HB HCb HK HCL RPOST.
    destruct RPOST as (fx' & R' & M' & M0 & mdl' & mp & grow & d' & naa' & id & x18 & x19 & RPOST).   (* [comment removed for export] *)
    cbv zeta in RPOST.
    destruct RPOST as (Ec' & HFX' & HH' & MW' & W' & RP' & MPG & DYN & APT & RAL & DX & CHG & SLA & SLI & STKD
                       & Y2 & Y4 & Y3 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ).
    subst c'. pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (st' := runS_st st mp n grow d' naa') in *.
    set (p := mp + sec_user_off n) in *. set (msz := sec_map_size n) in *.
    set (L' := (p, n) :: Lc) in *.
    set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. rewrite <- HTP in CP4.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & _ & _ & _ & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    (* [comment removed for export] *)
    assert (Hn34 : 64513 <= n <= 2 ^ 34).
    { pose proof (proj1 BD) as BD0. clear - Hn HB BD0. unfold GBUDGET, MBLK in HB. lia. }
    (* [comment removed for export] *)
    assert (HS' : In (SCH mp n) (a_sec st')).
    { (lazymatch goal with |- ?G => let G' := eval unfold st', runS_st, depot_st, op_sec_alloc, set_sec, op_meter, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec] in G in change_no_check G' end). apply in_or_app. right. left. reflexivity. }
    pose proof (sec_facts bt st' L' FF W' (SCH mp n) HS') as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7 & SF8).
    unfold sc_user, sc_mapsz in SF2, SF4, SF5, SF6, SF8. cbn [sc_map sc_n] in SF1, SF2, SF3, SF4, SF5, SF6, SF7, SF8.
    (* [comment removed for export] *)
    assert (MP0 : mp mod 4096 = 0) by exact MPG.
    set (um := mp + 4096) in *.
    set (k := um / 8) in *. set (n8 := n / 8) in *. set (nm := n mod 8) in *.
    set (re := sbre um n) in *. set (asz := sbasz n) in *. set (r8 := re / 8) in *. set (a8 := asz / 8) in *.
    assert (UM0 : um mod 4096 = 0) by ((lazymatch goal with |- ?G => let G' := eval unfold um in G in change_no_check G' end); clear - MP0; Z.div_mod_to_equations; lia).
    destruct (sb_shadow_arith2 um n UM0 ltac:((lazymatch goal with |- ?G => let G' := eval unfold um in G in change_no_check G' end); clear - SF1; lia) ltac:(clear - Hn34; lia) k n8 nm re r8 asz a8 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (LIN & HZ & HNZ & IDS).
    destruct IDS as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
    destruct (sbtop_arith mp n MP0 ltac:(clear - SF1; lia) ltac:(clear - Hn34; lia) um k r8 a8 eq_refl eq_refl eq_refl eq_refl)
      as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    pose proof (sec_hx_lin mp n MP0 ltac:(clear - SF1; lia) ltac:(clear - Hn34; lia) um k r8 a8 eq_refl eq_refl eq_refl eq_refl) as HXL.
    assert (Ep : p = um + 2048) by ((lazymatch goal with |- ?G => let G' := eval unfold p, um in G in change_no_check G' end); rewrite E2; clear; lia).
    assert (Emsz : msz = asz + 4096) by exact E1.
    assert (P8 : p / 8 = k + 256) by exact E4.
    assert (PN8 : (p + n + 7) / 8 = r8) by exact E5.
    assert (M8 : (mp + msz) / 8 = k + a8) by exact E6.
    assert (M8' : (mp + msz + 7) / 8 = k + a8) by exact E8.
    assert (Erz : rz n = 2048) by (apply rz_sec; clear - Hn34; lia).
    pose proof (sec_needed_bnd n ltac:(clear - Hn34; lia)) as Hsnb.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st' L' FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & SB0 & SB1).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. destruct DYN as (DY1 & DY2 & DY3 & DY4 & DY5). cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI, DY4.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    destruct (fixed_members bt st Lc FF W0) as (IN6 & IN8 & INFS & INT & INN & INS & INC).
    pose proof W0 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & R6a & R6b & _) & _).
    pose proof (APT _ _ (all_ranges_fixed bt st _ INT)) as APT_T.
    pose proof (APT _ _ (all_ranges_fixed bt st _ INC)) as APT_C.
    pose proof (APT _ _ (all_ranges_fixed bt st _ IN6)) as APT_6.
    pose proof (APT _ _ (all_ranges_fixed bt st _ INFS)) as APT_FS.
    fold msz in APT_T, APT_C, APT_6, APT_FS. unfold PG, KSPACE in APT_T, R6b.
    (* [comment removed for export] *)
    assert (BASE : (um = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
                    /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
                   /\ 64513 <= n <= 2 ^ 34 /\ um = mp + 4096 /\ p = um + 2048 /\ msz = asz + 4096 /\ 0 < mp /\ mp + msz <= CEIL
                   /\ 140735332483072 <= CEIL <= 140737479966720 /\ CEIL + 3584 <= U S /\ U S + 16 <= 2 ^ 47 /\ 0 <= U S < 2 ^ 64
                   /\ 4096 <= T /\ T + 4096 <= CEIL /\ 0 < CTX /\ CTX + 65536 <= CEIL /\ 0 <= id < 2 ^ 32
                   /\ n + 4096 <= sec_needed n <= n + 4103 /\ 0x65d000 <= mp).
    { assert (X1 : um = mp + 4096) by reflexivity.
      assert (X2 : mp + msz <= CEIL) by exact SF2.
      assert (X3 : CEIL + 3584 <= U S) by (rewrite CP2; exact CPlo).
      assert (X4 : U S + 16 <= 2 ^ 47) by (rewrite CP2; exact CPhi).
      assert (X5 : T + 4096 <= CEIL) by exact GTC.
      assert (X6 : CTX + 65536 <= CEIL) by exact GCC.
      assert (X7 : 0x65d000 <= mp) by (clear - DY4 SF1 Emsz LIN Hn34; lia).
      split; [exact LIN|]. repeat split; first [assumption | apply Hn34 | apply CR | apply HSr | apply Hid | apply Hsnb]. }
    clear LIN.
    assert (GmT : hideW (um + asz <= T \/ T + 4096 <= um - 4096)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - APT_T BASE; lia).
    assert (Gmctx : hideW (um + asz <= CTX \/ CTX + 4096 <= um - 4096)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - APT_C BASE; lia).
    assert (Grng : hideW (um + asz <= 0x7fff7000 \/ 0x10007fff8000 <= um - 4096)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - DY5 BASE; lia).
    assert (GTband : hideW (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact GTB).
    assert (GTimg : hideW (T + 4096 <= AIMGLO \/ AIMGHI <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact GTI).
    assert (Gctxband : hideW (CTX + 0x10000 <= 0x7fff7000 \/ 0x10007fff8000 <= CTX)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact GCB).
    assert (Dsb : um < SBEG \/ SBEG + 2 ^ 37 <= um) by (clear - APT_6 R6a R6b BASE; lia).
    hidehyp GTB. hidehyp GTI. hidehyp GCB. hidehyp GCI. hidehyp APT_T. hidehyp APT_C. hidehyp APT_6. hidehyp DY4. hidehyp DY5.
    (* [comment removed for export] *)
    assert (NXimg : forall z, 0x10000 <= z < 0x65d000 -> ~ shxl um k r8 a8 z).
    { intros z Hz X. unfold shxl, SB in X. clear - BASE Hz X. lia. }
    assert (NXstk : forall z, CEIL <= z -> ~ shxl um k r8 a8 z).
    { intros z Hz X. unfold shxl, SB in X. clear - BASE Hz X. lia. }
    assert (NXT : forall z, T <= z < T + 4096 -> ~ shxl um k r8 a8 z).
    { intros z Hz X. unfold shxl, SB in X. unfold hideW in GmT, GTband. clear - BASE Hz X GmT GTband. lia. }
    assert (NXctx : forall z, CTX <= z < CTX + 4096 -> ~ shxl um k r8 a8 z).
    { intros z Hz X. unfold shxl, SB in X. unfold hideW in Gmctx, Gctxband. clear - BASE Hz X Gmctx Gctxband. lia. }
    assert (NXmap : forall z, (mp <= z < um \/ um + 16 <= z < um + 2032 \/ um + 2033 <= z < mp + msz) -> ~ shxl um k r8 a8 z).
    { intros z Hz X. unfold shxl, SB in X. unfold hideW in Grng. clear - BASE Hz X Grng. lia. }
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz BASE; lia|]. apply (OBL_nolazy_rt st' L' FF M0 mdl' z W' RP'). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - Hz. tauto. }
    assert (NHmap : forall z, mp <= z < mp + msz -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz BASE; lia|]. exact (rep_nolazy_sec bt st' L' FF M0 mdl' W' RP' (SCH mp n) z HS' Hz). }
    destruct R14 as (Bw1 & Bw2 & _).
    destruct R12 as (_ & _ & SH3 & _ & _ & SH6).
    assert (NHsh : forall z, SB + k <= z < SB + k + a8 -> Hd (Z_to_bv 64 z) = false /\ M0 (Z_to_bv 64 z) <> None).
    { intros z Hz. split.
      - apply HID_allowed. apply RAL. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end). rewrite E7, M8'. clear - Hz BASE. lia.
      - replace z with (SB + (z - SB)) by (clear; lia). apply (SH6 (SCH mp n) (z - SB) HS'). (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_n] in G in change_no_check G' end). fold msz.
        rewrite E7, M8. clear - Hz BASE. lia. }
    set (Mr := mrestrict Hd M').
    assert (DXL : forall a : word, M' a <> M0 a -> shxl um k r8 a8 (U a) /\ M' a <> None).
    { intros a NE. destruct (DX a NE) as [X D]. split; [apply (proj1 (HXL (U a))); exact X | exact D]. }
    assert (EQ0 : forall a : word, ~ shxl um k r8 a8 (U a) -> M' a = M0 a).
    { intros a NX. destruct (decide (M' a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DXL a NE))). }
    assert (GRM : mem_grows M M').
    { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [rewrite E; exact Ha | exact (proj2 (CHG a NE))]. }
    assert (GR0 : mem_grows M0 M').
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|NE]; [rewrite E; exact Ha | exact (proj2 (DX a NE))]. }
    (* [comment removed for export] *)
    assert (XMr : forall (z : Z) (w : nat) bs,
              (forall i, z <= i < z + Z.of_nat w -> ~ shxl um k r8 a8 i /\ Hd (Z_to_bv 64 i) = false) -> 0 <= z -> z + Z.of_nat w < 2 ^ 64 ->
              rdn ASEGS M0 (Z_to_bv 64 z) w = Some bs -> rdn ASEGS Mr (Z_to_bv 64 z) w = Some bs).
    { intros z w bs F Hz Hw Hr. assert (Uz : U (Z_to_bv 64 z) = z) by (apply u_Z2bv; clear - Hz Hw; lia).
      apply (rd_same ASEGS Mr M0); [| rewrite Uz; clear - Hw; lia | exact Hr].
      intros x Hx. rewrite Uz in Hx. destruct (F (U x) Hx) as [NX NHx]. rewrite Z_to_bv_bv_unsigned in NHx.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M' x NHx). apply EQ0. exact NX. }
    (* [comment removed for export] *)
    assert (KIMG : forall c w v, In (c, w, v) (bt_consts bt) -> 0x10000 <= c -> c + Z.of_nat w <= 0x65d000 ->
                     rdn ASEGS Mr (Z_to_bv 64 c) w = Some (word_to_le_bytes w (Z_to_bv 64 v))).
    { intros c w v Hin H1 H2. eapply XMr; [ | | | exact (const_cell bt M0 c w v R1 Hin)];
        [intros i Hi; split; [apply NXimg; clear - Hi H1 H2; lia | apply NHs; clear - Hi H1 H2; lia] | clear - H1; lia | clear - H2; lia]. }
    Ltac kimg KIMG C := refine (KIMG _ _ _ C _ _); clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by (clear; lia); kimg KIMG CELL_inited).
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by kimg KIMG CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by (clear; lia); kimg KIMG CELL_fum).
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by kimg KIMG CELL_mcs.
    assert (K_thr64 : rdn ASEGS Mr (Z_to_bv 64 (0x1990a8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by kimg KIMG CELL_thr64.
    assert (K_kif : rdn ASEGS Mr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by (clear; lia); kimg KIMG CELL_kif).
    assert (K_key : rdn ASEGS Mr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4 : word) by (apply bv_eq; reflexivity). kimg KIMG CELL_key. }
    assert (Utp : U tp = TP) by (rewrite CP4; apply u_Z2bv; clear - Gc8 Gc9; lia).
    assert (K_tsdp : rdn ASEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; f_equal; clear; lia).
      refine (KIMG _ _ _ CELL_tsdp _ _); clear - Gc8 Gc9; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (K_tctx : rdn ASEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by (refine (KIMG _ _ _ CELL_tctx _ _); clear - Gc1 Gc2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    assert (K_gsb : rdn ASEGS Mr (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578))) by kimg KIMG CELL_gsh.
    assert (K_sb : rdn ASEGS Mr (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 SB))).
    { pose proof R17 as Csb. cbn [ia_rtc_sb asan_addrs] in Csb.
      eapply XMr; [ | | | exact Csb]; [intros i Hi; split; [apply NXimg; clear - Hi; cbn in Hi; lia | apply NHs; clear - Hi; cbn in Hi; lia] | clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (K_cpm : rdn ASEGS Mr (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by (clear; lia); kimg KIMG CELL_cpm).
    assert (K_gmb : rdn ASEGS Mr (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268))) by kimg KIMG CELL_gmb.
    assert (K_mb : rdn ASEGS Mr (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0))) by kimg KIMG CELL_mb.
    assert (K_gme : rdn ASEGS Mr (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270))) by kimg KIMG CELL_gme.
    assert (K_me : rdn ASEGS Mr (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by kimg KIMG CELL_me.
    assert (K_ghe : rdn ASEGS Mr (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260))) by kimg KIMG CELL_ghe.
    assert (K_he : rdn ASEGS Mr (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by kimg KIMG CELL_he.
    assert (K_gfl : rdn ASEGS Mr (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL))) by kimg KIMG CELL_gfl.
    assert (UFL : forall d, 0 <= d < 4096 -> at_ (Z_to_bv 64 FL) d = Z_to_bv 64 (FL + d)).
    { intros d Hd0. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). rewrite u_Z2bv by (clear - Gc5 Gc6; lia). reflexivity. }
    assert (K_pp : rdn ASEGS Mr (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1]).
    { rewrite UFL by (clear; lia). rewrite <- (w2b1 1) by (clear; lia). refine (KIMG _ _ _ CELL_pp _ _); clear - Gc5 Gc6; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (K_mfs : rdn ASEGS Mr (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096)).
    { rewrite UFL by (clear; lia). refine (KIMG _ _ _ CELL_mfs _ _); clear - Gc5 Gc6; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (K_fill : rdn ASEGS Mr (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe)).
    { rewrite UFL by (clear; lia). refine (KIMG _ _ _ CELL_fill _ _); clear - Gc5 Gc6; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (K_grm : rdn ASEGS Mr (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0))) by kimg KIMG CELL_grm.
    assert (K_rm : rdn ASEGS Mr (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4))) by kimg KIMG CELL_rm.
    assert (K_glsn : rdn ASEGS Mr (Z_to_bv 64 0xffec8) 8 = Some (LE8 (Z_to_bv 64 0x10))) by kimg KIMG CELL_glsn.
    assert (K_lsn : rdn ASEGS Mr (at_ tp 0x10) 4 = Some (LE4 0)).
    { replace (at_ tp 0x10) with (Z_to_bv 64 (TP + 0x10)) by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; reflexivity).
      refine (KIMG _ _ _ CELL_lsn _ _); clear - Gc8 Gc9; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (K_magic : rdn ASEGS Mr (Z_to_bv 64 0x103b8) 8 = Some (LE8 (Z_to_bv 64 MAGIC))) by kimg KIMG CELL_magic.
    assert (K_hook : rdn ASEGS Mr (Z_to_bv 64 0x199040) 8 = Some (LE8 (Z_to_bv 64 0))) by kimg KIMG CELL_hook.
    assert (K_sbeg : rdn ASEGS Mr (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by kimg KIMG CELL_sbeg.
    assert (K_pg : rdn ASEGS Mr (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096))) by kimg KIMG SCELL_pg.
    (* [comment removed for export] *)
    assert (K_thr : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { assert (Uc : U (Z_to_bv 64 CTX) = CTX) by (apply u_Z2bv; clear - BASE; lia).
      replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Uc; reflexivity).
      eapply XMr; [ | | | exact Tback]; [intros i Hi; split; [apply NXctx; cbn in Hi; clear - Hi; lia | apply NHrt; cbn in Hi; clear - Hi; lia] | clear - BASE; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia]. }
    (* [comment removed for export] *)
    set (m := Z_to_bv 64 um : word) in *.
    assert (Um : U m = um) by ((lazymatch goal with |- ?G => let G' := eval unfold m in G in change_no_check G' end); apply u_Z2bv; clear - BASE; lia).
    assert (ATm : forall d, at_ m d = Z_to_bv 64 (um + d)) by (intros d; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Um; reflexivity).
    (* [comment removed for export] *)
    destruct (In_nth_error _ _ HS') as (isec & Hnth).
    destruct (R7 isec (SCH mp n) Hnth) as (_ & _ & SC16 & _ & SCW). unfold sc_mapsz in SCW. cbn [sc_map sc_n] in SC16, SCW. fold msz in SCW. rewrite BT_segs in SC16, SCW.
    assert (K_sz : rdn ASEGS Mr (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n)))).
    { rewrite ATm. replace (um + -4080) with (mp + 16) by (clear - BASE; lia).
      eapply XMr; [ | | | exact SC16]; [intros i Hi; split; [apply NXmap; cbn in Hi; clear - Hi BASE; lia | apply NHmap; cbn in Hi; clear - Hi BASE; lia] | clear - BASE; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia]. }
    (* [comment removed for export] *)
    Ltac hoffs NH B := apply hid_off_of; intros z Hz; split; [clear - Hz B; lia | apply NH; clear - Hz B; lia].
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite at_u by (clear - BASE; lia); hoffs NHs BASE].
      eapply store_ok_mono; [exact GRM|]. apply store_ok_bytes; [| rewrite at_u by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia].
      intros x Hx. rewrite at_u in Hx by (clear - BASE; lia). apply CPstk. cbn in Hx. rewrite <- CP2. clear - Hx. lia. }
    assert (C_Tdef : forall i, T + 2800 <= i < T + 2912 -> Mr (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by (apply NHrt; clear - Hi; lia). apply GR0. exact (proj1 (TW i ltac:(clear - Hi; lia))). }
    assert (C_Tw : store_ok ASEGS Mr (at_ (Z_to_bv 64 T) 2800) 112 = true).
    { assert (Ut : U (Z_to_bv 64 T) = T) by (apply u_Z2bv; clear - BASE; lia).
      assert (Ut2 : U (Z_to_bv 64 (T + 2800)) = T + 2800) by (apply u_Z2bv; clear - BASE; lia).
      replace (at_ (Z_to_bv 64 T) 2800) with (Z_to_bv 64 (T + 2800)) by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Ut; reflexivity).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Ut2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite Ut2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoffs NHrt BASE].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); rewrite ?Ut2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia. }
    assert (C_chunk : store_ok ASEGS Mr m (Z.to_nat 6144) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoffs NHmap BASE].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ SCW); rewrite ?Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia. }
    assert (A8nn : 0 <= a8) by (clear - BASE; lia).
    assert (C_shw : store_ok ASEGS Mr (Z_to_bv 64 (SB + U m / 8)) (Z.to_nat (sbasz n / 8)) = true).
    { rewrite Um. fold k asz a8.
      assert (Ush : U (Z_to_bv 64 (SB + k)) = SB + k) by (apply u_Z2bv; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); clear - BASE; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Ush, Z2Nat.id by exact A8nn; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); clear - BASE; lia
        | rewrite Ush, Z2Nat.id by exact A8nn; apply hid_off_of; intros z Hz; split; [unfold SB in *; clear - Hz BASE; lia | exact (proj1 (NHsh z Hz))] ].
      apply store_ok_bytes; [| rewrite Ush, Z2Nat.id by exact A8nn; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); clear - BASE; lia]. intros x Hx. rewrite Ush, Z2Nat.id in Hx by exact A8nn.
      apply store_ok1_some. apply GR0. pose proof (proj2 (NHsh (U x) Hx)) as Dx. rewrite Z_to_bv_bv_unsigned in Dx. exact Dx. }
    (* [comment removed for export] *)
    destruct (proj1 R8 p n ltac:(left; reflexivity)) as (HD16 & (b1 & Hb1 & HD15) & _ & _ & _ & HD4 & HDL).
    destruct (HDL ltac:(rewrite Erz; clear; lia)) as [HDL1 HDL2]. clear HDL.
    rewrite BT_segs in HD16, HD15, HD4, HDL1, HDL2.
    assert (A15 : U (Z_to_bv 64 (p - 15)) = p - 15) by (apply u_Z2bv; clear - BASE; lia).
    assert (D15 : M0 (Z_to_bv 64 (p - 15)) = Some (Z_to_bv 8 b1)).
    { pose proof (proj1 (SCW (p - 15) ltac:(clear - BASE; lia))) as Dd. unfold byteZ, cellN in HD15.
      rewrite (w2b1 b1) in HD15 by (clear - Hb1; unfold hdr1_ok in Hb1; lia). cbn [rdn] in HD15.
      destruct (M0 (Z_to_bv 64 (p - 15))) as [y|]; [| exfalso; exact (Dd eq_refl)]. cbn in HD15. injection HD15 as ->. reflexivity. }
    assert (D15' : M' (Z_to_bv 64 (p - 15)) = Some (Z_to_bv 8 b1)).
    { rewrite (EQ0 (Z_to_bv 64 (p - 15))); [exact D15|]. rewrite A15. apply NXmap. clear - BASE. lia. }
    assert (HB2 : Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U (Z_to_bv 8 b1))))) = Z_to_bv 8 b1).
    { clear - Hb1. destruct Hb1 as [-> | ->]; apply bv_eq; vm_compute; reflexivity. }
    assert (K_h1 : rdn ASEGS Mr (at_ m (rz n - 15)) 1 = Some [Z_to_bv 8 b1]).
    { rewrite ATm, Erz. replace (um + (2048 - 15)) with (p - 15) by (clear - BASE; lia).
      apply heap_rdn1; [rewrite A15; clear - BASE; lia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [exact D15'|]. apply NHmap. clear - BASE. lia. }
    (* [comment removed for export] *)
    assert (VISstk : forall x : word, U S - 3584 <= U x < U S -> Mr x = M' x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x) as Hxr; clear - Hxr; lia|]. left. clear - Hx BASE. lia. }
    assert (STK : forall k0 bs (w : nat), -3584 <= k0 -> k0 + Z.of_nat w <= 0 -> rdn ASEGS M' (at_ S k0) w = Some bs -> rdn ASEGS Mr (at_ S k0) w = Some bs).
    { intros k0 bs w Hk1 Hk2 Hr. apply (rd_same ASEGS Mr M'); [| rewrite at_u by (clear - BASE Hk1 Hk2; lia); clear - BASE Hk1 Hk2; lia | exact Hr].
      intros x Hx. rewrite at_u in Hx by (clear - BASE Hk1 Hk2; lia). apply VISstk. clear - Hx Hk1 Hk2. lia. }
    assert (K_fflag : rdn ASEGS Mr (at_ (at_ S (-2272)) 8) 8 = Some (LE8 (Z_to_bv 64 1))).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). apply STK; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia |]. apply SLA. (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). auto 20. }
    assert (K_slots4 : forall (k0 : Z) (v : word),
              In (k0, v) (amE4_slots ARB S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81)) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S) ->
              rdn ASEGS Mr (at_ (at_ S (-2272)) k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. rewrite at_at. unfold amE4_slots in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); apply STK; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia |]; apply SLA; (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20 |]).
      destruct Hin. }
    assert (K_slotsI : forall (k0 : Z) (v : word),
              In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS Mr (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply STK; [clear - Hk; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hk; lia | exact (SLI k0 v Hin)]. }
    (* [comment removed for export] *)
    assert (RETR : ret_ok (getr R 1)) by (fold ra0; rewrite CP1; apply ret_ok_lit; [clear - CPr; lia | exact CPe]).
    assert (GSx : 140735332483072 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0).
    { split; [clear - BASE; lia | split; [clear - BASE; lia | rewrite CP2; exact CP16]]. }
    assert (Gmx : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sbasz n <= U S - 3584 /\ U m + sbasz n + 4096 <= 2 ^ 47).
    { rewrite Um. fold asz. split; [exact UM0|]. assert (X : 4096 <= mp) by (clear - MP0 BASE; Z.div_mod_to_equations; lia). clear - X BASE. lia. }
    destruct (@run_sB fx' Mr (seg_rom ASEGS) R' R S tp m T CTX n id SBEG FL MIDEND TSDP (Z_to_bv 8 b1) x18 x19
                Y2 Y3 Y4 Y8 Y9 Y10 ltac:(rewrite Y18; reflexivity) Y19
                ltac:(rewrite Y20, ATm, Erz; f_equal; clear - BASE; lia) ltac:(rewrite Y21, ATm, Erz; f_equal; clear - BASE; lia) Y22 Y24
                ltac:(rewrite Y25, ATm, Erz; f_equal; clear - BASE; lia) RETR GSx Hn34 Hid Gmx
                ltac:(rewrite Um; exact Grng)
                ltac:(rewrite Um; (lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); fold asz; unfold hide in DY4; clear - DY4 BASE; lia)
                ltac:(clear - SB0 SB1 CR; lia) ltac:(rewrite Um; exact Dsb)
                ltac:(clear - BASE; lia) ltac:(unfold hideW, hide in *; exact GTI) GTband ltac:(rewrite Um; exact GmT)
                ltac:(clear - BASE; lia) Gctxband ltac:(rewrite Um; exact Gmctx)
                ltac:(rewrite Utp; clear - Gc8 Gc9; lia) ltac:(clear - Gc1 Gc2; lia) ltac:(clear - Gc5 Gc6; lia) Gc7 SOKstk
                K_inited K_gcf K_fum K_mcs K_thr64 K_kif K_key K_tsdp K_tctx K_thr K_gsb K_sb K_cpm K_gmb K_mb K_gme K_me K_ghe K_he K_gfl K_pp K_mfs K_fill
                K_grm K_rm K_glsn K_lsn K_magic K_hook K_sbeg K_pg K_sz C_Tdef C_Tw C_chunk C_shw K_h1 K_fflag K_slots4 K_slotsI)
      as (rF & Mf & RUN & REGS & Q_off & Q_gr & Q_ctx & Q_lrz & Q_rrz & Q_z & Q_p & Q_st & Q_h1 & Q_l1 & Q_l2).
    destruct REGS as (F10 & F1 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    (* [comment removed for export] *)
    rewrite Um in Q_off, Q_lrz, Q_rrz, Q_z, Q_p. fold k re asz r8 n8 nm in Q_lrz, Q_rrz, Q_z, Q_p.
    rewrite I1 in Q_rrz. rewrite I4 in Q_z. rewrite I6 in Q_p.
    rewrite ATm, Erz in Q_ctx, Q_st, Q_h1. rewrite ATm in Q_l2. rewrite (ATm (rz n - 16)), Erz in Q_l2.
    change (0 * 2 ^ 32 + id) with id in Q_ctx.
    rewrite HB2 in Q_h1.
    assert (FOOTL : forall z, sb_foot (U S) um T n z -> sbfl (U S) um T k a8 z).
    { intros z F. unfold sb_foot, sb_foot1, sb_foot2 in F. fold asz k in F. rewrite I1 in F. (lazymatch goal with |- ?G => let G' := eval unfold sbfl in G in change_no_check G' end). clear - F. lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st' L' FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x4bed0) M' (seg_rom ASEGS)) (@mkst fx' rF (getr R 1) Mf (seg_rom ASEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HH'. }
    { rewrite restrict_mkst'. exact RUN. }
    clear RUN K_inited K_gcf K_fum K_mcs K_thr64 K_kif K_key K_tsdp K_tctx K_thr K_gsb K_sb K_cpm K_gmb K_mb K_gme K_me K_ghe K_he K_gfl K_pp K_mfs K_fill
          K_grm K_rm K_glsn K_lsn K_magic K_hook K_sbeg K_pg K_sz C_Tdef C_Tw C_chunk C_shw K_h1 K_fflag K_slots4 K_slotsI KIMG XMr.
    intros mdl2 MI2 SBM2 HC2. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x4bed0) M' (seg_rom ASEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl2 SBM2) as SF2'.
    destruct SF2' as (_ & Evm2 & Elz2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh2 & _ & _ & _ & Eeg2).
    set (Mfin := munrestrict Hd M' Mf).
    assert (VIS : forall a : word, Hd a = false -> Mfin a = Mf a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> Mr a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply Q_gr. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    assert (GRfin0 : mem_grows M0 Mfin) by (eapply mem_grows_trans; [exact GR0 | exact GRfin']).
    (* [comment removed for export] *)
    assert (DIFF : forall a : word, Mfin a <> M' a -> Hd a = false /\ sbfl (U S) um T k a8 (U a)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|]. split; [reflexivity|].
      destruct (sbfl_dec (U S) um T k a8 (U a)) as [F|NF]; [exact F|]. exfalso. apply NE.
      rewrite (VIS a Eh). rewrite <- (MrM' a Eh). apply Q_off. intros SF. exact (NF (FOOTL _ SF)). }
    (* [comment removed for export] *)
    assert (AW : forall (a : word) z, U a = z -> a = Z_to_bv 64 z) by (intros a z E; rewrite <- E; symmetry; apply Z_to_bv_bv_unsigned).
    assert (UZ : forall z, 0 <= z <= CEIL + 2 ^ 40 -> U (Z_to_bv 64 z) = z) by (intros z Hz; apply u_Z2bv; clear - Hz CR; lia).
    (* [comment removed for export] *)
    assert (VISmap : forall a : word, mp <= U a < mp + msz -> Mfin a = Mf a).
    { intros a Ha. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHmap. exact Ha. }
    assert (VISsh : forall a : word, SB + k <= U a < SB + k + a8 -> Mfin a = Mf a).
    { intros a Ha. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj1 (NHsh (U a) Ha)). }
    assert (RDfin : forall z (w : nat) bs, mp <= z -> z + Z.of_nat w <= mp + msz -> rdn ASEGS Mf (Z_to_bv 64 z) w = Some bs -> rdn ASEGS Mfin (Z_to_bv 64 z) w = Some bs).
    { intros z w bs H1 H2 Hr. assert (Uz : U (Z_to_bv 64 z) = z) by (apply UZ; clear - H1 H2 BASE; lia).
      apply (rd_same ASEGS Mfin Mf); [| rewrite Uz; clear - H2 BASE; lia | exact Hr]. intros x Hx. rewrite Uz in Hx. apply VISmap. clear - Hx H1 H2. lia. }
    (* [comment removed for export] *)
    assert (PIN : forall a : word, shxl um k r8 a8 (U a) -> Mfin a = M0 a).
    { intros a X. unfold shxl in X. destruct X as [X | [X | [X | X]]].
      - (* [comment removed for export] *) assert (Ea : a = Z_to_bv 64 (um + (2048 - 16))) by (apply AW; clear - X; lia).
        apply (pin_byte Mfin M0 a 2 ltac:(clear; lia)).
        + rewrite VISmap by (clear - X BASE; lia). rewrite Ea. exact Q_st.
        + replace (U a) with (p - 16) by (clear - X BASE; lia). exact HD16.
        + rewrite Ea. apply (proj1 (SCW (um + (2048 - 16)) ltac:(clear - BASE; lia))).
      - (* [comment removed for export] *)
        assert (D0 : M0 a <> None) by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply (proj1 (SCW (U a) ltac:(clear - X BASE; lia)))).
        assert (Df : Mfin a <> None) by (apply GRfin0; exact D0).
        unfold cellZ, cellN in HDL1, HDL2. rewrite Erz in HDL1, HDL2.
        replace (p - 2048) with um in HDL1 by (clear - BASE; lia). replace (p - 2048 + 8) with (um + 8) in HDL2 by (clear - BASE; lia).
        replace (p - 16) with (um + (2048 - 16)) in HDL2 by (clear - BASE; lia).
        destruct (Z_lt_le_dec (U a) (um + 8)) as [Lo | Hi].
        + apply (rdn_pt_eq ASEGS 8 Mfin M0 (Z_to_bv 64 um) _ (RDfin um 8%nat _ ltac:(clear - BASE; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia) Q_l1) HDL1);
            [rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - X Lo; lia | exact Df | exact D0].
        + apply (rdn_pt_eq ASEGS 8 Mfin M0 (Z_to_bv 64 (um + 8)) _ (RDfin (um + 8) 8%nat _ ltac:(clear - BASE; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia) Q_l2) HDL2);
            [rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - X Hi; lia | exact Df | exact D0].
      - (* [comment removed for export] *)
        apply (pin_byte Mfin M0 a 250 ltac:(clear; lia)).
        + rewrite VISsh by (clear - X BASE; lia). apply Q_lrz. exact X.
        + pose proof (SH3 (SCH mp n) (U a - SB) HS') as B3. unfold sc_mapsz, sc_user, user_granule in B3. cbn [sc_map sc_n] in B3. fold msz p in B3.
          rewrite E7, M8, P8, PN8, BT_segs in B3. replace (SB + (U a - SB)) with (U a) in B3 by (clear; lia). apply B3; clear - X BASE; lia.
        + rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (NHsh (U a) ltac:(clear - X BASE; lia))).
      - (* [comment removed for export] *)
        apply (pin_byte Mfin M0 a 250 ltac:(clear; lia)).
        + rewrite VISsh by (clear - X BASE; lia). apply Q_rrz. clear - X. lia.
        + pose proof (SH3 (SCH mp n) (U a - SB) HS') as B3. unfold sc_mapsz, sc_user, user_granule in B3. cbn [sc_map sc_n] in B3. fold msz p in B3.
          rewrite E7, M8, P8, PN8, BT_segs in B3. replace (SB + (U a - SB)) with (U a) in B3 by (clear; lia). apply B3; clear - X BASE; lia.
        + rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (NHsh (U a) ltac:(clear - X BASE; lia))). }
    (* [comment removed for export] *)
    assert (HPsec : is_primary n = false).
    { (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). apply Z.leb_gt. rewrite Erz. pose proof (rounded_ge n) as (Q1 & _). clear - Q1 Hn34. lia. }
    assert (INL : In (p, n) L') by (left; reflexivity).
    assert (REPfin : Rep bt st' L' FF Mfin mdl2).
    { apply (Rep_sbm bt st' L' FF Mfin mdl' mdl2); [| exact MI2 | exact SBM2].
      apply (Rep_frame bt st' L' FF M0 Mfin mdl' W' RP'). intros a NE.
      assert (DEF : Mfin a <> None).
      { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GRfin0 in D. rewrite EF in D. exact (D eq_refl). }
      split; [| exact DEF]. intros RCa.
      assert (NX : ~ shxl um k r8 a8 (U a)) by (intros X; exact (NE (PIN a X))).
      assert (E0 : M' a = M0 a) by (apply EQ0; exact NX).
      assert (N' : Mfin a <> M' a) by (rewrite E0; exact NE).
      destruct (DIFF a N') as [Eh F]. unfold sbfl in F. unfold shxl in NX.
      destruct F as [F | [F | [F | [F | [F | [F | [F | F]]]]]]].
      - (* [comment removed for export] *)
        destruct (Z_lt_le_dec (U a) (um + 2044)) as [Lo | Hi].
        + apply (secgap_vs_rep bt st' L' FF W' p n (U a) INL HPsec ltac:(clear - F Lo BASE; lia) RCa).
        + apply NE. unfold cellZ, cellN in HD4.
          pose proof (RDfin (um + (2048 - 8)) 8%nat _ ltac:(clear - BASE; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia) Q_ctx) as C8.
          pose proof (rdn_skip ASEGS Mfin (Z_to_bv 64 (um + (2048 - 8))) 8 _ 4 C8 ltac:(clear; lia) ltac:(rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia)) as C4.
          rewrite (le8_high_zero id Hid) in C4. change (8 - 4)%nat with 4%nat in C4.
          replace (at_ (Z_to_bv 64 (um + (2048 - 8))) (Z.of_nat 4)) with (Z_to_bv 64 (p - 4)) in C4
            by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite UZ by (clear - BASE; lia); f_equal; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia).
          apply (rdn_pt_eq ASEGS 4 Mfin M0 (Z_to_bv 64 (p - 4)) _ C4 HD4);
            [rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - BASE; lia | rewrite UZ by (clear - BASE; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - F Hi BASE; lia | exact DEF |].
          rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj1 (SCW (U a) ltac:(clear - F BASE; lia))).
      - (* [comment removed for export] *) apply (ceil_not_cells bt st' L' FF W' (U a) ltac:(clear - F BASE; lia) RCa).
      - (* [comment removed for export] *)
        apply (bsh_vs_rep bt st' L' FF W' p n (U a) INL ltac:((lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end); rewrite P8, PN8; clear - F NX BASE; lia) RCa).
      - apply (stats_not_cells bt st' L' FF W' (U a) ltac:(clear - F; lia) RCa).
      - apply (stats_not_cells bt st' L' FF W' (U a) ltac:(clear - F; lia) RCa).
      - (* [comment removed for export] *) apply (blk_vs_rep bt st' L' FF W' p n (U a) INL ltac:(clear - F BASE; lia) RCa).
      - (* [comment removed for export] *)
        assert (Ea : a = Z_to_bv 64 (um + (2048 - 15))) by (apply AW; clear - F NX; lia).
        apply N'. rewrite VISmap by (clear - F BASE; lia). rewrite Ea. rewrite Q_h1. symmetry.
        replace (um + (2048 - 15)) with (p - 15) by (clear - BASE; lia). exact D15'.
      - exfalso. clear - F NX. lia. }
    (* [comment removed for export] *)
    assert (IMGLO : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo asan_addrs] in G in change_no_check G' end); clear; lia).
    assert (PRIVmap : forall z, mp <= z < mp + msz -> rt_priv asan_addrs Lc FF z).
    { intros z Hz. pose proof (sec_live_private bt st' L' FF W' IMGLO [] Lc p n (SCH mp n) z eq_refl HPsec HS' eq_refl eq_refl Hz) as X.
      rewrite BT_ia in X. exact X. }
    assert (PRIVsh : forall z, SB + k <= z < SB + k + a8 -> rt_priv asan_addrs Lc FF z).
    { intros z Hz. assert (MS8 : msz / 8 = a8 + 512) by (rewrite Emsz; clear - BASE; Z.div_mod_to_equations; lia).
      pose proof (sec_live_shadow_private bt st' L' FF W' IMGLO [] Lc p n (SCH mp n) z eq_refl HPsec HS' eq_refl eq_refl) as X.
      unfold sc_mapsz, sh_lo in X. cbn [sc_map sc_n] in X. fold msz in X. rewrite E7, MS8, BT_ia in X. apply X. clear - Hz. lia. }
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv asan_addrs Lc FF z).
    { intros z Hz. pose proof (OBL_rt_private st' L' FF z W' ltac:(left; exact Hz)) as X.
      apply (rt_priv_sub asan_addrs L' Lc FF z); [intros x Hx; right; exact Hx | exact X]. }
    assert (Up : U (at_ m (rz n)) = p) by (rewrite ATm, Erz; rewrite UZ by (clear - BASE; lia); clear - BASE; lia).
    pose proof W' as (_ & _ & _ & _ & (WL1 & WL2 & WL3) & _).
    destruct (WL1 p n INL) as (_ & P16 & PABLK & _). rewrite BT_ia in PABLK.
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold malloc_ok, cfg in G in change_no_check G' end).
    exists fx', rF, Mfin, mdl2, (at_ m (rz n)).
    split; [rewrite <- CP1; reflexivity|].
    split; [exact HFX'|].
    repeat match goal with |- _ /\ _ => split end.
    - (* [comment removed for export] *) apply regs_kept_intro; rewrite ?F2, ?F3, ?F4, ?F8, ?F9, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F24, ?F25, ?F26, ?F27; try reflexivity;
      (lazymatch goal with |- ?G => let G' := eval unfold tp in G in change_no_check G' end); reflexivity.
    - exact F10.
    - rewrite Up. exact P16.
    - (* [comment removed for export] *) rewrite Up. exact PABLK.
    - intros _. rewrite Up. rewrite Ep. (lazymatch goal with |- ?G => let G' := eval unfold um in G in change_no_check G' end). clear - MP0. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *) intros b mm Hin. rewrite Up.
      assert (NEb : (p, n) <> (b, mm)).
      { intros E. apply NoDup_cons_iff in WL2. apply (proj1 WL2). rewrite E. exact Hin. }
      destruct (WL3 p n b mm INL ltac:(right; exact Hin) NEb) as [D|D]; [left; exact D | right; exact D].
    - (* [comment removed for export] *) intros f kk Hin. rewrite Up.
      pose proof (fake_frame_facts bt st Lc FF W0 f kk Hin) as (Ff1 & Ff2 & _). unfold FAKE_SIZE in *.
      clear - Ff1 Ff2 APT_FS BASE. lia.
    - (* [comment removed for export] *) intros a Ha. rewrite Up in Ha.
      assert (D9 : Mfin a <> None).
      { apply GRfin0. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj1 (SCW (U a) ltac:(clear - Ha BASE; lia))). }
      split; [exact D9 | apply store_ok1_some; exact D9].
    - (* [comment removed for export] *) intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Up, P8. fold n8 in Hi.
      assert (Ux : U (Z_to_bv 64 (SB + (k + 256) + i)) = SB + (k + 256) + i) by (apply UZ; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); clear - Hi BASE; lia).
      rewrite VISsh by (rewrite Ux; clear - Hi BASE; lia). apply Q_z. rewrite Ux. clear - Hi. lia.
    - (* [comment removed for export] *) intros Hm8. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Up, P8. fold n8 nm. fold nm in Hm8.
      assert (Ux : U (Z_to_bv 64 (SB + (k + 256) + n8)) = SB + (k + 256) + n8) by (apply UZ; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); clear - BASE; lia).
      assert (ER8 : r8 = k + 256 + n8 + 1) by (unfold hideW in HNZ; exact (HNZ Hm8)).
      rewrite VISsh by (rewrite Ux; clear - ER8 BASE; lia).
      replace (SB + (k + 256) + n8) with (SB + (k + 256 + n8)) by (clear; lia). exact (Q_p Hm8).
    - (* [comment removed for export] *) intros a Ha. unfold sh_lo, sh_hi in Ha. rewrite Up, P8, PN8 in Ha.
      apply store_ok1_some. apply GRfin0. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (NHsh (U a) ltac:(clear - Ha BASE; lia))).
    - (* [comment removed for export] *)
      intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
      destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|X]] _].
        - left. rewrite <- CP2. exact X.
        - right; left. exact X.
        - right; right; left. exact X. }
      destruct (DIFF a N) as [_ F]. unfold sbfl in F.
      destruct F as [F | [F | [F | [F | [F | [F | [F | F]]]]]]].
      + right; left. apply PRIVmap. clear - F BASE. lia.
      + left. rewrite <- CP2. clear - F. lia.
      + right; left. apply PRIVsh. exact F.
      + right; left. apply PRIVT. clear - F. lia.
      + right; left. apply PRIVT. clear - F. lia.
      + right; left. apply PRIVmap. clear - F BASE. lia.
      + right; left. apply PRIVmap. clear - F BASE. lia.
      + right; left. apply PRIVmap. clear - F BASE. lia.
    - (* [comment removed for export] *)
      intros a _ D. exact (GRfin a D).
    - (* [comment removed for export] *)
      intros a Ha. split.
      + apply GRfin. apply store_ok1_heap; [clear - Ha CPlo CR; lia|]. apply CPstk. exact Ha.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. exact Ha.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold AAINVP in G in change_no_check G' end). exists st'. rewrite Up.
      split; [exact W' | split; [exact REPfin | split; [split | exact (model_ivs_wf_sbm mdl' mdl2 SBM2 MW')]]].
      + (* [comment removed for export] *)
        unfold bounds in BD |- *. (lazymatch goal with |- ?G => let G' := eval unfold L' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [PHI length snd] in G in change_no_check G' end).
        replace (a_kact st') with (a_kact st + EVT) by reflexivity.                 (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold kcost_malloc in G in change_no_check G' end). destruct BD as (BDa & BDb & BDc). rewrite Nat2Z.inj_succ.
        clear - BDa BDb BDc Hn34. (lazymatch goal with |- ?G => let G' := eval unfold MBLK, EVT in G in change_no_check G' end). lia.
      + (* [comment removed for export] *)
        apply HCL; [intros c; split; reflexivity | reflexivity].
    - eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM2].
    - intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz2; reflexivity|]. apply LZ. exact Ha.
    - rewrite Eh2. exact HH'.
  Qed.
End TOPSB.
