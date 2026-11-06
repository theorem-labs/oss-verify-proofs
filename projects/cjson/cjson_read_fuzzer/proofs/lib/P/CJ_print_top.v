(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaSplit.
Module CJ_pv_lit.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBS mm b l o := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 dep);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).
  (* [comment removed for export] *)
  Definition pv_ctx (mm : word -> option byte) (mo : Model) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (errv : word)
      (LB : list cblock) (buf len off : Z) (bs : list byte) : Prop :=
    LHEAP HI SPB LB mm mo /\ Permutation ((buf, len) :: LR) LB /\ PBS mm buf len off /\ u8arr psegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off dep /\ PVFRAME mm loc /\ stk psegs mm lo SPF /\ rw_cells psegs mm PERRNO [C4 errv] /\ mem_inv psegs mm /\ CJST mm
    /\ frm0 fcc /\ FAG18 F Fc /\ pv_agree LR (bv_unsigned sp) PB m mm /\ cj_chain CJ_PRINTABLE mm n p B.

  Ltac open_ctx CTX :=
    (nelim CTX 15%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA CH);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    (nelimp PL 3%nat; intros PL1 PL2 PL3); pose proof PN as PNc; (nelim PN 3%nat; intros PN1 PN2 PN3); unfold PERRNO in ERR;
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.

  (* [comment removed for export] *)
  Lemma pv_false_write : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs -> off + 7 <= len ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x137d4) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX ROOM. open_ctx CTX.
    pose proof (munch_refl [(buf + off, buf + off + 7)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep.
    do 5 step.
    ustore_at buf off (buf + off + 4) 4 (wb 101) ltac:(reflexivity).
    ustore_at buf off (buf + off + 5) 5 (wb 0) ltac:(reflexivity).
    ustore_at buf off (buf + off) 0 (wb 102) ltac:(reflexivity).
    ustore_at buf off (buf + off + 1) 1 (wb 97) ltac:(reflexivity).
    ustore_at buf off (buf + off + 2) 2 (wb 108) ltac:(reflexivity).
    ustore_at buf off (buf + off + 3) 3 (wb 115) ltac:(reflexivity).
    step.
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | exact PNc|].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|exact I].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D]. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor].
      do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - exists 5. split; [lia|]. split; [lia|]. rewrite ?nth_error_upd_other by lia. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_false : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13164) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as CTX0. open_ctx CTX.
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    assert (LO' : lo <= bv_unsigned sp - PV_STACK n) by (unfold PV_STACK, PV_BASE; lia).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. step. zstep. zstep. if_cases Koff; zify_cond Koff.
    { apply evt_done. cbv beta.
      eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]]. }
    zstep. zstep. if_cases Kroom; zify_cond Kroom.
    { apply evt_done. cbv beta. eapply pv_false_write with (len := len); [exact CTX0| lia]. }
    step. step. if_cases Kna; zify_cond Kna; [exfalso; apply Kna; reflexivity|]. clear Kna.
    (* [comment removed for export] *)
    assert (GROW : forall ns x11',
      off + 7 <= ns < 2^31 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 ns) (Z_to_bv 64 buf) x11' (Z_to_bv 64 len) (Z_to_bv 64 (len + -1)) x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x1368c) fcc None mm (seg_rom psegs))).
    { intros ns x11' NS.
      step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
      step. step.
      replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 RES)
.
      rewrite E1 in ST2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x1369c)) with (Z_to_bv 64 0x1369c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RES as [(-> & HL2 & PR2) | (B' & junk & -> & CR & HB & HL2 & PR2 & BLK)].
      - rewrite E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HP| right; apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
        step. apply evt_done. cbv beta.
        eapply pv_fail_free; [split; [exact PL1| split; [exact PL2| exact PL3]]| exact CEIL'| exact LO'| exact TP| exact SPhi| exact N1| exact FR| exact ST2| exact MI2| exact ERR2| exact CJ| exact FRM| exact FA| exact PVA2| exact CH2| exact BLR| exact HL2| exact HP| exact PBS0].
      - rewrite E1 in PR2. unfold wz.
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HPr| apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
        clear PVA PR2 MI ST ERR HL ARR CH.
        rewrite (Z.min_l len ns) in BLK by lia.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
        assert (HP2 : Permutation ((B', ns) :: LR) ((B', ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        step. step. step.
        apply evt_done. cbv beta.
        eapply pv_false_write with (buf := B') (len := ns); [| lia].
        split. { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
        split; [exact HP2|]. split; [exact PBS0|]. split; [exact ARR2|]. split; [rewrite length_app, La, Lb; lia|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FR|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split.
        { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia. }
        split; [exact FRM|]. split; [exact FA|]. split.
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia]. }
        eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
        intros A' n' Hin. (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
        try rewrite alloc_ceiling_eq in Q. cbn. lia. }
    zstep. zstep. if_cases K30; zify_cond K30.
    - zstep. apply GROW. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
    - zstep. zstep. if_cases K31; zify_cond K31.
      + apply evt_done. cbv beta.
        eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]].
      + step. step. step. apply GROW. rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_true_write : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs -> off + 6 <= len ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13768) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX ROOM. open_ctx CTX.
    pose proof (munch_refl [(buf + off, buf + off + 6)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep.
    ustore_at buf off (buf + off + 4) 4 (wb 0) ltac:(reflexivity).
    do 4 step.
    ustore_at buf off (buf + off) 0 (wb 116) ltac:(reflexivity).
    ustore_at buf off (buf + off + 1) 1 (wb 114) ltac:(reflexivity).
    ustore_at buf off (buf + off + 2) 2 (wb 117) ltac:(reflexivity).
    ustore_at buf off (buf + off + 3) 3 (wb 101) ltac:(reflexivity).
    step.
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | exact PNc|].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|exact I].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D]. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor].
      do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - exists 4. split; [lia|]. split; [lia|]. rewrite ?nth_error_upd_other by lia. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_true : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13424) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as CTX0. open_ctx CTX.
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    assert (LO' : lo <= bv_unsigned sp - PV_STACK n) by (unfold PV_STACK, PV_BASE; lia).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. step. zstep. zstep. if_cases Koff; zify_cond Koff.
    { apply evt_done. cbv beta.
      eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]]. }
    zstep. zstep. if_cases Kroom; zify_cond Kroom.
    { apply evt_done. cbv beta. eapply pv_true_write with (len := len); [exact CTX0| lia]. }
    step. step. if_cases Kna; zify_cond Kna; [exfalso; apply Kna; reflexivity|]. clear Kna.
    (* [comment removed for export] *)
    assert (GROW : forall ns x11',
      off + 6 <= ns < 2^31 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 ns) (Z_to_bv 64 buf) x11' (Z_to_bv 64 len) (Z_to_bv 64 (len + -1)) x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x13670) fcc None mm (seg_rom psegs))).
    { intros ns x11' NS.
      step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
      step. step.
      replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 RES)
.
      rewrite E1 in ST2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x13680)) with (Z_to_bv 64 0x13680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RES as [(-> & HL2 & PR2) | (B' & junk & -> & CR & HB & HL2 & PR2 & BLK)].
      - rewrite E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HP| right; apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
        step. apply evt_done. cbv beta.
        eapply pv_fail_free; [split; [exact PL1| split; [exact PL2| exact PL3]]| exact CEIL'| exact LO'| exact TP| exact SPhi| exact N1| exact FR| exact ST2| exact MI2| exact ERR2| exact CJ| exact FRM| exact FA| exact PVA2| exact CH2| exact BLR| exact HL2| exact HP| exact PBS0].
      - rewrite E1 in PR2. unfold wz.
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HPr| apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
        clear PVA PR2 MI ST ERR HL ARR CH.
        rewrite (Z.min_l len ns) in BLK by lia.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
        assert (HP2 : Permutation ((B', ns) :: LR) ((B', ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        step. step. step.
        apply evt_done. cbv beta.
        eapply pv_true_write with (buf := B') (len := ns); [| lia].
        split. { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
        split; [exact HP2|]. split; [exact PBS0|]. split; [exact ARR2|]. split; [rewrite length_app, La, Lb; lia|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FR|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split.
        { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia. }
        split; [exact FRM|]. split; [exact FA|]. split.
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia]. }
        eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
        intros A' n' Hin. (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
        try rewrite alloc_ceiling_eq in Q. cbn. lia. }
    zstep. zstep. if_cases K30; zify_cond K30.
    - zstep. apply GROW. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
    - zstep. zstep. if_cases K31; zify_cond K31.
      + apply evt_done. cbv beta.
        eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]].
      + step. step. step. apply GROW. rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_null_write : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs -> off + 6 <= len ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13700) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX ROOM. open_ctx CTX.
    pose proof (munch_refl [(buf + off, buf + off + 6)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep.
    ustore_at buf off (buf + off + 4) 4 (wb 0) ltac:(reflexivity).
    do 3 step.
    ustore_at buf off (buf + off) 0 (wb 110) ltac:(reflexivity).
    ustore_at buf off (buf + off + 1) 1 (wb 117) ltac:(reflexivity).
    ustore_at buf off (buf + off + 2) 2 (wb 108) ltac:(reflexivity).
    ustore_at buf off (buf + off + 3) 3 (wb 108) ltac:(reflexivity).
    step.
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | exact PNc|].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|exact I].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CH| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D]. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor].
      do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - exists 4. split; [lia|]. split; [lia|]. rewrite ?nth_error_upd_other by lia. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_null : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    pv_ctx mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13390) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as CTX0. open_ctx CTX.
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    assert (LO' : lo <= bv_unsigned sp - PV_STACK n) by (unfold PV_STACK, PV_BASE; lia).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. step. zstep. zstep. if_cases Koff; zify_cond Koff.
    { apply evt_done. cbv beta.
      eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]]. }
    zstep. zstep. if_cases Kroom; zify_cond Kroom.
    { apply evt_done. cbv beta. eapply pv_null_write with (len := len); [exact CTX0| lia]. }
    step. step. if_cases Kna; zify_cond Kna; [exfalso; apply Kna; reflexivity|]. clear Kna.
    (* [comment removed for export] *)
    assert (GROW : forall ns x11',
      off + 6 <= ns < 2^31 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 ns) (Z_to_bv 64 buf) x11' (Z_to_bv 64 len) (Z_to_bv 64 (len + -1)) x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x13654) fcc None mm (seg_rom psegs))).
    { intros ns x11' NS.
      step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
      step. step.
      replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 RES)
.
      rewrite E1 in ST2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x13664)) with (Z_to_bv 64 0x13664) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RES as [(-> & HL2 & PR2) | (B' & junk & -> & CR & HB & HL2 & PR2 & BLK)].
      - rewrite E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HP| right; apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
        step. apply evt_done. cbv beta.
        eapply pv_fail_free; [split; [exact PL1| split; [exact PL2| exact PL3]]| exact CEIL'| exact LO'| exact TP| exact SPhi| exact N1| exact FR| exact ST2| exact MI2| exact ERR2| exact CJ| exact FRM| exact FA| exact PVA2| exact CH2| exact BLR| exact HL2| exact HP| exact PBS0].
      - rewrite E1 in PR2. unfold wz.
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CH) in PR2 as CH2. 2:{ intros b Hb. eapply Permutation_in; [exact HPr| apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
        clear PVA PR2 MI ST ERR HL ARR CH.
        rewrite (Z.min_l len ns) in BLK by lia.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
        assert (HP2 : Permutation ((B', ns) :: LR) ((B', ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        step. step. step.
        apply evt_done. cbv beta.
        eapply pv_null_write with (buf := B') (len := ns); [| lia].
        split. { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
        split; [exact HP2|]. split; [exact PBS0|]. split; [exact ARR2|]. split; [rewrite length_app, La, Lb; lia|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FR|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split.
        { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia. }
        split; [exact FRM|]. split; [exact FA|]. split.
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia]. }
        eapply cj_chain_frame; [exact CH2| exact MU| exact WM|].
        intros A' n' Hin. (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
        try rewrite alloc_ceiling_eq in Q. cbn. lia. }
    zstep. zstep. if_cases K30; zify_cond K30.
    - zstep. apply GROW. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
    - zstep. zstep. if_cases K31; zify_cond K31.
      + apply evt_done. cbv beta.
        eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CH| exact HL| exact PBS0| right; split; [lia| exact HP]].
      + step. step. step. apply GROW. rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_lit.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_update.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
Module CJ_pv_numA.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS ?R ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F "REGS" R;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma disjoint_from_forall : forall (W : list (Z * Z)) A k,
  (forall iv, In iv W -> A + k <= fst iv \/ snd iv <= A) -> disjoint_from W A k.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros A k HW; cbn; [exact I|]. split.
  - exact (HW (lo1, hi1) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply HW. right; exact Hiv.
Qed.

Lemma outside_forall : forall (W : list (Z * Z)) a,
  (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros a HW; cbn; [exact I|]. split.
  - exact (HW (lo1, hi1) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply HW. right; exact Hiv.
Qed.

Lemma Forall_forall_W : forall (P : Z * Z -> Prop) (W : list (Z * Z)),
  (forall iv, In iv W -> P iv) -> Forall P W.
Proof. intros P W H. apply Forall_forall. exact H. Qed.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).

  (* [comment removed for export] *)
  Definition PJ0 (mm : word -> option byte) (j0 : list byte) : Prop := rw_cells psegs mm (bv_unsigned sp + -128) [CB 8 j0].
  Definition PTST (mm : word -> option byte) (t : word) : Prop := rw_cells psegs mm (bv_unsigned sp + -120) [C8 t].
  Definition PTXT (mm : word -> option byte) (tx : list byte) : Prop := rw_cells psegs mm (bv_unsigned sp + -112) [CB 32 tx].
  Definition PFH (mm : word -> option byte) : Prop :=
    rw_cells psegs mm (bv_unsigned sp + -80)
      [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition NCTX (depc : Z) (mm : word -> option byte) (mo : Model) (errv : word)
      (LB : list cblock) (buf len off : Z) (bs : list byte) : Prop :=
    LHEAP HI SPB LB mm mo /\ Permutation ((buf, len) :: LR) LB /\ PBSd mm buf len off depc /\ u8arr psegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off depc /\ stk psegs mm lo SPF /\ rw_cells psegs mm PERRNO [C4 errv] /\ mem_inv psegs mm /\ CJST mm
    /\ pv_agree LR (bv_unsigned sp) PB m mm.

  Lemma pieces_join : forall mm j0 t tx,
    PJ0 mm j0 -> PTST mm t -> PTXT mm tx -> PFH mm -> PVFRAME mm (j0 ++ le8 t ++ tx).
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm j0 t tx H0 H1 H2 H3.
    assert (L0 : length j0 = 8%nat) by (destruct H0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    unfold PJ0, PTST, PTXT, PFH in *.
    assert (H1' : rw_cells psegs mm (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 8 j0])) [C8 t]).
    { replace (bv_unsigned sp + -128 + Z.of_nat (cells_size [CB 8 j0])) with (bv_unsigned sp + -120) by (cbn [cells_size csize Nat.add]; lia). exact H1. }
    pose proof (proj2 (F_fwritex.rw_cells_app _ _ _ _ _) (conj H0 H1')) as J1.
    assert (H2' : rw_cells psegs mm (bv_unsigned sp + -128 + Z.of_nat (cells_size ([CB 8 j0] ++ [C8 t]))) [CB 32 tx]).
    { replace (bv_unsigned sp + -128 + Z.of_nat (cells_size ([CB 8 j0] ++ [C8 t]))) with (bv_unsigned sp + -112) by (cbn [cells_size csize Nat.add app]; lia). exact H2. }
    pose proof (proj2 (F_fwritex.rw_cells_app _ _ _ _ _) (conj J1 H2')) as J2.
    assert (H3' : rw_cells psegs mm (bv_unsigned sp + -128 + Z.of_nat (cells_size (([CB 8 j0] ++ [C8 t]) ++ [CB 32 tx])))
                    [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { replace (bv_unsigned sp + -128 + Z.of_nat (cells_size (([CB 8 j0] ++ [C8 t]) ++ [CB 32 tx]))) with (bv_unsigned sp + -80) by (cbn [cells_size csize Nat.add app]; lia). exact H3. }
    pose proof (proj2 (F_fwritex.rw_cells_app _ _ _ _ _) (conj J2 H3')) as J3.
    cbn [app] in J3.
    change (CB 8 j0 :: C8 t :: CB 32 tx :: ?rest) with ([] ++ [CB 8 j0; C8 t; CB 32 tx] ++ rest) in J3.
    pose proof (rw_cells_merge _ _ _ [] [CB 8 j0; C8 t; CB 32 tx] _ J3) as J.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in J. rewrite app_nil_r in J.
    exact J.
  Qed.

  Lemma pieces_split : forall mm j0 t tx,
    PVFRAME mm (j0 ++ le8 t ++ tx) -> length j0 = 8%nat -> length tx = 32%nat ->
    PJ0 mm j0 /\ PTST mm t /\ PTXT mm tx /\ PFH mm.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm j0 t tx FR L0 LTX.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 32]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    rewrite firstn_app, L0, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in FR by lia.
    rewrite skipn_app, L0, Nat.sub_diag, skipn_O, skipn_all2 in FR by lia. cbn [app] in FR.
    rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in FR by (rewrite length_le8; lia).
    rewrite skipn_app, length_le8, Nat.sub_diag, skipn_O, skipn_all2 in FR by (rewrite length_le8; lia). cbn [app] in FR.
    rewrite firstn_all2 in FR by lia.
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [CB 8 j0] _)) in FR. destruct FR as [H0 FR].
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [CB 8 (le8 t)] _)) in FR. destruct FR as [H1 FR].
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [CB 32 tx] _)) in FR. destruct FR as [H2 H3].
    cbn [cells_size csize Nat.add] in H1, H2, H3.
    replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in H1 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -112) in H2 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -80) in H3 by lia.
    split; [exact H0|]. split; [| split; [exact H2| exact H3]].
    unfold PTST. destruct H1 as [[Hwf HB] HW]. split; [split; [cbn; split; exact I| exact HB]| exact HW].
  Qed.

  Lemma nctx_actx : forall depc mm mo Fc fcc errv LB buf len off bs loc,
    NCTX depc mm mo errv LB buf len off bs -> PVFRAME mm loc -> frm0 fcc -> FAG18 F Fc -> ACTX depc mm mo loc Fc fcc errv LB buf len off bs.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until loc. intros (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA) FR FRM FA.
    split; [exact HL|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
    split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ|]. split; [exact FRM|]. split; [exact FA| exact PVA].
  Qed.

  Lemma actx_nctx : forall depc mm mo Fc fcc errv LB buf len off bs loc,
    ACTX depc mm mo loc Fc fcc errv LB buf len off bs -> NCTX depc mm mo errv LB buf len off bs /\ PVFRAME mm loc /\ frm0 fcc /\ FAG18 F Fc.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until loc. intros nelH_; (nelim nelH_ 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    split; [| split; [exact FR| split; [exact FRM| exact FA]]].
    split; [exact HL|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
    split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ| exact PVA].
  Qed.

  Lemma nctx_err : forall depc mm mo errv LB buf len off bs,
    NCTX depc mm mo errv LB buf len off bs -> rw_cells psegs mm PERRNO [C4 errv].
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0. intros until bs. intros nelH_; (nelim nelH_ 9%nat; intros _ _ _ _ _ _ _ ERR _). exact ERR. Qed.

  Lemma nctx_heap : forall depc mm mo errv LB buf len off bs,
    NCTX depc mm mo errv LB buf len off bs -> LHEAP HI SPB LB mm mo.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0. intros until bs. intros (HL & _). exact HL. Qed.

  (* [comment removed for export] *)
  Lemma nctx_call : forall depc mm mm' mo errv errv' LB buf len off bs (W : list (Z * Z)),
    NCTX depc mm mo errv LB buf len off bs ->
    munch W mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' -> stk psegs mm' lo SPF ->
    rw_cells psegs mm' PERRNO [C4 errv'] ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SPF + 48) \/ iv = (PERRNO, PERRNO + 4)) ->
    NCTX depc mm' mo errv' LB buf len off bs.
  Proof using PL CEIL LO. clear TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until W. intros (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA) MU WM MI' ST' ERR' HW.
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 3%nat; intros PL1 PL2 PL3).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    assert (DJ : forall A k, (A + k <= lo \/ SPF + 48 <= A) -> (A + k <= PERRNO \/ PERRNO + 4 <= A) -> disjoint_from W A k).
    { intros A k H1 H2. apply disjoint_from_forall. intros iv Hiv. destruct (HW iv Hiv) as [[X1 X2]| ->]; cbn [fst snd] in *; lia. }
    unfold PERRNO in DJ.
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. apply Forall_forall_W. intros [lo1 hi1] Hiv.
             destruct (HW _ Hiv) as [[X1 X2]|E]; [| inversion E; subst]; cbn [fst snd] in *.
             - right; left. cbn [fst snd]. try rewrite alloc_ceiling_eq. lia.
             - right; right; left. cbn [fst snd]. lia. }
    split; [exact HP|].
    split. { eapply rw_cells_transport; [exact PBS0| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply u8arr_transport; [exact ARR| exact MU| exact WM|]. apply DJ; lia. }
    split; [exact LEN|]. split; [exact PN|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { destruct CJ as (CJa & (ge1 & ge2 & CJb) & CJc).
             split; [| split; [exists ge1, ge2|]];
               (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; unfold PHOOKS, PGERROR, PLCONV; cbn [cells_size csize Nat.add]; lia]). }
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha [Hc Hn]. apply outside_forall. intros iv Hiv. destruct (HW iv Hiv) as [[X1 X2]| ->]; cbn [fst snd]; unfold PERRNO.
    - destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ Q _).
      try rewrite alloc_ceiling_eq in Q. lia.
    - destruct Hc as [Hs|[[Hd Hns]|(A' & n' & Hin & Hr)]]; [lia| | ].
      + intros X. apply Hns. unfold palloc_static, PERRNO. lia.
      + (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ Q Q5).
        try rewrite alloc_ceiling_eq in Q. unfold PIMG_LO, PIMG_HI in Q5. lia.
  Qed.

  Ltac open_actx CTX :=
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    (nelimp PL 3%nat; intros PL1 PL2 PL3); pose proof PN as PNc; (nelim PN 3%nat; intros PN1 PN2 PN3); unfold PERRNO in ERR;
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.
  Ltac tree_now CTX CHn := assert (CHn : cj_chain CJ_PRINTABLE _ n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).

  (* [comment removed for export] *)
  Lemma num_T : forall mm mo loc Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs -> 0 <= r -> off + r + 2 <= len ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 (Z_to_bv 64 (buf + off + r)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x135ec) fcc None mm (seg_rom psegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX R0 ROOM. tree_now CTX CHn. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    ustore_at buf off (buf + off + r) r (wb 0) ltac:(reflexivity).
    step. zstep. step. step.
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | |].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; unfold PDATA_LO, PIMG_HI; lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CHn| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
      try rewrite alloc_ceiling_eq in Q. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor; [|constructor]].
      + do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
      + right; left. cbn. lia.
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - split; [lia| split; [exact PN2| exact DEP0]].
    - exists 0. split; [lia|]. split; [lia|]. replace (off + r + 0) with (off + r) by lia. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tx_read : forall mm (tx : list byte) (i : Z),
    bytes_at psegs mm (bv_unsigned sp + -112) tx -> length tx = 32%nat -> 0 <= i < 32 ->
    exists b : byte, ov_read_bytes psegs mm (wa (bv_unsigned sp + -112 + i)) 1 = Some [b].
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm tx i TX LTX Hi.
    destruct (nth_error tx (Z.to_nat i)) as [b|] eqn:E.
    - exists b. eapply u8ro_read; [exact TX| exact E| lia| reflexivity].
    - exfalso. apply nth_error_None in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma num_loop : forall (r : Z) (tx : list byte) (m0 : word -> option byte) (buf off len : Z) (Fc : bvmap 5 word) (fcc : bv 32)
      x1 x5 x6 x7 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 (k : nat) (i : Z) mm (bsi : list byte) x13 (a0v a2v : Z),
    a0v = buf + off + i -> a2v = bv_unsigned sp + -112 + i ->
    (Z.to_nat (r - i) <= k)%nat -> 0 <= i < r -> r <= 32 -> length tx = 32%nat ->
    0 <= off -> off + r + 2 <= len -> cblock_range buf len ->
    u8arr psegs mm buf bsi -> Z.of_nat (length bsi) = len -> bytes_at psegs mm (bv_unsigned sp + -112) tx -> mem_inv psegs mm ->
    munch [(buf + off, buf + off + r)] m0 mm -> wmono psegs m0 mm ->
    evt psegs (fun ms' => exists mm' bs' x12' x13',
        ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + r)) (Z_to_bv 64 (buf + off + r)) x12' x13' x14 x15 x16 x17
                     x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                Fc (Z_to_bv 64 0x135ec) fcc None mm' (seg_rom psegs)
        /\ u8arr psegs mm' buf bs' /\ Z.of_nat (length bs') = len /\ bytes_at psegs mm' (bv_unsigned sp + -112) tx /\ mem_inv psegs mm'
        /\ munch [(buf + off, buf + off + r)] m0 mm' /\ wmono psegs m0 mm')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 a0v) (Z_to_bv 64 (buf + off + r)) (Z_to_bv 64 a2v) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x135dc) fcc None mm (seg_rom psegs)).
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until fcc. intros x1 x5 x6 x7 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31.
    induction k as [|k IH]; intros i mm bsi x13 a0v a2v -> -> Hk Hi Hr LTX OFF ROOM CR ARR LEN TX MI MU WM; [exfalso; lia|].
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelim CR 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    (* [comment removed for export] *)
    assert (STORE : forall v : Z, 0 <= v < 256 ->
      evt psegs (fun ms' => exists mm' bs' x12' x13',
        ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + r)) (Z_to_bv 64 (buf + off + r)) x12' x13' x14 x15 x16 x17
                     x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                Fc (Z_to_bv 64 0x135ec) fcc None mm' (seg_rom psegs)
        /\ u8arr psegs mm' buf bs' /\ Z.of_nat (length bs') = len /\ bytes_at psegs mm' (bv_unsigned sp + -112) tx /\ mem_inv psegs mm'
        /\ munch [(buf + off, buf + off + r)] m0 mm' /\ wmono psegs m0 mm')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + i)) (Z_to_bv 64 (buf + off + r)) (Z_to_bv 64 (bv_unsigned sp + -112 + i)) (Z_to_bv 64 v) x14 x15 x16 x17
               x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x135cc) fcc None mm (seg_rom psegs))).
    { intros v Hv.
      ustore_at buf off (buf + off + i) i (wb v) ltac:(symmetry; apply le1_lit8; lia).
      zstep. zstep. step. if_cases Ke; zify_cond Ke.
      - apply evt_done. replace (buf + off + i + 1) with (buf + off + r) by lia. nexists 4%nat. split; [reflexivity|].
        split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact TX|]. split; [exact MI|]. split; [exact MU| exact WM].
      - eapply (IH (i + 1)); [lia| lia| lia| lia| exact Hr| exact LTX| exact OFF| exact ROOM| | exact ARR| rewrite upd_length; exact LEN| exact TX| exact MI| exact MU| exact WM].
        split; [lia|]. split; [exact R2|]. split; [lia|]. split; [try rewrite alloc_ceiling_eq; lia| unfold PIMG_LO, PIMG_HI; lia]. }
    destruct (tx_read mm tx i TX LTX ltac:(lia)) as [b RD].
    pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
    step. step. if_cases Kd; zify_cond Kd.
    - apply STORE. lia.
    - step. step. apply STORE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma actx_block_write : forall depc mm mm' mo loc Fc fcc errv LB buf len off bs bs' (a b : Z),
    ACTX depc mm mo loc Fc fcc errv LB buf len off bs ->
    munch [(a, b)] mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
    u8arr psegs mm' buf bs' -> Z.of_nat (length bs') = len -> buf <= a -> b <= buf + len ->
    ACTX depc mm' mo loc Fc fcc errv LB buf len off bs'.
  Proof using PL CEIL LO. clear TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until b. intros CTX MU WM MI' ARR' LEN' A0 Bl.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 3%nat; intros PL1 PL2 PL3).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor].
             do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia]. }
    split; [exact HP|].
    split. { eapply rw_cells_transport; [exact PBS0| exact MU| exact WM|]. cbn. lia. }
    split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN|].
    split. { eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia. }
    split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold PERRNO. cbn. lia. }
    split; [exact MI'|].
    split. { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]; inversion E1; subst; unfold PDATA_LO, PIMG_HI; lia. }
    split; [exact FRM|]. split; [exact FA|].
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros x Hx [Hc Hn]. cbn [outside]. split; [| exact I].
    destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_tx : forall mm j0 t tx,
    PVFRAME mm (j0 ++ le8 t ++ tx) -> length j0 = 8%nat -> length tx = 32%nat ->
    bytes_at psegs mm (bv_unsigned sp + -112) tx.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm j0 t tx FR L0 LTX. (nelim (pieces_split mm j0 t tx FR L0 LTX) 4%nat; intros _ _ H2 _).
    destruct H2 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY.
  Qed.

  (* [comment removed for export] *)
  Lemma num_J : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo (j0 ++ le8 t ++ tx) Fc fcc errv LB buf len off bs -> length j0 = 8%nat -> length tx = 32%nat ->
    0 <= r <= 25 -> off + r + 2 <= len ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off)) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x135bc) fcc None mm (seg_rom psegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX L0 LTX Hr ROOM. pose proof CTX as (HL & HP & _ & ARR & LEN & (PN1 & PN2 & PN3) & FR & _ & _ & MI & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 3%nat; intros PL1 PL2 PL3).
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as CR. (nelimp CR 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    pose proof (frame_tx mm j0 t tx FR L0 LTX) as TX.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. step. if_cases K0; zify_cond K0.
    - apply evt_done. cbv beta. subst r. eapply num_T; [exact CTX| lia| lia].
    - zstep. step.
      eapply evt_cut.
      { eapply (num_loop r tx mm buf off len Fc fcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat r) 0 mm bs);
          [lia| lia| lia| lia| lia| exact LTX| lia| exact ROOM| exact CR| exact ARR| exact LEN| exact TX| exact MI| apply munch_refl| apply wmono_refl]. }
      cbv beta. intros ms' nelH_; (nelim nelH_ 11%nat; intros mm' bs' x12' x13' -> ARR' LEN' TX' MI' MU' WM').
      apply evt_done. eapply num_T; [eapply actx_block_write; [exact CTX| exact MU'| exact WM'| exact MI'| exact ARR'| exact LEN'| lia| lia]| lia| lia].
  Qed.

  Ltac open_fctx FC := (nelim FC 9%nat; intros FR ST ERR MI CJ FRM FA PVA CHn); unfold PERRNO in ERR.

  (* [comment removed for export] *)
  Lemma num_E : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo (j0 ++ le8 t ++ tx) Fc fcc errv LB buf len off bs -> length j0 = 8%nat -> length tx = 32%nat ->
    0 <= r <= 25 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x135ac) fcc None mm (seg_rom psegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX L0 LTX Hr. pose proof CTX as (HL & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. step. step. apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX| lia]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 buf2 len2 -> HL2 FC2 PBS2 OUT).
    replace (ret_pc (Z_to_bv 64 0x135b8)) with (Z_to_bv 64 0x135b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
    - step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta.
      open_fctx FC2.
      eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
      exists LB2, buf2, len2, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBS2| exact HB].
    - (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ (proj1 (proj2 CTX2)))) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). pose proof CTX2 as (_ & _ & _ & _ & _ & (PN1 & PN2 & PN3) & _).
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. apply evt_done. cbv beta.
      eapply num_J; [exact CTX2| exact L0| exact LTX| exact Hr| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_L : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo (j0 ++ le8 t ++ tx) Fc fcc errv LB buf len off bs -> length j0 = 8%nat -> length tx = 32%nat ->
    0 <= r <= 25 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1359c) fcc None mm (seg_rom psegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX L0 LTX Hr. pose proof CTX as (HL & _).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done. cbv beta.
    eapply num_E; [exact CTX| exact L0| exact LTX| exact Hr].
  Qed.

End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS ?R ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F "REGS" R;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_numA.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
Module CJ_pv_obj.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEPN : dep + Z.of_nat n <= 2^40.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  Hypothesis REC : forall d, (d < n)%nat -> pvalue_spec_at HI d.
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).
  Notation ux := (bv_unsigned (sx32 fw)).

  Ltac tree_now CTX CHn := assert (CHn : cj_chain CJ_PRINTABLE _ n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).
  Ltac open_actx CTX :=
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    (nelimp PL 3%nat; intros PL1 PL2 PL3); pose proof PN as PNc; (nelim PN 3%nat; intros PN1 PN2 PN3); unfold PERRNO in ERR;
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.
  Ltac open_fctx FC := (nelim FC 9%nat; intros FR ST ERR MI CJ FRM FA PVA CHn); unfold PERRNO in ERR.
  Ltac pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA := split; [exact HL|]; split; [exact HP|]; split; [exact PBS0|]; split; [exact ARR|];
    split; [first [exact LEN | rewrite ?upd_length; exact LEN]|]; split; [split; [lia| split; [lia|lia]]|];
    split; [exact FR|]; split; [exact ST|]; split; [exact ERR|]; split; [exact MI|]; split; [exact CJ|]; split; [exact FRM|]; split; [exact FA| exact PVA].
  (* [comment removed for export] *)
  Ltac fail_epi FC HLx LBx bufx lenx offx depx PBSx HBx :=
    let FR := fresh "FR" in let ST := fresh "ST" in let ERR := fresh "ERR" in let MI := fresh "MI" in let CJ := fresh "CJ" in
    let FRM := fresh "FRM" in let FA := fresh "FA" in let PVA := fresh "PVA" in let CHn := fresh "CHn" in
    (nelim FC 9%nat; intros FR ST ERR MI CJ FRM FA PVA CHn);
    eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|];
    exists LBx, bufx, lenx, offx; split; [exact HLx|]; left; split; [reflexivity|]; exists depx; split; [exact PBSx| exact HBx].

  (* [comment removed for export] *)
  Lemma tab_loop1 : forall (k : nat) (i : Z) mm (bsc : list byte) buf len off D mo loc Fc fcc errv LB
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    Z.of_nat k = D - i -> 0 <= i < D -> off + D + 1 <= len ->
    ACTX D mm mo loc Fc fcc errv LB buf len off bsc ->
    evt psegs (fun ms' => exists mm' bsc', ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 (buf + off)) (Z_to_bv 64 D) (Z_to_bv 64 D) x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 9) s7 s8 s9 s10 s11 x28 x29 x30 x31) Fc (Z_to_bv 64 0x132a4) fcc None mm' (seg_rom psegs)
                 /\ ACTX D mm' mo loc Fc fcc errv LB buf len off bsc')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 (buf + off)) (Z_to_bv 64 i) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 9) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13288) fcc None mm (seg_rom psegs)).
  Proof using CEIL LO N1 PL SPAL TP.
    induction k as [|k IH]; intros until x31; intros Hk Hi ROOM CTX; [lia|].
    pose proof PL as PLc. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    zstep. ustore_at buf off (buf + off + i) i (wb 9) ltac:(reflexivity).
    step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    pose proof (lh_frame HI _ _ _ m2 _ _ HL MU WM) as HL2.
    assert (CTX2 : ACTX D m2 mo loc Fc fcc errv LB buf len off (upd bsc (Z.to_nat (off + i)) (wb 9))).
    { split. { apply HL2. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia]. }
      split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact PNc|].
      split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split.
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
      split; [exact FRM|]. split; [exact FA|].
      eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D']. lia. }
    if_cases K; zify_cond K.
    - eapply (IH (i + 1)); [lia| lia| exact ROOM| exact CTX2].
    - step. apply evt_done. replace (i + 1) with D by lia. do 2 eexists. split; [reflexivity| exact CTX2].
  Qed.

  (* [comment removed for export] *)
  Lemma tab_loop2 : forall (k : nat) (i : Z) mm (bsc : list byte) buf len off D mo loc Fc fcc errv LB
      x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    Z.of_nat k = D - 1 - i -> 0 <= i < D - 1 -> off + D + 1 <= len ->
    ACTX D mm mo loc Fc fcc errv LB buf len off bsc ->
    evt psegs (fun ms' => exists mm' bsc' x13', ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 (buf + off)) (Z_to_bv 64 (D - 1)) (Z_to_bv 64 9) x13' x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) Fc (Z_to_bv 64 0x13644) fcc None mm' (seg_rom psegs)
                 /\ ACTX D mm' mo loc Fc fcc errv LB buf len off bsc')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 (buf + off)) (Z_to_bv 64 i) (Z_to_bv 64 9) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1362c) fcc None mm (seg_rom psegs)).
  Proof using CEIL LO N1 PL SPAL TP.
    induction k as [|k IH]; intros until x31; intros Hk Hi ROOM CTX; [lia|].
    pose proof PL as PLc. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    zstep. ustore_at buf off (buf + off + i) i (wb 9) ltac:(reflexivity).
    step. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    pose proof (lh_frame HI _ _ _ m2 _ _ HL MU WM) as HL2.
    assert (CTX2 : ACTX D m2 mo loc Fc fcc errv LB buf len off (upd bsc (Z.to_nat (off + i)) (wb 9))).
    { split. { apply HL2. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia]. }
      split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact PNc|].
      split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split.
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
      split; [exact FRM|]. split; [exact FA|].
      eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D']. lia. }
    if_cases K; zify_cond K.
    - eapply (IH (i + 1)); [lia| lia| exact ROOM| exact CTX2].
    - apply evt_done. replace (i + 1) with (D - 1) by lia. nexists 3%nat. split; [reflexivity| exact CTX2].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_end : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX (dep + 1) mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13508) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as (HL0 & _ & PBSc & _ & _ & (PNa & PNb & PNc') & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'. (nelimp PL 3%nat; intros PL1 PL2 PL3).
    pose proof (bv_unsigned_in_range 64 (sx32 fw)) as UXR.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL0|].
    (* [comment removed for export] *)
    assert (NEED : forall (nd : Z),
      (ux = 0 /\ nd = 2) \/ (ux <> 0 /\ nd = dep + 1 + 1) ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (sx32 fw) (Z_to_bv 64 nd) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x13604) fcc None mm (seg_rom psegs))).
    { intros nd ND. step. step. apply evt_done. cbv beta.
      eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX| lia]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 buf2 len2 -> HL2 FC2 PBS2 OUT).
      replace (ret_pc (Z_to_bv 64 0x1360c)) with (Z_to_bv 64 0x1360c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
      { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta.
        fail_epi FC2 HL2 LB2 buf2 len2 off (dep + 1) PBS2 HB. }
      pose proof CTX2 as (HLb & HPb & PBSb & _ & _ & (PN1 & PN2 & PN3) & _).
      (nelimp (lh_block_range HI _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      step. step. if_cases Kf; zify_cond Kf.
      - (* [comment removed for export] *)
        destruct ND as [[_ ->]|[X _]]; [| exfalso; lia].
        step. step. apply evt_done. cbv beta. replace (buf2 + off) with (buf2 + off + 0) by lia.
        eapply pv_close; first [exact PL| exact CEIL| exact LO| exact N1| exact BLR| exact SPAL| exact DEPN| exact DEP0| exact PNZ| exact CH0| exact REC| exact CTX2| exact TP| exact SPhi| lia].
      - step. step. step. if_cases K1; zify_cond K1.
        + (* [comment removed for export] *)
          destruct ND as [[X _]|[_ ->]]; [exfalso; lia|].
          step. step. apply evt_done. cbv beta. replace (buf2 + off) with (buf2 + off + 0) by lia.
          eapply pv_close; first [exact PL| exact CEIL| exact LO| exact N1| exact BLR| exact SPAL| exact DEPN| exact DEP0| exact PNZ| exact CH0| exact REC| exact CTX2| exact TP| exact SPhi| lia].
        + step. step.
          destruct ND as [[X _]|[_ ->]]; [exfalso; lia|].
          eapply evt_cut. { eapply (tab_loop2 (Z.to_nat dep) 0) with (D := dep + 1) (len := len2); [lia| lia| lia| exact CTX2]. }
          cbv beta. intros ms3 PO. (nelim PO 5%nat; intros m3 bs3 x13' -> CTX3).
          zstep. step. step. apply evt_done. cbv beta.
          eapply pv_close; first [exact PL| exact CEIL| exact LO| exact N1| exact BLR| exact SPAL| exact DEPN| exact DEP0| exact PNZ| exact CH0| exact REC| exact CTX3| exact TP| exact SPhi| lia]. }
    step. step. if_cases K; zify_cond K.
    - step. apply NEED. left. split; [lia| reflexivity].
    - pose proof PBSc as PBS0. step. zstep. step. apply NEED. right. split; [lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma obj_iter : forall (kk : nat) (d : nat) (c : Z) (Bc : list cblock) mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
    (length Bc <= kk)%nat -> (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    ACTX (dep + 1) mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 c) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 58) (Z_to_bv 64 10) (Z_to_bv 64 44) (Z_to_bv 64 9) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13264) fcc None mm (seg_rom psegs)) mo.
  Proof.
    induction kk as [|kk IH]; intros until x31; intros LENB Dlt CHc CNZ SUB CTX.
    { exfalso. pose proof (cj_chain_head_block _ _ _ _ _ CHc CNZ) as HIN. destruct Bc; [destruct HIN| cbn in LENB; lia]. }
    pose proof CTX as (HL0 & _ & PBSc & _ & _ & (PNa & PNb & _) & _). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 3%nat; intros PL1 PL2 PL3). pose proof (bv_unsigned_in_range 64 (sx32 fw)) as UXR.
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHc CNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY _ SV SK CHC CHN EBc).
    assert (CIN : In (c, 64) B) by (apply SUB; rewrite EBc; left; reflexivity).
    (* [comment removed for export] *)
    assert (J180 : forall mm' mo' LB' buf' len' bs' off' errv' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
      ACTX (dep + 1) mm' mo' loc Fc fcc errv' LB' buf' len' off' bs' ->
      SCPS psegs POST
        (MS (mkR y1 (Z_to_bv 64 SPF) gp tp y5 y6 y7 (Z_to_bv 64 PB) (Z_to_bv 64 c) y10 y11 y12 y13 y14 y15 y16 y17
                 x18 (Z_to_bv 64 58) (Z_to_bv 64 10) (Z_to_bv 64 44) (Z_to_bv 64 9) s7 s8 s9 s10 s11 y28 y29 y30 y31)
            Fc (Z_to_bv 64 0x132b0) fcc None mm' (seg_rom psegs)) mo').
    2: {
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL0|].
      pose proof PBSc as PBS0.
      step. step. if_cases Kf; zify_cond Kf.
      { apply evt_done. cbv beta. eapply J180. exact CTX. }
      step. step. step. apply evt_done. cbv beta.
      eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX| lia]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 buf2 len2 -> HL2 FC2 PBS2 OUT).
      replace (ret_pc (Z_to_bv 64 0x13278)) with (Z_to_bv 64 0x13278) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
      { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta.
        fail_epi FC2 HL2 LB2 buf2 len2 off (dep + 1) PBS2 HB. }
      pose proof CTX2 as (HLb & HPb & PBSb & _ & _ & (PN1 & PN2 & PN3) & _).
      (nelimp (lh_block_range HI _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step.
      eapply evt_cut. { eapply (tab_loop1 (Z.to_nat (dep + 1)) 0) with (D := dep + 1) (len := len2); [lia| lia| lia| exact CTX2]. }
      cbv beta. intros ms3 PO. (nelim PO 4%nat; intros m3 bs3 -> CTX3).
      (nelim CTX3 14%nat; intros HL HP PBS0' ARR LEN PN FR ST ERR MI CJ FRM FA PVA). clear PBS0. rename PBS0' into PBS0. unfold PERRNO in ERR.
      pose proof (munch_refl [(PB, PB + 64)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
      step. zstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      pose proof (lh_frame HI _ _ _ m4 _ _ HL MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL4.
      pose proof (CJST_frame _ _ m4 CJ MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E1|[]]; inversion E1; subst; lia)) as CJ4.
      assert (PVA4 : pv_agree LR (bv_unsigned sp) PB m m4) by (eapply pv_agree_trans; [exact PVA| eapply pv_agree_hole; [exact MU| exact WM| lia| lia]]).
      clear MU WM HL CJ PVA. rename HL4 into HL. rename CJ4 into CJ. rename PVA4 into PVA.
      apply evt_done. cbv beta. eapply J180. pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA. }
    intros mm' mo' LB' buf' len' bs' off' errv' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CTX1.
    clear HL0 PBSc PNa PNb.
    pose proof CTX1 as (HL1 & _).
    (* [comment removed for export] *)
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX1 ND (node_cells_size _ _ _ _ _ _ _ _ _ _) CIN) as NDn.
    unfold node_cells in NDn.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL1|].
    step. unfold wz. step. step. apply evt_done. cbv beta.
    eapply scps_bind.
    { eapply (actx_pstr HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact SPRU| exact CTX1| exact SK|].
      intros b Hb. apply SUB. rewrite EBc. right. rewrite !in_app_iff. right; left; exact Hb. }
    cbv beta. intros ms2 mo2 PO. clear NDn.
    (nelim PO 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc2 fcc2 m2 errv2 LB2 buf2 len2 off2 -> HL2 FC2 OUT)
.
    replace (ret_pc (Z_to_bv 64 0x132bc)) with (Z_to_bv 64 0x132bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & dep' & PBS2 & HB) | (-> & bs2 & CTX2 & NUL2)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. fail_epi FC2 HL2 LB2 buf2 len2 off2 dep' PBS2 HB. }
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    (* [comment removed for export] *)
    pose proof CTX2 as (_ & HP2 & PBS2 & _ & _ & (PN1 & PN2 & PN3) & _ & _ & _ & _ & _ & FRM2 & FA2 & _).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
    step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step. zstep. step.
    eapply evt_cut. { eapply (actx_strlen HI); [exact N1| exact CTX2| exact NUL2]. }
    cbv beta. intros ms3 PO. clear PBS2.
    (nelim PO 22%nat; intros k t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 errv3 -> CTX3 K0 K1 KN).
    replace (ret_pc (Z_to_bv 64 0x132d4)) with (Z_to_bv 64 0x132d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim CTX3 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR.
    pose proof (munch_refl [(PB, PB + 64)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    pose proof (lh_frame HI _ _ _ m4 _ _ HL MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL4.
    pose proof (CJST_frame _ _ m4 CJ MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E1|[]]; inversion E1; subst; lia)) as CJ4.
    assert (PVA4 : pv_agree LR (bv_unsigned sp) PB m m4) by (eapply pv_agree_trans; [exact PVA| eapply pv_agree_hole; [exact MU| exact WM| lia| lia]]).
    clear MU WM HL CJ PVA. rename HL4 into HL. rename CJ4 into CJ. rename PVA4 into PVA.
    assert (CTX4 : ACTX (dep + 1) m4 mo2 loc Fc2 fcc2 errv3 LB2 buf2 len2 (k + off2) bs2) by (pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA).
    (* [comment removed for export] *)
    step. zstep. zstep. step. step. step.
    set (fnz := 0 <? ux) in *.
    assert (FNZ : 0 <= Z.b2z fnz <= 1) by (destruct fnz; cbn; lia).
    apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX4| lia]. }
    cbv beta. intros ms5 mo5 PO. clear HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA CTX4.
    (nelim PO 25%nat; intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m5 errv5 LB5 buf5 len5 -> HL5 FC5 PBS5 OUT5).
    replace (ret_pc (Z_to_bv 64 0x132f4)) with (Z_to_bv 64 0x132f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL5|].
    destruct OUT5 as [(-> & HB) | (bs5 & -> & CTX5 & ROOM5)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. fail_epi FC5 HL5 LB5 buf5 len5 (k + off2) (dep + 1) PBS5 HB. }
    clear FC5 PBS5.
    (nelim CTX5 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR. (nelim PN 3%nat; intros PN1' PN2' PN3').
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros Z1 _ _ Z4 Z5). try rewrite alloc_ceiling_eq in Z4. unfold PIMG_LO, PIMG_HI in Z5.
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    pose proof (munch_refl [(buf5 + (k + off2), buf5 + len5); (PB, PB + 64)] m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    ustore_at buf5 (k + off2) (buf5 + (k + off2)) 0 (wb 58) ltac:(reflexivity).
    (* [comment removed for export] *)
    assert (J1d8 : forall mq (bsq : list byte) x11q,
      u8arr psegs mq buf5 bsq -> Z.of_nat (length bsq) = len5 ->
      munch [(buf5 + (k + off2), buf5 + len5); (PB, PB + 64)] m5 mq -> wmono psegs m5 mq -> mem_inv psegs mq ->
      rw_cells psegs mq PB [C8 (Z_to_bv 64 buf5); C8 (Z_to_bv 64 len5); C8 (Z_to_bv 64 (k + off2)); C8 (Z_to_bv 64 (dep + 1)); C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)] ->
      PVFRAME mq loc -> stk psegs mq lo SPF -> rw_cells psegs mq 210924 [C4 errv5] ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo5)
        (MS (mkR (Z_to_bv 64 0x132f4) (Z_to_bv 64 SPF) gp tp t0x t1x t2x (Z_to_bv 64 PB) (Z_to_bv 64 c) (Z_to_bv 64 (buf5 + (k + off2))) x11q a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 (Z.b2z fnz + 1)) (Z_to_bv 64 58) (Z_to_bv 64 10) (Z_to_bv 64 44) (Z_to_bv 64 9) s7 s8 s9 s10 s11 t3x t4x t5x t6x)
            Fc2 (Z_to_bv 64 0x13308) fcc2 None mq (seg_rom psegs))).
    2: { step. step. if_cases Kf; zify_cond Kf.
         - eapply J1d8; [exact ARR| rewrite !upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR].
         - ustore_at buf5 (k + off2) (buf5 + (k + off2) + 1) 1 (wb 9) ltac:(reflexivity).
           eapply J1d8; [exact ARR| rewrite !upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR]. }
    clear ARR MI ST FR PBS0 ERR MU WM.
    intros mq bsq x11q ARRq LENq MUq WMq MIq PBSq FRq STq ERRq.
    step. zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m7 end.
    pose proof (lh_frame HI _ _ _ m7 _ _ HL MUq WMq) as HL7.
    assert (CTX7 : ACTX (dep + 1) m7 mo5 loc Fc2 fcc2 errv5 LB5 buf5 len5 (k + off2 + (Z.b2z fnz + 1)) bsq).
    { split. { apply HL7. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf5, len5. split; [eapply perm_in_head; exact HP| cbn; lia]. }
      split; [exact HP|]. split; [exact PBSq|]. split; [exact ARRq|]. split; [exact LENq|]. split; [split; [lia| split; [lia| lia]]|].
      split; [exact FRq|]. split; [exact STq|]. split; [exact ERRq|]. split; [exact MIq|]. split.
      { eapply CJST_frame; [exact CJ| exact MUq| exact WMq|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
      split; [exact FRM|]. split; [exact FA|].
      eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MUq| exact WMq|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D']. lia. }
    clear HL7 HL HP PBSq ARRq LENq FRq STq ERRq MIq CJ PVA MUq WMq LEN FRM FA.
    (* [comment removed for export] *)
    step. step. step. apply evt_done. cbv beta.
    eapply scps_bind.
    { eapply (actx_rec HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact SPAL| apply REC; exact Dlt| exact Dlt| exact CTX7| lia| exact CHc| exact CNZ| exact SUB]. }
    cbv beta. intros ms8 mo8 PO. clear CTX7.
    (nelim PO 27%nat; intros u0 u1 u2 w0 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 Fc8 fcc8 m8 errv8 LB8 buf8 len8 off8 -> HL8 FC8 OUT8).
    replace (ret_pc (Z_to_bv 64 0x13320)) with (Z_to_bv 64 0x13320) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL8|].
    destruct OUT8 as [(-> & dep8 & PBS8 & HB8) | (-> & bs8 & CTX8 & NUL8)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. fail_epi FC8 HL8 LB8 buf8 len8 off8 dep8 PBS8 HB8. }
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    (* [comment removed for export] *)
    pose proof CTX8 as (_ & HP8 & PBS8 & _ & _ & (PM1 & PM2 & PM3) & _).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL8 (perm_in_head _ _ _ HP8)) 5%nat; intros V1 _ _ V4 _). try rewrite alloc_ceiling_eq in V4.
    step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step. zstep. step.
    eapply evt_cut. { eapply (actx_strlen HI); [exact N1| exact CTX8| exact NUL8]. }
    cbv beta. intros ms9 PO. clear PBS8.
    (nelim PO 22%nat; intros k2 v0 v1 v2 q1 q2 q3 q4 q5 q6 q7 v3 v4 v5 v6 m9 errv9 -> CTX9 J0 J1 JN9).
    replace (ret_pc (Z_to_bv 64 0x13338)) with (Z_to_bv 64 0x13338) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim CTX9 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR.
    pose proof (munch_refl [(PB, PB + 64)] m9) as MU. pose proof (wmono_refl psegs m9) as WM.
    zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m10 end.
    pose proof (lh_frame HI _ _ _ m10 _ _ HL MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL10.
    pose proof (CJST_frame _ _ m10 CJ MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E1|[]]; inversion E1; subst; lia)) as CJ10.
    assert (PVA10 : pv_agree LR (bv_unsigned sp) PB m m10) by (eapply pv_agree_trans; [exact PVA| eapply pv_agree_hole; [exact MU| exact WM| lia| lia]]).
    clear MU WM HL CJ PVA. rename HL10 into HL. rename CJ10 into CJ. rename PVA10 into PVA.
    assert (CTX10 : ACTX (dep + 1) m10 mo8 loc Fc8 fcc8 errv9 LB8 buf8 len8 (k2 + off8) bs8) by (pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA).
    (* [comment removed for export] *)
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX10 ND (node_cells_size _ _ _ _ _ _ _ _ _ _) CIN) as NDn.
    unfold node_cells in NDn.
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros NX0 _ NX2).
    step. step. unfold wz. zstep. zstep. zstep. zstep. step. step.
    set (hnx := 0 <? nx) in *. change (0 <? ux) with fnz.
    assert (HNX : 0 <= Z.b2z hnx <= 1) by (destruct hnx; cbn; lia).
    apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX10| lia]. }
    cbv beta. intros ms11 mo11 PO. clear HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA NDn CTX10.
    (nelim PO 25%nat; intros r0 r1 r2 g0 g1 g2 g3 g4 g5 g6 g7 r3 r4 r5 r6 m11 errv11 LB11 buf11 len11 -> HL11 FC11 PBS11 OUT11).
    replace (ret_pc (Z_to_bv 64 0x13360)) with (Z_to_bv 64 0x13360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL11|].
    destruct OUT11 as [(-> & HB) | (bs11 & -> & CTX11 & ROOM11)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. fail_epi FC11 HL11 LB11 buf11 len11 (k2 + off8) (dep + 1) PBS11 HB. }
    clear FC11 PBS11.
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX11 ND (node_cells_size _ _ _ _ _ _ _ _ _ _) CIN) as NDn.
    unfold node_cells in NDn.
    (nelim CTX11 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR. (nelim PN 3%nat; intros PQ1 PQ2 PQ3).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros W1 _ _ W4 W5). try rewrite alloc_ceiling_eq in W4. unfold PIMG_LO, PIMG_HI in W5.
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP c 64 (BLR _ CIN)) as [_ CD2].
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact CIN])) 5%nat; intros _ _ _ C4'' _). try rewrite alloc_ceiling_eq in C4''.
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    pose proof (munch_refl [(buf11 + (k2 + off8), buf11 + len11); (PB, PB + 64)] m11) as MU. pose proof (wmono_refl psegs m11) as WM.
    (* [comment removed for export] *)
    assert (JN : forall mz (bsz : list byte) x11z,
      u8arr psegs mz buf11 bsz -> Z.of_nat (length bsz) = len11 ->
      munch [(buf11 + (k2 + off8), buf11 + len11); (PB, PB + 64)] m11 mz -> wmono psegs m11 mz -> mem_inv psegs mz ->
      rw_cells psegs mz PB [C8 (Z_to_bv 64 buf11); C8 (Z_to_bv 64 len11); C8 (Z_to_bv 64 (k2 + off8)); C8 (Z_to_bv 64 (dep + 1)); C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)] ->
      PVFRAME mz loc -> stk psegs mz lo SPF -> rw_cells psegs mz 210924 [C4 errv11] ->
      rw_cells psegs mz c [C8 (Z_to_bv 64 nx); C8 pv; C8 (Z_to_bv 64 ch); C4 (Z_to_bv 64 ty); C4 p1; C8 (Z_to_bv 64 vs); C4 vi; C4 p2; C8 vd; C8 (Z_to_bv 64 ky)] ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo11)
        (MS (mkR (Z_to_bv 64 0x13360) (Z_to_bv 64 SPF) gp tp r0 r1 r2 (Z_to_bv 64 PB) (Z_to_bv 64 c) (Z_to_bv 64 (buf11 + (k2 + off8) + (Z.b2z hnx + Z.b2z fnz))) x11z g2 g3 g4 g5 g6 g7
                 (Z_to_bv 64 (Z.b2z hnx + Z.b2z fnz)) (Z_to_bv 64 58) (Z_to_bv 64 10) (Z_to_bv 64 44) (Z_to_bv 64 9) s7 s8 s9 s10 s11 r3 r4 r5 r6)
            Fc8 (Z_to_bv 64 0x1324c) fcc8 None mz (seg_rom psegs))).
    { intros mz bsz x11z ARRz LENz MUz WMz MIz PBSz FRz STz ERRz NDz. clear ARR LEN MI PBS0 FR ST ERR NDn MU WM.
      rename ARRz into ARR.
      ustore_at buf11 (k2 + off8) (buf11 + (k2 + off8) + (Z.b2z hnx + Z.b2z fnz)) (Z.b2z hnx + Z.b2z fnz) (wb 0) ltac:(reflexivity).
      step. step. zstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m13 end.
      pose proof (lh_frame HI _ _ _ m13 _ _ HL MUz WMz) as HL13.
      assert (CTX13 : ACTX (dep + 1) m13 mo11 loc Fc8 fcc8 errv11 LB11 buf11 len11 (k2 + off8 + (Z.b2z hnx + Z.b2z fnz)) (upd bsz (Z.to_nat (k2 + off8 + (Z.b2z hnx + Z.b2z fnz))) (wb 0))).
      { split. { apply HL13. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf11, len11. split; [eapply perm_in_head; exact HP| cbn; lia]. }
        split; [exact HP|]. split; [exact PBSz|]. split; [exact ARR|]. split; [rewrite upd_length; exact LENz|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FRz|]. split; [exact STz|]. split; [exact ERRz|]. split; [exact MIz|]. split.
        { eapply CJST_frame; [exact CJ| exact MUz| exact WMz|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
        split; [exact FRM|]. split; [exact FA|].
        eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MUz| exact WMz|].
        intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
        destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D']. lia. }
      step. if_cases Knx; zify_cond Knx.
      - apply evt_done. cbv beta. eapply obj_end. exact CTX13.
      - apply evt_done. cbv beta. eapply (IH d nx Bn); [ rewrite EBc in LENB; cbn in LENB; rewrite !length_app in LENB; lia | lia | rewrite <- Ed in CHN; exact CHN | lia
                              | intros b Hb; apply SUB; rewrite EBc; right; rewrite !in_app_iff; right; right; right; exact Hb | exact CTX13]. }
    (* [comment removed for export] *)
    Ltac useJN JN ARR LEN MU WM MI PBS0 FR ST ERR NDn :=
      first [ eapply JN; [exact ARR| first [exact LEN| rewrite !upd_length; exact LEN]| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR| exact NDn]
            | shmem; match goal with |- ?g => idtac g end ].
    step. unfold wz. step. if_cases Knx; zify_cond Knx.
    - assert (Eh : hnx = false) by (subst hnx; apply Z.ltb_ge; lia). rewrite Eh in *. cbn [Z.b2z] in *.
      step. step. if_cases Kf; zify_cond Kf.
      + assert (Ef : fnz = false) by (subst fnz; apply Z.ltb_ge; lia). rewrite Ef in *. cbn [Z.b2z] in *.
        replace (Z_to_bv 64 (buf11 + (k2 + off8))) with (Z_to_bv 64 (buf11 + (k2 + off8) + (0 + 0))) by (f_equal; lia).
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (0 + 0)) by reflexivity.
        useJN JN ARR LEN MU WM MI PBS0 FR ST ERR NDn.
      + assert (Ef : fnz = true) by (subst fnz; apply Z.ltb_lt; lia). rewrite Ef in *. cbn [Z.b2z] in *.
        zstep. ustore_at buf11 (k2 + off8) (buf11 + (k2 + off8)) 0 (wb 10) ltac:(reflexivity). step. step.
        replace (Z_to_bv 64 (buf11 + (k2 + off8) + 1)) with (Z_to_bv 64 (buf11 + (k2 + off8) + (0 + 1))) by (f_equal; lia).
        replace (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)) by reflexivity.
        useJN JN ARR LEN MU WM MI PBS0 FR ST ERR NDn.
    - assert (Eh : hnx = true) by (subst hnx; apply Z.ltb_lt; lia). rewrite Eh in *. cbn [Z.b2z] in *.
      zstep. ustore_at buf11 (k2 + off8) (buf11 + (k2 + off8)) 0 (wb 44) ltac:(reflexivity). step.
      step. step. if_cases Kf; zify_cond Kf.
      + assert (Ef : fnz = false) by (subst fnz; apply Z.ltb_ge; lia). rewrite Ef in *. cbn [Z.b2z] in *.
        replace (Z_to_bv 64 (buf11 + (k2 + off8) + 1)) with (Z_to_bv 64 (buf11 + (k2 + off8) + (1 + 0))) by (f_equal; lia).
        replace (Z_to_bv 64 1) with (Z_to_bv 64 (1 + 0)) by reflexivity.
        useJN JN ARR LEN MU WM MI PBS0 FR ST ERR NDn.
      + assert (Ef : fnz = true) by (subst fnz; apply Z.ltb_lt; lia). rewrite Ef in *. cbn [Z.b2z] in *.
        zstep. ustore_at buf11 (k2 + off8) (buf11 + (k2 + off8) + 1) 1 (wb 10) ltac:(reflexivity). step. step.
        replace (Z_to_bv 64 (buf11 + (k2 + off8) + 1 + 1)) with (Z_to_bv 64 (buf11 + (k2 + off8) + (1 + 1))) by (f_equal; lia).
        replace (Z_to_bv 64 2) with (Z_to_bv 64 (1 + 1)) by reflexivity.
        useJN JN ARR LEN MU WM MI PBS0 FR ST ERR NDn.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_obj.

(* [comment removed for export] *)
Module CJ_pv_objB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr CJ_pv_obj.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.


Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEPN : dep + Z.of_nat n <= 2^40.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  Hypothesis REC : forall d, (d < n)%nat -> pvalue_spec_at HI d.
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).
  Notation ux := (bv_unsigned (sx32 fw)).

  Ltac tree_now CTX CHn := assert (CHn : cj_chain CJ_PRINTABLE _ n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).
  Ltac open_actx CTX :=
    destruct CTX as (HL & HP & PBS0 & ARR & LEN & PN & FR & ST & ERR & MI & CJ & FRM & FA & PVA);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    destruct PL as (PL1 & PL2 & PL3); pose proof PN as PNc; destruct PN as (PN1 & PN2 & PN3); unfold PERRNO in ERR;
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4 & R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.
  Ltac open_fctx FC := destruct FC as (FR & ST & ERR & MI & CJ & FRM & FA & PVA & CHn); unfold PERRNO in ERR.
  Ltac fail_epi FC HLx LBx bufx lenx offx depx PBSx HBx :=
    let FR := fresh "FR" in let ST := fresh "ST" in let ERR := fresh "ERR" in let MI := fresh "MI" in let CJ := fresh "CJ" in
    let FRM := fresh "FRM" in let FA := fresh "FA" in let PVA := fresh "PVA" in let CHn := fresh "CHn" in
    destruct FC as (FR & ST & ERR & MI & CJ & FRM & FA & PVA & CHn);
    eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|];
    exists LBx, bufx, lenx, offx; split; [exact HLx|]; left; split; [reflexivity|]; exists depx; split; [exact PBSx| exact HBx].

  (* [comment removed for export] *)
  Lemma pv_obj : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x131e0) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as CTX0.
    destruct (cj_chain_cons_inv _ _ _ _ _ CH0 PNZ) as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bcc & Bn & Ed & ND & TY & _ & SV & SK & CHC & CHN & EB).
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND (node_cells_size _ _ _ _ _ _ _ _ _ _) ltac:(rewrite EB; left; reflexivity)) as NDn.
    unfold node_cells in NDn.
    pose proof CTX as (HL0 & _ & PBSc & _). pose proof PBSc as PBS0.
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'. pose proof PL as (PL1 & PL2 & PL3).
    pose proof (bv_unsigned_in_range 64 (sx32 fw)) as UXR.
    pose proof (cj_chain_ptr_range _ _ _ _ _ CHC) as (CR1 & _ & CR3).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL0|].
    step. step. unfold wz. zstep. zstep. step. step.
    set (fz := ux <? 1) in *.
    assert (FZ : Z.lxor (Z.b2z fz) 3 = 3 - Z.b2z fz /\ 0 <= Z.b2z fz <= 1) by (destruct fz; split; reflexivity || (cbn; lia)).
    destruct FZ as [EFZ RFZ]. rewrite EFZ.
    apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX0| lia]. }
    cbv beta. intros ms2 mo2 PO. clear PBS0 NDn.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & LB2 & buf2 & len2 & -> & HL2 & FC2 & PBS2 & OUT).
    replace (ret_pc (Z_to_bv 64 0x131f8)) with (Z_to_bv 64 0x131f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. fail_epi FC2 HL2 LB2 buf2 len2 off dep PBS2 HB. }
    clear FC2 PBS2.
    destruct CTX2 as (HL & HP & PBS0 & ARR & LEN & PN & FR & ST & ERR & MI & CJ & FRM & FA & PVA). unfold PERRNO in ERR. destruct PN as (PN1 & PN2 & PN3).
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (Z1 & _ & _ & Z4 & Z5). try rewrite alloc_ceiling_eq in Z4. unfold PIMG_LO, PIMG_HI in Z5.
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    pose proof (munch_refl [(buf2 + off, buf2 + len2); (PB, PB + 64)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    step. ustore_at buf2 off (buf2 + off) 0 (wb 123) ltac:(reflexivity).
    step. step. step. zstep. zstep. step.
    (* [comment removed for export] *)
    assert (JN : forall mq (bsq : list byte) a2q,
      u8arr psegs mq buf2 bsq -> Z.of_nat (length bsq) = len2 ->
      munch [(buf2 + off, buf2 + len2); (PB, PB + 64)] m2 mq -> wmono psegs m2 mq -> mem_inv psegs mq ->
      PBSd mq buf2 len2 off (dep + 1) -> PVFRAME mq loc -> stk psegs mq lo SPF -> rw_cells psegs mq PERRNO [C4 errv2] ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo2)
        (MS (mkR (Z_to_bv 64 0x131f8) (Z_to_bv 64 SPF) gp tp t0' t1' t2' (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 (buf2 + off)) (Z_to_bv 64 (2 - Z.b2z fz)) a2q (sx32 fw) a4' a5' a6' a7'
                 (Z_to_bv 64 (Z.b2z fz)) x19 x20 x21 x22 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            Fc (Z_to_bv 64 0x13228) fcc None mq (seg_rom psegs))).
    { intros mq bsq a2q ARRq LENq MUq WMq MIq PBSq FRq STq ERRq. clear ARR MI PBS0 FR ST ERR MU WM. unfold PERRNO in ERRq.
      step. zstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      pose proof (lh_frame HI _ _ _ m4 _ _ HL MUq WMq) as HL4.
      assert (CTX4 : ACTX (dep + 1) m4 mo2 loc Fc fcc errv2 LB2 buf2 len2 (off + (2 - Z.b2z fz)) bsq).
      { split. { apply HL4. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf2, len2. split; [eapply perm_in_head; exact HP| cbn; lia]. }
        split; [exact HP|]. split; [exact PBSq|]. split; [exact ARRq|]. split; [exact LENq|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FRq|]. split; [exact STq|]. split; [exact ERRq|]. split; [exact MIq|]. split.
        { eapply CJST_frame; [exact CJ| exact MUq| exact WMq|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
        split; [exact FRM|]. split; [exact FA|].
        eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MUq| exact WMq|].
        intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
        destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D']. lia. }
      step. if_cases Kch; zify_cond Kch.
      - apply evt_done. cbv beta.
        eapply (obj_end HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP N1 BLR SPAL DEPN DEP0 CH0). exact CTX4.
      - step. step. step. step. step. apply evt_done. cbv beta.
        eapply (obj_iter HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP N1 BLR SPAL DEPN DEP0 CH0 REC SPRU (length Bcc) d0 ch Bcc);
          [lia| lia| exact CHC| exact Kch| rewrite EB; intros b Hb; right; rewrite !in_app_iff; right; right; left; exact Hb| exact CTX4]. }
    step. if_cases Kf; zify_cond Kf.
    - eapply JN; [exact ARR| rewrite ?upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR].
    - step. ustore_at buf2 off (buf2 + off + 1) 1 (wb 10) ltac:(reflexivity).
      eapply JN; [exact ARR| rewrite ?upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR].
  Qed.
End S.

Theorem pv_obj_case : forall HI, F_printf_iface.sprintf_u04x_stmt -> forall n, pv_case_at PV_OBJ_ENTRY HI n.
Proof.
  intros HI SPRU n. unfold pv_case_at, PV_OBJ_ENTRY. intros until lo. intros PL CEIL LO TP SPhi N1 BLR SPAL DEPN DEP0 PNZ CH0 REC. intros.
  eapply pv_obj; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_objB.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pvalue.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pstr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases CJ_pv_lit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.




(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.


Section S.
  Variable HI : cj_heap_iface.
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.
  Hypothesis OBJ : forall n, pv_case_at PV_OBJ_ENTRY HI n.
  Hypothesis NUM : forall n, pv_case_at PV_NUM_ENTRY HI n.

  Section N.
    Variable n : nat.
    Hypothesis REC : forall d, (d < n)%nat -> pvalue_spec_at HI d.

    Lemma pvalue_at : pvalue_spec_at HI n.
    Proof.
      unfold pvalue_spec_at. intros until errv. intros HL HP PS PD PN DEPN CH PNZ BLR CJ PL SPAL ST CEIL LO ERR MI TP FRM A0 A1.
      unfold PVALUE_ENTRY, wz in A0, A1. subst a0 a1. unfold wz, PVALUE_ENTRY.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
      pose proof PL as (PL1 & PL2 & PL3). pose proof PN as (PN1 & PN2 & PN3). pose proof ST as STc; destruct STc as (_ & SPhi & _).
      destruct PD as [ARR LEN]. pose proof PS as PS'. pose proof PS as PBS0. unfold pb_struct, wz, PMALLOC, PFREE, PREALLOC in PBS0. unfold PERRNO in ERR.
      pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4 & R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
      destruct (cj_chain_cons_inv _ _ _ _ _ CH PNZ) as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bcc & Bn & Ed & ND & TY & PT & SV & SK & CHC & CHN & EB).
      assert (N1 : (1 <= n)%nat) by lia.
      assert (PIN : In (p, 64) LB). { eapply Permutation_in; [exact HP|]. right. apply BLR. rewrite EB. left. reflexivity. }
      pose proof (lh_block_range HI _ _ _ _ _ _ HL PIN) as (Q1 & _ & _ & Q4 & _). try rewrite alloc_ceiling_eq in Q4.
      pose proof ND as NDc. unfold node_cells, wz in ND.
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 128%nat ST.
      do 11 step.
      step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      pose proof (node_tyb_read m1 p nx pv ch ty p1 vs vi p2 vd ky ltac:(exact ND) TY) as RDT.
      zstep. cbv beta. rewrite (unsigned_lit8 ty) by lia.
      zstep. step. step.
      (* [comment removed for export] *)
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PVA1 : pv_agree LR (bv_unsigned sp) PB m m1).
      { eapply (pv_agree_stack HI); [exact HL| | exact MU| exact WM| try rewrite alloc_ceiling_eq; lia| lia]. intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia. }
      assert (FA0 : FAG18 F F) by (intros k Hk; reflexivity).
      lazymatch type of FR with rw_cells _ _ _ (CB 48 ?l :: _) => set (loc0 := l) in FR end.
      assert (CTX1 : actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo dep m1 mo loc0 F fc errv LB buf len off bs).
      { split; [exact HL1|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
        split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ1|]. split; [exact FRM|]. split; [exact FA0| exact PVA1]. }
      assert (CH1 : cj_chain CJ_PRINTABLE m1 n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX1| exact CH]).
      assert (PVC1 : pv_ctx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR B n p PB dep fw lo m1 mo loc0 F fc errv LB buf len off bs).
      { split; [exact HL1|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
        split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ1|]. split; [exact FRM|]. split; [exact FA0|]. split; [exact PVA1| exact CH1]. }
      destruct PT as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; rewrite <- E in *; zstep; if_false.
      all: zstep; zstep; zstep; zstep; step; zstep; step; apply evt_done; cbv beta.
      - eapply pv_false; first [exact PVC1| eassumption].
      - eapply pv_true; first [exact PVC1| eassumption].
      - eapply pv_null; first [exact PVC1| eassumption].
      - eapply (NUM n); first [exact CTX1| exact REC| eassumption| lia].
      - (* [comment removed for export] *)
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL1|].
        step. step. do 10 step. step. step.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. cbv beta.
        assert (SV1 : cj_str m1 vs Bv).
        { eapply cj_str_frame; [exact SV| exact MU| exact WM|]. intros A' n' Hin.
          pose proof (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; rewrite EB; right; apply in_or_app; left; exact Hin])) as (_ & _ & _ & X4 & _).
          try rewrite alloc_ceiling_eq in X4. cbn. lia. }
        eapply scps_mono.
        { eapply (pstr_spec HI SPRU) with (lo := lo) (LR := LR) (bs := bs) (Bv := Bv);
            first [ exact HL1 | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact SV1 | exact CJ1 | exact PL | exact ST | exact ERR | exact MI | exact TP | exact FRM | reflexivity
                  | intros b Hb; apply BLR; rewrite EB; right; apply in_or_app; left; exact Hb
                  | unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK; lia ]. }
        cbv beta. intros ms2 mo2 PO.
        destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Fc' & fcc' & m2 & errv2
                        & -> & MI2 & FRM2 & FA2 & ST2 & ERR2 & CJ2 & PVE & OUT).
        unfold pvalue_post. do 19 eexists. split; [reflexivity|].
        split; [exact MI2|]. split; [exact FRM2|]. split.
        { intros k Hk. rewrite (FA2 k ltac:(unfold fp_callee_saved in Hk; lia)). apply (FAG18_restore F F ltac:(intros k' _; reflexivity) k Hk). }
        split; [exact ST2|]. split; [exact ERR2|]. split; [exact CJ2|]. split.
        { eapply pv_agree_trans; [exact PVA1| exact PVE]. }
        split; [| exact OUT].
        eapply cj_chain_magree; [exact CH1| eapply magree_mono; [exact PVE|]|]. 2:{ intros a Ha; exact Ha. }
        cbv beta. intros a (A' & n' & Hin & Hr). split; [right; right; exists A', n'; split; [apply BLR; exact Hin| exact Hr]|].
        pose proof (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) as (_ & _ & _ & X4 & _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - eapply (pv_arr_case HI n); first [exact CTX1| exact REC| eassumption| lia].
      - eapply (OBJ n); first [exact CTX1| exact REC| eassumption| lia].
    Qed.
  End N.

  Theorem pvalue_spec : forall n, pvalue_spec_at HI n.
  Proof.
    intros n. induction n as [n IH] using lt_wf_ind. apply pvalue_at. exact IH.
  Qed.
End S.


End CeilWrap.
End CJ_pvalue.

(* [comment removed for export] *)
Module CJ_print.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases CJ_pvalue.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.




(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.



Lemma rw_cells_recell : forall m A cs cs',
  rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells psegs m A cs'.
Proof. intros m A cs cs' [[W B] R] W' EB ES. split; [split; [exact W'| rewrite EB; exact B]| rewrite ES; exact R]. Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells psegs m A (cs1 ++ cs2) <-> rw_cells psegs m A cs1 /\ rw_cells psegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app.
  split.
  - intros [[[W1 W2] BA] (R0 & R1 & R)]. apply bytes_at_app in BA. destruct BA as [B1 B2]. rewrite (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; [exact W1| exact B1]|]| split; [split; [exact W2| exact B2]|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply R. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply R. lia.
  - intros [[[W1 B1] (R0 & R1 & R)] [[W2 B2] (Q0 & Q1 & Q)]]. split; [split; [split; assumption|]|].
    + apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))); [apply R; lia|].
      replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Q. lia.
Qed.

Lemma rw_cells_split3 : forall m A j SC sv,
  rw_cells psegs m A (CB 8 j :: SC ++ sv) -> cells_size SC = 64%nat ->
  rw_cells psegs m A [CB 8 j] /\ rw_cells psegs m (A + 8) SC /\ rw_cells psegs m (A + 72) sv.
Proof.
  intros m A j SC sv H SZ. change (CB 8 j :: SC ++ sv) with ([CB 8 j] ++ (SC ++ sv)) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add] in H2. change (Z.of_nat 8) with 8 in H2.
  apply rw_cells_app in H2. destruct H2 as [H2 H3]. rewrite SZ in H3. change (Z.of_nat 64) with 64 in H3.
  replace (A + 8 + 64) with (A + 72) in H3 by lia. auto.
Qed.

Lemma rw_cells_join3 : forall m A j SC sv,
  rw_cells psegs m A [CB 8 j] -> rw_cells psegs m (A + 8) SC -> cells_size SC = 64%nat -> rw_cells psegs m (A + 72) sv ->
  rw_cells psegs m A (CB 8 j :: SC ++ sv).
Proof.
  intros m A j SC sv H1 H2 SZ H3. change (CB 8 j :: SC ++ sv) with ([CB 8 j] ++ (SC ++ sv)).
  apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
  apply rw_cells_app. split; [exact H2|]. rewrite SZ. change (Z.of_nat 64) with 64. replace (A + 8 + 64) with (A + 72) by lia. exact H3.
Qed.

Section S.
  Variable HI : cj_heap_iface.
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.
  Hypothesis OBJ : forall n, pv_case_at PV_OBJ_ENTRY HI n.
  Hypothesis NUM : forall n, pv_case_at PV_NUM_ENTRY HI n.

  Section Call.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte) (SPB : Z) (LB LR B : list cblock) (n : nat) (p lo : Z) (errv : word).
    Hypothesis HP : Permutation (B ++ LR) LB.
    Hypothesis CH : cj_chain CJ_PRINTABLE m n p B.
    Hypothesis PNZ : p <> 0.
    Hypothesis NMAX : (n <= 1001)%nat.
    Hypothesis SPB1 : bv_unsigned sp <= SPB.
    Hypothesis SPB2 : SPB < 2^62.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - PRINT_STACK n.
    Hypothesis TP : tp = wz PTP.

    Notation POST := (print_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p lo errv m).
    Notation SPF := (bv_unsigned sp + -112).
    Notation PB := (bv_unsigned sp + -104).
    Notation FRAME mm fj := (rw_cells psegs mm (bv_unsigned sp + -40) [CB 8 fj; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    Lemma N1 : (1 <= n)%nat.
    Proof. destruct n; [| lia]. exfalso. apply PNZ. exact (proj1 (cj_chain_zero_budget _ _ _ _ CH)). Qed.

    Lemma blocks_lo : forall SPB' LBX mm mo A k, LHEAP HI SPB' LBX mm mo -> In (A, k) LBX -> 0 < A /\ (0 <= k /\ A + k <= alloc_ceiling) /\ (A + k <= 65536 \/ 348160 <= A).
    Proof. intros. (nelimp (lh_block_range HI _ _ _ _ _ _ H H0) 5%nat; intros X1 _ X3 X4 X5). unfold PIMG_LO, PIMG_HI in X5. lia. Qed.

    (* [comment removed for export] *)
    Lemma print_epi_at : forall (pc : Z) (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (SC : list cell) (Fc : bvmap 5 word) (fcc : bv 32) (LB' : list cblock) (r : word)
        x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
      (pc = 0x13024 \/ pc = 0x130e0) ->
      rw_cells psegs mm (bv_unsigned sp + -112) (CB 8 fj :: SC ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) -> cells_size SC = 64%nat ->
      stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres (B ++ LR) (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B -> LHEAP HI SPB LB' mm mo' ->
      ((r = wz 0 /\ Permutation (B ++ LR) LB') \/ (exists q k, r = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB')) ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 pc) fcc None mm (seg_rom psegs)) mo'.
    Proof.
      intros until x31. intros HPC FR SZ ST MI ERR CJ FRM FA PR CHm HL' OUT.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PRINT_STACK, PV_STACK, PV_BASE in LO.
      pose proof (rw_cells_merge psegs mm _ [CB 8 fj] SC [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FR'. clear FR. rewrite SZ in FR'. cbn [app] in FR'.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      destruct HPC as [-> | ->]; do 7 step.
      2: release_frame FR' ST (bv_unsigned sp).
      2: apply evt_done; apply scps_done; unfold print_post.
      2: nexists 20%nat; split; [reflexivity|].
      2: split; [exact MI|]; split; [exact FRM|]; split; [exact FA|]; split; [exact ST|]; split; [exact ERR|]; split; [exact CJ|]; split; [exact PR|]; split; [exact CHm|].
      2: split; [exact HL'| exact OUT].
      release_frame FR' ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold print_post.
      nexists 20%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split; [exact FA|]. split; [exact ST|]. split; [exact ERR|]. split; [exact CJ|]. split; [exact PR|]. split; [exact CHm|].
      split; [exact HL'| exact OUT].
    Qed.

    Lemma print_epi : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (SC : list cell) (Fc : bvmap 5 word) (fcc : bv 32) (LB' : list cblock) (r : word)
        x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
      rw_cells psegs mm (bv_unsigned sp + -112) (CB 8 fj :: SC ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) -> cells_size SC = 64%nat ->
      stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres (B ++ LR) (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B -> LHEAP HI SPB LB' mm mo' ->
      ((r = wz 0 /\ Permutation (B ++ LR) LB') \/ (exists q k, r = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB')) ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x13024) fcc None mm (seg_rom psegs)) mo'.
    Proof. intros. eapply print_epi_at; eauto. Qed.

    (* [comment removed for export] *)
    Lemma print_failtail : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (SC : list cell) (Fc : bvmap 5 word) (fcc : bv 32) (LB' : list cblock) (b l : Z)
        x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
      rw_cells psegs mm (bv_unsigned sp + -112) (CB 8 fj :: SC ++ [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) -> cells_size SC = 64%nat ->
      stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, fp_callee_saved k -> reg_get Fc k = reg_get F k) ->
      cj_pres (B ++ LR) (bv_unsigned sp) m mm -> cj_chain CJ_PRINTABLE mm n p B -> LHEAP HI SPB LB' mm mo' ->
      ((b = 0 /\ Permutation (B ++ LR) LB') \/ (b <> 0 /\ Permutation ((b, l) :: B ++ LR) LB')) ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 b) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 PHOOKS) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x13010) fcc None mm (seg_rom psegs)) mo'.
    Proof.
      intros until x31. intros FR SZ ST MI ERR CJ FRM FA PR CHm HL' HB.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PRINT_STACK, PV_STACK, PV_BASE in LO'. pose proof N1 as N1'.
      assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
      (nelimp CJ 3%nat; intros HK _ _). unfold PHOOKS, wz, PMALLOC, PFREE, PREALLOC in HK. unfold PERRNO in ERR. unfold PHOOKS.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      destruct HB as [[-> HPn]|[BNZ HPn]].
      - step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. step. apply evt_done. cbv beta.
        eapply print_epi; [exact FR| exact SZ| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PR| exact CHm| exact HL'| left; split; [reflexivity| exact HPn]].
      - (nelimp (blocks_lo _ _ _ _ _ _ HL' (perm_in_head _ _ _ HPn)) 3%nat; intros Y1 Y4 _). try rewrite alloc_ceiling_eq in Y4.
        step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step. step. step.
        replace (ret_pc (Z_to_bv 64 86496)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta. eapply scps_bind.
        { eapply (lh_free HI) with (lo := lo) (A := b) (n := l); rewrite ?E1;
            first [ exact HL' | eapply perm_in_head; exact HPn | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
        cbv beta. intros ms3 mo3 PO.
        (nelim PO 22%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 -> MI3 ST3 ERR3 PR3 HL3).
        rewrite E1 in ST3, PR3.
        replace (ret_pc (Z_to_bv 64 0x13020)) with (Z_to_bv 64 0x13020) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HPn (lh_nodup HI _ _ _ _ HL')) as HP3.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in FR; [| left; lia].
        apply (CJST_pres _ _ _ _ PR3) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CHm) in PR3 as CH3. 2:{ intros bb Hb. eapply Permutation_in; [exact HP3| apply in_or_app; left; exact Hb]. }
        assert (PR' : cj_pres (B ++ LR) (bv_unsigned sp) m m3).
        { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR3| lia|]. intros bb Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL3|].
        step. apply evt_done. cbv beta.
        eapply print_epi; [exact FR| exact SZ| exact ST3| exact MI3| exact ERR3| exact CJ| exact FRM| exact FA| exact PR'| exact CH3| exact HL3| left; split; [reflexivity| exact HP3]].
    Qed.

    Lemma print_main : forall (mo : Model) (fc : bv 32) (fw t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> CJST m -> stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> frm0 fc ->
      SCPS psegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) fw a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x12efc) fc None m (seg_rom psegs)) mo.
    Proof.
      intros until t6. intros HL CJ ST ERR MI FRM.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PRINT_STACK, PV_STACK, PV_BASE in LO'.
      pose proof N1 as N1'. pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
      assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
      pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS, wz, PMALLOC, PFREE, PREALLOC in HK. unfold PGERROR in GE. unfold PLCONV, wz, PDOTSTR in LC. unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 112%nat ST.
      do 6 step. step. step. step. step. step.
      step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
      step. step. step.
      replace (ret_pc (Z_to_bv 64 86816)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ [CB 24 ?j1; ?c1; ?c2; C8 (Z_to_bv 64 0); CB 24 ?j2; ?r1; ?r2; ?r3; ?r4; ?r5] =>
        assert (FR' : rw_cells psegs m1 SPF [CB 24 j1; c1; c2; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 24 j2; r1; r2; r3; r4; r5])
          by (eapply rw_cells_recell; [exact FR| pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf cell_wf] in WF |- *; tauto| reflexivity| reflexivity]);
        clear FR; rename FR' into FR end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PR1 : cj_pres LB (bv_unsigned sp) m m1).
      { apply pv_agree_of_cj_pres with (PB := 0) in HL || idtac.
        intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
        destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        (nelimp (blocks_lo _ _ _ _ _ _ HL Hin) 3%nat; intros _ X _). try rewrite alloc_ceiling_eq in X. lia. }
      clear MU WM.
      apply evt_done. cbv beta. eapply scps_bind.
      { eapply (lh_malloc HI) with (lo := lo) (n := 256); rewrite ?E1;
          first [ exact HL1 | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES).
      rewrite E1 in ST2, PR2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x12f40)) with (Z_to_bv 64 0x12f40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in HK; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in GE; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in LC; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      assert (PR12 : cj_pres (B ++ LR) (bv_unsigned sp) m m2).
      { eapply cj_pres_trans; [eapply cj_pres_weaken; [exact PR1| lia| intros b Hb; eapply Permutation_in; [exact HP| exact Hb]]|].
        eapply cj_pres_weaken; [exact PR2| lia|]. intros b Hb; eapply Permutation_in; [exact HP| exact Hb]. }
      assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
      { eapply cj_chain_pres; [exact CH| exact PR12|]. intros b Hb. apply in_or_app; left; exact Hb. }
      clear PR1 PR2 MI ST ERR HL HL1.
      destruct RES as [[-> HL2] | (A & junkA & -> & CR & NIN & HL2 & BLK)].
      - (* [comment removed for export] *)
        pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        unfold wz. do 3 step. do 6 (step; fix_lit_store). step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        assert (PR13 : cj_pres (B ++ LR) (bv_unsigned sp) m m3).
        { eapply cj_pres_trans; [exact PR12|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
          destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
          (nelimp (blocks_lo _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP| exact Hin])) 3%nat; intros _ X _). try rewrite alloc_ceiling_eq in X. lia. }
        assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B).
        { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|]. intros A' n' Hin.
          (nelimp (blocks_lo _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) 3%nat; intros _ X _). try rewrite alloc_ceiling_eq in X. cbn. lia. }
        pose proof (lh_frame HI _ _ _ m3 _ _ HL2 MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL3.
        apply evt_done. cbv beta.
        lazymatch type of FR with rw_cells _ ?mc _ (CB 8 ?j1 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
          eapply (print_epi mc mo2 errv2 j1 [c1;c2;c3;c4;c5;c6;c7;c8;c9]); [exact FR| reflexivity| exact ST2| exact MI2| exact ERR2| | exact FRM| intros k Hk; reflexivity| exact PR13| exact CH3| exact HL3| left; split; [reflexivity| exact HP]] end.
        split; [exact HK|]. split; [exists e1, e2; exact GE| exact LC].
      - (* [comment removed for export] *)
        unfold wz.
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        do 3 step. do 6 (step; fix_lit_store). step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        zstep. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        assert (BB : forall A' n', In (A', n') LB -> A' + n' <= alloc_ceiling).
        { intros A' n' Hin. (nelimp (blocks_lo _ _ _ _ _ _ HL2 ltac:(right; exact Hin)) 3%nat; intros _ X _). lia. }
        assert (PR13 : cj_pres (B ++ LR) (bv_unsigned sp) m m3).
        { eapply cj_pres_trans; [exact PR12|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
          destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
        assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B).
        { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|]. intros A' n' Hin.
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) as X. try rewrite alloc_ceiling_eq in X. cbn. lia. }
        pose proof (lh_frame HI _ _ _ m3 _ _ HL2 MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL3.
        pose proof (u8arr_of_rw_cells psegs _ _ _ _ BLK) as ARR3. pose proof (proj1 (proj1 (proj1 BLK))) as LJ. cbn [cells_wf cell_wf] in LJ.
        clear MU WM HL2 CH2.
        (* [comment removed for export] *)
        lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j1 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
          (nelim (rw_cells_split3 m3 _ j1 [c1;c2;c3;c4;c5;c6;c7;c8;c9] rest FR eq_refl) 3%nat; intros FRh PBS FRs) end.
        replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in PBS by lia.
        apply evt_done. cbv beta. eapply scps_bind.
        { eapply (pvalue_spec HI SPRU OBJ NUM n) with (lo := lo) (LR := B ++ LR) (B := B) (bs := junkA) (dep := 0); rewrite ?E1;
            first [ exact HL3 | exact PBS | split; [exact ARR3| rewrite LJ; reflexivity] | exact CH3 | exact PNZ | exact ST2 | exact ERR2 | exact MI2 | exact TP | exact FRM
                  | apply perm_skip; exact HP
                  | intros b Hb; apply in_or_app; left; exact Hb
                  | split; [exact HK| split; [exists e1, e2; exact GE| exact LC]]
                  | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
                  | unfold pb_nums; lia | unfold pb_place; lia | unfold PV_STACK, PV_BASE; lia | lia | unfold wz; f_equal; cbn; lia ]. }
        cbv beta. intros ms4 mo4 PO.
        (nelim PO 29%nat; intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x Fc fcc m4 errv4 -> MI4 FRM4 FA4 ST4 ERR4 CJ4 PVE CH4 OUT4)
.
        rewrite E1 in ST4, PVE. unfold PERRNO in ERR4.
        replace (ret_pc (Z_to_bv 64 0x12f74)) with (Z_to_bv 64 0x12f74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (PR14 : cj_pres (B ++ LR) (bv_unsigned sp) m m4).
        { eapply cj_pres_trans; [exact PR13|]. eapply cj_pres_of_pv_agree; [exact PVE| unfold PIMG_HI; lia| lia| lia|].
          intros A' n' Hin. pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
        apply (rw_cells_magree _ m3 m4 _ _ PVE) in FRh; [| cbn; intros a Ha; split; [left; lia| lia]].
        apply (rw_cells_magree _ m3 m4 _ _ PVE) in FRs; [| cbn; intros a Ha; split; [left; lia| lia]].
        (nelimp CJ4 3%nat; intros HK4 _ _). unfold PHOOKS, wz, PMALLOC, PFREE, PREALLOC in HK4.
        clear PVE PBS ARR3 BLK HL3 ST2 ERR2 MI2 HK GE LC CH3.
        destruct OUT4 as (LB4 & buf4 & len4 & off4 & HL4 & [(-> & dep4 & PBS4 & HB4) | (-> & bs4 & HP4 & PBS4 & PD4 & PN4 & NUL4)]).
        + (* [comment removed for export] *)
          unfold pb_struct, wz, PMALLOC, PFREE, PREALLOC in PBS4. unfold wz.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL4|].
          step. step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
          apply evt_done. cbv beta.
          pose proof (rw_cells_join3 m4 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
          eapply print_failtail; [exact FRj| reflexivity| exact ST4| exact MI4| exact ERR4| exact CJ4| exact FRM4| exact FA4| exact PR14| exact CH4| exact HL4| exact HB4].
        + (* [comment removed for export] *)
          pose proof PBS4 as PS4. unfold pb_struct, wz, PMALLOC, PFREE, PREALLOC in PBS4. unfold wz. destruct PD4 as [ARR4 LEN4]. (nelim PN4 3%nat; intros PN1 PN2 PN3).
          (nelimp (blocks_lo _ _ _ _ _ _ HL4 (perm_in_head _ _ _ HP4)) 3%nat; intros W1 W4 W5). try rewrite alloc_ceiling_eq in W4.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL4|].
          step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          step. zstep. step.
          eapply evt_cut.
          { eapply (strlen_upd HI) with (off := off4); [exact HL4| eapply perm_in_head; exact HP4| exact ARR4| exact LEN4| lia| exact NUL4| exact MI4| reflexivity]. }
          cbv beta. intros ms5 PO.
          (nelim PO 23%nat; intros k t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y m5 -> MU5 WM5 MI5 K0 K1 KN).
          replace (ret_pc (Z_to_bv 64 0x12f8c)) with (Z_to_bv 64 0x12f8c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          eapply (rw_cells_transport psegs) in PBS4; [| exact MU5| exact WM5| exact I].
          eapply (rw_cells_transport psegs) in FRh; [| exact MU5| exact WM5| exact I].
          eapply (rw_cells_transport psegs) in FRs; [| exact MU5| exact WM5| exact I].
          eapply (rw_cells_transport psegs) in ERR4; [| exact MU5| exact WM5| exact I].
          eapply (rw_cells_transport psegs) in HK4; [| exact MU5| exact WM5| exact I].
          eapply (u8arr_transport psegs) in ARR4; [| exact MU5| exact WM5| exact I].
          eapply (stk_transport_disjoint psegs) in ST4; [| exact MU5| exact WM5| exact I].
          pose proof (lh_frame HI _ _ _ m5 _ _ HL4 MU5 WM5 ltac:(constructor)) as HL5.
          pose proof (CJST_frame _ _ m5 CJ4 MU5 WM5 ltac:(intros lo' hi' [])) as CJ5.
          assert (PR15 : cj_pres (B ++ LR) (bv_unsigned sp) m m5).
          { eapply cj_pres_trans; [exact PR14|]. intros a Ha Hc. split; [apply MU5; exact I| apply WM5]. }
          pose proof (cj_chain_frame _ _ m5 _ _ _ _ CH4 MU5 WM5 ltac:(intros; exact I)) as CH5.
          clear MU5 WM5 MI4 CJ4 PR14 CH4 HL4.
          (* [comment removed for export] *)
          pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m5) as MU. pose proof (wmono_refl psegs m5) as WM.
          zstep. step.
          step. step. if_false.
          step. zstep. step. step.
          replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
          pose proof (lh_frame HI _ _ _ m6 _ _ HL5 MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL6.
          assert (PR16 : cj_pres (B ++ LR) (bv_unsigned sp) m m6).
          { eapply cj_pres_trans; [exact PR15|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
            destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
          pose proof (CJST_frame _ _ m6 CJ5 MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E2|[]]; inversion E2; subst; lia)) as CJ6.
          pose proof (cj_chain_frame _ _ m6 _ _ _ _ CH5 MU WM) as CH6.
          specialize (CH6 ltac:(intros A' n' Hin; pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) as X; try rewrite alloc_ceiling_eq in X; cbn; lia)).
          clear MU WM HL5 PR15 CH5 CJ5.
          apply evt_done. cbv beta. eapply scps_bind.
          { eapply (lh_realloc HI) with (lo := lo) (A := buf4) (k := len4) (n := k + off4 + 1) (old := bs4); rewrite ?E1;
              first [ exact HL6 | eapply perm_in_head; exact HP4 | exact (proj1 ARR4) | exact LEN4 | exact ST4 | exact ERR4 | exact MI5 | exact TP | reflexivity | unfold RMALLOC_STACK; lia | unfold wz; f_equal; lia ]. }
          cbv beta. intros ms7 mo7 PO.
          (nelim PO 22%nat; intros t0z t1z t2z a0z a1z a2z a3z a4z a5z a6z a7z t3z t4z t5z t6z m7 errv7 -> MI7 ST7 ERR7 RES).
          rewrite E1 in ST7. unfold PERRNO in ERR7.
          replace (ret_pc (Z_to_bv 64 0x12fac)) with (Z_to_bv 64 0x12fac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct RES as [(-> & HL7 & PR7) | (B' & junk' & -> & CR' & HB' & HL7 & PR7 & BLK')]; rewrite E1 in PR7; unfold wz.
          * (* [comment removed for export] *)
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in FRh; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in PBS4; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in FRs; [| left; lia].
            apply (CJST_pres _ _ _ _ PR7) in CJ6.
            apply (cj_chain_pres _ _ _ _ _ _ _ _ CH6) in PR7 as CH7. 2:{ intros b Hb. eapply Permutation_in; [exact HP4| right; apply in_or_app; left; exact Hb]. }
            assert (PR17 : cj_pres (B ++ LR) (bv_unsigned sp) m m7).
            { eapply cj_pres_trans; [exact PR16|]. eapply cj_pres_weaken; [exact PR7| lia|]. intros b Hb. eapply Permutation_in; [exact HP4| right; exact Hb]. }
            eapply scps_step_evt; [eapply (lh_mok HI); exact HL7|].
            step. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K. step. step.
            apply evt_done. cbv beta.
            pose proof (rw_cells_join3 m7 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
            eapply print_failtail; [exact FRj| reflexivity| exact ST7| exact MI7| exact ERR7| exact CJ6| exact FRM4| exact FA4| exact PR17| exact CH7| exact HL7| right; split; [lia| exact HP4]].
          * (* [comment removed for export] *)
            (nelim CR' 5%nat; intros C1 _ _ C4' _). try rewrite alloc_ceiling_eq in C4'.
            pose proof (perm_cb_remove _ _ _ _ HP4 (lh_nodup HI _ _ _ _ HL6)) as HPr.
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in FRh; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in PBS4; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR7) in FRs; [| left; lia].
            apply (CJST_pres _ _ _ _ PR7) in CJ6.
            apply (cj_chain_pres _ _ _ _ _ _ _ _ CH6) in PR7 as CH7. 2:{ intros b Hb. eapply Permutation_in; [exact HPr| apply in_or_app; left; exact Hb]. }
            assert (PR17 : cj_pres (B ++ LR) (bv_unsigned sp) m m7).
            { eapply cj_pres_trans; [exact PR16|]. eapply cj_pres_weaken; [exact PR7| lia|]. intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
            eapply scps_step_evt; [eapply (lh_mok HI); exact HL7|].
            step. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
            apply evt_done. cbv beta.
            pose proof (rw_cells_join3 m7 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
            eapply print_epi; [exact FRj| reflexivity| exact ST7| exact MI7| exact ERR7| exact CJ6| exact FRM4| exact FA4| exact PR17| exact CH7| exact HL7|].
            right. exists B', (k + off4 + 1). split; [reflexivity|]. split; [lia|]. apply perm_skip. exact HPr.
    Qed.

    (* [comment removed for export] *)
    Lemma pbuffered_main : forall (mo : Model) (fc : bv 32) (pre : Z) (fw t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> CJST m -> stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> frm0 fc ->
      0 <= pre < 2^31 ->
      SCPS psegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 pre) fw a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x13048) fc None m (seg_rom psegs)) mo.
    Proof.
      intros until t6. intros HL CJ ST ERR MI FRM PRE.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PRINT_STACK, PV_STACK, PV_BASE in LO'.
      pose proof N1 as N1'. pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
      assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
      pose proof CJ as (HK & (e1 & e2 & GE) & LC). unfold PHOOKS, wz, PMALLOC, PFREE, PREALLOC in HK. unfold PGERROR in GE. unfold PLCONV, wz, PDOTSTR in LC. unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      assert (BB : forall A' n', In (A', n') LB -> A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (blocks_lo _ _ _ _ _ _ HL Hin) 3%nat; intros _ X _). lia. }
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 112%nat ST.
      do 6 step. step. fix_lit_store.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      do 8 step.
      replace (ret_pc (Z_to_bv 64 86816)) with (wz PMALLOC) by (unfold wz, PMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PR1 : cj_pres (B ++ LR) (bv_unsigned sp) m m1).
      { intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
        destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
      assert (CH1 : cj_chain CJ_PRINTABLE m1 n p B).
      { eapply cj_chain_frame; [exact CH| exact MU| exact WM|]. intros A' n' Hin.
        pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) as X. try rewrite alloc_ceiling_eq in X. cbn. lia. }
      clear MU WM.
      apply evt_done. cbv beta. eapply scps_bind.
      { eapply (lh_malloc HI) with (lo := lo) (n := pre); rewrite ?E1;
          first [ exact HL1 | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 PR2 RES).
      rewrite E1 in ST2, PR2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x13088)) with (Z_to_bv 64 0x13088) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in HK; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in GE; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in LC; [| right; left; unfold PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; cbn; lia].
      assert (PR12 : cj_pres (B ++ LR) (bv_unsigned sp) m m2).
      { eapply cj_pres_trans; [exact PR1|]. eapply cj_pres_weaken; [exact PR2| lia|]. intros b Hb; eapply Permutation_in; [exact HP| exact Hb]. }
      assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
      { eapply cj_chain_pres; [exact CH1| exact PR2|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app; left; exact Hb. }
      assert (CJ2 : CJST m2) by (split; [exact HK| split; [exists e1, e2; exact GE| exact LC]]).
      clear PR1 PR2 MI ST ERR HL CH1.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      destruct RES as [[-> HL2] | (A & junkA & -> & CR & NIN & HL2 & BLK)]; unfold wz.
      - (* [comment removed for export] *)
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. fix_lit_store. step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        assert (PR13 : cj_pres (B ++ LR) (bv_unsigned sp) m m3).
        { eapply cj_pres_trans; [exact PR12|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
          destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
        assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B).
        { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|]. intros A' n' Hin.
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) as X. try rewrite alloc_ceiling_eq in X. cbn. lia. }
        pose proof (lh_frame HI _ _ _ m3 _ _ HL2 MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL3.
        pose proof (CJST_frame _ _ m3 CJ2 MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E2|[]]; inversion E2; subst; lia)) as CJ3.
        apply evt_done. cbv beta.
        lazymatch type of FR with rw_cells _ ?mc _ (CB 8 ?j1 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
          eapply (print_epi_at 0x130e0 mc mo2 errv2 j1 [c1;c2;c3;c4]); [right; reflexivity| exact FR| reflexivity| exact ST2| exact MI2| exact ERR2| exact CJ3| exact FRM| intros k Hk; reflexivity| exact PR13| exact CH3| exact HL3| left; split; [reflexivity| exact HP]] end.
      - (* [comment removed for export] *)
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        do 3 step. do 7 (step; fix_lit_store). zstep. step. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        assert (PR13 : cj_pres (B ++ LR) (bv_unsigned sp) m m3).
        { eapply cj_pres_trans; [exact PR12|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
          destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
        assert (CH3 : cj_chain CJ_PRINTABLE m3 n p B).
        { eapply cj_chain_frame; [exact CH2| exact MU| exact WM|]. intros A' n' Hin.
          pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])) as X. try rewrite alloc_ceiling_eq in X. cbn. lia. }
        pose proof (lh_frame HI _ _ _ m3 _ _ HL2 MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL3.
        pose proof (CJST_frame _ _ m3 CJ2 MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E2|[]]; inversion E2; subst; lia)) as CJ3.
        pose proof (u8arr_of_rw_cells psegs _ _ _ _ BLK) as ARR3. pose proof (proj1 (proj1 (proj1 BLK))) as LJ. cbn [cells_wf cell_wf] in LJ.
        clear MU WM HL2 CH2 CJ2.
        lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j1 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
          (nelim (rw_cells_split3 m3 _ j1 [c1;c2;c3;c4;c5;c6;c7;c8;c9] rest FR eq_refl) 3%nat; intros FRh PBS FRs) end.
        replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in PBS by lia.
        apply evt_done. cbv beta. eapply scps_bind.
        { eapply (pvalue_spec HI SPRU OBJ NUM n) with (lo := lo) (LR := B ++ LR) (B := B) (bs := junkA) (dep := 0); rewrite ?E1;
            first [ exact HL3 | exact PBS | split; [exact ARR3| rewrite LJ; lia] | exact CH3 | exact PNZ | exact ST2 | exact ERR2 | exact MI2 | exact TP | exact FRM | exact CJ3
                  | apply perm_skip; exact HP
                  | intros b Hb; apply in_or_app; left; exact Hb
                  | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
                  | unfold pb_nums; lia | unfold pb_place; lia | unfold PV_STACK, PV_BASE; lia | lia | unfold wz; f_equal; cbn; lia ]. }
        cbv beta. intros ms4 mo4 PO.
        (nelim PO 29%nat; intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x Fc fcc m4 errv4 -> MI4 FRM4 FA4 ST4 ERR4 CJ4 PVE CH4 OUT4)
.
        rewrite E1 in ST4, PVE. unfold PERRNO in ERR4.
        replace (ret_pc (Z_to_bv 64 0x130c4)) with (Z_to_bv 64 0x130c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (PR14 : cj_pres (B ++ LR) (bv_unsigned sp) m m4).
        { eapply cj_pres_trans; [exact PR13|]. eapply cj_pres_of_pv_agree; [exact PVE| unfold PIMG_HI; lia| lia| lia|].
          intros A' n' Hin. pose proof (BB A' n' ltac:(eapply Permutation_in; [exact HP| exact Hin])) as X. try rewrite alloc_ceiling_eq in X. lia. }
        apply (rw_cells_magree _ m3 m4 _ _ PVE) in FRh; [| cbn; intros a Ha; split; [left; lia| lia]].
        apply (rw_cells_magree _ m3 m4 _ _ PVE) in FRs; [| cbn; intros a Ha; split; [left; lia| lia]].
        (nelimp CJ4 3%nat; intros HK4 _ _). unfold PHOOKS, wz, PMALLOC, PFREE, PREALLOC in HK4.
        clear PVE PBS ARR3 BLK HL3 ST2 ERR2 MI2 HK GE LC CH3 CJ3.
        destruct OUT4 as (LB4 & buf4 & len4 & off4 & HL4 & [(-> & dep4 & PBS4 & HB4) | (-> & bs4 & HP4 & PBS4 & PD4 & PN4 & NUL4)]);
          unfold pb_struct, wz, PMALLOC, PFREE, PREALLOC in PBS4; unfold wz;
          replace (SPF + Z.of_nat 8) with (bv_unsigned sp + -104) in PBS4 by (cbn; lia);
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL4| | eapply (lh_mok HI); exact HL4|].
        + (* [comment removed for export] *)
          step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
          step. step. step.
          replace (ret_pc (Z_to_bv 64 86496)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct HB4 as [[-> HPn]|[BNZ HPn]].
          * (* [comment removed for export] *)
            eapply evt_cut; [eapply (lh_free_null HI); reflexivity|]. cbv beta. intros ms5 ->.
            replace (ret_pc (Z_to_bv 64 0x130dc)) with (Z_to_bv 64 0x130dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            step. apply evt_done. cbv beta.
            pose proof (rw_cells_join3 m4 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
            eapply (print_epi_at 0x130e0); [right; reflexivity| exact FRj| reflexivity| exact ST4| exact MI4| exact ERR4| exact CJ4| exact FRM4| exact FA4| exact PR14| exact CH4| exact HL4| left; split; [reflexivity| exact HPn]].
          * (nelimp (blocks_lo _ _ _ _ _ _ HL4 (perm_in_head _ _ _ HPn)) 3%nat; intros Y1 Y4 _). try rewrite alloc_ceiling_eq in Y4.
            apply evt_done. cbv beta. eapply scps_bind.
            { eapply (lh_free HI) with (lo := lo) (A := buf4) (n := len4); rewrite ?E1;
                first [ exact HL4 | eapply perm_in_head; exact HPn | exact ST4 | exact ERR4 | exact MI4 | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
            cbv beta. intros ms5 mo5 PO.
            (nelim PO 22%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 -> MI5 ST5 ERR5 PR5 HL5).
            rewrite E1 in ST5, PR5.
            replace (ret_pc (Z_to_bv 64 0x130dc)) with (Z_to_bv 64 0x130dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            pose proof (perm_cb_remove _ _ _ _ HPn (lh_nodup HI _ _ _ _ HL4)) as HP5.
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR5) in FRh; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR5) in FRs; [| left; lia].
            apply (cj_pres_rw_cells _ _ _ _ _ _ PR5) in PBS4; [| left; lia].
            apply (CJST_pres _ _ _ _ PR5) in CJ4.
            apply (cj_chain_pres _ _ _ _ _ _ _ _ CH4) in PR5 as CH5. 2:{ intros bb Hb. eapply Permutation_in; [exact HP5| apply in_or_app; left; exact Hb]. }
            assert (PR15 : cj_pres (B ++ LR) (bv_unsigned sp) m m5).
            { eapply cj_pres_trans; [exact PR14|]. eapply cj_pres_weaken; [exact PR5| lia|]. intros bb Hb. eapply Permutation_in; [exact HP5| exact Hb]. }
            eapply scps_step_evt; [eapply (lh_mok HI); exact HL5|].
            step. apply evt_done. cbv beta.
            pose proof (rw_cells_join3 m5 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
            eapply (print_epi_at 0x130e0); [right; reflexivity| exact FRj| reflexivity| exact ST5| exact MI5| exact ERR5| exact CJ4| exact FRM4| exact FA4| exact PR15| exact CH5| exact HL5| left; split; [reflexivity| exact HP5]].
        + (* [comment removed for export] *)
          (nelimp (blocks_lo _ _ _ _ _ _ HL4 (perm_in_head _ _ _ HP4)) 3%nat; intros Y1 Y4 _).
          step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          step. step. apply evt_done. cbv beta.
          pose proof (rw_cells_join3 m4 _ _ _ _ FRh ltac:(replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia; exact PBS4) eq_refl FRs) as FRj.
          eapply (print_epi_at 0x130e0); [right; reflexivity| exact FRj| reflexivity| exact ST4| exact MI4| exact ERR4| exact CJ4| exact FRM4| exact FA4| exact PR14| exact CH4| exact HL4|].
          right. exists buf4, len4. split; [reflexivity|]. split; [lia| exact HP4].
    Qed.
  End Call.

  Ltac enter_print :=
    intros until errv; intros HL HP CH PNZ NMAX CJ SPB1 SPB2 SPAL ST CEIL LO ERR MI TP FRM A0 ARGS;
    unfold wz in A0; rewrite A0.

  Theorem print_spec : print_stmt HI.
  Proof.
    unfold print_stmt, print_pre_stmt. enter_print. unfold PRINT_ENTRY, wz.
    eapply print_main; eassumption.
  Qed.

  Theorem cjprint_spec : cjprint_stmt HI.
  Proof.
    unfold cjprint_stmt, print_pre_stmt. enter_print. unfold CJPRINT_ENTRY, wz.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|]. step. step. apply evt_done. cbv beta.
    eapply print_main; eassumption.
  Qed.

  Theorem cjprintu_spec : cjprintu_stmt HI.
  Proof.
    unfold cjprintu_stmt, print_pre_stmt. enter_print. unfold CJPRINTU_ENTRY, wz.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|]. step. step. apply evt_done. cbv beta.
    eapply print_main; eassumption.
  Qed.

  Theorem pbuffered_spec : pbuffered_stmt HI.
  Proof.
    unfold pbuffered_stmt, print_pre_stmt. enter_print. unfold PBUFD_ENTRY, wz.
    (nelim ARGS 3%nat; intros pre -> PRE). unfold wz.
    eapply pbuffered_main; eassumption.
  Qed.
End S.


End CeilWrap.
End CJ_print.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require NumFactsG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
Module CJ_pv_numB.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases CJ_pv_numA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.NumFacts_iface.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gch_numch : forall o, Forall num_gch o -> Forall (fun c => FmtFp_facts3.is_numch c = true) o.
Proof.
  intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. unfold FmtFp_facts3.is_numch.
  destruct Hc as [Hc|[->|[->|[->|[->| ->]]]]]; try reflexivity.
  replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma gch_bytes : forall o, Forall num_gch o -> Forall (fun c => 0 <= c < 256) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma gch_nox : forall o, Forall num_gch o -> Forall (fun c => c <> 120 /\ c <> 88) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma Forall_range_unsigned : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; cbn; constructor; [| exact IH]. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. Qed.

Lemma map_zb_unsigned : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma zb_map : forall l, F_fmt_fp_lib.zb l = map (Z_to_bv 8) l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dfin_of_test : forall vd : word,
  Z.shiftr (bv_unsigned (fabs_d vd)) 52 < 2047 -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047.
Proof.
  intros vd H. unfold fabs_d in H. rewrite Z_to_bv_unsigned in H.
  pose proof (bv_unsigned_in_range 64 vd) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite Z.land_ones in H by lia. unfold bv_wrap in H. change (bv_modulus 64) with (2^64) in H.
  rewrite (Z.mod_small (bv_unsigned vd mod 2^63) (2^64)) in H by (pose proof (Z.mod_pos_bound (bv_unsigned vd) (2^63)); lia).
  rewrite Z.shiftr_div_pow2 in H by lia. rewrite (Z.mod_small (bv_unsigned vd) (2^64)) by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma word_int_arg : forall w : word, exists i, bv_unsigned w mod 2^32 = i mod 2^32 /\ -2^31 <= i < 2^31.
Proof.
  intros w. exists ((bv_unsigned w + 2^31) mod 2^32 - 2^31).
  pose proof (bv_unsigned_in_range 64 w) as R. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma FAG18_set : forall F Fc (k : bv 5) v, FAG18 F Fc -> bv_unsigned k < 18 -> FAG18 F (bvmap_set k v Fc).
Proof.
  intros F Fc k v FA Hk r Hr. rewrite freg_get_other; [apply FA; exact Hr|]. unfold bv_eqb. apply Z.eqb_neq. lia.
Qed.

Lemma FAG18_call10 : forall F Fc Ft, FAG18 F Fc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get Fc k) -> FAG18 F Ft.
Proof. intros F Fc Ft FA H r Hr. rewrite (H r) by lia. apply FA. exact Hr. Qed.

Lemma FAG18_call3 : forall F Fc Ft, FAG18 F Fc ->
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get Ft k = reg_get Fc k) -> FAG18 F Ft.
Proof. intros F Fc Ft FA H r Hr. rewrite (H r) by lia. apply FA. exact Hr. Qed.

Lemma tx_after_len : forall (o : list Z) (tx : list byte),
  (length o < 32)%nat -> length tx = 32%nat -> length (F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) tx) = 32%nat.
Proof. intros o tx Ho Ht. rewrite length_app. cbn [length]. rewrite zb_map, length_map, length_skipn. lia. Qed.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  (* [comment removed for export] *)
  Hypothesis SPRD : F_printf_iface.sprintf_d_stmt.
  Hypothesis SPRG : forall prec, F_printf_iface.sprintf_g_stmt prec.
  Hypothesis SSC : Scan_iface.rsscanf_lg_stmt.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).
  Notation NCTX' := (NCTX HI sp m SPB LR PB fw lo).
  (* [comment removed for export] *)
  Ltac useA L := eapply (L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0).
  Notation PJ0' := (PJ0 sp). Notation PTST' := (PTST sp). Notation PTXT' := (PTXT sp).
  Notation PFH' := (PFH ra sp s0 s1 s2 s3 s4 s5 s6 F).

  Ltac facts :=
    pose proof CEIL as CEIL'; try rewrite alloc_ceiling_eq in CEIL'; pose proof LO as LO'; unfold PV_STACK, PV_BASE in LO';
    (nelimp PL 3%nat; intros PL1 PL2 PL3).

  Lemma canary_of : forall depc mm mo errv LB buf len off bs,
    NCTX' depc mm mo errv LB buf len off bs -> exists canary, F_pad.ssp_cells mm canary.
  Proof.
    intros until bs. intros CTX. pose proof CTX as (HL & _). (nelim (lh_ssp HI _ _ _ _ HL) 3%nat; intros G canary C).
    exists canary. unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard. unfold PGOT_SSP, PSSP, wz in G, C. split; [exact G| exact C].
  Qed.

  (* [comment removed for export] *)
  Lemma num_R : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    0 <= r <= 25 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13598) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA Hr.
    assert (L0 : length j0 = 8%nat) by (destruct H0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo _ _ _ _ _ _ _ _ _ _ _ _ CTX (pieces_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3) FRM FA) as ACT.
    pose proof CTX as (HL & _).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. apply evt_done. cbv beta.
    useA num_L; [exact ACT| exact L0| exact LTX| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G17 : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (vd : word)
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13584) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA DFIN. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (GTOT (bv_unsigned vd) 17 DFIN ltac:(right; reflexivity)) 4%nat; intros o EG OG OL).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. zstep. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_g_stmt in SPRG.
      eapply (SPRG 17) with (n := 32%nat) (junk := tx) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact GRET | exact GLEN25 | exact H2 | exact EG | right; reflexivity | reflexivity
              | exact (GFACTS _ _ _ _ ltac:(right; reflexivity) EG) | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PJ0 in H0. unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call psegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x13598)) with (Z_to_bv 64 0x13598) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_R m3 mo j0 t); [exact CTX3| exact H0| exact H1| unfold PTXT; exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_C : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (vd : word) (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> 0 <= r <= 25 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13554) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA DFIN Hr. facts.
    assert (L0 : length j0 = 8%nat) by (destruct H0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    (* [comment removed for export] *)
    assert (TAIL : forall (Fx : bvmap 5 word) (fcx : bv 32) (x10' : word), frm0 fcx -> FAG18 F Fx ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10' x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x13568) fcx None mm (seg_rom psegs))).
    { intros Fx fcx x10' FRMx FAx.
      step. step. step. step. step. step.
      step; rewrite bword_nez; if_cases K; [|].
      - apply evt_done. cbv beta.
        useA num_L; [| exact L0| exact LTX| exact Hr].
        eapply (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo); [exact CTX| exact (pieces_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3)| assumption|].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FAx.
      - apply evt_done. cbv beta.
        eapply num_G17; [exact CTX| exact H0| exact H1| exact H2| exact H3| assumption| | exact DFIN].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FAx. }
    unfold PTST in H1.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. step.
    step; rewrite bword_nez; if_cases K; [|].
    - eapply TAIL; [assumption|]. repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
    - step. eapply TAIL; [assumption|]. repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
  Qed.

  Ltac freg H n :=
    match goal with |- context [reg_get ?Fq ?r] =>
      let e := eval cbv in (bv_unsigned r) in
      lazymatch e with n => rewrite (H r eq_refl) end end.

  (* [comment removed for export] *)
  Lemma num_S : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (vd : word) (o : list Z) (r : Z)
      x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm (F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: tx) -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> Forall num_gch o -> r = zlength o -> 0 <= r <= 25 ->
    SCPS psegs POST
      (MS (mkR (Z_to_bv 64 0x13534) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13534) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA DFIN OG Er Hr. facts.
    assert (L0 : length j0 = 8%nat) by (destruct H0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    assert (LTX : length (F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: tx) = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof LTX as LREST. rewrite length_app, zb_map, length_map in LREST. cbn [length] in LREST.
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    pose proof (bv_unsigned_in_range 64 sp) as SPR.
    (* [comment removed for export] *)
    set (txt := o ++ 0 :: map bv_unsigned tx).
    assert (LT : zlength txt = 32) by (subst txt; unfold zlength in *; rewrite length_app; cbn [length]; rewrite length_map; lia).
    destruct (scan_sscanf_lg (o ++ [0])) as [[rr res]|] eqn:ES.
    2:{ exfalso. exact (scan_sscanf_lg_total_gen o (gch_bytes o OG) (gch_nox o OG) ES). }
    assert (ES' : scan_sscanf_lg txt = Some (rr, res)) by (subst txt; rewrite (SJUNK o _ (gch_numch o OG)); exact ES).
    assert (TXTB : bytes_at psegs mm (bv_unsigned sp + -112) (map (Z_to_bv 8) txt)).
    { subst txt. rewrite map_app. cbn [map]. rewrite map_zb_unsigned, <- zb_map.
      destruct H2 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY. }
    assert (AL8 : (bv_unsigned sp + -112 + zlength txt) mod 8 = 0).
    { rewrite LT. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as DM. rewrite SPAL, Z.add_0_r in DM. rewrite DM.
      replace (16 * (bv_unsigned sp / 16) + -112 + 32) with ((2 * (bv_unsigned sp / 16) - 10) * 8) by lia. apply Z.mod_mul. lia. }
    unfold PTST in H1. pose proof ERR as ERR0. unfold PERRNO in ERR0.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. zstep. zstep. zstep. step.
    eapply evt_cut.
    { unfold Scan_iface.rsscanf_lg_stmt in SSC.
      eapply SSC with (T := bv_unsigned sp + -112) (PD := bv_unsigned sp + -120) (txt := txt) (pre := o) (post := map bv_unsigned tx) (r := rr) (res := res) (djunk := t) (lo := lo) (canary := canary) (ev := errv);
        rewrite ?unsigned_lit by lia;
        first [ exact TXTB | exact H1 | exact ES' | exact MI | exact FRM | exact AL8 | exact ST | exact SSP | exact TP
              | subst txt; reflexivity
              | exact (gch_numch o OG)
              | unfold Scan_iface.RERRNO; exact ERR0
              | subst txt; apply Forall_app; split; [exact (gch_bytes o OG)| constructor; [lia| apply Forall_range_unsigned]]
              | reflexivity
              | f_equal; lia
              | unfold Scan_iface.RSSCANF_DEPTH, Scan_iface.RGLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 29%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m3 ev' -> MUc WMc MI3 FRM2 HF2 ST3 TST3 TXB3 SSP3 ERR3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
    unfold Scan_iface.RERRNO in MUc, ERR3. unfold Scan_iface.RSSCANF_DEPTH in *.
    unfold PJ0 in H0. unfold PTXT in H2. unfold PFH in H3. clear TXTB.
    transport_after_call psegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x1354c)) with (Z_to_bv 64 0x1354c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo ev' LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR3|].
      intros iv [<-|[<-|[<-|[]]]]; [left; cbn; lia| left; cbn; lia| right; reflexivity]. }
    assert (FA2 : FAG18 F F2) by (eapply FAG18_call3; [exact FA| exact HF2]).
    zstep. step. if_cases K; zify_cond K.
    - apply evt_done. cbv beta.
      eapply num_G17; [exact CTX3| exact H0| unfold PTST; exact TST3| exact H2| exact H3| exact FRM2| exact FA2| exact DFIN].
    - apply evt_done. cbv beta.
      eapply num_C; [exact CTX3| exact H0| unfold PTST; exact TST3| exact H2| exact H3| exact FRM2| exact FA2| exact DFIN| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G15 : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (vd : word)
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    (forall r : bv 5, bv_unsigned r = 8 -> reg_get Fc r = vd) -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1351c) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA HF8 DFIN. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (GTOT (bv_unsigned vd) 15 DFIN ltac:(left; reflexivity)) 4%nat; intros o EG OG OL).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. freg HF8 8. step. zstep. step. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_g_stmt in SPRG.
      eapply (SPRG 15) with (n := 32%nat) (junk := tx) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact GRET | exact GLEN25 | exact H2 | exact EG | left; reflexivity | reflexivity
              | exact (GFACTS _ _ _ _ ltac:(left; reflexivity) EG) | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PJ0 in H0. unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call psegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x13534)) with (Z_to_bv 64 0x13534) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_S m3 mo j0 t); [exact CTX3| exact H0| exact H1| exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| exact DFIN| exact OG| reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_D : forall mm mo j0 t tx Fc fcc errv LB buf len off bs (wi : word)
      x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PJ0' mm j0 -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 wi x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x134f8) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX H0 H1 H2 H3 FRM FA. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (word_int_arg wi) 3%nat; intros i Ei Ri).
    (nelim (DTOT i) 5%nat; intros o ED OG _ OL). specialize (OL Ri).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. zstep. step. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_d_stmt in SPRD.
      eapply SPRD with (n := 32%nat) (junk := tx) (i := i) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact H2 | exact Ei | exact Ri | exact ED | reflexivity
              | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PJ0 in H0. unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call psegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x13598)) with (Z_to_bv 64 0x13598) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_R m3 mo j0 t);
      [exact CTX3| exact H0| exact H1| unfold PTXT; exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| lia].
  Qed.
End S.


End CeilWrap.
End CJ_pv_numB.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module CJ_pv_num.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases CJ_pv_numA CJ_pv_numB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.NumFacts_iface.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  (* [comment removed for export] *)
  Hypothesis SPRD : F_printf_iface.sprintf_d_stmt.
  Hypothesis SPRG : forall prec, F_printf_iface.sprintf_g_stmt prec.
  Hypothesis SSC : Scan_iface.rsscanf_lg_stmt.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).
  Notation NCTX' := (NCTX HI sp m SPB LR PB fw lo).
  (* [comment removed for export] *)
  Ltac useA L := eapply (L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0).
  Notation PJ0' := (PJ0 sp). Notation PTST' := (PTST sp). Notation PTXT' := (PTXT sp).
  Notation PFH' := (PFH ra sp s0 s1 s2 s3 s4 s5 s6 F).

  Ltac facts :=
    pose proof CEIL as CEIL'; try rewrite alloc_ceiling_eq in CEIL'; pose proof LO as LO'; unfold PV_STACK, PV_BASE in LO';
    pose proof PL as (PL1 & PL2 & PL3).


  Hypothesis DEPN : dep + Z.of_nat n <= 2^40.
  Notation FH := [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma frame_pieces : forall mm j0 t mid,
    rw_cells psegs mm SPF ([CB 8 j0; C8 t] ++ mid ++ FH) -> cells_size mid = 32%nat ->
    PJ0' mm j0 /\ PTST' mm t /\ PTXT' mm (cells_bytes mid) /\ PFH' mm.
  Proof.
    clear. intros mm j0 t mid FR SZ.
    apply rw_cells_merge in FR. rewrite SZ in FR. cbn [app] in FR.
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [CB 8 j0] _)) in FR. destruct FR as [H0 FR].
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [C8 t] _)) in FR. destruct FR as [H1 FR].
    apply (proj1 (F_fwritex.rw_cells_app _ _ _ [CB 32 (cells_bytes mid)] _)) in FR. destruct FR as [H2 H3].
    cbn [cells_size csize Nat.add] in H1, H2, H3.
    replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in H1 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -112) in H2 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -80) in H3 by lia.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  Lemma pv_num : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x133d4) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX.
    destruct (cj_chain_cons_inv _ _ _ _ _ CH0 PNZ) as (d0 & nx & pv & ch & ty & p1 & vs & vi & p2 & vd & ky & Bv & Bk & Bcc & Bn & Ed & ND & TY & _ & SV & SK & CHC & CHN & EB).
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND (node_cells_size _ _ _ _ _ _ _ _ _ _) ltac:(rewrite EB; left; reflexivity)) as NDn.
    unfold node_cells in NDn.
    pose proof (lh_block_range HI _ _ _ _ _ _ (proj1 CTX) ltac:(eapply Permutation_in; [exact (proj1 (proj2 CTX))| right; apply BLR; rewrite EB; left; reflexivity])) as (_ & _ & _ & P4 & _). try rewrite alloc_ceiling_eq in P4.
    destruct (actx_nctx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo _ _ _ _ _ _ _ _ _ _ _ _ CTX) as (NC & FR & FRM & FA).
    pose proof NC as (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA). facts. unfold PERRNO in ERR.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & R2 & R3 & R4 & R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    pose proof (munch_refl [(SPF, SPF + 48)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    pose proof CJ as (CJa & (ge1 & ge2 & CJb) & CJc). unfold PHOOKS, PGERROR, PLCONV, PDOTSTR, PMALLOC, PFREE, PREALLOC, wz in CJa, CJb, CJc.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    step. step. step. step.
    step. step. step. step. step. step. step. fix_lit_store.
    lazymatch goal with |- context [zxb ?b] => change (zxb b) with (Z_to_bv 64 46) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    assert (NC0 : NCTX' dep m9 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact NC| exact MU| exact WM| exact MI| exact ST| unfold PERRNO; exact ERR|].
      intros iv [<-|[]]. left. cbn. lia. }
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      pose proof (dfin_of_test vd K0) as DFIN.
      step. step. step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?rest) =>
        change (a :: b :: c :: d :: e :: f :: g :: rest) with ([a; b] ++ [c; d; e; f; g] ++ rest) in FR end.
      destruct (frame_pieces _ _ _ _ FR eq_refl) as (H0 & H1 & H2 & H3).
      if_cases K1.
      + (* [comment removed for export] *) apply evt_done. cbv beta.
        eapply (num_G15 HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0 SPRG SSC GRET GLEN25 GFACTS GTOT SJUNK); [exact NC0| exact H0| exact H1| exact H2| exact H3| assumption| | | exact DFIN].
        * repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
        * intros r Hr. apply freg_get_same. rewrite Hr. reflexivity.
      + (* [comment removed for export] *) apply evt_done. cbv beta.
        eapply (num_D HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0 SPRD DTOT); [exact NC0| exact H0| exact H1| exact H2| exact H3| assumption|].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
    - (* [comment removed for export] *)
      step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?rest) =>
        change (a :: b :: c :: d :: e :: f :: g :: rest) with ([a; b] ++ [c; d; e; f; g] ++ rest) in FR end.
      apply rw_cells_merge in FR. cbn [cells_size csize cells_bytes cbytes Nat.add] in FR.
      step. fix_lit_store. step. fix_lit_store. step. step.
      lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?rest) =>
        change (a :: b :: c :: d :: e :: rest) with ([a; b] ++ [c; d; e] ++ rest) in FR end.
      destruct (frame_pieces _ _ _ _ FR eq_refl) as (H0 & H1 & H2 & H3).
      assert (L0 : length (firstn 8 (firstn 16 loc)) = 8%nat) by (destruct H0 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m8 end.
      assert (NC1 : NCTX' dep m8 mo errv LB buf len off bs).
      { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact NC| exact MU| exact WM| exact MI| exact ST| unfold PERRNO; exact ERR|].
        intros iv [<-|[]]. left. cbn. lia. }
      apply evt_done. cbv beta.
      useA num_E; [eapply (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo); [exact NC1| eapply pieces_join; [exact H0| exact H1| exact H2| exact H3]| assumption| repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]); exact FA]
                  | exact L0 | destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W | lia].
  Qed.
End S.

Theorem pv_num_case : forall HI,
  F_printf_iface.sprintf_d_stmt -> (forall prec, F_printf_iface.sprintf_g_stmt prec) -> Scan_iface.rsscanf_lg_stmt ->
  F_printf_iface.FMT_G_RET -> F_printf_iface.FMT_G_LEN25 ->
  NUM_FMT_G_FACTS -> NUM_FMT_G_TOTAL -> NUM_FMT_D_TOTAL -> NUM_SSCANF_JUNK ->
  forall n, pv_case_at PV_NUM_ENTRY HI n.
Proof.
  intros HI SPRD SPRG SSC GRET GLEN25 GFACTS GTOT DTOT SJUNK n. unfold pv_case_at, PV_NUM_ENTRY.
  intros until lo. intros PL CEIL LO TP SPhi N1 BLR SPAL DEPN DEP0 PNZ CH0 REC. intros.
  eapply pv_num; eassumption.
Qed.


End CeilWrap.
End CJ_pv_num.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_arr.CJ_pv_cases.
Import CJ_pv_objB.
Import CJ_pv_num.
Import CJ_pvalue.
Import CJ_print.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require NumFactsG.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.NumFactsG.NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import NumFactsG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface Scan_iface F_vsnprintf F_sscanf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Theorem pv_obj_case' : forall HI n, pv_case_at PV_OBJ_ENTRY HI n.
Proof. intros HI n. exact (pv_obj_case HI F_vsnprintf.sprintf_u04x_proof n). Qed.

Theorem pv_num_case' : forall HI n, pv_case_at PV_NUM_ENTRY HI n.
Proof.
  intros HI n.
  exact (pv_num_case HI F_vsnprintf.sprintf_d_proof F_vsnprintf.sprintf_g_proof F_sscanf.rsscanf_lg_proof
           fmt_g_ret_proof fmt_g_len25_proof num_fmt_g_facts_proof num_fmt_g_total_proof num_fmt_d_total_proof num_sscanf_junk_proof n).
Qed.

Theorem pvalue_spec' : forall HI n, pvalue_spec_at HI n.
Proof. intros HI n. exact (pvalue_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI) n). Qed.

Theorem print_spec' : forall HI, print_stmt HI.
Proof. intros HI. exact (print_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprint_spec' : forall HI, cjprint_stmt HI.
Proof. intros HI. exact (cjprint_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem cjprintu_spec' : forall HI, cjprintu_stmt HI.
Proof. intros HI. exact (cjprintu_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.

Theorem pbuffered_spec' : forall HI, pbuffered_stmt HI.
Proof. intros HI. exact (pbuffered_spec HI F_vsnprintf.sprintf_u04x_proof (pv_obj_case' HI) (pv_num_case' HI)). Qed.


End CeilWrap.
