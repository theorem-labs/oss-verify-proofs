(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_fm RF_huf_fdw_st.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AProg_kit ABytes AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_seg AF_huf_fdw_top1 AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_fdt_defs.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section FTF.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation TB := (DT + 4).
  Notation TBC := (concat (map fse_cell_bytes (dt_cells d))).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis STK0 : stk bsegs m0 lo SP1.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 1.
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis TBB : bytes_at bsegs m0 TB TBC.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis NS : zlen bs <= 65536.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis RESOK : dres_ok (decompress_usingDTable bs d dcap true).
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis MI0 : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Notation R := (decompress_usingDTable bs d dcap true).
  Hypothesis K : forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch W0 m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] -> rw_cells bsegs m1 (SP1 + 32) FRC ->
       dresA DST dcap R m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs)).
  Notation ftA_inv := (AF_huf_fdt_defs.ftA_inv m0 SPV FF DST dcap S0 DT lo bs d).

  Notation FN pc mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac fappW := unfold appW; repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGH, KLOW; lia |]); apply Forall_nil.
  Ltac ftA_lin :=
    pose proof atop_range as ATR; pose proof (spaf_props SPV SP16) as (SPAB & SPA32);
    pose proof (ablk_lin _ _ HDT) as (HDTa & HDTb & HDTc & HDTd);
    pose proof (ablk_lin _ _ HDST) as (HDSa & HDSb & HDSc & HDSd); pose proof (ablk_lin _ _ HS0) as (HSa & HSb & HSc & HSd);
    unfold AIMG_HI in HDTa, HDSa, HSa; unfold DEC_STACK in LO.

  Lemma ffA_cb : forall mm x jp junk, ftA_inv mm x jp junk -> exists j, rw_cells bsegs mm (SP1 + 80) [CB 72 j].
  Proof.
    intros mm x jp junk I. destruct I as (_ & _ & _ & _ & _ & _ & H1 & H2 & _).
    assert (H : rw_cells bsegs mm (SP1 + 80)
                  ([C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)]
                   ++ bitdz_cellsA S0 (de_bd x) jp)).
    { apply (proj2 (ABytes.rw_cells_app bsegs mm (SP1 + 80) _ _)). split; [exact H1|].
      cbn [cells_size csize]. replace (SP1 + 80 + Z.of_nat (8 + (8 + (8 + (8 + 0))))) with (SP1 + 112) by lia. exact H2. }
    destruct (rw_cells_forget bsegs mm _ _ H) as [j Hj]. exists j. exact Hj.
  Qed.

  Lemma ffA_art : forall m, munch W0 m0 m -> wmono bsegs m0 m -> artcells m.
  Proof.
    intros m MU WM. ftA_lin. pose proof RTC as A0. unfold artcells in A0 |- *.
    repeat match type of A0 with _ /\ _ => let H := fresh "AC" in destruct A0 as [H A0] end.
    repeat match goal with |- _ /\ _ => split end;
      (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [disjoint_from cells_size csize]; lia]).
  Qed.

  Lemma ffA_ok : forall mm x jp junk (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    ftA_inv mm x jp junk -> R = Ok (de_out x) -> zlen (de_out x) <= dcap ->
    evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 (zlen (de_out x)))
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
               y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x98318) fc None mm (seg_rom bsegs)).
  Proof.
    intros mm x jp junk y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 I RE L.
    destruct (ffA_cb mm x jp junk I) as [j CB].
    destruct I as (MU & WM & MI & STK & _ & FRC1 & _ & _ & OUT & LJ & _).
    eapply (K mm (zlen (de_out x)) j); try eassumption.
    - rewrite RE. unfold dresA. split; [reflexivity | exists junk; split; assumption].
    - lia.
  Qed.

  Lemma ffA_inv0 : forall m x jp junk,
    munch W0 m0 m -> wmono bsegs m0 m -> mem_inv bsegs m -> stk bsegs m lo SP1 ->
    rw_cells bsegs m (SP1 + 32) FRC ->
    rw_cells bsegs m (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) ->
    u8arr bsegs m DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m S0 (map (Z_to_bv 8) bs) ->
    ftA_inv m x jp junk.
  Proof.
    intros m x jp junk MU WM MI STK FRC1 FO BD OUT LJ SRC1.
    ftA_lin.
    assert (AW : appW W0) by (pose proof HDST as HDSx; unfold ablk, KLS, AIMG_HI in HDSx; fappW).
    pose proof (ffA_art m MU WM) as ART.
    assert (TBL : zlen TBC = 4 * 2^tl) by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (TB1 : bytes_at bsegs m TB TBC)
      by (eapply bytes_at_transport; [exact TBB | exact MU | cbn [disjoint_from]; rewrite TBL; lia]).
    assert (Z1 : zshadow m (SP1 + 80) 72) by (eapply zshadow_appW; [exact ZOBJ | exact MU | exact AW | lia | lia]).
    assert (Z2 : zshadow m DT (4 + 4 * 2^tl)) by (eapply zshadow_appW; [exact ZDT | exact MU | exact AW | lia | lia]).
    assert (Z3 : zshadow m DST dcap) by (eapply zshadow_appW; [exact ZDST | exact MU | exact AW | lia | lia]).
    assert (Z4 : zshadow m ABIT_MASK 128)
      by (eapply zshadow_appW; [exact ZMK | exact MU | exact AW | unfold ABIT_MASK; lia | unfold ABIT_MASK; lia]).
    assert (U1 : 0 < zlen bs -> unpoisoned m S0 (S0 + zlen bs))
      by (intros NZ; eapply unpoisoned_appW; [exact USRC | exact MU | exact AW | lia | lia]).
    exact (conj MU (conj WM (conj MI (conj STK (conj ART (conj FRC1 (conj FO (conj BD (conj OUT (conj LJ
             (conj SRC1 (conj TB1 (conj Z1 (conj Z2 (conj Z3 (conj Z4 U1)))))))))))))))).
  Qed.

  Ltac fzl :=
    repeat match goal with H : ?T |- _ =>
      lazymatch type of T with Prop =>
        lazymatch T with
        | _ <= _ => fail | _ < _ => fail | _ = _ :> Z => fail | _ <= _ <= _ => fail | _ <= _ < _ => fail
        | _ => clear H end end end;
    Z.div_mod_to_equations; lia.
  Ltac fzdec :=
    repeat match goal with
    | |- context [?a =? ?b] =>
        first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; fzl)
              | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; fzl) ]
    | |- context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; fzl)
              | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; fzl) ]
    end.
  Ltac fzbr :=
    unfold zx32; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?bv_lts_zero_r, ?bv_lts_zero_l, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite ?land64_mod, ?Z.shiftl_mul_pow2 by lia; try change (2 ^ 2) with 4;
    rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 3) with 8;
    repeat match goal with |- context [?a mod 2 ^ ?k] =>
      rewrite (Z.mod_small a (2 ^ k)) by fzl end;
    fzdec; vm_compute; reflexivity.
  Ltac br :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with false; [cbv iota | symmetry; fzbr]
            | replace c with true; [cbv iota | symmetry; fzbr] ] end.

  Ltac ftA_acc := lazymatch goal with
    | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + _), 1%nat) =>
        match goal with H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ =>
          constr_eq A A'; apply (acc_shZ R A len a H); lia end
    | |- acc_in ?R _ => match goal with H : rng R _ _ |- _ => solve_acc_with H end
    end.
  Local Ltac acc_hint ::= first [ bdtA_acc_hint | ftA_acc ].

  Ltac pc_in P1 P2 := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
    let b := eval vm_compute in (orb (Z.eqb (bv_unsigned pc) P1) (Z.eqb (bv_unsigned pc) P2)) in
    lazymatch b with true => idtac end end.
  Ltac wto P1 P2 := repeat (tryif pc_in P1 P2 then fail else first [ zstep | br ]).
  Local Tactic Notation "wton" int_or_var(n) constr(P1) constr(P2) :=
    do n (tryif pc_in P1 P2 then idtac else first [ zstep | br ]).
  Ltac pcq := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PCIF"
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
      let v := eval vm_compute in (bv_unsigned pc - 0x98160) in idtac "PC" v end.
  Ltac wtr n P1 P2 := lazymatch n with
    | O => idtac
    | Datatypes.S ?k => tryif pc_in P1 P2 then idtac else
        (pcq; tryif first [ zstep | br ] then wtr k P1 P2 else idtac "STUCK") end.
  Ltac pcp := lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac "PCIF"
    | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) =>
      let v := eval vm_compute in (bv_unsigned pc - 0x98160) in idtac "PC" v end.

  Lemma ffA_upd : forall (l r : list byte) (y b : byte), upd (l ++ y :: r) (length l) b = l ++ b :: r.
  Proof. induction l as [|a l IH]; intros r y b; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma ffA_inv_byte : forall m1 x jp junk (o0 s1a s2n : Z) (d1 : bitD) (j i : Z),
    munch W0 m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo SP1 ->
    rw_cells bsegs m1 (SP1 + 32) FRC ->
    rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 s2n); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 s1a); C8 (Z_to_bv 64 TB)] ->
    rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 d1 jp) ->
    u8arr bsegs m1 DST (map (Z_to_bv 8) (de_out x) ++ junk) -> zlen junk = dcap - zlen (de_out x) ->
    bytes_at bsegs m1 S0 (map (Z_to_bv 8) bs) ->
    store_ok bsegs m1 (Z_to_bv 64 (DST + j + i)) 1%nat = true ->
    zlen (de_out x) = j + i -> zlen (de_out x) < dcap -> 0 <= j -> 0 <= i ->
    ftA_inv (write_to_mem m1 (Z_to_bv 64 (DST + j + i)) [Z_to_bv 8 o0]) (mkDec (de_out x ++ [o0]) s1a s2n d1) jp
      (List.tl junk).
  Proof.
    intros m1 x jp junk o0 s1a s2n d1 j i MU WM MI STK FRC1 FO BD OUT LJ SRC1 SOK LJI LD J0 I0.
    ftA_lin.
    destruct junk as [|b0 junk0]; [cbn [length] in LJ; lia|]. cbn [List.tl].
    change (Z_to_bv 64 (DST + j + i)) with (wa (DST + j + i)).
    apply ffA_inv0.
    - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
    - apply wmono_write; exact WM.
    - apply mem_inv_store; [exact MI | exact SOK].
    - apply stk_write; [exact STK | lia | cbn [length]; lia].
    - apply rw_cells_frame; [exact FRC1 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact FO | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - apply rw_cells_frame; [exact BD | lia | cbn [length]; lia | unfold bitdz_cellsA; cbn [cells_size csize length]; lia].
    - pose proof (u8arr_write bsegs m1 DST _ (j + i) (Z_to_bv 8 o0) OUT
                    ltac:(rewrite length_app, length_map; cbn [length]; lia)) as U.
      replace (DST + (j + i)) with (DST + j + i) in U by lia.
      replace (Z.to_nat (j + i)) with (length (map (Z_to_bv 8) (de_out x))) in U by (rewrite length_map; lia).
      rewrite ffA_upd in U. cbn [de_out]. rewrite map_app. cbn [map]. rewrite <- app_assoc. exact U.
    - cbn [de_out]. rewrite length_app. cbn [length] in LJ |- *. lia.
    - apply bytes_at_write_other; [exact SRC1 | lia | cbn [length]; lia | rewrite length_map; cbn [length]; lia].
  Qed.

  Ltac ff_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
  Ltac fsub := let z := fresh "z" in let HX := fresh "HX" in intros z HX; cbn [outside] in *; unfold DSYM_STACK in *; lia.

  Lemma ftA_f1 : forall x mm jp junk (j i : Z) (st : dstatus) (d1r : bitD)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
    reload_dstream bs (de_bd x) = Ok (st, d1r) -> 64 < bd_bits (de_bd x) ->
    bitd_ok bs (de_bd x) -> zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    R = (let! q := decode_sym d true (de_s2 x) d1r in let '(o1, _, _) := q in Ok (de_out x ++ [o1])) ->
    evtF bsegs RNG Q (FN 0x99bc8 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31).
  Proof using All.
    intros x mm jp junk j i st d1r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31
      RLD BG BOK LJI LD J0 I0 I RE.
    ftA_lin.
    unfold reload_dstream in RLD. rewrite (proj2 (Z.ltb_lt _ _) BG) in RLD. injection RLD as <- <-.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    assert (P2T : 2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in P2T. change (2^12) with 4096 in P2T.
    revert RE.
    lazymatch goal with |- _ = bind ?t _ -> _ => destruct t as [[[o1 s2'] d2] | e | |] eqn:DS2 end;
      intros RE;
      [ | exfalso; exact (RF_huf_fdw_st.decode_sym_not_err _ _ _ _ _ DS2)
        | exfalso; pose proof RESOK as RK; rewrite RE in RK; exact RK
        | exfalso; pose proof RESOK as RK; rewrite RE in RK; exact RK ].
    cbn [bind] in RE.
    apply (proj1 (ABytes.rw_cells_app _ _ _ [_; _] _)) in FO2 as [FA FB].
    lazymatch type of FB with rw_cells _ _ ?A _ => replace A with (SP1 + 96) in FB by (cbn [cells_size csize]; lia) end.
    wto 0x99be0 ADSYM_FAST.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      lazymatch goal with
      | M : munch W0 m0 mg, WW : wmono bsegs m0 mg, MI' : mem_inv bsegs mg, ST' : stk bsegs mg lo SP1,
        FR' : rw_cells bsegs mg (SP1 + 32) FRC, FA' : rw_cells bsegs mg (SP1 + 80) _, FB' : rw_cells bsegs mg (SP1 + 96) _,
        BD' : rw_cells bsegs mg (SP1 + 112) _, OU' : u8arr bsegs mg DST _, SR' : bytes_at bsegs mg S0 _ |- _ =>
        pose proof (ffA_inv0 mg (mkDec (de_out x) (de_s1 x) (de_s2 x)
                                  (mkBD (bd_cont (de_bd x)) (bd_bits (de_bd x)) (bd_ptr (de_bd x)) true)) jp junk
                      M WW MI' ST' FR'
                      ltac:(apply (proj2 (ABytes.rw_cells_app _ _ _ [_; _] [_; _])); split;
                            [exact FA' | cbn [cells_size csize]; replace (SP1 + 80 + Z.of_nat (8 + (8 + 0))) with (SP1 + 96) by lia; exact FB'])
                      ltac:(unfold bitdz_cellsA; cbn [bd_zero bd_cont bd_bits bd_ptr]; exact BD') OU' LJ2 SR') as I1
      end end.
    destruct I1 as (_ & _ & _ & _ & ART1 & _ & _ & _ & _ & _ & _ & TB1 & Z11 & Z21 & Z31 & Z41 & _).
    pose proof fse_dsym_fast_proofA as DSF. unfold dsym_stmtA, ADSYM_FAST, mkR in DSF.
    eapply evtF_cut.
    { eapply DSF with (DS := SP1 + 80) (BD := SP1 + 112) (SPV := SP1) (lo := lo) (dt := d) (S := S0) (DT := DT) (jp := jp)
        (d := mkBD (bd_cont (de_bd x)) (bd_bits (de_bd x)) (bd_ptr (de_bd x)) true);
      clear DSF;
      first [ exact DS2 | eassumption | reflexivity | (cbn [bd_cont bd_bits]; lia) | (unfold DSYM_STACK; lia)
            | (unfold bitdz_cellsA; cbn [bd_zero bd_cont bd_bits bd_ptr]; eassumption)
            | (eapply rng_sub; [exact RO | lia | lia])
            | (eapply rng_sub; [exact RSTK | unfold DSYM_STACK; lia | unfold DSYM_STACK; lia])
            | (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia)
            | (eapply zshadow_sub; [exact Z11 | lia | lia])
            | fzl ]. }
    intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & m1 & -> & MU1 & WM1 & MI1 & STK1 & DS1 & BD1).
    ff_retlit.
    lazymatch goal with
    | M : munch W0 m0 ?mg, WW : wmono bsegs m0 ?mg, MU1' : munch _ ?mg m1,
      FR' : rw_cells bsegs ?mg (SP1 + 32) FRC, FB' : rw_cells bsegs ?mg (SP1 + 96) _,
      OU' : u8arr bsegs ?mg DST _, SR' : bytes_at bsegs ?mg S0 _ |- _ =>
        assert (MW1 : munch W0 m0 m1) by (eapply munch_trans; [exact M | eapply munch_weaken; [| exact MU1']; fsub]);
        pose proof (wmono_trans bsegs _ _ _ WW WM1) as WM01;
        pose proof (rw_cells_transport bsegs _ _ _ _ _ FR' MU1' WM1 ltac:(cbn [disjoint_from cells_size csize]; unfold DSYM_STACK; lia)) as FRC1;
        pose proof (rw_cells_transport bsegs _ _ _ _ _ FB' MU1' WM1 ltac:(cbn [disjoint_from cells_size csize]; unfold DSYM_STACK; lia)) as FB1;
        pose proof (u8arr_transport bsegs _ _ _ _ _ OU' MU1' WM1 ltac:(cbn [disjoint_from]; rewrite length_app, length_map; unfold DSYM_STACK; lia)) as OUT1;
        pose proof (bytes_at_transport bsegs _ _ _ _ _ SR' MU1' ltac:(cbn [disjoint_from]; rewrite length_map; unfold DSYM_STACK; lia)) as SRC1
    end.
    pose proof (ffA_inv0 m1 (mkDec (de_out x) (de_s1 x) s2' d2) jp junk MW1 WM01 MI1 STK1 FRC1
                  ltac:(apply (proj2 (ABytes.rw_cells_app _ _ _ [_; _] [_; _])); split;
                        [exact DS1 | cbn [cells_size csize]; replace (SP1 + 80 + Z.of_nat (8 + (8 + 0))) with (SP1 + 96) by lia; exact FB1])
                  BD1 OUT1 LJ2 SRC1) as I2.
    destruct I2 as (_ & _ & _ & _ & ART2 & _ & _ & _ & _ & _ & _ & TB3 & Z12 & Z22 & Z32 & Z42 & _).
    pose proof (zsh_cell m1 DST dcap (DST + j + i + 1) Z32 ltac:(lia) ltac:(lia)) as SH6.
    pose proof (AProg_kit.shad_lt_KHIGH (DST + j + i + 1) ltac:(lia) ltac:(unfold KEND; lia)) as SB6.
    unfold ASHOFF in SH6, SB6.
    lazymatch type of SB6 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    pose proof (u8arr_store_ok bsegs m1 DST _ (j + (i + 1)) (Z_to_bv 64 (DST + j + (i + 1))) OUT1
                  ltac:(rewrite length_app, length_map; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    assert (FO1 : rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 s2'); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)])
      by (apply (proj2 (ABytes.rw_cells_app _ _ _ [_; _] [_; _])); split;
          [exact DS1 | cbn [cells_size csize]; replace (SP1 + 80 + Z.of_nat (8 + (8 + 0))) with (SP1 + 96) by lia; exact FB1]).
    pose proof (ffA_inv_byte m1 x jp junk o1 (de_s1 x) s2' d2 j (i + 1) MW1 WM01 MI1 STK1 FRC1 FO1 BD1 OUT1 LJ2 SRC1 SOK
                  ltac:(lia) ltac:(lia) J0 ltac:(lia)) as I3.
    wto 0x99c40 0x98318.
    rewrite FseWalkKit.le1_lit.
    pose proof I3 as I3k.
    destruct I3k as (MU3 & WM3 & MI3 & STK3 & ART3 & FRC3 & FO3 & BD3 & OUT3 & LJ3 & SRC3 & TB3' & Z13 & Z23 & Z33 & Z43 & U13).
    unfold bitdz_cellsA in BD3.
    wto 0x98318 0x98318.
    replace (DST + j + i + 2 - DST) with (zlen (de_out (mkDec (de_out x ++ [o1]) (de_s1 x) s2' d2)))
      by (cbn [de_out]; rewrite length_app; cbn [length]; lia).
    eapply ffA_ok; [exact I3 | cbn [de_out]; exact RE | cbn [de_out]; rewrite length_app; cbn [length]; lia].
  Qed.

  Lemma ftA_f2 : forall x mm jp junk (j i : Z) (st : dstatus) (d2r : bitD)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
    reload_dstream bs (de_bd x) = Ok (st, d2r) -> 64 < bd_bits (de_bd x) ->
    bitd_ok bs (de_bd x) -> zlen (de_out x) = j + i + 2 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
    ftA_inv mm x jp junk ->
    R = (let! q := decode_sym d true (de_s1 x) d2r in let '(o2, _, _) := q in Ok (de_out x ++ [o2])) ->
    evtF bsegs RNG Q (FN 0x99c04 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31).
  Proof using All.
    intros x mm jp junk j i st d2r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31
      RLD BG BOK LJI LD J0 I0 I RE.
    ftA_lin.
    unfold reload_dstream in RLD. rewrite (proj2 (Z.ltb_lt _ _) BG) in RLD. injection RLD as <- <-.
    pose proof I as Ik.
    destruct Ik as (MU & WM & MI & STK & ART & FRC2 & FO2 & BD2 & OUT2 & LJ2 & SRC2 & TB2 & Z1 & Z2 & Z3 & Z4 & U1).
    unfold bitdz_cellsA in BD2.
    pose proof BOK as BOK'. destruct BOK' as (BC & BBt & BP & BP8 & BPZ & BZ).
    assert (P2T : 2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia).
    change (2^5) with 32 in P2T. change (2^12) with 4096 in P2T.
    revert RE.
    lazymatch goal with |- _ = bind ?t _ -> _ => destruct t as [[[o2 s1'] d2] | e | |] eqn:DS2 end;
      intros RE;
      [ | exfalso; exact (RF_huf_fdw_st.decode_sym_not_err _ _ _ _ _ DS2)
        | exfalso; pose proof RESOK as RK; rewrite RE in RK; exact RK
        | exfalso; pose proof RESOK as RK; rewrite RE in RK; exact RK ].
    cbn [bind] in RE.
    apply (proj1 (ABytes.rw_cells_app _ _ _ [_; _] _)) in FO2 as [FA FB].
    lazymatch type of FB with rw_cells _ _ ?A _ => replace A with (SP1 + 96) in FB by (cbn [cells_size csize]; lia) end.
    wto 0x99c1c ADSYM_FAST.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      lazymatch goal with
      | M : munch W0 m0 mg, WW : wmono bsegs m0 mg, MI' : mem_inv bsegs mg, ST' : stk bsegs mg lo SP1,
        FR' : rw_cells bsegs mg (SP1 + 32) FRC, FA' : rw_cells bsegs mg (SP1 + 80) _, FB' : rw_cells bsegs mg (SP1 + 96) _,
        BD' : rw_cells bsegs mg (SP1 + 112) _, OU' : u8arr bsegs mg DST _, SR' : bytes_at bsegs mg S0 _ |- _ =>
        pose proof (ffA_inv0 mg (mkDec (de_out x) (de_s1 x) (de_s2 x)
                                  (mkBD (bd_cont (de_bd x)) (bd_bits (de_bd x)) (bd_ptr (de_bd x)) true)) jp junk
                      M WW MI' ST' FR'
                      ltac:(apply (proj2 (ABytes.rw_cells_app _ _ _ [_; _] [_; _])); split;
                            [exact FA' | cbn [cells_size csize]; replace (SP1 + 80 + Z.of_nat (8 + (8 + 0))) with (SP1 + 96) by lia; exact FB'])
                      ltac:(unfold bitdz_cellsA; cbn [bd_zero bd_cont bd_bits bd_ptr]; exact BD') OU' LJ2 SR') as I1
      end end.
    destruct I1 as (_ & _ & _ & _ & ART1 & _ & _ & _ & _ & _ & _ & TB1 & Z11 & Z21 & Z31 & Z41 & _).
    pose proof fse_dsym_fast_proofA as DSF. unfold dsym_stmtA, ADSYM_FAST, mkR in DSF.
    eapply evtF_cut.
    { eapply DSF with (DS := SP1 + 96) (BD := SP1 + 112) (SPV := SP1) (lo := lo) (dt := d) (S := S0) (DT := DT) (jp := jp)
        (d := mkBD (bd_cont (de_bd x)) (bd_bits (de_bd x)) (bd_ptr (de_bd x)) true);
      clear DSF;
      first [ exact DS2 | eassumption | reflexivity | (cbn [bd_cont bd_bits]; lia) | (unfold DSYM_STACK; lia)
            | (unfold bitdz_cellsA; cbn [bd_zero bd_cont bd_bits bd_ptr]; eassumption)
            | (eapply rng_sub; [exact RO | lia | lia])
            | (eapply rng_sub; [exact RSTK | unfold DSYM_STACK; lia | unfold DSYM_STACK; lia])
            | (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia)
            | (eapply zshadow_sub; [exact Z11 | lia | lia])
            | fzl ]. }
    intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & m1 & -> & MU1 & WM1 & MI1 & STK1 & DS1 & BD1).
    ff_retlit.
    lazymatch goal with
    | M : munch W0 m0 ?mg, WW : wmono bsegs m0 ?mg, MU1' : munch _ ?mg m1,
      FR' : rw_cells bsegs ?mg (SP1 + 32) FRC, FA' : rw_cells bsegs ?mg (SP1 + 80) _,
      OU' : u8arr bsegs ?mg DST _, SR' : bytes_at bsegs ?mg S0 _ |- _ =>
        assert (MW1 : munch W0 m0 m1) by (eapply munch_trans; [exact M | eapply munch_weaken; [| exact MU1']; fsub]);
        pose proof (wmono_trans bsegs _ _ _ WW WM1) as WM01;
        pose proof (rw_cells_transport bsegs _ _ _ _ _ FR' MU1' WM1 ltac:(cbn [disjoint_from cells_size csize]; unfold DSYM_STACK; lia)) as FRC1;
        pose proof (rw_cells_transport bsegs _ _ _ _ _ FA' MU1' WM1 ltac:(cbn [disjoint_from cells_size csize]; unfold DSYM_STACK; lia)) as FA1;
        pose proof (u8arr_transport bsegs _ _ _ _ _ OU' MU1' WM1 ltac:(cbn [disjoint_from]; rewrite length_app, length_map; unfold DSYM_STACK; lia)) as OUT1;
        pose proof (bytes_at_transport bsegs _ _ _ _ _ SR' MU1' ltac:(cbn [disjoint_from]; rewrite length_map; unfold DSYM_STACK; lia)) as SRC1
    end.
    assert (FO1 : rw_cells bsegs m1 (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 s1'); C8 (Z_to_bv 64 TB)])
      by (apply (proj2 (ABytes.rw_cells_app _ _ _ [_; _] [_; _])); split;
          [exact FA1 | cbn [cells_size csize]; replace (SP1 + 80 + Z.of_nat (8 + (8 + 0))) with (SP1 + 96) by lia; exact DS1]).
    pose proof (ffA_inv0 m1 (mkDec (de_out x) s1' (de_s2 x) d2) jp junk MW1 WM01 MI1 STK1 FRC1 FO1 BD1 OUT1 LJ2 SRC1) as I2.
    destruct I2 as (_ & _ & _ & _ & ART2 & _ & _ & _ & _ & _ & _ & TB3 & Z12 & Z22 & Z32 & Z42 & _).
    pose proof (zsh_cell m1 DST dcap (DST + j + i + 2) Z32 ltac:(lia) ltac:(lia)) as SH6.
    pose proof (AProg_kit.shad_lt_KHIGH (DST + j + i + 2) ltac:(lia) ltac:(unfold KEND; lia)) as SB6.
    unfold ASHOFF in SH6, SB6.
    lazymatch type of SB6 with _ <= ?K => assert (KH : K <= ATOP_MIN) by (vm_compute; intro HH; discriminate HH) end.
    pose proof ATOP_range as AR. unfold ATOP_MIN, ATOP_MAX in AR, KH.
    pose proof (u8arr_store_ok bsegs m1 DST _ (j + (i + 2)) (Z_to_bv 64 (DST + j + (i + 2))) OUT1
                  ltac:(rewrite length_app, length_map; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    pose proof (ffA_inv_byte m1 x jp junk o2 s1' (de_s2 x) d2 j (i + 2) MW1 WM01 MI1 STK1 FRC1 FO1 BD1 OUT1 LJ2 SRC1 SOK
                  ltac:(lia) ltac:(lia) J0 ltac:(lia)) as I3.
    wto 0x99c40 0x98318.
    rewrite FseWalkKit.le1_lit.
    pose proof I3 as I3k.
    destruct I3k as (MU3 & WM3 & MI3 & STK3 & ART3 & FRC3 & FO3 & BD3 & OUT3 & LJ3 & SRC3 & TB3' & Z13 & Z23 & Z33 & Z43 & U13).
    unfold bitdz_cellsA in BD3.
    wto 0x98318 0x98318.
    replace (DST + j + i + 3 - DST) with (zlen (de_out (mkDec (de_out x ++ [o2]) s1' (de_s2 x) d2)))
      by (cbn [de_out]; rewrite length_app; cbn [length]; lia).
    eapply ffA_ok; [exact I3 | cbn [de_out]; exact RE | cbn [de_out]; rewrite length_app; cbn [length]; lia].
  Qed.

End FTF.

End CANSEC1.
