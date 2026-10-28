(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmLeaf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition offs_ok (offs : list (Z * Z)) : bool :=
  forallb (fun on => (24 <=? fst on) && (0 <=? snd on) && (fst on + snd on <=? 11584))%bool offs.

Definition offs_acc (ins : list nat) (offs : list (Z * Z)) : bool := forallb (fun on => acc_ok ins (fst on) (snd on)) offs.

Definition offs_apart (offs : list (Z * Z)) (ks : list Z) : bool :=
  forallb (fun k => forallb (fun on => (k + 8 <=? fst on) || (fst on + snd on <=? k))%bool offs) ks.

Definition offs_wins (ff : Z) (offs : list (Z * Z)) : list (Z * Z) := map (fun on => (ff + fst on, ff + fst on + snd on)) offs.

Lemma offs_ok_in : forall offs k n, offs_ok offs = true -> In (k, n) offs -> 24 <= k /\ 0 <= n /\ k + n <= 11584.
Proof.
  intros offs k n Hok Hin. pose proof (proj1 (forallb_forall _ _) Hok (k, n) Hin) as K. cbn [fst snd] in K.
  apply andb_true_iff in K as [K K3]. apply andb_true_iff in K as [K1 K2].
  apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.leb_le in K3. lia.
Qed.

Lemma rw_cells_def_hi : forall m A cs a, rw_cells asegs m A cs -> AIMG_TOP <= A ->
  A <= a < A + Z.of_nat (cells_size cs) -> m (Z_to_bv 64 a) <> None.
Proof.
  intros m A cs a [[Hwf HB] _] Ha Hr. pose proof HB as (B0 & B1 & B).
  rewrite (cells_bytes_length cs Hwf) in B1, B.
  specialize (B (Z.to_nat (a - A)) ltac:(lia)). rewrite Z2Nat.id in B by lia. replace (A + (a - A)) with a in B by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:Eb;
    [| apply nth_error_None in Eb; rewrite (cells_bytes_length cs Hwf) in Eb; lia].
  change (wa a) with (Z_to_bv 64 a) in B. exact (def_of_mrd_hi m a b ltac:(lia) B).
Qed.

Section LeafW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pm_tl_cell : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k n,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    24 <= k -> 0 <= n -> k + n <= 11584 -> acc_ok ins k n = true ->
    tl_cell m (wa_s1 w) (wa_ff w + k) n.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k n OK X Hk Hn Hkn Hacc.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    unfold tl_cell. split; [| split; [| split; [| split]]].
    - eapply wr_at_sub; [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | change (fsz PM_FCLASS) with 16384; lia | lia].
    - apply (ff_accessible m (wa_ff w) ins k n (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); try lia; [unfold AAPP_HI; lia | exact Hacc].
    - eapply aconst_ok_app; [exact FA | cbn; lia | cbn; lia].
    - left. unfold TL_STACK. lia.
    - cbn. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, AFS_HDR in *. destruct FA as [FA|FA]; [left | right]; lia.
  Qed.

  Lemma pm_leafW : forall {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
      (Wf : X -> list (Z * Z)) (Qf : X -> mem -> word -> word -> mem -> Prop),
    tleaf entry STK PRE Wf Qf ->
    forall (x : X) (offs : list (Z * Z)) (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop) ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= STK <= 4096 -> Wf x = offs_wins (wa_ff w) offs -> offs_ok offs = true ->
    PRE x m (wa_s1 w) (PropExec.getr R 10%bv) (PropExec.getr R 11%bv) (PropExec.getr R 12%bv) (PropExec.getr R 13%bv) ->
    keys_nonneg (map fst tbl) = true -> incl ftbl' ftbl -> fkeys_ok (map fst ftbl') = true -> offs_apart offs (map fst ftbl') = true ->

    (forall r0 r1 m1 k n a, Qf x m r0 r1 m1 -> In (k, n) offs -> wa_ff w + k <= a < wa_ff w + k + n ->
       m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl' TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch ((wa_s1 w - STK, wa_s1 w) :: offs_wins (wa_ff w) offs) m m1 -> wmono asegs m m1 ->
       Qf x m (PropExec.getr R1 10%bv) (PropExec.getr R1 11%bv) m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros X entry STK PRE Wf Qf HL x offs w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q ftbl' OK XA KR VIS RF
           G2 G1 Hret2 Hret HSTK HW Hoffs HPRE Ht If Hfk Hap HQD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (wk_s1 H w OK) as (S7 & S8).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) as STK0.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK0 ltac:(lia)) as [STK1 STK2].
    rewrite (rfull_eq R RF) in VIS.
    eapply (ahh_evt_then H HH _); [exact KR | exact VIS | |].
    { eapply (HL x (PropExec.getr R 1%bv) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv)
                 (PropExec.getr R 5%bv) (PropExec.getr R 6%bv) (PropExec.getr R 7%bv) (PropExec.getr R 8%bv)
                 (PropExec.getr R 9%bv) (PropExec.getr R 10%bv) (PropExec.getr R 11%bv) (PropExec.getr R 12%bv)
                 (PropExec.getr R 13%bv) (PropExec.getr R 14%bv) (PropExec.getr R 15%bv) (PropExec.getr R 16%bv)
                 (PropExec.getr R 17%bv) (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv)
                 (PropExec.getr R 21%bv) (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv)
                 (PropExec.getr R 25%bv) (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) (PropExec.getr R 28%bv)
                 (PropExec.getr R 29%bv) (PropExec.getr R 30%bv) (PropExec.getr R 31%bv) F fc m (wa_lo w)).
      - rewrite G2, u64_of_Z by lia. exact STK1.
      - exact S1.
      - rewrite G2, u64_of_Z by lia. unfold APM_STACK in *. lia.
      - rewrite G2, u64_of_Z by lia. rewrite <- (Z.mul_1_l 16) at 1. clear - S8. Z.div_mod_to_equations. lia.
      - rewrite G2, u64_of_Z by lia. unfold AAPP_HI in *. lia.
      - exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA).
      - exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA).
      - rewrite G2, u64_of_Z by lia. exact HPRE. }
    intros msF1 mo1 KR1 MP1 POST.
    destruct POST as (t0 & t1 & t2 & a0' & a1' & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & VIS1 & MU & WM & MI & STK' & AC' & QQ).
    rewrite HW in MU. rewrite G2 in MU, STK'. rewrite !u64_of_Z in MU by lia. rewrite !u64_of_Z in STK' by lia.
    rewrite G1 in VIS1. rewrite (ret_pc_even ret Hret Hret2) in VIS1.
    set (W := (wa_s1 w - STK, wa_s1 w) :: offs_wins (wa_ff w) offs) in MU.

    assert (WIN : forall lo' hi', In (lo', hi') W -> (lo' = wa_s1 w - STK /\ hi' = wa_s1 w)
                                                  \/ (exists k n, In (k, n) offs /\ lo' = wa_ff w + k /\ hi' = wa_ff w + k + n
                                                                  /\ 24 <= k /\ 0 <= n /\ k + n <= 11584)).
    { intros lo' hi' Hin. subst W. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; left; split; reflexivity | right].
      unfold offs_wins in Hin. apply in_map_iff in Hin. destruct Hin as ([k n] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
      destruct (offs_ok_in offs k n Hoffs Hin) as (B1 & B2 & B3). exists k, n. repeat split; try assumption; reflexivity. }
    assert (DM : forall y, m y <> None -> m' y <> None).
    { intros y Hy. destruct (outside_dec W (bv_unsigned y)) as [Ho|(lo' & hi' & Hin & Hr)].
      - rewrite (MU y Ho). exact Hy.
      - pose proof (bv_unsigned_in_range 64 y) as Ry. change (bv_modulus 64) with (2 ^ 64) in Ry.
        rewrite <- (Z_to_bv_bv_unsigned y).
        destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)].
        + destruct STK' as (_ & _ & SS). destruct (SS (bv_unsigned y) ltac:(unfold APM_STACK in *; lia)) as [_ (b & Hb)].
          unfold wa in Hb. exact (def_of_mrd_hi m' (bv_unsigned y) _ ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) Hb).
        + apply (HQD a0' a1' m' k n (bv_unsigned y) QQ Hkn ltac:(lia)). rewrite Z_to_bv_bv_unsigned. exact Hy. }
    assert (FD : forall a len, (forall lo' hi', In (lo', hi') W -> a + len <= lo' \/ hi' <= a) -> disjoint_from W a len).
    { intros a len HA. clear - HA. induction W as [|[lo' hi'] W' IH]; [exact I|]. cbn [disjoint_from].
      split; [exact (HA lo' hi' (or_introl eq_refl)) | apply IH; intros lo'' hi'' Hin; exact (HA lo'' hi'' (or_intror Hin))]. }
    assert (STK'' : stk asegs m' (wa_lo w) (wa_sp0 w)).
    { apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
      eapply (stk_transport_disjoint asegs W m m' (wa_s1 w) (wa_sp0 w) STK2 MU WM).
      apply FD. intros lo' hi' Hin. destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; right; lia. }
    assert (X1 : PMXAT H LINV w s LB LBs m' mo c ins tbl ftbl' TB spal).
    { eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl ftbl' OK XA MU WM DM MI STK'').
      - apply Forall_forall. intros [lo' hi'] Hin. destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)].
        + left. cbn [fst snd]. unfold APM_STACK in *. lia.
        + right; left. cbn [fst snd]. change (fsz PM_FCLASS) with 16384. lia.
      - apply Forall_forall. intros [lo' hi'] Hin. cbn [fst snd]. destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; lia.
      - apply FD. intros lo' hi' Hin. unfold PM_NSH in *. rewrite Q13 in *.
        destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; [left; lia|].
        destruct Q6 as [Q6|Q6]; [right | left]; unfold SHBASE in *; lia.
      - apply FD. intros lo' hi' Hin. unfold O_WIDX, O_FLAGS, PARSER_SIZE in *.
        destruct (WIN lo' hi' Hin) as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; [left; lia|].
        unfold PARSER_SIZE in PAF. destruct PAF as [D|D]; [right | left]; lia.
      - apply incl_refl.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Ht kk (in_map fst _ (kk, e) Hin)) as Kk. apply Z.leb_le in Kk.
        apply FD. intros lo' hi' Hin'. destruct (WIN lo' hi' Hin') as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; [right; lia|].
        right. lia.
      - exact If.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Hfk kk (in_map fst _ (kk, e) Hin)) as Kb.
        apply andb_true_iff in Kb as [Kb1 Kb2]. apply Z.leb_le in Kb1. apply Z.leb_le in Kb2.
        pose proof (proj1 (forallb_forall _ _) Hap kk (in_map fst _ (kk, e) Hin)) as Ka.
        apply FD. intros lo' hi' Hin'. destruct (WIN lo' hi' Hin') as [[-> ->]|(k & n & Hkn & -> & -> & B1 & B2 & B3)]; [left; lia|].
        pose proof (proj1 (forallb_forall _ _) Ka (k, n) Hkn) as Kc. cbn [fst snd] in Kc.
        apply orb_true_iff in Kc as [Kc|Kc]; apply Z.leb_le in Kc; [left | right]; lia. }
    eapply K; [exact KR1 | exact VIS1 | apply rfull_mkR | eapply (pmxa_mpres H HH LINV); [exact X1 | exact MP1] | | exact MU | exact WM | exact QQ].
    intros r Hr.
    repeat (destruct Hr as [<-|Hr]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr.
  Qed.

  Lemma pm_opcode_split : opcode_split_stmtA ->
    forall (fw kwc kop : Z) (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop) ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_OPCODE_SPLIT) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 10%bv = Z_to_bv 64 (sx32A fw) -> 0 <= fw < 2 ^ 32 ->
    PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + kwc) -> PropExec.getr R 12%bv = Z_to_bv 64 (wa_ff w + kop) ->
    kwc mod 2 = 0 -> kop mod 2 = 0 -> (kwc + 2 <= kop \/ kop + 2 <= kwc) ->
    offs_ok [(kwc, 2); (kop, 2)] = true -> acc_ok ins kwc 2 = true -> acc_ok ins kop 2 = true ->
    keys_nonneg (map fst tbl) = true -> incl ftbl' ftbl -> fkeys_ok (map fst ftbl') = true ->
    offs_apart [(kwc, 2); (kop, 2)] (map fst ftbl') = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl' TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch ((wa_s1 w - TL_STACK, wa_s1 w) :: offs_wins (wa_ff w) [(kwc, 2); (kop, 2)]) m m1 -> wmono asegs m m1 ->
       rw_cells asegs m1 (wa_ff w + kwc) [C2 (Z_to_bv 64 (fw / 2 ^ 16))] ->
       rw_cells asegs m1 (wa_ff w + kop) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))] ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HL fw kwc kop w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q ftbl' OK XA KR VIS RF G2 G1 Hret2 Hret
           G10 Hfw G11 G12 Mwc Mop Hap2 Hoffs Hacc1 Hacc2 Ht If Hfk Hap K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    destruct (offs_ok_in _ kwc 2 Hoffs (or_introl eq_refl)) as (A1 & A2 & A3).
    destruct (offs_ok_in _ kop 2 Hoffs (or_intror (or_introl eq_refl))) as (B1 & B2 & B3).
    eapply (pm_leafW AT_OPCODE_SPLIT TL_STACK _ _ _ HL (fw, wa_ff w + kwc, wa_ff w + kop) [(kwc, 2); (kop, 2)]
              w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q ftbl' OK XA KR VIS RF G2 G1 Hret2 Hret);
      [unfold TL_STACK; lia | reflexivity | exact Hoffs | | exact Ht | exact If | exact Hfk | exact Hap | |].
    - cbn beta iota. split; [exact Hfw|]. split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
      split; [clear - Q2 Mwc; Z.div_mod_to_equations; lia|].
      split; [clear - Q2 Mop; Z.div_mod_to_equations; lia|].
      split; [exact (pm_tl_cell w s LB LBs m mo c ins tbl ftbl TB spal kwc 2 OK XA A1 A2 A3 Hacc1)|].
      split; [exact (pm_tl_cell w s LB LBs m mo c ins tbl ftbl TB spal kop 2 OK XA B1 B2 B3 Hacc2) | lia].
    - intros r0 r1 m1 k n a [QW QO] Hin Ha Hm. cbn in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      + eapply (rw_cells_def_hi m1 _ _ a QW); [unfold AIMG_TOP, AFS_HDR in *; lia | cbn; lia].
      + eapply (rw_cells_def_hi m1 _ _ a QO); [unfold AIMG_TOP, AFS_HDR in *; lia | cbn; lia].
    - intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 KEPT MU WM [QW QO].
      eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact KEPT | exact MU | exact WM | exact QW | exact QO].
  Qed.

  Lemma pm_lookup : forall pc nargs found hnd, lookup_shapeA pc nargs found hnd ->
    forall (x y kd : Z) (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop) ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 10%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
    (nargs = 2%nat -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + kd)) ->
    (nargs = 3%nat -> PropExec.getr R 11%bv = Z_to_bv 64 (sx32A y) /\ 0 <= y < 2 ^ 32 /\ PropExec.getr R 12%bv = Z_to_bv 64 (wa_ff w + kd)) ->
    kd mod 8 = 0 -> offs_ok [(kd, 8)] = true -> acc_ok ins kd 8 = true ->
    keys_nonneg (map fst tbl) = true -> incl ftbl' ftbl -> fkeys_ok (map fst ftbl') = true ->
    offs_apart [(kd, 8)] (map fst ftbl') = true ->
    mdef m (wa_ff w + kd) 8 ->
    (forall msF1 mo1 m1 R1 (r : Z), as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl' TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch ((wa_s1 w - TL_STACK, wa_s1 w) :: offs_wins (wa_ff w) [(kd, 8)]) m m1 -> wmono asegs m m1 ->
       PropExec.getr R1 10%bv = Z_to_bv 64 r -> - 2 ^ 31 <= r < 2 ^ 31 -> (r = 0 <-> found x y) ->
       (r = 0 -> exists d, rw_cells asegs m1 (wa_ff w + kd) [C8 (Z_to_bv 64 d)] /\ hnd d x y) ->
       (r <> 0 -> forall a, wa_ff w + kd <= a < wa_ff w + kd + 8 -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros pc nargs found hnd HL x y kd w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q ftbl' OK XA KR VIS RF G2 G1 Hret2 Hret
           G10 Hx G2a G3a Mkd Hoffs Hacc Ht If Hfk Hap MD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    destruct (offs_ok_in _ kd 8 Hoffs (or_introl eq_refl)) as (A1 & A2 & A3).
    eapply (pm_leafW pc TL_STACK _ _ _ HL (x, y, wa_ff w + kd) [(kd, 8)]
              w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q ftbl' OK XA KR VIS RF G2 G1 Hret2 Hret);
      [unfold TL_STACK; lia | reflexivity | exact Hoffs | | exact Ht | exact If | exact Hfk | exact Hap | |].
    - cbn beta iota. split; [exact Hx|]. split; [exact G10|]. split; [exact G2a|]. split; [exact G3a|].
      split; [clear - Q2 Mkd; Z.div_mod_to_equations; lia|].
      exact (pm_tl_cell w s LB LBs m mo c ins tbl ftbl TB spal kd 8 OK XA A1 A2 A3 Hacc).
    - intros r0 r1 m1 k n a QQ Hin Ha Hm. cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-.
      destruct QQ as (r & Er & Hr & Hiff & Hfound & Hmiss).
      destruct (Z.eq_dec r 0) as [R0|R0].
      + destruct (Hfound R0) as (d & RW & _). eapply (rw_cells_def_hi m1 _ _ a RW); [unfold AIMG_TOP, AFS_HDR in *; lia | cbn; lia].
      + rewrite (Hmiss R0 a ltac:(lia)). exact Hm.
    - intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 KEPT MU WM QQ.
      destruct QQ as (r & Er & Hr & Hiff & Hfound & Hmiss).
      eapply (K msF1 mo1 m1 R1 r); [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact KEPT | exact MU | exact WM | exact Er | exact Hr | exact Hiff | exact Hfound | exact Hmiss].
  Qed.
End LeafW.
