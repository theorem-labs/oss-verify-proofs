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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmLeaf LbB_DiagStmt LbB_PmXp LbB_PmDS LbB_PmGlue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma strlen_cstr_tleaf {HCEIL : HeapCeil} : strlen_icpt_stmt ->
  @tleaf HCEIL (Z * Z) ASTRLEN_STUB AINTRIN_STACK
    (fun pn m _ a0 _ _ _ => cstrA (fst pn) (snd pn) /\ a0 = Z_to_bv 64 (fst pn))
    (fun _ => [])
    (fun pn _ r0 _ _ => r0 = Z_to_bv 64 (snd pn)).
Proof.
  intros SL [p n] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         ST CE LO SP16 SP47 MI AC [CSTR Ha0]. cbn [fst snd] in *.
  pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
  destruct CSTR as (P1 & N1 & P2 & IA & AS & CS). destruct (AS m AC) as [ACC SV]. destruct (CS m MI) as (str & slack & BA & LEN & NI & SLK).
  unfold AIMG_LO in P1.
  assert (Hk : 0 <= (- (p + n + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (k := (- (p + n + 1)) mod 8) in Hk, SLK.
  set (slack' := firstn (Z.to_nat k) slack).
  assert (LS : Z.of_nat (length slack') = k) by (subst slack'; rewrite length_firstn; lia).
  assert (BA' : bytes_at asegs m p (str ++ Z_to_bv 8 0 :: slack')).
  { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ ([Z_to_bv 8 0] ++ slack)) in BA.
    change (str ++ Z_to_bv 8 0 :: slack') with (str ++ ([Z_to_bv 8 0] ++ slack')).
    rewrite app_assoc in BA |- *. apply bytes_at_app in BA as [B1 B2]. apply bytes_at_app. split; [exact B1|].
    subst slack'. rewrite <- (firstn_skipn (Z.to_nat k) slack) in B2. apply bytes_at_app in B2 as [B3 _]. exact B3. }
  subst a0.
  eapply evt_mono.
  { eapply (SL ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack' lo);
      rewrite ?u64_of_Z by lia;
      [ exact BA' | exact NI | rewrite LEN, LS; apply Z.le_refl | rewrite LEN; exact ACC | rewrite LEN; exact SV | exact ST | exact CE | exact LO
      | exact MI | exact AC | lia | rewrite LEN; exact IA | left; rewrite LS; lia ]. }
  intros ms' POST.
  destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & _ & AC').
  exists u0, u1, u2, (Z_to_bv 64 (Z.of_nat (length str))), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
  split; [exact EQ|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AC'|].
  rewrite LEN. reflexivity.
Qed.

Section LeafS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pm_leafS : forall {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
      (Wf : X -> list (Z * Z)) (Qf : X -> mem -> word -> word -> mem -> Prop),
    tleaf entry STK PRE Wf Qf ->
    forall (x : X) (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (ret : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= STK <= 4096 -> Wf x = [] ->
    PRE x m (wa_s1 w) (PropExec.getr R 10%bv) (PropExec.getr R 11%bv) (PropExec.getr R 12%bv) (PropExec.getr R 13%bv) ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c ins tbl ftbl TB spal ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       munch [(wa_s1 w - STK, wa_s1 w)] m m1 -> wmono asegs m m1 ->
       Qf x m (PropExec.getr R1 10%bv) (PropExec.getr R1 11%bv) m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros X entry STK PRE Wf Qf HL x w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc ret Q OK XA KR VIS RF
           G2 G1 Hret2 Hret HSTK HW HPRE Ht Hfk K.
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
    set (W := [(wa_s1 w - STK, wa_s1 w)]) in MU.
    assert (DM : forall y, m y <> None -> m' y <> None).
    { intros y Hy. destruct (outside_dec W (bv_unsigned y)) as [Ho|(lo' & hi' & Hin & Hr)].
      - rewrite (MU y Ho). exact Hy.
      - pose proof (bv_unsigned_in_range 64 y) as Ry. change (bv_modulus 64) with (2 ^ 64) in Ry.
        rewrite <- (Z_to_bv_bv_unsigned y). subst W.
        destruct Hin as [Hin|[]]. injection Hin as <- <-.
        destruct STK' as (_ & _ & SS). destruct (SS (bv_unsigned y) ltac:(unfold APM_STACK in *; lia)) as [_ (b & Hb)].
        unfold wa in Hb. exact (def_of_mrd_hi m' (bv_unsigned y) _ ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) Hb). }
    assert (STK'' : stk asegs m' (wa_lo w) (wa_sp0 w)).
    { apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
      eapply (stk_transport_disjoint asegs W m m' (wa_s1 w) (wa_sp0 w) STK2 MU WM).
      subst W. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (X1 : PMXAT H LINV w s LB LBs m' mo c ins tbl ftbl TB spal).
    { eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m' W tbl ftbl OK XA MU WM DM MI STK'').
      - subst W. apply Forall_cons; [left; cbn [fst snd]; unfold APM_STACK in *; lia | apply Forall_nil].
      - subst W. apply Forall_cons; [cbn; lia | apply Forall_nil].
      - subst W. cbn [disjoint_from]. unfold PM_NSH in *. rewrite Q13 in *.
        split; [left; lia | exact I].
      - subst W. cbn [disjoint_from]. unfold O_WIDX, O_FLAGS, PARSER_SIZE in *.
        split; [left; lia | exact I].
      - apply incl_refl.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Ht kk (in_map fst _ (kk, e) Hin)) as Kk. apply Z.leb_le in Kk.
        subst W. cbn [disjoint_from]. split; [right; lia | exact I].
      - apply incl_refl.
      - apply Forall_forall. intros [kk e] Hin. cbn [fst].
        pose proof (proj1 (forallb_forall _ _) Hfk kk (in_map fst _ (kk, e) Hin)) as Kb.
        apply andb_true_iff in Kb as [Kb1 Kb2]. apply Z.leb_le in Kb1. apply Z.leb_le in Kb2.
        subst W. cbn [disjoint_from]. split; [left; lia | exact I]. }
    eapply K; [exact KR1 | exact VIS1 | apply rfull_mkR | eapply (pmxa_mpres H HH LINV); [exact X1 | exact MP1] | | exact MU | exact WM | exact QQ].
    intros r Hr.
    repeat (destruct Hr as [<-|Hr]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr.
  Qed.
End LeafS.

Lemma sl_sh_lt_2_45 {HCEIL : HeapCeil} : forall a, 0 <= a <= 2 ^ 47 -> sh a < 2 ^ 45 - 8.
Proof. intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

Section DSLeaf.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Lemma ds_rep_leaf : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m1 STK dso err len,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    munch [(wa_s1 w - STK, wa_s1 w)] m m1 -> 0 <= STK <= 4096 -> 24 <= dso -> dso + DS_SIZE <= 16384 ->
    ds_repA LB m (wa_ff w + dso) err len TB -> ds_repA LB m1 (wa_ff w + dso) err len TB.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m1 STK dso err len OK X MU HS D1 D2 DS0.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN _]. pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (ITB : forall b, In b TB -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN)). rewrite !in_app_iff. right; right. exact Hb. }
    eapply (dla_err _ _ DSL) in DS0 as ERR0 || idtac.
    eapply (dla_frame _ _ DSL); [exact DS0 | | exact ITB].
    intros a Ha HIN. apply MU. rewrite u64_of_Z by lia. cbn [outside]. split; [| exact Logic.I].
    destruct HIN as [H1|[H2|[H3|H4]]].
    - unfold DS_SIZE in *. lia.
    - destruct H2 as (b & Hb & Hr). destruct b as [[pb Ab] nb].
      pose proof (ah_blocks H (proj1 HHbp) _ _ _ _ RH (ITB _ Hb)) as (_ & _ & _ & _ & R5 & _). cbn [blk_addr blk_size fst snd] in *. lia.
    - destruct H3 as (b & Hb & Hr). destruct b as [[pb Ab] nb].
      pose proof (ah_blocks H (proj1 HHbp) _ _ _ _ RH (ITB _ Hb)) as (R1 & _ & R3 & _ & R5 & _). cbn [blk_addr blk_size fst snd] in *.
      pose proof (sl_sh_lt_2_45 (Ab + nb) ltac:(unfold AAPP_HI; lia)) as SB.
      assert (sh Ab + nsh nb <= sh (Ab + nb) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
    - pose proof (sl_sh_lt_2_45 (wa_ff w + dso + DS_SIZE) ltac:(unfold AAPP_HI, DS_SIZE in *; lia)) as SB.
      assert (sh (wa_ff w + dso) + nsh DS_SIZE <= sh (wa_ff w + dso + DS_SIZE) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
  Qed.
End DSLeaf.

Section CseqCstr.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Lemma cstrA_img : forall p n m, cstrA p n -> mem_inv asegs m ->
    AIMG_LO + 64 <= p /\ p + n + 64 <= AIMG_TOP /\ 0 <= n
    /\ (forall m', ACONST m' -> accessible m' p n)
    /\ (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs).
  Proof.
    intros p n m (P1 & N1 & P2 & IA & AS & CS) MI.
    split; [exact P1|]. split; [unfold AIMG_TOP; lia|]. split; [lia|].
    split; [intros m' AC'; destruct (AS m' AC') as [ACC _]; eapply accessible_sub; [exact ACC | lia | lia | lia]|].
    destruct (CS m MI) as (str & slack & BA & LEN & NI & SL).
    exists str. split; [lia|]. intros m' MI'.
    apply bytes_at_app in BA as [BA _]. unfold AIMG_LO in P1.
    destruct BA as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi).

    assert (RO : forall mm, mem_inv asegs mm -> mm (wa (p + Z.of_nat i)) = None).
    { intros mm MM. destruct (mm (wa (p + Z.of_nat i))) as [b|] eqn:Eb; [| reflexivity]. exfalso.
      pose proof (MM _ _ Eb) as RR. unfold wa in RR. rewrite (ro_addr_seg01 (p + Z.of_nat i) ltac:(lia)) in RR. discriminate. }
    unfold mrd. rewrite (RO m' MI'), (RO m MI). reflexivity.
  Qed.

  Lemma pm_put_cseq_cstr : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    cstrA p n ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD CSTR DS0 Hlen Hsc K.
    destruct (cstrA_img p n m CSTR (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) as (I1 & I2 & I3 & I4 & I5).
    exact (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q
             OK X Hknn Hfk KR VIS RF FZ G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD I3 I1 I2 I4 I5 DS0 Hlen Hsc K).
  Qed.
End CseqCstr.
