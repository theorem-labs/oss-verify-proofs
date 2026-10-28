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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma sc_rd_w4s : forall E m (sa : saddr) (a : Z) bs (e : expr),
  adenot E sa = Z_to_bv 64 a -> PropExec.rdn asegs m (Z_to_bv 64 a) 4 = Some bs ->
  edenot E e = Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs)) ->
  sc_denot asegs m E (SCReadBase sa 4 true e).
Proof. intros E m sa a bs e Ha Hr He. cbn [sc_denot]. exists bs. rewrite Ha. split; [exact Hr|]. rewrite He. reflexivity. Qed.

Lemma sc_rd_fld4s : forall E m (sa : saddr) (a v : Z) (e : expr),
  fld ASEGS m a 4 v -> 0 <= v < 2 ^ 31 -> adenot E sa = Z_to_bv 64 a -> edenot E e = Z_to_bv 64 v ->
  sc_denot asegs m E (SCReadBase sa 4 true e).
Proof.
  intros E m sa a v e HF Hv Ha He. cbn [sc_denot]. exists (word_to_le_bytes 4 (Z_to_bv 64 v)). rewrite Ha. split; [exact HF|].
  rewrite He. f_equal. cbn [extz]. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite Z_to_bv_unsigned. unfold bv_wrap at 1. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 32)) by lia.
  unfold bv_swrap, bv_wrap. change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32). change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31).
  rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. lia.
Qed.

Lemma swrap32_sx32A : forall x, 0 <= x < 2 ^ 32 -> Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 (sx32A x).
Proof.
  intros x Hx. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec x (2 ^ 31)) as [L|L]; apply bv_eq; rewrite !Z_to_bv_unsigned;
    unfold bv_swrap, bv_wrap; change (bv_modulus 32) with (2 ^ 32); change (bv_half_modulus 32) with (2 ^ 31);
    change (bv_modulus 64) with (2 ^ 64).
  - rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia. reflexivity.
  - replace (x + 2 ^ 31) with ((x - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - 2 ^ 31)) by lia.
    rewrite <- (Z_mod_plus_full (x - 2 ^ 31 - 2 ^ 31) 1 (2 ^ 64)). f_equal. lia.
Qed.

Section Leaf.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pm_leaf0 : forall {X : Type} (entry STK : Z) (PRE : X -> mem -> Z -> word -> word -> word -> word -> Prop)
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
End Leaf.

Ltac sc_w4 H w E HE :=
  eapply sc_rd_w4s;
  [ rewrite (adenot_Z E _ (wa_words w)); [reflexivity | cbn [a_base]; pm_evx H w HE | lia]
  | eassumption
  | reflexivity ].
Ltac sc_fld4 H w E HE F :=
  eapply sc_rd_fld4s;
  [ exact F
  | lia
  | rewrite (adenot_Z E _ (wa_p w)); [reflexivity | cbn [a_base]; pm_evx H w HE | unfold PARSER_SIZE in *; lia]
  | reflexivity ].

Lemma cc_gen_nth_part : forall k mid, 0 <= mid -> mid mod 8 <> 0 ->
  nth_error (LbB_PrsStmt.cc_gen k mid) (Z.to_nat (mid / 8)) = Some (b8 (mid mod 8)).
Proof.
  intros k mid Hm Hr. unfold LbB_PrsStmt.cc_gen, shadow_of. rewrite <- app_assoc.
  rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag.
  destruct (Z.eqb_spec (mid mod 8) 0); [contradiction|]. reflexivity.
Qed.

Section WordsPart.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmk_sh_words_part : forall w s LB LBs m mo c ins tbl ftbl TB spal E j,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> wa_words w <> 0 ->
    j = 8 * ((4 * wa_n w) / 8) -> (4 * wa_n w) mod 8 = 4 ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_WORDS) (ELit j)) (ELit 3)) SHBASE) 1 (ELit 4)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E j OK X HE Hw Hj Hr.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (wk_n H w OK) as N1.
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    assert (Hk : 0 < k) by (assert (0 < 4 * wa_n w) by (Z.div_mod_to_equations; lia); lia).
    assert (Hl : Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w))) = nsh k).
    { unfold LbB_PrsStmt.cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
      assert (nsh (4 * wa_n w) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia). lia. }
    pose proof (pmx_words_sh H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal pw k _ OK X Hin Hk Hl Wsh) as SH.
    assert (D8 : 8 * ((4 * wa_n w) / 8) + 4 = 4 * wa_n w) by (Z.div_mod_to_equations; lia).
    assert (Hx : wa_words w <= wa_words w + j < wa_words w + 8 * Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w)))).
    { rewrite Hl. unfold nsh. subst j. assert (0 <= (4 * wa_n w) / 8) by (apply Z.div_pos; lia). split; [lia|].
      assert (4 * wa_n w + 7 <= k + 7) by lia.
      assert (8 * ((4 * wa_n w) / 8) + 8 <= 8 * ((k + 7) / 8)) by (Z.div_mod_to_equations; lia). lia. }
    destruct (shk_of_SHAD m _ _ _ SH Hx) as (b & Hb & K).
    replace (wa_words w + j - wa_words w) with j in Hb by lia.
    assert (Ej : Z.to_nat (j / 8) = Z.to_nat ((4 * wa_n w) / 8)) by (subst j; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite Ej in Hb. rewrite (cc_gen_nth_part k (4 * wa_n w) ltac:(lia) ltac:(lia)) in Hb. injection Hb as <-.
    rewrite Hr in K. change (bv_unsigned (b8 4)) with 4 in K.
    apply (kshadow E m _ (wa_words w + j) 4 (ELit 4)); [apply ev_add; [exact EW | lia | lia] | lia | lia | reflexivity | exact K].
  Qed.
End WordsPart.
