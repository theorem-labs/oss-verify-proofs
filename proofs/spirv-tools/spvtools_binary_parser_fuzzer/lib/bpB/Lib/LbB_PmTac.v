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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section KX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmx_p_range : forall w, pmw_okA H w -> 0 < wa_p w /\ wa_p w mod 16 = 0 /\ wa_p w + PARSER_SIZE <= aceil.
  Proof.
    intros w OK. pose proof (wk_papp H w OK) as (P1 & P2 & P3). pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    split; [exact P2|]. split; [exact P3|].
    destruct P1 as [(Q1 & Q2)|(Q1 & Q2)]; [unfold aapp_lo, ALOWSH_LO in *; lia | exact Q2].
  Qed.
  Lemma pmx_cons_range : forall w, pmw_okA H w -> 0 < wa_cons w /\ wa_cons w mod 16 = 0 /\ wa_cons w + 48 <= aceil.
  Proof.
    intros w OK. pose proof (wk_capp H w OK) as (P1 & P2 & P3). pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    split; [exact P2|]. split; [exact P3|].
    destruct P1 as [(Q1 & Q2)|(Q1 & Q2)]; [unfold aapp_lo, ALOWSH_LO in *; lia | exact Q2].
  Qed.

  Lemma ev_add : forall E (n : N) (x k : Z), edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
    edenot E (EAlu ALU_ADD (EVar n) (ELit k)) = Z_to_bv 64 (x + k).
  Proof.
    intros E n x k Hx H0 H1. cbn [edenot]. change (ev E n) with (edenot E (EVar n)). rewrite Hx.
    cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small x) by lia. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Lemma pmk_sh_p : forall w s LB LBs m mo c ins tbl ftbl TB spal E k,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> 0 <= k < 288 ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit k)) (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E k OK X HE Hk. pose proof (pmx_p_range w OK) as (P1 & P2 & P3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EP : edenot E (EVar WV_P) = Z_to_bv 64 (wa_p w)) by (apply (ev_wv H w E _ 0 _ HE eq_refl); [lia | reflexivity]).
    apply (kshadow0 E m _ (wa_p w + k)); [apply ev_add; [exact EP | unfold PARSER_SIZE in *; lia | unfold PARSER_SIZE in *; lia] | unfold PARSER_SIZE in *; lia |].
    destruct (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & AP & _).
    eapply sh0_of_addressable; [exact AP|]. unfold PARSER_SIZE. change (288 / 8) with 36. lia.
  Qed.

  Lemma pmk_sh_s1 : forall w s LB LBs m mo c ins tbl ftbl TB spal E k,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> 0 <= k < 832 ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_S1) (ELit k)) (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E k OK X HE Hk.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (wk_stack H w OK) as (S1a & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (ES1 : edenot E (EVar WV_S1) = Z_to_bv 64 (wa_s1 w)) by (apply (ev_wv H w E _ 3 _ HE eq_refl); [lia | reflexivity]).
    apply (kshadow0 E m _ (wa_s1 w + k)); [apply ev_add; [exact ES1 | unfold AAPP_HI in *; lia | unfold AAPP_HI in *; lia] | unfold AAPP_HI in *; lia |].
    destruct (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (g & G1 & G2 & G3 & AD).
    eapply sh0_of_addressable; [exact AD|].
    assert (E8 : 8 * ((wa_shi w - g) / 8) = wa_shi w - g) by (Z.div_mod_to_equations; lia).
    rewrite E8. lia.
  Qed.

  Lemma pmk_sh_cons : forall w s LB LBs m mo c ins tbl ftbl TB spal E k,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> 0 <= k < 48 ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_CONS) (ELit k)) (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E k OK X HE Hk. pose proof (pmx_cons_range w OK) as (P1 & P2 & P3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EP : edenot E (EVar WV_CONS) = Z_to_bv 64 (wa_cons w)) by (apply (ev_wv H w E _ 6 _ HE eq_refl); [lia | reflexivity]).
    apply (kshadow0 E m _ (wa_cons w + k)); [apply ev_add; [exact EP | lia | lia] | lia |].
    destruct (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & AC).
    eapply sh0_of_addressable; [exact AC|]. change (48 / 8) with 6. lia.
  Qed.

  Lemma pmk_sh_ff : forall w s LB LBs m mo c ins tbl ftbl TB spal E k v,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> 0 <= k < 11584 -> k mod 8 = 0 ->
    fsh_at ins k = v ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_FF) (ELit k)) (ELit 3)) SHBASE) 1 (ELit v)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E k v OK X HE Hk H8 <-. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by (apply (ev_wv H w E _ 1 _ HE eq_refl); [lia | reflexivity]).
    assert (Hj : (Z.to_nat (k / 8) < 1448)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); change (Z.of_nat 1448) with 1448; apply Z.div_lt_upper_bound; lia).
    assert (Hv : 0 <= fsh_at ins k < 256).
    { unfold fsh_at. apply fsh_pat_byte_range. }
    apply (kshadow E m _ (wa_ff w + k) (fsh_at ins k)); [apply ev_add; [exact EF | lia | lia] | lia | exact Hv | cbn [edenot]; reflexivity |].
    replace (wa_ff w + k) with (wa_ff w + 8 * Z.of_nat (Z.to_nat (k / 8))).
    2:{ rewrite Z2Nat.id by (apply Z.div_pos; lia). Z.div_mod_to_equations. lia. }
    eapply shk_of_fsh; [exact (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact Hj | reflexivity | exact Hv].
  Qed.
End KX.

Section WV.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Lemma ev_world_all : forall (w : pmwA H) E, env_world H w E ->
    edenot E (EVar 32) = Z_to_bv 64 (wa_p w) /\ edenot E (EVar 33) = Z_to_bv 64 (wa_ff w)
    /\ edenot E (EVar 34) = Z_to_bv 64 (wa_sp0 w) /\ edenot E (EVar 35) = Z_to_bv 64 (wa_s1 w)
    /\ edenot E (EVar 36) = Z_to_bv 64 (wa_words w) /\ edenot E (EVar 37) = Z_to_bv 64 (wa_n w)
    /\ edenot E (EVar 38) = Z_to_bv 64 (wa_cons w) /\ edenot E (EVar 39) = Z_to_bv 64 (wa_user w)
    /\ edenot E (EVar 40) = Z_to_bv 64 (wa_diag w).
  Proof.
    intros w E HE.
    repeat split; [ apply (ev_wv H w E _ 0 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 1 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 2 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 3 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 5 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 6 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 7 _ HE eq_refl); [lia | reflexivity]
                  | apply (ev_wv H w E _ 8 _ HE eq_refl); [lia | reflexivity] ].
  Qed.

  Lemma ev_xseed : forall (w : pmwA H) R X n v, N.leb 41 n = true -> nth_error X (N.to_nat n - 41) = Some v ->
    edenot (Eseed R (wenv_vals w ++ X)) (EVar n) = v.
  Proof.
    intros w R X n v Hn Hv. apply N.leb_le in Hn. cbn [edenot]. rewrite Eseed_world by lia.
    rewrite app_nth2 by (rewrite wenv_vals_length; lia). rewrite wenv_vals_length.
    replace (N.to_nat n - 32 - 9)%nat with (N.to_nat n - 41)%nat by lia.
    apply nth_error_nth. exact Hv.
  Qed.
End WV.

Ltac ev_xs :=
  repeat match goal with
  | |- context [edenot (Eseed ?R (wenv_vals ?w ++ ?X)) (EVar ?n)] =>
      lazymatch eval vm_compute in (N.leb 41 n) with
      | true => rewrite (ev_xseed _ w R X n _ eq_refl eq_refl)
      end
  end.

Ltac byte_ranges :=
  repeat match goal with
  | b : byte |- _ =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned b < 256 |- _ => fail
      | _ => let Hb := fresh "Hb" in pose proof (bv_unsigned_in_range 8 b) as Hb; change (bv_modulus 8) with 256 in Hb
      end
  end.

Ltac pm_wv H w E HE :=
  let E32 := fresh "E32" in let E33 := fresh "E33" in let E34 := fresh "E34" in let E35 := fresh "E35" in
  let E36 := fresh "E36" in let E37 := fresh "E37" in let E38 := fresh "E38" in let E39 := fresh "E39" in
  let E40 := fresh "E40" in
  destruct (ev_world_all H w E HE) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40);
  rewrite ?E32, ?E33, ?E34, ?E35, ?E36, ?E37, ?E38, ?E39, ?E40;
  clear E32 E33 E34 E35 E36 E37 E38 E39 E40.

Ltac pm_br H w E HE :=
  cbn [sc_denot]; pm_wv H w E HE; ev_xs; cbn [edenot];
  rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.

Section Words.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmx_words_sh : forall w s LB LBs m mo c ins tbl ftbl TB spal pw k sbs,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> In (pw, wa_words w, k) (wa_LB0 w) ->
    0 < k -> Z.of_nat (length sbs) = nsh k ->
    SHAD (wa_m0 w) (wa_words w) sbs -> SHAD m (wa_words w) sbs.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal pw k sbs OK X Hin Hk Hl (S0 & S8 & [B W]).
    destruct (xa_xpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (XS & FXS & XP).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (fsobj_block H HH _ _ _ (wa_LF0 w) _ _ _ RH HinLB) as FO.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_rfs0 H w OK) as RF0.
    pose proof (fsobj_windows H HH _ _ _ _ _ _ _ RF0 FO (wk_fresh H w OK) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as (D1 & D2 & D3 & D4).
    change (fshn PM_FCLASS) with 2048 in D2.
    pose proof (pmx_p_range H w OK) as (P1 & P2 & P3).
    pose proof (wk_papp H w OK) as (PA & _ & _).
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & _).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    assert (FA : aapp (wa_ff w) 16384) by (eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; change (fsz PM_FCLASS) with 16384 in *; lia | change (fsz PM_FCLASS) with 16384 in *; lia]).
    assert (XR : xclient_range H (wa_LB0 w) (wa_sp0 w)
                   ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (wa_p w, wa_p w + PARSER_SIZE) :: (wa_ff w, wa_ff w + fsz PM_FCLASS) :: (sh (wa_ff w), sh (wa_ff w) + fshn PM_FCLASS) :: XS)
                   (sh (wa_words w)) (Z.of_nat (length sbs))).
    { split.
      - right; right; right; left. exists (pw, wa_words w, k). split; [exact Hin|]. cbn [blk_addr blk_size fst snd]. lia.
      - rewrite Hl. change (fsz PM_FCLASS) with 16384. change (fshn PM_FCLASS) with 2048.
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons]]]; cbn [fst snd].
        + right. unfold sh. rewrite ASHADOW_BASE_val. unfold RtB_Td.ATDLOC. clear - RI. unfold AIMG_TOP in RI. Z.div_mod_to_equations. lia.
        + pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (wa_words w) k PA ltac:(lia) ltac:(unfold AAPP_HI in *; lia) ltac:(lia)). lia.
        + pose proof (aapp_disjoint_sh (wa_ff w) 16384 (wa_words w) k FA ltac:(lia) ltac:(unfold AAPP_HI in *; lia) ltac:(lia)). lia.
        + lia.
        + apply Forall_forall. intros iv Hiv.
          pose proof (fsobj_scratch_sh H HH (wa_LF0 w) (wa_words w) k _ iv RF0 FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)
                        (proj1 (Forall_forall _ _) FXS iv Hiv)). lia. }
    split; [exact S0|]. split; [exact S8|]. split.
    - eapply xpres_bytes_at; [exact XP | exact B | exact XR].
    - eapply xpres_wr_at; [exact XP | exact W | exact XR].
  Qed.
End Words.

Section Words2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma cc_gen_nth0 : forall k mid i, 0 <= mid -> (i < Z.to_nat (mid / 8))%nat ->
    nth_error (LbB_PrsStmt.cc_gen k mid) i = Some (b8 0).
  Proof.
    intros k mid i Hm Hi. unfold LbB_PrsStmt.cc_gen, shadow_of. rewrite <- app_assoc.
    rewrite nth_error_app1 by (rewrite repeat_length; exact Hi). apply nth_error_repeat. exact Hi.
  Qed.

  Lemma pmx_words_sh0 : forall w s LB LBs m mo c ins tbl ftbl TB spal j,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 -> 0 <= j < 8 * ((4 * wa_n w) / 8) ->
    sh0 m (wa_words w + j).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal j OK X Hw Hj.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (wk_n H w OK) as N1.
    assert (Hk : 0 < k) by (assert (0 < 4 * wa_n w) by (Z.div_mod_to_equations; lia); lia).
    assert (Hl : Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w))) = nsh k).
    { unfold LbB_PrsStmt.cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
      assert (nsh (4 * wa_n w) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia). lia. }
    pose proof (pmx_words_sh H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal pw k _ OK X Hin Hk Hl Wsh) as SH.
    assert (Hx : wa_words w <= wa_words w + j < wa_words w + 8 * Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w)))).
    { rewrite Hl. unfold nsh. split; [lia|]. assert (8 * ((4 * wa_n w) / 8) <= 8 * ((k + 7) / 8)).
      { apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.div_le_mono; lia. } lia. }
    destruct (shk_of_SHAD m _ _ _ SH Hx) as (b & Hb & K).
    rewrite cc_gen_nth0 in Hb.
    - injection Hb as <-. exact K.
    - lia.
    - replace (wa_words w + j - wa_words w) with j by lia. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by (apply Z.div_pos; lia).
      apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma pmk_sh_words : forall w s LB LBs m mo c ins tbl ftbl TB spal E j,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> wa_words w <> 0 ->
    0 <= j < 8 * ((4 * wa_n w) / 8) ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_WORDS) (ELit j)) (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E j OK X HE Hw Hj.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    assert (D8 : 8 * ((4 * wa_n w) / 8) <= 4 * wa_n w) by (apply Z.mul_div_le; lia).
    apply (kshadow0 E m _ (wa_words w + j)); [apply ev_add; [exact EW | lia | lia] | lia |].
    exact (pmx_words_sh0 w s LB LBs m mo c ins tbl ftbl TB spal j OK X Hw Hj).
  Qed.

  Lemma pmk_sh_words0 : forall w s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> wa_words w <> 0 -> 2 <= wa_n w ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL (EVar WV_WORDS) (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hw Hn.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    apply (kshadow0 E m _ (wa_words w)); [exact EW | lia |].
    replace (wa_words w) with (wa_words w + 0) by lia.
    apply (pmx_words_sh0 w s LB LBs m mo c ins tbl ftbl TB spal 0 OK X Hw). Z.div_mod_to_equations. lia.
  Qed.
End Words2.

Section KX2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmk_sh_ffdisj : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr) x,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 x -> 0 <= x -> x + 1 <= 2 ^ 47 ->
    kentry_ok ASEGS E m (KDisj (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e x OK X HE He H0 H1. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & _).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (FA : aapp (wa_ff w) 16384) by (eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; change (fsz PM_FCLASS) with 16384 in *; lia | change (fsz PM_FCLASS) with 16384 in *; lia]).
    assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by (apply (ev_wv H w E _ 1 _ HE eq_refl); [lia | reflexivity]).
    rewrite (srl3_val E e x He ltac:(lia)), EF, !elit_u, u64_of_Z by lia.
    pose proof (aapp_disjoint_sh (wa_ff w) 16384 x 1 FA H0 ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
    unfold sh, nsh, ASHADOW_BASE, SHBASE in *. change ((1 + 7) / 8) with 1 in D. lia.
  Qed.

  Lemma pmk_sh_pdisj : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr) x,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 x -> 0 <= x -> x + 1 <= 2 ^ 47 ->
    kentry_ok ASEGS E m (KDisj (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_P) 0) (ELit 288)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e x OK X HE He H0 H1. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
    pose proof (wk_papp H w OK) as (PA & P0 & _). pose proof (pmx_p_range H w OK) as (Q1 & Q2 & Q3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EP : edenot E (EVar WV_P) = Z_to_bv 64 (wa_p w)) by (apply (ev_wv H w E _ 0 _ HE eq_refl); [lia | reflexivity]).
    rewrite (srl3_val E e x He ltac:(lia)), EP, !elit_u, u64_of_Z by (unfold PARSER_SIZE in *; lia).
    pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE x 1 PA H0 ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
    unfold sh, nsh, ASHADOW_BASE, SHBASE, PARSER_SIZE in *. change ((1 + 7) / 8) with 1 in D. lia.
  Qed.

  Lemma pmk_sh_s1disj : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr) x,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 x -> 0 <= x -> x + 1 <= 2 ^ 47 ->
    kentry_ok ASEGS E m (KDisj (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO))).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e x OK X HE He H0 H1. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (ES : edenot E (EVar WV_S1) = Z_to_bv 64 (wa_s1 w)) by (apply (ev_wv H w E _ 3 _ HE eq_refl); [lia | reflexivity]).
    rewrite (srl3_val E e x He ltac:(lia)), ES, !elit_u, u64_of_Z by (unfold PM_RF_LO; lia).
    assert (SB : x / 8 + SHBASE < aceil) by (unfold SHBASE; Z.div_mod_to_equations; lia).
    unfold PM_RF_LO in *. lia.
  Qed.

  Lemma pmw_apart_ff : forall w s LB LBs m mo c ins tbl ftbl TB spal, pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    (wa_p w + PARSER_SIZE <= wa_ff w \/ wa_ff w + 16384 <= wa_p w)
    /\ (wa_cons w + 48 <= wa_ff w \/ wa_ff w + 16384 <= wa_cons w)
    /\ (wa_words w <> 0 -> wa_words w + 4 * wa_n w <= wa_ff w \/ wa_ff w + 16384 <= wa_words w).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X. pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmx_p_range H w OK) as (P1 & P2 & P3). pose proof (pmx_cons_range H w OK) as (C1 & C2 & C3).
    pose proof (fsobj_windows H HH _ _ _ _ _ _ (wa_m0 w) (wk_rfs0 H w OK) (wk_pobj H w OK) (wk_fresh H w OK) ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia)) as (D1 & _).
    pose proof (fsobj_windows H HH _ _ _ _ _ _ (wa_m0 w) (wk_rfs0 H w OK) (wk_cobj H w OK) (wk_fresh H w OK) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as (D2 & _).
    change (fsz PM_FCLASS) with 16384 in D1, D2.
    split; [exact D1|]. split; [exact D2|]. intros Hw.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (fsobj_block H HH _ _ _ (wa_LF0 w) _ _ _ RH HinLB) as FO.
    pose proof (fsobj_windows H HH _ _ _ _ _ _ (wa_m0 w) (wk_rfs0 H w OK) FO (wk_fresh H w OK) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as (D3 & _).
    change (fsz PM_FCLASS) with 16384 in D3. lia.
  Qed.

  Lemma pmk_sh_fshdisj : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr) x,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 x -> 0 <= x -> x + 1 <= 2 ^ 47 -> (x + 1 <= wa_ff w \/ wa_ff w + 16384 <= x) ->
    kentry_ok ASEGS E m (KDisj (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e x OK X HE He H0 H1 Hout. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off].
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    rewrite (srl3_val E e x He ltac:(lia)), (ev_fshb H w E OK HE), !elit_u by (unfold PM_NSH; lia).
    unfold PM_NSH, SHBASE.
    destruct Hout as [Hlt|Hge].
    - left. assert (x / 8 < wa_ff w / 8) by (apply Z.div_lt_upper_bound; [lia|]; Z.div_mod_to_equations; lia). lia.
    - right. assert (wa_ff w / 8 + 2048 <= x / 8) by (apply Z.div_le_lower_bound; [lia|]; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma pmk_words_s1 : forall w s LB LBs m mo c ins tbl ftbl TB spal E len,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> wa_words w <> 0 -> 0 <= len <= 4 * wa_n w ->
    kentry_ok ASEGS E m (KDisj (SA (EVar WV_WORDS) 0) (ELit len) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO))).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E len OK X HE Hw Hl.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    assert (ES1 : edenot E (EVar WV_S1) = Z_to_bv 64 (wa_s1 w)) by (apply (ev_wv H w E _ 3 _ HE eq_refl); [lia | reflexivity]).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EW, ES1, !elit_u, !u64_of_Z by (unfold PM_RF_LO; lia).
    unfold PM_RF_LO. lia.
  Qed.

  Lemma pmk_words_ff : forall w s LB LBs m mo c ins tbl ftbl TB spal E len,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> wa_words w <> 0 -> 0 <= len <= 4 * wa_n w ->
    kentry_ok ASEGS E m (KDisj (SA (EVar WV_WORDS) 0) (ELit len) (SA (EVar WV_FF) 0) (ELit 16384)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E len OK X HE Hw Hl.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (fsobj_block H HH _ _ _ (wa_LF0 w) _ _ _ RH HinLB) as FO.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (fsobj_windows H HH _ _ _ _ _ _ _ (wk_rfs0 H w OK) FO (wk_fresh H w OK) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as (D1 & _).
    change (fsz PM_FCLASS) with 16384 in D1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & _).
    assert (EW : edenot E (EVar WV_WORDS) = Z_to_bv 64 (wa_words w)) by (apply (ev_wv H w E _ 4 _ HE eq_refl); [lia | reflexivity]).
    assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by (apply (ev_wv H w E _ 1 _ HE eq_refl); [lia | reflexivity]).
    cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EW, EF, !elit_u, !u64_of_Z by lia. lia.
  Qed.
End KX2.

Definition SCAL_X (c : pmc) : list word :=
  [Z_to_bv 64 (c_widx c); Z_to_bv 64 (c_icount c); Z_to_bv 64 (c_endian c); Z_to_bv 64 (c_reqconv c)].
Definition SCAL_KN : list kentry :=
  [KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 41); KWord (SA (EVar WV_P) O_ICOUNT) 8 (EVar 42);
   KWord (SA (EVar WV_P) O_ENDIAN) 4 (EVar 43); KWord (SA (EVar WV_P) O_FLAGS) 1 (EVar 44);
   KWord (SA (EVar WV_P) (O_FLAGS + 1)) 1 (ELit 0)].

Section KX3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmw_bounds : forall w, pmw_okA H w ->
    0 < wa_p w /\ wa_p w + 288 <= 2 ^ 47 /\ 0 < wa_cons w /\ wa_cons w + 48 <= 2 ^ 47
    /\ 0 <= wa_words w /\ wa_words w + 4 * wa_n w <= 2 ^ 47 /\ 0 <= wa_n w < 2 ^ 24
    /\ 0 < wa_ff w /\ wa_ff w + 16384 <= 2 ^ 47 /\ 0 < wa_s1 w /\ wa_s1 w + 832 <= wa_sp0 w /\ wa_sp0 w <= 2 ^ 47.
  Proof.
    intros w OK. pose proof (pmx_p_range H w OK) as (P1 & P2 & P3). pose proof (pmx_cons_range H w OK) as (C1 & C2 & C3).
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). pose proof (wk_n H w OK) as N1.
    assert (WB : 0 <= wa_words w /\ wa_words w + 4 * wa_n w <= 2 ^ 47).
    { destruct (wk_words H w OK) as [[E0 E1]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; lia. }
    unfold PARSER_SIZE in *. lia.
  Qed.

  Lemma estart_p : forall w E k, pmw_okA H w -> env_world H w E -> estart E (SA (EVar WV_P) k) = wa_p w + k.
  Proof. intros w E k OK HE. unfold estart. cbn [a_base a_off]. rewrite (ev_p H w E OK HE). reflexivity. Qed.

  Lemma pmk_scal_widx : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 (c_widx c) -> kentry_ok ASEGS E m (KWord (SA (EVar WV_P) O_WIDX) 8 e).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e OK X HE Hv. pose proof (pmw_bounds w OK) as BND.
    apply (kword_of_fld E m (wa_p w + O_WIDX) 8 (c_widx c)); [exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | | | | exact Hv];
      [rewrite (estart_p w E _ OK HE); reflexivity | unfold O_WIDX, PARSER_SIZE in *; lia | unfold O_WIDX, PARSER_SIZE in *; cbn; lia].
  Qed.
  Lemma pmk_scal_icount : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 (c_icount c) -> kentry_ok ASEGS E m (KWord (SA (EVar WV_P) O_ICOUNT) 8 e).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e OK X HE Hv. pose proof (pmw_bounds w OK) as BND.
    apply (kword_of_fld E m (wa_p w + O_ICOUNT) 8 (c_icount c)); [exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | | | | exact Hv];
      [rewrite (estart_p w E _ OK HE); reflexivity | unfold O_ICOUNT, PARSER_SIZE in *; lia | unfold O_ICOUNT, PARSER_SIZE in *; cbn; lia].
  Qed.
  Lemma pmk_scal_endian : forall w s LB LBs m mo c ins tbl ftbl TB spal E (e : expr),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E e = Z_to_bv 64 (c_endian c) -> kentry_ok ASEGS E m (KWord (SA (EVar WV_P) O_ENDIAN) 4 e).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e OK X HE Hv. pose proof (pmw_bounds w OK) as BND.
    apply (kword_of_fld E m (wa_p w + O_ENDIAN) 4 (c_endian c)); [exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | | | | exact Hv];
      [rewrite (estart_p w E _ OK HE); reflexivity | unfold O_ENDIAN, PARSER_SIZE in *; lia | unfold O_ENDIAN, PARSER_SIZE in *; cbn; lia].
  Qed.
  Lemma pmk_scal_flags : forall w s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    edenot E (EVar 44) = Z_to_bv 64 (c_reqconv c) -> kentry_ok ASEGS E m (KWord (SA (EVar WV_P) O_FLAGS) 1 (EVar 44)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hv. pose proof (pmw_bounds w OK) as BND.
    apply (kword_of_fld E m (wa_p w + O_FLAGS) 1 (c_reqconv c)); [exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | | | | exact Hv];
      [rewrite (estart_p w E _ OK HE); reflexivity | unfold O_FLAGS, PARSER_SIZE in *; lia | unfold O_FLAGS, PARSER_SIZE in *; cbn; lia].
  Qed.
  Lemma pmk_scal_retry : forall w s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    kentry_ok ASEGS E m (KWord (SA (EVar WV_P) (O_FLAGS + 1)) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE. pose proof (pmw_bounds w OK) as BND.
    apply (kword_of_fld E m (wa_p w + O_FLAGS + 1) 1 0); [exact (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | | | | reflexivity];
      [rewrite (estart_p w E _ OK HE); lia | unfold O_FLAGS, PARSER_SIZE in *; lia | unfold O_FLAGS, PARSER_SIZE in *; cbn; lia].
  Qed.
End KX3.

Ltac pm_evx_var H w HE n :=
  let E32 := fresh "E32" in let E33 := fresh "E33" in let E34 := fresh "E34" in let E35 := fresh "E35" in
  let E36 := fresh "E36" in let E37 := fresh "E37" in let E38 := fresh "E38" in let E39 := fresh "E39" in
  let E40 := fresh "E40" in
  destruct (ev_world_all H w _ HE) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40);
  lazymatch eval compute in n with
  | 32%N => exact E32 | 33%N => exact E33 | 34%N => exact E34 | 35%N => exact E35 | 36%N => exact E36
  | 37%N => exact E37 | 38%N => exact E38 | 39%N => exact E39 | 40%N => exact E40
  end.
Ltac pm_evx H w HE :=
  lazymatch goal with
  | |- edenot _ (EVar ?n) = _ => pm_evx_var H w HE n
  | |- edenot _ (EAlu ALU_ADD (EVar ?n) (ELit _)) = _ => eapply ev_add; [pm_evx_var H w HE n | lia | lia]
  end.

Ltac zlia := first [ lia | reflexivity | (Z.div_mod_to_equations; lia) ].

Ltac pmk_entry H HH w OK X HE :=
  let BND := fresh "BND" in
  pose proof (pmw_bounds H w OK) as BND;
  lazymatch goal with
  | |- kentry_ok _ _ _ (KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar ?n) (ELit _)) (ELit 3)) _) _ _) =>
      lazymatch eval compute in n with
      | 32%N => eapply pmk_sh_p with (1 := OK) (2 := X) (3 := HE); zlia
      | 35%N => eapply pmk_sh_s1 with (1 := OK) (2 := X) (3 := HE); zlia
      | 38%N => eapply pmk_sh_cons with (1 := OK) (2 := X) (3 := HE); zlia
      | 33%N => eapply pmk_sh_ff with (1 := OK) (2 := X) (3 := HE); [zlia | zlia | vm_compute; reflexivity]
      | 36%N => first [eapply pmk_sh_words with (1 := HH) (2 := OK) (3 := X) (4 := HE) | eapply pmk_sh_words with (1 := OK) (2 := X) (3 := HE)]; [assumption | zlia]
      end
  | |- kentry_ok _ _ _ (KWord (SA (EAlu ALU_SRL (EVar ?n) (ELit 3)) _) _ _) =>
      lazymatch eval compute in n with
      | 36%N => first [eapply pmk_sh_words0 with (1 := HH) (2 := OK) (3 := X) (4 := HE) | eapply pmk_sh_words0 with (1 := OK) (2 := X) (3 := HE)]; [assumption | zlia]
      end
  | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_SRL _ (ELit 3)) _) _ (SA (EAlu ALU_SRL (EVar _) (ELit 3)) _) _) =>
      eapply pmk_sh_fshdisj with (1 := OK) (2 := X) (3 := HE);
        [pm_evx H w HE | zlia | zlia | let PA := fresh "PA" in pose proof (pmw_apart_ff H HH _ w _ _ _ _ _ _ _ _ _ _ _ OK X) as PA; unfold PARSER_SIZE in PA; zlia]
  | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_SRL _ (ELit 3)) _) _ (SA (EVar ?n) _) _) =>
      lazymatch eval compute in n with
      | 33%N => eapply pmk_sh_ffdisj with (1 := OK) (2 := X) (3 := HE); [pm_evx H w HE | zlia | zlia]
      | 32%N => eapply pmk_sh_pdisj with (1 := OK) (2 := X) (3 := HE); [pm_evx H w HE | zlia | zlia]
      | 35%N => eapply pmk_sh_s1disj with (1 := OK) (2 := X) (3 := HE); [pm_evx H w HE | zlia | zlia]
      end
  | |- kentry_ok _ _ _ (KDisj (SA (EVar ?n1) _) _ (SA (EVar ?n) _) _) =>
      lazymatch eval compute in (n1, n) with
      | (36%N, 35%N) => first [eapply pmk_words_s1 with (1 := HH) (2 := OK) (3 := X) (4 := HE) | eapply pmk_words_s1 with (1 := OK) (2 := X) (3 := HE)]; [assumption | zlia]
      | (36%N, 33%N) => first [eapply pmk_words_ff with (1 := HH) (2 := OK) (3 := X) (4 := HE) | eapply pmk_words_ff with (1 := OK) (2 := X) (3 := HE)]; [assumption | zlia]
      end
  | |- kentry_ok _ _ _ (KWord (SA (EVar ?n) ?k) _ _) =>
      lazymatch eval compute in (n, k) with
      | (32%N, 72) => eapply pmk_scal_widx with (1 := OK) (2 := X) (3 := HE); reflexivity
      | (32%N, 80) => eapply pmk_scal_icount with (1 := OK) (2 := X) (3 := HE); reflexivity
      | (32%N, 88) => eapply pmk_scal_endian with (1 := OK) (2 := X) (3 := HE); reflexivity
      | (32%N, 92) => eapply pmk_scal_flags with (1 := OK) (2 := X) (3 := HE); reflexivity
      | (32%N, 93) => eapply pmk_scal_retry with (1 := OK) (2 := X) (3 := HE)
      end
  end;
  clear BND.

Ltac pmk_list H HH w OK X HE :=
  lazymatch goal with
  | |- Forall _ [] => apply Forall_nil
  | |- Forall _ (_ :: _) => apply Forall_cons; [pmk_entry H HH w OK X HE | pmk_list H HH w OK X HE]
  end.

Ltac pm_go HHH LINVF OK X KR VIS RF HT Xs extra fuel stops dirs nx ins' ks fks tbl' ftbl' RT' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let kn0 := constr:(pm_kn_base tbl ftbl ++ extra) in
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(pm_kn_base tbl ftbl ++ (extra ++ fixes)) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_run H HHH LINV LINVF w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                ins' ks fks tbl' ftbl' RT' _ OK X KR VIS RF (regs_tbl_ext w _ Xs R RT HT ltac:(vm_compute; reflexivity)));
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split;
        [ eapply (pm_kn_base_ok H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X (env_world_seed H w R Xs));
          vm_compute; reflexivity
        | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs) ]
      | idtac
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | idtac ]
    end end end end.

Ltac lfield_rw :=
  repeat match goal with
  | |- context [lfield ?L ?b ?k ?w] =>
      let r := eval vm_compute in (lfield L b k w) in
      let Eq := fresh "Elf" in
      assert (Eq : lfield L b k w = r) by (vm_compute; reflexivity);
      rewrite Eq; clear Eq
  end.

Ltac pm_goS HHH LINVF OK X KR VIS RF HT Xs extra fuel stops dirs nx ins' ks fks tbl' ftbl' RT' c' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let kn0 := constr:(pm_kn_base tbl ftbl ++ extra) in
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(pm_kn_base tbl ftbl ++ (extra ++ fixes)) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_runS H HHH LINV LINVF w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                ins' ks fks tbl' ftbl' RT' c' _ OK X KR VIS RF (regs_tbl_ext w _ Xs R RT HT ltac:(vm_compute; reflexivity)));
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split;
        [ eapply (pm_kn_base_ok H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X (env_world_seed H w R Xs));
          vm_compute; reflexivity
        | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs) ]
      | idtac
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold sval; lfield_rw; vm_compute; reflexivity
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac ]
    end end end end.

Ltac pm_goSX HHH LINVF OK X KR VIS RF HT Xs extra fuel stops dirs nx ins' ks fks tbl' ftbl' RT' c' spal' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let kn0 := constr:(pm_kn_base tbl ftbl ++ extra) in
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(pm_kn_base tbl ftbl ++ (extra ++ fixes)) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_runSX H HHH LINV LINVF w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                ins' ks fks tbl' ftbl' RT' c' spal' _ OK X KR VIS RF (regs_tbl_ext w _ Xs R RT HT ltac:(vm_compute; reflexivity)));
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split;
        [ eapply (pm_kn_base_ok H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ OK X (env_world_seed H w R Xs));
          vm_compute; reflexivity
        | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs) ]
      | idtac
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | unfold sval; lfield_rw; vm_compute; reflexivity
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac
      | idtac ]
    end end end end.

