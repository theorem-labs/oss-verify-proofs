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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_ContStmt LbB_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pt_app_sh : forall a n b k, 0 <= b -> 0 <= k -> b + k <= 2 ^ 47 ->
  ((0 <= a /\ a + n <= 0x7fff7000) \/ 0x10007fff8000 <= a) ->
  a + n <= sh b \/ sh b + nsh k <= a.
Proof. intros a n b k Hb Hk Hbk Ha. unfold sh, nsh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma pt_sh_apart : forall a n b c, 0 <= a -> 0 <= b -> 0 < n -> 0 <= c -> a mod 8 = 0 -> b mod 8 = 0 ->
  a + n <= b \/ b + c <= a -> sh a + nsh n <= sh b \/ sh b + nsh c <= sh a.
Proof.
  intros a n b c A0 B0 N0 C0 A8 B8 D. unfold sh, nsh.
  destruct D as [D|D]; [left | right]; Z.div_mod_to_equations; nia.
Qed.

Section PT4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma pt_fresh_cls : forall s LB p A n SP m0 a,
    as_RHEAP H s ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP -> aclient_addr H LB SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s LB p A n SP m0 a RH NI HSP Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
      assert (Hid : blk_id b <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
      assert (Hid : blk_id b <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. split; [lia|]. split; [destruct RAPP; lia | lia].
  Qed.

  Lemma pt_xp_drop : forall s LB' p A n SPc X m0 m m',
    as_RHEAP H s ((p, A, n) :: LB') m0 -> ~ In p (map blk_id LB') -> aceil <= SPc ->
    xpres H ((p, A, n) :: LB') SPc (X ++ [(A, A + n); (sh A, sh A + nsh n)]) m m' ->
    xpres H LB' SPc X m m'.
  Proof.
    intros s LB' p A n SPc X m0 m m' RH NI HS XP a Ha [Hc Hx]. apply XP; [exact Ha|]. split.
    - eapply aclient_addr_weaken; [exact Hc | lia | intros bb Hb; right; exact Hb].
    - rewrite rin_ivs_app. intros [K|K]; [exact (Hx K)|].
      pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
      unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
      assert (SHA : sh A + nsh n <= sh aceil) by (unfold sh, nsh; acb; Z.div_mod_to_equations; nia).
      assert (K2 : sh aceil < aceil) by (pose proof aceil_facts; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      destruct (pt_fresh_cls s LB' p A n SPc m0 a RH NI HS Hc) as [C|(C1 & C2 & C3)]; cbn [rin_ivs fst snd] in K; lia.
  Qed.

  Lemma pt_xp_munch : forall s LB' p A n SP X W m0 m m',
    as_RHEAP H s ((p, A, n) :: LB') m0 -> ~ In p (map blk_id LB') -> aceil <= SP ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB' SP X m m'.
  Proof.
    intros s LB' p A n SP X W m0 m m' RH NI HS MU WM FW a Ha [Hc Hx].
    pose proof (pt_fresh_cls s LB' p A n SP m0 a RH NI HS Hc) as CL.
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as K. cbn [fst snd] in K. split; [|apply IH; apply (Forall_inv_tail FW)].
      destruct K as [K|[K|[K|K]]].
      - destruct CL as [C|(C1 & C2 & C3)]; [|lia].
        pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        unfold blk_addr, blk_size in RC. cbn [fst snd] in RC. lia.
      - destruct CL as [C|(C1 & C2 & C3)]; [|lia].
        pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        unfold blk_addr, blk_size in R0, Rn, RC. cbn [fst snd] in R0, Rn, RC.
        assert (sh A + nsh n <= sh aceil) by (unfold sh, nsh; acb; Z.div_mod_to_equations; nia).
        assert (sh aceil < aceil) by (pose proof aceil_facts; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        lia.
      - lia.
      - intros Kin. apply Hx. apply K. exact Kin. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma pt_xp_lift : forall LB' SPc Xc LB SP X m m',
    xpres H LB' SPc Xc m m' -> SPc <= SP ->
    (forall bb, In bb LB -> In bb LB' \/
       (forall a, (blk_addr bb <= a < blk_addr bb + blk_size bb \/ sh (blk_addr bb) <= a < sh (blk_addr bb) + nsh (blk_size bb)) ->
        rin_ivs X a)) ->
    (forall a, rin_ivs Xc a -> rin_ivs X a) ->
    xpres H LB SP X m m'.
  Proof.
    intros LB' SPc Xc LB SP X m m' XP HS HB HX a Ha [Hc Hx]. apply XP; [exact Ha|].
    split; [|intros K; exact (Hx (HX a K))].
    unfold aclient_addr in *.
    destruct Hc as [Hc|[Hc|[(bb & Hb & Hr)|[(bb & Hb & Hr)|Hc]]]]; [left; lia | right; left; exact Hc | | | right; right; right; right; exact Hc].
    - destruct (HB bb Hb) as [IN|EX]; [|exfalso; exact (Hx (EX a (or_introl Hr)))].
      right; right; left. exists bb. split; [exact IN | exact Hr].
    - destruct (HB bb Hb) as [IN|EX]; [|exfalso; exact (Hx (EX a (or_intror Hr)))].
      right; right; right; left. exists bb. split; [exact IN | exact Hr].
  Qed.

  Lemma pt_acr_LBi : forall LB LBi spz spz' A n b c,
    aclient_range H LB spz A n -> spz' <= spz -> 0 < n ->
    (forall bb, In bb LB -> In bb LBi \/ (blk_addr bb = b /\ blk_size bb = c)) ->
    (A + n <= b \/ b + c <= A) -> (A + n <= sh b \/ sh b + nsh c <= A) ->
    aclient_range H LBi spz' A n.
  Proof.
    intros LB LBi spz spz' A n b c K HS N0 HB D1 D2. unfold aclient_range in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|K]]]].
    - left. lia.
    - right; left. exact K.
    - destruct (HB bb Hb) as [IN|(E1 & E2)].
      + right; right; left. exists bb. split; [exact IN | lia].
      + rewrite E1, E2 in *. lia.
    - destruct (HB bb Hb) as [IN|(E1 & E2)].
      + right; right; right; left. exists bb. split; [exact IN | lia].
      + rewrite E1, E2 in *. lia.
    - right; right; right; right. exact K.
  Qed.

  Lemma pt_awo_LBi : forall LB LBi A n b c,
    aclient_write_ok H LB (A, A + n) -> 0 < n ->
    (forall bb, In bb LB -> In bb LBi \/ (blk_addr bb = b /\ blk_size bb = c)) ->
    (A + n <= b \/ b + c <= A) -> (A + n <= sh b \/ sh b + nsh c <= A) ->
    aclient_write_ok H LBi (A, A + n).
  Proof.
    intros LB LBi A n b c K N0 HB D1 D2. unfold aclient_write_ok in *. cbn [fst snd] in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|K]]]].
    - left. exact K.
    - right; left. exact K.
    - destruct (HB bb Hb) as [IN|(E1 & E2)].
      + right; right; left. exists bb. split; [exact IN | lia].
      + rewrite E1, E2 in *. lia.
    - destruct (HB bb Hb) as [IN|(E1 & E2)].
      + right; right; right; left. exists bb. split; [exact IN | lia].
      + rewrite E1, E2 in *. lia.
    - right; right; right; right. exact K.
  Qed.

  Lemma pt_afs_LF : forall LF LF' iv, afs_write_ok H LF iv -> (forall f, In f LF -> In f LF') -> afs_write_ok H LF' iv.
  Proof.
    intros LF LF' iv K I. unfold afs_write_ok in *. destruct K as [K|(f & Hf & K)]; [left; exact K | right; exists f; split; [exact (I f Hf) | exact K]].
  Qed.

  Lemma pt_objwin_LBi : forall LB LBi LF LF' spz spz' lo v b c,
    obj_win H LB LF spz lo v 24 -> spz' <= spz -> (v + 24 <= lo \/ spz' <= v) ->
    (forall bb, In bb LB -> In bb LBi \/ (blk_addr bb = b /\ blk_size bb = c)) ->
    (forall f, In f LF -> In f LF') ->
    0 <= v -> v mod 8 = 0 -> 0 <= b -> b mod 8 = 0 -> 0 <= c -> b + c <= 2 ^ 47 ->
    ((0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) ->
    (v + 24 <= b \/ b + c <= v) -> ((0 <= b /\ b + c <= 0x7fff7000) \/ 0x10007fff8000 <= b) -> v + 24 <= 2 ^ 47 ->
    obj_win H LBi LF' spz' lo v 24.
  Proof.
    intros LB LBi LF LF' spz spz' lo v b c (CL & CLS & WO & FW & CO & SD) HS SD' HB HF V0 V8 B0 B8 C0 BC VB DJ BB V47.
    assert (D2 : v + 24 <= sh b \/ sh b + nsh c <= v) by (apply pt_app_sh; lia).
    assert (D3 : sh v + nsh 24 <= b \/ b + c <= sh v).
    { destruct (pt_app_sh b c v 24 V0 ltac:(lia) V47 BB) as [X|X]; [right | left]; lia. }
    assert (D4 : sh v + nsh 24 <= sh b \/ sh b + nsh c <= sh v).
    { apply pt_sh_apart; lia. }
    split; [eapply pt_acr_LBi; [exact CL | exact HS | lia | exact HB | exact DJ | exact D2]|].
    split; [eapply pt_acr_LBi; [exact CLS | exact HS | vm_compute; reflexivity | exact HB | exact D3 | exact D4]|].
    split; [eapply pt_awo_LBi; [exact WO | lia | exact HB | exact DJ | exact D2]|].
    split; [exact (pt_afs_LF LF LF' _ FW HF)|].
    split; [exact CO | exact SD'].
  Qed.
End PT4.
