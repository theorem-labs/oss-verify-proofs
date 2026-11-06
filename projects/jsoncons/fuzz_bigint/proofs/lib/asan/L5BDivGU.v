(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivHL L5BDivHM L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA L5BDivGB L5BDivGC L5BDivGD L5BRed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGU.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA. Import L5ADVGB. Import L5ADVGC. Import L5ADVGD.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis HSSH : L5OMA.stksh ar M (E - SCRD).
Hypothesis HSC8 : SCRD mod 8 = 0.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation SH := (F / 8 + 2147450880).
Local Notation offx := (L5ADVEA.offx L ar FF E F).
Local Notation tob := (L5ADVEA.tob).
Local Notation HSCR0 := (L5ADVGA.HSCR0 SCRD HSCR).

Local Ltac open_ctx BI :=
  let PF := fresh "PF" in
  pose proof (pf_of_binv L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as PF;
  destruct PF as (W384 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB);
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & OWNv & _ & (_ & _ & FV & SV & SHV));
  change (ff_bytes 3) with 512 in FV; change (ff_bytes 3 / 8) with 64 in SHV.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stksh_callee W BX Mc modelc LKc crc Ac scr : binv W BX Mc modelc LKc crc Ac -> L5OMA.stksh ar M (E - SCRD) -> 0 <= scr -> 384 + scr <= SCRD -> SCRD mod 8 = 0 -> scr mod 8 = 0 ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) -> L5OMA.stksh ar Mc (SPA - scr).
Proof.
  intros (B1 & _ & _ & _ & _ & _ & EK & _) SSH HS0 HS SC8 sc8 NW.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF0.
  assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
  set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (MX : mx <= 2 ^ 47 /\ E <= mx) by (subst mx; split; [apply Z.max_lub; [clear - SPT; lia | exact TOP] | clear - SHI; lia]).
  set (lo := SPA - scr). set (lo0 := E - SCRD).
  assert (LOR : lo0 <= lo /\ ahl_ceil ar <= lo0 /\ lo <= E /\ 0 <= lo0) by (subst lo lo0; clear - HS0 HS SLO SPC FR FCEIL; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (DV : lo0 / 8 <= lo / 8 /\ ahl_ceil ar / 8 <= lo0 / 8 /\ 0 <= lo0 / 8 /\ lo / 8 + (mx - lo) / 8 <= lo0 / 8 + (mx - lo0) / 8 /\ lo0 / 8 + (mx - lo0) / 8 <= 17592186044416)
    by (subst lo lo0; clear - LOR MX EA SC8 sc8; unfold aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct DV as (D1 & D2 & D3 & D4 & D5).
  unfold L5OMA.stksh in *. fold mx in SSH |- *. fold lo lo0 in SSH |- *.
  intros j Hj. unfold byte_at, S. rewrite EK.
  - unfold shadow_zero, byte_at, S in SSH. replace (lo / 8 + SB + j) with (lo0 / 8 + SB + (lo / 8 - lo0 / 8 + j)) by (clear; lia). apply SSH. clear - Hj D1 D4; lia.
  - assert (ISH : in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (lo / 8 + SB + j)).
    { unfold in_shadow_of, S. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415. clear - Hj D1 D2 D4 D5. lia. }
    split. unfold SB. clear - Hj D1 D3 D4 D5; lia. split. 2: exact (NW _ ISH). right; right; right; right; left. exact ISH.
Qed.

Lemma unnorm_stage (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac xs sd (b : L5.bigobj) ws (Hunn : L5DIA.unnorm_specA L ar HI) :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 11) = Z_to_bv 64 ro -> getr Rc (reg 12) = Z_to_bv 64 xs -> 0 <= xs <= 63 -> getr Rc (reg 13) = Z_to_bv 64 sd -> (sd = 0 \/ sd = 1) ->
  getr Rc (reg 1) = Z_to_bv 64 0x934bc ->
  384 + L5DIA.UNNORM_SCR <= SCRD -> SCRD mod 8 = 0 -> ffrk 1 FF LK 5 -> ffrk 3 FF LK 3 ->
  L5OMA.stksh ar M (E - SCRD) -> (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) ->
  L5.big_at RSEGS Mc ro b -> L5C.obj_limbs RSEGS Mc b ws -> (1 <= L5.bo_len b <= 299)%nat -> Z.testbit (L5.bo_fb b) 1 = false ->
  aobj FF ro 32 -> shadow_zero Mc ro 4 -> (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (sd = 1 -> exists qX, L5.bo_st b = L5.BDyn 8 qX /\ (2 <= L5.bo_len b <= 6)%nat) ->
  (sd = 1 -> L5OMA.acredit_for L crc L5DIA.DIVN_K L5DIA.DIVN_BYTES) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32); (L5.bo_data ro b, 8 * L5.bo_cap b)] a) ->
  (forall (fx' : FPState) R' M' model' cr' LK' A',
      L5DIA.unnorm_postA L ar (BX ++ LB) FF' crc Mc M' Rc R' ro SPA b cr' ->
      binv W1 BX M' model' LK' cr' A' -> incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x934bc M' model') K) ->
  (forall (fx' : FPState) R' M' model' qX LB' cr' LK' A' (F1 fl1 F3 fl3 F1c fl1c F1d fl1d : Z),
      sd = 1 -> L5.bo_st b = L5.BDyn 8 qX ->
      L5DIA.unnorm_e3A L ar (BX ++ LB) FF' crc Mc M' Rc R' ro qX (L5.bo_len b) SPA F1 fl1 F3 fl3 F1c fl1c F1d fl1d LB' cr' ->
      model_rt modelc model' -> incl Ac A' -> amodel_ok A' model' -> incl LK' LKc ->
      ri_inv HI LB' (L5DIA.ff_u FF' SPA F1 F3 F1c F1d) LK' cr' A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ASSERT_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc L5DSA.UNNORM Mc modelc) K.
Proof.
  intros BI RI X11 X12 XSR X13 SDR X1 HSU SC8 FFR5 FFR3 SSH NWSH OB OL LENB SGN AOB SZ INB SD1 CRD WSUB KN KE.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  assert (USCR : L5DIA.UNNORM_SCR = 5328) by reflexivity.
  edestruct L5ADVEA.callee_pre with (SCRc := L5DIA.UNNORM_SCR) as (STKc & _ & RSc & A32c); [exact HIok | exact EA | exact FFR1 | exact FFRS | exact BI | rewrite USCR; clear; lia | clear - HSU; lia | ].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LKc))). { clear - WF. decompose [and] WF. assumption. } clear WF.
  assert (ROOM1 : ffrk 1 FF' LKc 5). { apply (ffrk_push_other 1 FF LK LKc (F, 3, SPA + 32) 5). cbn [ff_class fst snd]. clear; lia. exact FFR5. exact B5. exact ND. }
  assert (ROOM3 : ffrk 3 FF' LKc 2). { apply (ffrk_push 3 FF LK LKc (F, 3, SPA + 32) 3 2 FFR3 B5 ND). clear; lia. }
  pose proof (stksh_callee W BX Mc modelc LKc crc Ac L5DIA.UNNORM_SCR BI SSH ltac:(rewrite USCR; clear; lia) HSU SC8 ltac:(rewrite USCR; reflexivity) NWSH) as SSHc.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOB SZ)
    as ((ORP & ORG & O8) & OBIG & _ & _ & OFR & OF & OSH & _).
  pose proof RI as (Z2 & _ & _ & _ & Z4 & _).
  assert (OCR : forall a, docell E a -> SPA <= a < E). { destruct G as [_ _ _ _ _ OCR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact OCR0. }
  apply (Hunn fx Rc Mc modelc K (BX ++ LB) FF' LKc crc Ac ro xs sd SPA 0x934bc b ws B1 B2 HK).
  - rewrite r11. exact X11.
  - rewrite r12. exact X12.
  - exact XSR.
  - replace (13%bv : bv 5) with (reg 13) by (apply bv_eq; reflexivity). exact X13.
  - exact SDR.
  - rewrite r1. exact X1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Z2.
  - exact A32c.
  - rewrite r4, Z4. rewrite <- G4. reflexivity.
  - exact STKc.
  - exact SSHc.
  - exact ROOM1.
  - exact ROOM3.
  - exact RSc.
  - exact OB.
  - exact OL.
  - exact LENB.
  - exact SGN.
  - apply aobj_cons. exact AOB.
  - exact SZ.
  - exact INB.
  - exact SD1.
  - exact CRD.
  - intros fx3 R3 M3 model3 cr3 LK3 A3 POST RT3 IA3 AM3 ILK3 HH3.
    pose proof POST as (_ & _ & _ & AH3).
    assert (BI3 : binv W1 BX M3 model3 LK3 cr3 A3).
    { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
               W W1 BX BX BX Mc modelc LKc crc Ac M3 model3 LK3 cr3 A3 L5DIA.UNNORM_SCR _ BI AH3 HH3 AM3 RT3 IA3 ILK3).
      + rewrite USCR; clear; lia.
      + clear - HSU; lia.
      + intros rr a [Hr|[Hr|[]]] IR; subst rr; unfold L5.in_rng in IR; cbn [fst snd] in IR.
        * split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
          change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
        * destruct b as [fb len sto]. unfold L5.bo_data, L5.bo_cap in IR. cbn [L5.bo_st] in *. destruct sto as [v0 v1|cap q].
          -- split. { intros D. pose proof (OCR a D) as X. clear - X IR OFR. lia. }
             change (ff_bytes 3 / 8) with 64. unfold SB. clear - IR OSH. lia.
          -- edestruct L5ADVEA.blk_avoid with (a := a) as (Y1 & Y2 & _); try first [exact LY | exact HIok | exact G | exact HSCR0 | exact HSCR]; [exact BI | exact (INB cap q eq_refl) | clear - IR; lia | ].
             split. exact Y1. exact Y2.
      + intros a _ X. exact (proj2 (WSUB a X)).
      + intros a X. exact (proj1 (WSUB a X)). }
    apply (KN fx3 R3 M3 model3 cr3 LK3 A3 POST BI3 IA3 ILK3).
  - intros fx3 R3 M3 model3 qX LB3 cr3 LK3 A3 F1 fl1 F3 fl3 F1c fl1c F1d fl1d S1 EST E3 RT3 IA3 AM3 ILK3 HH3.
    apply (KE fx3 R3 M3 model3 qX LB3 cr3 LK3 A3 F1 fl1 F3 fl3 F1c fl1c F1d fl1d S1 EST E3 RT3 IA3 AM3 ILK3 HH3).
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGU.
