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
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5BCopyS L5BCopyS16 L5BOpModF L5BDetailG L5BFrameK L5ArithSpecsB0 L5ParseSpecsBB0 L5BStrctorS L5BTopP1 L5BTopP2 L5BTopH.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ATD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ATP1. Import L5ATP2. Import L5ADH. Import L5ATH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
(* [comment removed for export] *)
Local Ltac al := match goal with
  | H : L5ATP2.aligned ?x ?y |- L5ATP1.aligned ?x ?y => exact H
  | H : L5ATP1.aligned ?x ?y |- L5ATP2.aligned ?x ?y => exact H end.
Local Ltac sc := first [ asm | al | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

(* [comment removed for export] *)
Lemma lb_remove_app_skip : forall q l1 l2, ~ In q (map fst l1) -> lb_remove q (l1 ++ l2) = l1 ++ lb_remove q l2.
Proof.
  intros q l1 l2. induction l1 as [|[a n] l1 IH]; intros NI. reflexivity.
  cbn [app]. rewrite lb_remove_skip. rewrite IH. reflexivity. intros X; apply NI; right; exact X. intros E; apply NI; left; cbn [fst]; exact E.
Qed.
Definition ostr (sk : option (Z * Z)) : list (Z * Z) := match sk with None => [] | Some b => [b] end.

(* [comment removed for export] *)
Definition obj_at (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (blk : option (Z * Z)) : Prop :=
  L5.big_at RSEGS Mk o b /\ match L5.bo_st b with L5.BInl _ _ => blk = None | L5.BDyn cap q => blk = Some (q, 8 * cap) end.
Lemma obj_at_agree Mk Mk1 o b blk : obj_at Mk o b blk -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  (forall i, o <= i < o + 32 -> Mk1 (Z_to_bv 64 i) = Mk (Z_to_bv 64 i)) -> obj_at Mk1 o b blk.
Proof. intros [B E] H0 H1 AG. split. eapply L5C.big_at_agree. 4: exact B. exact AG. exact H0. exact H1. exact E. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).

Section TOP.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (V2 cls r SCRT : Z) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation S := (V2 + cls).
Local Notation SPA := (V2 - 192).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2A : aligned V2 32.
Hypothesis V2R : 140735332487424 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis G3 : getr R (reg 3) = Z_to_bv 64 67584.                 (* [comment removed for export] *)
Hypothesis HSCR : 208 + 4096 <= SCRT.
(* [comment removed for export] *)
Variables (d1 d2 d3 : Z).
Hypothesis FFR1 : ffrk 1 FF LK d1.
Hypothesis FFR2 : ffrk 2 FF LK d2.
Hypothesis FFR3 : ffrk 3 FF LK (d3 + 1).
Hypothesis FFRS : ffrs FF S.
Hypothesis STKSH : L5OMA.stksh ar M (V2 + cls - SCRT).      (* [comment removed for export] *)
Hypothesis HSCR8 : SCRT mod 8 = 0.
Hypothesis HD1 : 5 <= d1.
Hypothesis HD2 : 2 <= d2.
Hypothesis HS_COPY : 208 + COPY_SCR <= SCRT.
Local Abbreviation binv := (L5AFK.binv L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3).
Local Abbreviation rinvT := (L5ATH.rinvT R V2 cls F).
Local Notation FF' := ((F, 3, V2 - 192 + 32) :: FF).
Local Abbreviation binv_piece := (L5AFK.binv_piece L ar HI M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G).
Local Abbreviation binv_callee := (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G).
Local Abbreviation binv_model := (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3).
Local Abbreviation vis_facts := (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G).

(* [comment removed for export] *)
Definition XIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21; 23; 25; 26]%nat.
Definition rinvX (Rc : bvmap 5 word) : Prop :=
  rinvT Rc /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96) /\ getr Rc (reg 23) = Z_to_bv 64 (F + 160) /\
  getr Rc (reg 25) = Z_to_bv 64 (F + 288) /\ getr Rc (reg 26) = Z_to_bv 64 (F + 224).
Lemma rinvX_keep Ra Rb : rinvX Ra -> (forall k, In k XIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvX Rb.
Proof.
  intros (XT & X21 & X23 & X25 & X26) KS. unfold rinvX. rewrite !KS by (apply L5K.in_b; vm_compute; reflexivity).
  split. { apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply KS. revert Hk. apply (L5K.incl_b TIDX XIDX). vm_compute; reflexivity. }
  repeat split; assumption.
Qed.
Lemma rinvX_ks Ra Rb (KS : list nat) : rinvX Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) XIDX = true -> rinvX Rb.
Proof. intros RI HKS HB. apply (rinvX_keep Ra Rb RI). intros k Hk. apply HKS. exact (L5K.incl_b XIDX KS HB k Hk). Qed.
Lemma rinvX_pres Ra Rb : rinvX Ra -> regs_preserved Ra Rb -> rinvX Rb.
Proof.
  intros RI RP. apply (rinvX_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP).
  revert Hk. apply (L5K.incl_b XIDX cs_all). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition pf (MV : word -> option byte) : Prop :=
  L5.writable RSEGS MV (V2 - 192) 192 /\ L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV 911160 2147450880 /\ L5.u32_at RSEGS MV 911168 1 /\
  L5.defined MV F 512 /\ L5.writable RSEGS MV F 512 /\ L5.writable RSEGS MV (F / 8 + SB) 64 /\ L5.u64_at RSEGS MV (F + 504) fl /\ L5.writable RSEGS MV fl 1.
Lemma NUM : (0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= V2 < 2 ^ 64) /\ 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327 /\ aligned F 32
  /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 512 <= fl \/ fl + 1 <= F) /\ (V2 - 192 + 192 <= F \/ F + 512 <= V2 - 192) /\ (V2 - 192 + 192 <= fl \/ fl + 1 <= V2 - 192)
  /\ (F + 512 <= V2 - 192 /\ fl + 1 <= V2 - 192).
Proof.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *.
  split. clear - FR FLR V2R; lia. split. clear - FR; lia. split. clear - FLR; lia. split. exact F32. split. exact FBIG. split. exact FLBIG. split. exact FLA.
  assert (SFB : F + 512 <= V2 - 192 /\ fl + 1 <= V2 - 192) by (clear - FCEIL FLR SPC SLO; lia).
  split. clear - SFB; lia. split. clear - SFB; lia. exact SFB.
Qed.
Lemma pf_of_binv BX Mc modelc LKc crc Ac : binv [] BX Mc modelc LKc crc Ac -> pf (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros BI.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac BI)
    as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F + 512 - 8) with (F + 504) in FLCv by (clear; lia).
  unfold pf. split. { eapply L5.writable_sub. exact WSv. clear; lia. clear - CLS; lia. }
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition inl_run (rin rout : bvmap 5 word -> Prop) (pc pcn ox : Z) : Prop :=
  forall (fx : FPState) Rc MV fb, rin Rc -> pf MV -> L5.u8_at RSEGS MV ox fb -> 0 <= fb < 256 -> Z.testbit fb 0 = false ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc pc MV) (st fx' R' pcn MV) /\ rout R'.
Definition dyn_run (rin rout : bvmap 5 word -> Prop) (pc pcn ox : Z) : Prop :=
  forall (fx : FPState) Rc MV fb q cap, rin Rc -> pf MV -> L5.u8_at RSEGS MV ox fb -> 0 <= fb < 256 -> Z.testbit fb 0 = true ->
  L5.u64_at RSEGS MV (ox + 24) q -> 4096 <= q <= 2 ^ 47 -> L5.u64_at RSEGS MV (ox + 16) cap -> 1 <= cap <= 2 ^ 27 ->
  exists (fx' : FPState) R', msteps RSEGS (st fx Rc pc MV) (st fx' R' OPDEL_SIZED MV) /\ rout R'
    /\ getr R' (reg 1) = Z_to_bv 64 pcn /\ getr R' (reg 10) = Z_to_bv 64 q /\ getr R' (reg 11) = Z_to_bv 64 (8 * cap).

Lemma dtor_stage (rin rout : bvmap 5 word -> Prop) (pc pcn ox : Z) :
  inl_run rin rout pc pcn ox -> dyn_run rin rout pc pcn ox ->
  (forall Rc, rout Rc -> rinvT Rc) -> (forall Ra Rb, rout Ra -> regs_preserved Ra Rb -> rout Rb) -> L5.ra_ok pcn ->
  ((F <= ox /\ ox + 32 <= F + 512) \/ (SPA <= ox /\ ox + 32 <= S)) ->
  forall (fx : FPState) Rc Mc modelc BX BXn LKc crc Ac b blk,
  binv [] BX Mc modelc LKc crc Ac -> rin Rc -> obj_at Mc ox b blk ->
  match blk with None => BXn = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXn ++ LB end ->
  (forall (fx' : FPState) R' M' model' A',
      binv [] BXn M' model' LKc crc A' -> rout R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXn ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros INL DYN ROT RPR RAn OXR fx Rc Mc modelc BX BXn LKc crc Ac b blk BI RI [OB OBLK] BLK KF.
  pose proof (pf_of_binv BX Mc modelc LKc crc Ac BI) as PF.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac BI)
    as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 3) with 512 in FV.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OXN : 4096 <= ox /\ ox + 32 <= 2 ^ 47) by (clear - OXR FRP V2R V2S CLS; lia).
  assert (OV : avis (ahid Ac modelc) ox 32).
  { destruct OXR as [X|X]. eapply avis_sub. exact FV. clear - X; lia. clear - X; lia. eapply avis_sub. exact SV. clear - X; lia. clear - X; lia. }
  assert (CELLV : forall a v, ox <= a -> a + 8 <= ox + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact OV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 OXN; lia) ltac:(clear - H2 OXN; lia))). exact Hc. }
  assert (CELL1 : forall v, L5.u8_at RSEGS Mc ox v -> L5.u8_at RSEGS MV ox v).
  { intros v Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc ox v ltac:(eapply avis_sub; [exact OV | clear; lia | clear; lia]) ltac:(clear - OXN; lia) ltac:(clear - OXN; lia))). exact Hc. }
  destruct b as [fb len sto]. destruct OB as (O0 & FBR & _ & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    subst blk. subst BXn. destruct OST as (BT0 & _).
    destruct (INL fx Rc MV fb RI PF (CELL1 _ O0) FBR BT0) as (fx1 & R1 & MS1 & RO1).
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 pcn K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1 RO1 (incl_refl _)). intros a _ _. reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    destruct (DYN fx Rc MV fb q cap RI PF (CELL1 _ O0) FBR BT1 (CELLV (ox + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) ltac:(clear - Q4096 Q47 CAPR; lia)
                  (CELLV (ox + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) CAPR) as (fx1 & R1 & MS1 & RO1 & dR1 & dR10 & dR11).
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 OPDEL_SIZED K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof (ROT R1 RO1) as (Z2 & _ & _ & _ & _ & _ & _ & _ & Z4).
    assert (SPA16 : (V2 - 192) mod 16 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA pcn HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + exact RAn.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. exact G4.
    + replace SPA with (S - (192 + cls)) by (clear; lia). apply (astk_sub ar Mc Mc S SCRT (192 + cls) OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear - CLS; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ; clear - HSCR CLS; lia. replace (S - (192 + cls)) with (V2 - 192) by (clear; lia). exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv [] BXn M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2
                 (L5AFK.GCTX L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS)
                 [] [] BX BXn BXn Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - rewrite DEL_EQ; clear - HSCR CLS; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      apply (KF fx3 R3 M3 model3 A3 BI3 (RPR R1 R3 RO1 RP3) IA3).
      intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
Qed.

(* [comment removed for export] *)
Definition jmp_run (rout : bvmap 5 word -> Prop) (pcd pcn : Z) : Prop :=
  forall (fx : FPState) Rc MV, rout Rc -> pf MV -> exists (fx' : FPState) R', msteps RSEGS (st fx Rc pcd MV) (st fx' R' pcn MV) /\ rout R'.
Lemma dtor_stage_j (rin rout : bvmap 5 word -> Prop) (pc pcn pcd ox : Z) :
  inl_run rin rout pc pcn ox -> dyn_run rin rout pc pcd ox -> jmp_run rout pcd pcn ->
  (forall Rc, rout Rc -> rinvT Rc) -> (forall Ra Rb, rout Ra -> regs_preserved Ra Rb -> rout Rb) -> L5.ra_ok pcd ->
  ((F <= ox /\ ox + 32 <= F + 512) \/ (SPA <= ox /\ ox + 32 <= S)) ->
  forall (fx : FPState) Rc Mc modelc BX BXn LKc crc Ac b blk,
  binv [] BX Mc modelc LKc crc Ac -> rin Rc -> obj_at Mc ox b blk ->
  match blk with None => BXn = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXn ++ LB end ->
  (forall (fx' : FPState) R' M' model' A',
      binv [] BXn M' model' LKc crc A' -> rout R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXn ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros INL DYN JMP ROT RPR RAn OXR fx Rc Mc modelc BX BXn LKc crc Ac b blk BI RI [OB OBLK] BLK KF.
  pose proof (pf_of_binv BX Mc modelc LKc crc Ac BI) as PF.
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac BI)
    as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 3) with 512 in FV.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OXN : 4096 <= ox /\ ox + 32 <= 2 ^ 47) by (clear - OXR FRP V2R V2S CLS; lia).
  assert (OV : avis (ahid Ac modelc) ox 32).
  { destruct OXR as [X|X]. eapply avis_sub. exact FV. clear - X; lia. clear - X; lia. eapply avis_sub. exact SV. clear - X; lia. clear - X; lia. }
  assert (CELLV : forall a v, ox <= a -> a + 8 <= ox + 32 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v).
  { intros a v H1 H2 Hc. apply (proj2 (u64_at_vis (ahid Ac modelc) Mc a v ltac:(eapply avis_sub; [exact OV | clear - H1; lia | clear - H2; lia]) ltac:(clear - H1 OXN; lia) ltac:(clear - H2 OXN; lia))). exact Hc. }
  assert (CELL1 : forall v, L5.u8_at RSEGS Mc ox v -> L5.u8_at RSEGS MV ox v).
  { intros v Hc. apply (proj2 (u8_at_vis (ahid Ac modelc) Mc ox v ltac:(eapply avis_sub; [exact OV | clear; lia | clear; lia]) ltac:(clear - OXN; lia) ltac:(clear - OXN; lia))). exact Hc. }
  destruct b as [fb len sto]. destruct OB as (O0 & FBR & _ & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct sto as [v0 v1|cap q].
  - (* [comment removed for export] *)
    subst blk. subst BXn. destruct OST as (BT0 & _).
    destruct (INL fx Rc MV fb RI PF (CELL1 _ O0) FBR BT0) as (fx1 & R1 & MS1 & RO1).
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 pcn K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1 RO1 (incl_refl _)). intros a _ _. reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    destruct (DYN fx Rc MV fb q cap RI PF (CELL1 _ O0) FBR BT1 (CELLV (ox + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) ltac:(clear - Q4096 Q47 CAPR; lia)
                  (CELLV (ox + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) CAPR) as (fx1 & R1 & MS1 & RO1 & dR1 & dR10 & dR11).
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 OPDEL_SIZED K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof (ROT R1 RO1) as (Z2 & _ & _ & _ & _ & _ & _ & _ & Z4).
    assert (SPA16 : (V2 - 192) mod 16 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA pcd HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + exact RAn.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. exact G4.
    + replace SPA with (S - (192 + cls)) by (clear; lia). apply (astk_sub ar Mc Mc S SCRT (192 + cls) OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear - CLS; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ; clear - HSCR CLS; lia. replace (S - (192 + cls)) with (V2 - 192) by (clear; lia). exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv [] BXn M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2
                 (L5AFK.GCTX L ar HI LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS)
                 [] [] BX BXn BXn Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - rewrite DEL_EQ; clear - HSCR CLS; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      (* [comment removed for export] *)
      destruct (JMP fx3 R3 (mrestrict (ahid A3 model3) M3) (RPR R1 R3 RO1 RP3) (pf_of_binv BXn M3 model3 LKc crc A3 BI3)) as (fx4 & R4 & MS4 & RO4).
      pose proof BI3 as (B31 & B32 & _).
      apply (apure (BXn ++ LB) FF' LKc crc A3 M3 model3 fx3 fx4 R3 pcd R4 pcn K B31 B32 MS4).
      intros model4 HH4 AM4 RT4 AH4.
      pose proof (L5AFK.binv_model L ar HI M model LB FF LK A S SCRT SPA (town V2 cls F R) F 3 [] BXn M3 model3 LKc crc A3 model4 BI3 HH4 AM4 RT4) as BI4.
      apply (KF fx4 R4 M3 model4 A3 BI4 RO4 IA3).
      intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
Qed.

(* [comment removed for export] *)
Local Ltac open_pf PF := destruct PF as (W192 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
Local Ltac run_inl PIECE KS :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in
  intros fx Rc MV fb RI PF O0 FBR BT0; open_pf PF;
  pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26);
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | apply (rinvX_ks Rc R1 KS RI pKS); vm_compute; reflexivity].
Local Ltac run_dyn PIECE KS :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in let q := fresh "q" in let cap := fresh "cap" in
  intros fx Rc MV fb q cap RI PF O0 FBR BT1 O24 QR O16 CAPR; open_pf PF;
  pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26);
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  assert (QR' : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64) by (clear - QR; lia); destruct QR' as [QR' QR''];
  assert (CR' : 1 <= cap <= 134217728 /\ 0 <= cap < 2 ^ 64) by (clear - CAPR; lia); destruct CR' as [CR' CR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | split; [apply (rinvX_ks Rc R1 KS RI pKS); vm_compute; reflexivity | split; [exact pR1 | split; [exact pR10 | exact pR11]]]].

Lemma run_Ki : inl_run rinvX rinvX 0x8e344 0x8e364 (F + 288). Proof. run_inl tpKi_conc KS_tpKi. Qed.
Lemma run_Kd : dyn_run rinvX rinvX 0x8e344 0x8e364 (F + 288).
Proof. unfold dyn_run. replace (F + 288 + 24) with (F + 312) by (clear; lia). replace (F + 288 + 16) with (F + 304) by (clear; lia). run_dyn tpKd_conc KS_tpKd. Qed.
Lemma run_Li : inl_run rinvX rinvX 0x8e364 0x8e384 (V2 - 168). Proof. run_inl tpLi_conc KS_tpLi. Qed.
Lemma run_Ld : dyn_run rinvX rinvX 0x8e364 0x8e384 (V2 - 168).
Proof. unfold dyn_run. replace (V2 - 168 + 24) with (V2 - 144) by (clear; lia). replace (V2 - 168 + 16) with (V2 - 152) by (clear; lia). run_dyn tpLd_conc KS_tpLd. Qed.
Lemma run_Mi : inl_run rinvX rinvX 0x8e384 0x8e3a4 (V2 - 136). Proof. run_inl tpMi_conc KS_tpMi. Qed.
Lemma run_Md : dyn_run rinvX rinvX 0x8e384 0x8e3a4 (V2 - 136).
Proof. unfold dyn_run. replace (V2 - 136 + 24) with (V2 - 112) by (clear; lia). replace (V2 - 136 + 16) with (V2 - 120) by (clear; lia). run_dyn tpMd_conc KS_tpMd. Qed.
Lemma run_Ni : inl_run rinvX rinvX 0x8e3a4 0x8e3c4 (F + 160). Proof. run_inl tpNi_conc KS_tpNi. Qed.
Lemma run_Nd : dyn_run rinvX rinvX 0x8e3a4 0x8e3c4 (F + 160).
Proof. unfold dyn_run. replace (F + 160 + 24) with (F + 184) by (clear; lia). replace (F + 160 + 16) with (F + 176) by (clear; lia). run_dyn tpNd_conc KS_tpNd. Qed.

(* [comment removed for export] *)
Lemma tcl LBx scr a : 0 <= scr -> (F + 32 <= a < F + 504 \/ SPA <= a < S) -> aclient L ar LBx FF' SPA scr a.
Proof.
  intros Hs [X|X].
  - apply (fframe_client L ar LBx FF' SPA scr F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - X; lia.
  - destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    apply stack_client. clear - X SLO SPC SHI SPT; lia. clear - X Hs; lia.
Qed.
Definition tobj (o : Z) : Prop := (F + 32 <= o /\ o + 32 <= F + 504) \/ (SPA <= o /\ o + 32 <= S).
Lemma obj_keep LBx scr Mc M1 o b blk : obj_at Mc o b blk -> tobj o -> 0 <= scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> obj_at M1 o b blk.
Proof.
  intros OB TO Hs AG. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  apply (obj_at_agree Mc M1 o b blk OB). clear - TO FRP V2R; unfold tobj in TO; lia. clear - TO FRP V2R V2S CLS; unfold tobj in TO; lia.
  intros i Hi. apply AG. clear - Hi TO FRP V2R V2S CLS; unfold tobj in TO; lia. apply tcl. exact Hs. clear - Hi TO; unfold tobj in TO; lia.
Qed.
Definition str_at (Mc : word -> option byte) (sk : option (Z * Z)) : Prop :=
  match sk with
  | None => exists b0, L5.u8_at RSEGS Mc (F + 32) b0 /\ 0 <= b0 < 256 /\ Z.testbit b0 0 = false
  | Some (pd, nb) => exists w0, L5.u64_at RSEGS Mc (F + 32) w0 /\ 0 <= w0 < 2 ^ 64 /\ Z.testbit w0 0 = true /\ L5.u64_at RSEGS Mc (F + 48) pd /\ 4096 <= pd <= 2 ^ 47
  end.
Lemma str_agree Mc M1 sk : str_at Mc sk -> (forall i, F + 32 <= i < F + 56 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)) -> str_at M1 sk.
Proof.
  intros ST AGI. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  destruct sk as [[pd nb]|]; cbn [str_at] in *.
  - destruct ST as (w0 & S0 & W0R & W0T & SPD & PDR). exists w0. split. { eapply L5C.u64_at_agree. 4: exact S0. intros j Hj; apply AGI; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. exact W0R. split. exact W0T. split. { eapply L5C.u64_at_agree. 4: exact SPD. intros j Hj; apply AGI; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. } exact PDR.
  - destruct ST as (b0 & S0 & B0R & B0T). exists b0. split. { eapply L5C.u8_at_agree. 4: exact S0. intros j Hj; apply AGI; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. exact B0R. exact B0T.
Qed.
Lemma str_keep LBx scr Mc M1 sk : str_at Mc sk -> 0 <= scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> str_at M1 sk.
Proof.
  intros ST Hs AG. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _). apply (str_agree Mc M1 sk ST).
  intros i Hi. apply AG. clear - Hi FRP; lia. apply tcl. exact Hs. left; clear - Hi; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DT.
Variable crmin : credit.
Hypothesis KF : forall (fxf : FPState) Rf Mf modelf LKf Af crf,
      regs_preserved R Rf -> getr Rf (reg 10) = Z_to_bv 64 0 ->
      ahpres L ar LB FF S SCRT [] M Mf ->
      model_rt model modelf -> incl A Af -> amodel_ok Af modelf -> incl LKf LK -> credit_le crmin crf ->
      ri_inv HI LB FF LKf crf Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K.

(* [comment removed for export] *)
Lemma ph_str (fx : FPState) Rc Mc modelc LKc crc Ac sk :
  binv [] (ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvT Rc -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e408 Mc modelc) K.
Proof.
  intros BI CRL RI ST.
  apply (L5ATH.top_tail L ar C HI LY HIok Hdel R M model K LB FF LK A V2 cls r SCRT F fl LK2 M2 model2 cr2 G CLS V2A V2R V2S HK RA UR1 G2 G4 HSCR
           fx Rc Mc modelc (ostr sk) [] LKc crc Ac BI RI).
  - destruct sk as [[pd nb]|]; cbn [str_at ostr] in *.
    + right. destruct ST as (w0 & S0 & W0R & W0T & SPD & PDR). exists w0, pd, nb. split. exact S0. split. exact W0R. split. exact W0T. split. exact SPD. split. exact PDR.
      split. left; reflexivity. cbn [app]. apply lb_remove_head.
    + left. destruct ST as (b0 & S0 & B0R & B0T). exists b0. split. exact S0. split. exact B0R. split. exact B0T. reflexivity.
  - intros fxf Rf Mf modelf LKf Af RPf R10f _ AHf RTf IAf AMf LKIf HHf. exact (KF fxf Rf Mf modelf LKf Af crc RPf R10f AHf RTf IAf AMf LKIf CRL HHf).
Qed.

(* [comment removed for export] *)
Lemma fsh_client LBx a : F / 8 + SB <= a < F / 8 + SB + 64 -> aclientw L ar LBx FF' 0 0 a /\ ~ (0x10000 <= a < 0x634000).      (* [comment removed for export] *)
Proof.
  intros Ha. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  split. apply (fframe_shadow_client L ar LBx FF' 0 0 F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S. rewrite (proj1 (proj2 F8)). clear - Ha. lia.
  clear - Ha FR F8. unfold SB in Ha. lia.
Qed.
Lemma obj_vis_cell BX Mc modelc LKc crc Ac o v : binv [] BX Mc modelc LKc crc Ac -> tobj o -> L5.u8_at RSEGS Mc o v -> L5.u8_at RSEGS (mrestrict (ahid Ac modelc) Mc) o v.
Proof.
  intros BI TO Hc. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A S SCRT SPA SPA S (tocell V2 cls) (town V2 cls F R) F fl 3 LK2 M2 model2 cr2 G [] BX Mc modelc LKc crc Ac BI)
    as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 3) with 512 in FV.
  apply (proj2 (u8_at_vis (ahid Ac modelc) Mc o v ltac:(destruct TO as [X|X]; [eapply avis_sub; [exact FV | clear - X; lia | clear - X; lia] | eapply avis_sub; [exact SV | clear - X; lia | clear - X; lia]])
           ltac:(clear - TO FRP V2R; unfold tobj in TO; lia) ltac:(clear - TO FRP V2R V2S CLS; unfold tobj in TO; lia))). exact Hc.
Qed.

(* [comment removed for export] *)
Lemma ph_a (fx : FPState) Rc Mc modelc LKc crc Ac sk ba :
  binv [] (ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc -> getr Rc (reg 22) = Z_to_bv 64 18446744073709551608 ->
  obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e3d8 Mc modelc) K.
Proof.
  intros BI CRL RI X22 [OB OBLK] ST.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF.
  assert (TA : tobj (F + 96)) by (left; clear; lia).
  destruct ba as [fb len sto]. destruct OB as (O0 & FBR & _ & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  destruct sto as [v0 v1|cap q]; [|discriminate OBLK]. destruct OST as (BT0 & _).
  pose proof (obj_vis_cell _ _ _ _ _ _ _ _ BI TA O0) as O0v.
  pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26).
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia). destruct FBR' as [FBR' FBR''].
  pose proof (tpOi_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  assert (RI1 : rinvX R1). { apply (rinvX_ks Rc R1 KS_tpOi RI pKS). vm_compute; reflexivity. }
  assert (Y22 : getr R1 (reg 22) = Z_to_bv 64 18446744073709551608). { rewrite (pKS 22%nat) by inl. exact X22. }
  pose proof RI1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & Y21 & Y23 & Y25 & Y26).
  pose proof (tpO2_conc fx1 R1 MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & MG2 & oFR & oFZ & (oMS & oKS & _)).
  set (W2 := fun a => F / 8 + SB + 12 <= a < F / 8 + SB + 16).
  apply (apiece L ar C HI LY HIok (ostr sk ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e3d8 R2 0x8e408 M2v W2 K B1 B2 (msteps_trans _ _ _ _ pMS oMS) MG2).
  { intros a Ha Hna. apply oFZ. exact Ha. clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W2; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] (ostr sk) Mc modelc LKc crc Ac M3 model3 W2 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W2; cbn beta in Wa; lia. }
  apply (ph_str fx2 R2 M3 model3 LKc crc Ac sk BI3 CRL).
  - apply (L5ATH.rinvT_ks R V2 cls F R1 R2 KS_tpO2 (proj1 RI1) oKS). vm_compute; reflexivity.
  - apply (str_agree Mc M3 sk ST). intros i Hi. apply FRM3. clear - Hi FRP; lia. subst W2; cbn beta. clear - Hi FRP FBIG. unfold SB.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fsh_off i : (F <= i < F + 512 \/ SPA <= i < S) -> ~ (F / 8 + SB <= i < F / 8 + SB + 64).
Proof.
  intros Hi. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & _). clear - Hi FRP FBIG V2R V2S CLS. unfold SB.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma tobj_rng o i : tobj o -> o <= i < o + 32 -> (F <= i < F + 512 \/ SPA <= i < S) /\ 0 <= i < 2 ^ 64.
Proof. intros TO Hi. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _). unfold tobj in TO. clear - TO Hi FRP V2R V2S CLS. lia. Qed.

(* [comment removed for export] *)
Lemma ph_N2 (fx : FPState) Rc Mc modelc LKc crc Ac sk ba :
  binv [] (ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc -> obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e3c4 Mc modelc) K.
Proof.
  intros BI CRL RI OA ST.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26).
  pose proof (tpN2_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & MG2 & oFR & oFZ & (oMS & oKS & oR22 & _)).
  set (W2 := fun a => F / 8 + SB + 20 <= a < F / 8 + SB + 24).
  apply (apiece L ar C HI LY HIok (ostr sk ++ LB) FF' LKc crc Ac Mc modelc fx fx2 Rc 0x8e3c4 R2 0x8e3d8 M2v W2 K B1 B2 oMS MG2).
  { intros a Ha Hna. apply oFZ. exact Ha. clear - Hna; subst W2; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W2; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] (ostr sk) Mc modelc LKc crc Ac M3 model3 W2 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W2; cbn beta in Wa; lia. }
  assert (AG3 : forall i, (F <= i < F + 512 \/ SPA <= i < S) -> 0 <= i < 2 ^ 64 -> M3 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
  { intros i Hi Hr. apply FRM3. exact Hr. intros X. apply (fsh_off i Hi). clear - X; subst W2; cbn beta in X; lia. }
  apply (ph_a fx2 R2 M3 model3 LKc crc Ac sk ba BI3 CRL).
  - apply (rinvX_ks Rc R2 KS_tpN2 RI oKS). vm_compute; reflexivity.
  - exact oR22.
  - assert (TA : tobj (F + 96)) by (left; clear; lia).
    apply (obj_at_agree Mc M3 _ _ _ OA). clear - FRP; lia. clear - FRP; lia. intros i Hi. destruct (tobj_rng _ i TA Hi) as [X Y]. apply AG3. exact X. exact Y.
  - apply (str_agree Mc M3 sk ST). intros i Hi. apply AG3. left; clear - Hi; lia. clear - Hi FRP; lia.
Qed.

(* [comment removed for export] *)
Lemma rinvX_T Rc : rinvX Rc -> rinvT Rc. Proof. intros X; exact (proj1 X). Qed.
Lemma blk_head (o : option (Z * Z)) (rest : list (Z * Z)) :
  match o with None => rest = ostr o ++ rest | Some (q, n) => In (q, n) ((ostr o ++ rest) ++ LB) /\ lb_remove q ((ostr o ++ rest) ++ LB) = rest ++ LB end.
Proof. destruct o as [[q n]|]; cbn [ostr app]. split. left; reflexivity. apply lb_remove_head. reflexivity. Qed.

Lemma ph_b (fx : FPState) Rc Mc modelc LKc crc Ac sk ob bb ba :
  binv [] (ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc -> obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e3a4 Mc modelc) K.
Proof.
  intros BI CRL RI OB OA ST.
  apply (dtor_stage rinvX rinvX 0x8e3a4 0x8e3c4 (F + 160) run_Ni run_Nd rinvX_T rinvX_pres ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia)
           fx Rc Mc modelc (ostr ob ++ ostr sk) (ostr sk) LKc crc Ac bb ob BI RI OB).
  - pose proof (blk_head ob (ostr sk)) as X. destruct ob as [[q n]|]. exact X. symmetry in X. cbn [ostr app] in X |- *. reflexivity.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_N2 fx' R' M' model' LKc crc A' sk ba BI' CRL RI').
    + apply (obj_keep (ostr sk ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (str_keep (ostr sk ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

Lemma ph_c (fx : FPState) Rc Mc modelc LKc crc Ac sk ob oc bc bb ba :
  binv [] (ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc ->
  obj_at Mc (V2 - 136) bc oc -> obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e384 Mc modelc) K.
Proof.
  intros BI CRL RI OC OB OA ST.
  apply (dtor_stage rinvX rinvX 0x8e384 0x8e3a4 (V2 - 136) run_Mi run_Md rinvX_T rinvX_pres ltac:(split; [clear; lia | reflexivity]) ltac:(right; clear - CLS; lia)
           fx Rc Mc modelc (ostr oc ++ ostr ob ++ ostr sk) (ostr ob ++ ostr sk) LKc crc Ac bc oc BI RI OC).
  - pose proof (blk_head oc (ostr ob ++ ostr sk)) as X. destruct oc as [[q n]|]. exact X. reflexivity.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_b fx' R' M' model' LKc crc A' sk ob bb ba BI' CRL RI').
    + apply (obj_keep ((ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OB). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (str_keep ((ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

(* [comment removed for export] *)
Lemma ph_d (fx : FPState) Rc Mc modelc LKc crc Ac sk ob oc od bd bc bb ba :
  binv [] (ostr od ++ ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc ->
  obj_at Mc (V2 - 168) bd od -> obj_at Mc (V2 - 136) bc oc -> obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e364 Mc modelc) K.
Proof.
  intros BI CRL RI OD OC OB OA ST.
  apply (dtor_stage rinvX rinvX 0x8e364 0x8e384 (V2 - 168) run_Li run_Ld rinvX_T rinvX_pres ltac:(split; [clear; lia | reflexivity]) ltac:(right; clear - CLS; lia)
           fx Rc Mc modelc (ostr od ++ ostr oc ++ ostr ob ++ ostr sk) (ostr oc ++ ostr ob ++ ostr sk) LKc crc Ac bd od BI RI OD).
  - pose proof (blk_head od (ostr oc ++ ostr ob ++ ostr sk)) as X. destruct od as [[q n]|]. exact X. reflexivity.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_c fx' R' M' model' LKc crc A' sk ob oc bc bb ba BI' CRL RI').
    + apply (obj_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OC). right; clear - CLS; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OB). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (str_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

(* [comment removed for export] *)
Lemma blk_second (oh o : option (Z * Z)) (rest : list (Z * Z)) Mc modelc LKc crc Ac :
  ri_inv HI ((ostr oh ++ ostr o ++ rest) ++ LB) FF' LKc crc Ac Mc (vml_of modelc) ->
  match o with None => ostr oh ++ rest = ostr oh ++ ostr o ++ rest
             | Some (q, n) => In (q, n) ((ostr oh ++ ostr o ++ rest) ++ LB) /\ lb_remove q ((ostr oh ++ ostr o ++ rest) ++ LB) = (ostr oh ++ rest) ++ LB end.
Proof.
  intros HH. destruct o as [[q n]|]; [|reflexivity]. destruct oh as [[qh nh]|]; cbn [ostr app].
  - assert (NEQ : qh <> q).
    { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF8. assert (ND : NoDup (map fst (((qh, nh) :: (q, n) :: rest) ++ LB))). { clear - WF8. decompose [and] WF8. assumption. }
      cbn [map fst app] in ND. inversion ND as [|x l NI _]. subst. intros E. apply NI. rewrite E. constructor. }
    split. right; left; reflexivity. rewrite lb_remove_skip by exact NEQ. rewrite lb_remove_head. reflexivity.
  - split. left; reflexivity. apply lb_remove_head.
Qed.

(* [comment removed for export] *)
Lemma ph_y (fx : FPState) Rc Mc modelc LKc crc Ac sk ob oc oy od by_ bd bc bb ba :
  binv [] (ostr od ++ ostr oy ++ ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> credit_le crmin crc -> rinvX Rc ->
  obj_at Mc (F + 288) by_ oy -> obj_at Mc (V2 - 168) bd od -> obj_at Mc (V2 - 136) bc oc -> obj_at Mc (F + 160) bb ob -> obj_at Mc (F + 96) ba None -> str_at Mc sk ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e344 Mc modelc) K.
Proof.
  intros BI CRL RI OY OD OC OB OA ST.
  apply (dtor_stage rinvX rinvX 0x8e344 0x8e364 (F + 288) run_Ki run_Kd rinvX_T rinvX_pres ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia)
           fx Rc Mc modelc (ostr od ++ ostr oy ++ ostr oc ++ ostr ob ++ ostr sk) (ostr od ++ ostr oc ++ ostr ob ++ ostr sk) LKc crc Ac by_ oy BI RI OY).
  - pose proof (blk_second od oy (ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac (proj1 BI)) as X. destruct oy as [[q n]|]. exact X. reflexivity.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    apply (ph_d fx' R' M' model' LKc crc A' sk ob oc od bd bc bb ba BI' CRL RI').
    + apply (obj_keep ((ostr od ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OD). right; clear - CLS; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr od ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OC). right; clear - CLS; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr od ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OB). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (obj_keep ((ostr od ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OA). left; clear; lia. rewrite DEL_EQ; clear; lia. exact AG'.
    + apply (str_keep ((ostr od ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST). rewrite DEL_EQ; clear; lia. exact AG'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma callee_pre W BX Mc modelc LKc crc Ac SCRc : binv W BX Mc modelc LKc crc Ac -> 0 <= SCRc -> SCRc + 208 <= SCRT ->
  astk ar Mc SPA SCRc /\ ffrk 1 FF' LKc d1 /\ ffrk 2 FF' LKc d2 /\ ffrk 3 FF' LKc d3 /\ ffrs FF' SPA /\ SPA mod 32 = 0.
Proof.
  intros (B1 & B2 & B3 & B4 & B5 & B6 & _) HS0 HS.
  assert (SA : (V2 - 192) mod 16 = 0 /\ (V2 - 192) mod 32 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as WF.
  assert (ND : NoDup (map ff_addr (FF' ++ LKc))). { clear - WF. decompose [and] WF. assumption. }
  split. { replace SPA with (S - (192 + cls)) by (clear; lia). apply (astk_sub ar Mc Mc S SCRT (192 + cls) SCRc B6 (mem_grows_refl Mc)).
           clear - CLS; lia. exact HS0. clear - HS CLS; lia. replace (S - (192 + cls)) with (V2 - 192) by (clear; lia). exact (proj1 SA). }
  split. { apply (ffrk_push_other 1 FF LK LKc (F, 3, V2 - 192 + 32) d1). cbn [ff_class fst snd]. clear; lia. exact FFR1. exact B5. exact ND. }
  split. { apply (ffrk_push_other 2 FF LK LKc (F, 3, V2 - 192 + 32) d2). cbn [ff_class fst snd]. clear; lia. exact FFR2. exact B5. exact ND. }
  split. { apply (ffrk_push 3 FF LK LKc (F, 3, V2 - 192 + 32) (d3 + 1) d3 FFR3 B5 ND). clear; lia. }
  split. { apply (ffrs_push FF S). exact FFRS. clear; lia. clear - CLS; lia. }
  exact (proj2 SA).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stksh_now BX Mc modelc LKc crc Ac lo : binv [] BX Mc modelc LKc crc Ac -> V2 + cls - SCRT <= lo -> lo mod 8 = 0 -> L5OMA.stksh ar Mc lo.
Proof.
  intros (_ & _ & _ & _ & _ & _ & B7 & _) H1 H8 j Hj. unfold byte_at.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _).
  assert (E : HeapIfaceA.S lo + j = HeapIfaceA.S (V2 + cls - SCRT) + ((lo - (V2 + cls - SCRT)) / 8 + j) /\ 0 <= (lo - (V2 + cls - SCRT)) / 8 + j < (Z.max (ar_sptop ar) (ar_stack_top ar) - (V2 + cls - SCRT)) / 8).
  { unfold HeapIfaceA.S. clear - H1 H8 Hj V2A CLS HSCR8. unfold aligned in V2A. lia. }
  destruct E as [E ER]. rewrite E. rewrite B7. apply STKSH. exact ER.
  split. { unfold HeapIfaceA.S, SB. clear - ER V2R CLS SPC SPT SLO TOP47. lia. }
  split. 2:{ intros rr []. }
  right; right; right; right; left. unfold in_shadow_of, HeapIfaceA.S. clear - ER SLO SHI SPC SPT CLS V2R V2A HSCR8 TOP47. unfold aligned in V2A. unfold SB. lia.
Qed.
Lemma stk_shadow BX Mc modelc LKc crc Ac o : binv [] BX Mc modelc LKc crc Ac -> SPA <= o -> o + 32 <= V2 -> o mod 8 = 0 -> shadow_zero Mc o 4.
Proof.
  intros BI H1 H2 H8 j Hj.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  apply (stksh_now BX Mc modelc LKc crc Ac o BI). clear - H1 SPC HSCR CLS; lia. exact H8. clear - Hj H2 H8 SHI CLS. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition objL (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (ws : list Z) (blk : option (Z * Z)) : Prop :=
  obj_at Mk o b blk /\ L5C.obj_limbs RSEGS Mk b ws /\ shadow_zero Mk o 4.

Lemma u8_of_defined Mk a : Mk (Z_to_bv 64 a) <> None -> exists v, L5.u8_at RSEGS Mk a v /\ 0 <= v < 256.
Proof.
  intros D. destruct (Mk (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence].
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. split; [|clear - Hb; lia].
  unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rinvY (Rc : bvmap 5 word) : Prop :=
  rinvT Rc /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96) /\ getr Rc (reg 23) = Z_to_bv 64 (F + 160) /\ getr Rc (reg 26) = Z_to_bv 64 (F + 224).
Definition YIDX : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21; 23; 26]%nat.
Lemma rinvY_keep Ra Rb : rinvY Ra -> (forall k, In k YIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvY Rb.
Proof.
  intros (XT & X21 & X23 & X26) KS. unfold rinvY. rewrite !KS by (apply L5K.in_b; vm_compute; reflexivity).
  split. { apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply KS. revert Hk. apply (L5K.incl_b TIDX YIDX). vm_compute; reflexivity. }
  repeat split; assumption.
Qed.
Lemma rinvY_ks Ra Rb (KS : list nat) : rinvY Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) YIDX = true -> rinvY Rb.
Proof. intros RI HKS HB. apply (rinvY_keep Ra Rb RI). intros k Hk. apply HKS. exact (L5K.incl_b YIDX KS HB k Hk). Qed.
Lemma rinvY_pres Ra Rb : rinvY Ra -> regs_preserved Ra Rb -> rinvY Rb.
Proof.
  intros RI RP. apply (rinvY_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP).
  revert Hk. apply (L5K.incl_b YIDX cs_all). vm_compute; reflexivity.
Qed.
Lemma rinvX_of_Y Rc : rinvY Rc -> getr Rc (reg 25) = Z_to_bv 64 (F + 288) -> rinvX Rc.
Proof. intros (XT & X21 & X23 & X26) X25. unfold rinvX. split. exact XT. split. exact X21. split. exact X23. split. exact X25. exact X26. Qed.

Lemma run_Hi : inl_run rinvY rinvX 0x8e304 0x8e328 (F + 224).
Proof.
  intros fx Rc MV fb RI PF O0 FBR BT0. open_pf PF.
  pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26).
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia). destruct FBR' as [FBR' FBR''].
  pose proof (tpHi_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _ & pR25)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. apply rinvX_of_Y. apply (rinvY_ks Rc R1 KS_tpHi RI pKS). vm_compute; reflexivity. exact pR25.
Qed.
Lemma run_Hd : dyn_run rinvY rinvX 0x8e304 0x8e328 (F + 224).
Proof.
  unfold dyn_run. replace (F + 224 + 24) with (F + 248) by (clear; lia). replace (F + 224 + 16) with (F + 240) by (clear; lia).
  intros fx Rc MV fb q cap RI PF O0 FBR BT1 O24 QR O16 CAPR. open_pf PF.
  pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26).
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia). destruct FBR' as [FBR' FBR''].
  assert (QR' : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64) by (clear - QR; lia). destruct QR' as [QR' QR''].
  assert (CR' : 1 <= cap <= 134217728 /\ 0 <= cap < 2 ^ 64) by (clear - CAPR; lia). destruct CR' as [CR' CR''].
  pose proof (tpHd_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR25)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  exists fx1, R1. split. exact pMS. split. { apply rinvX_of_Y. apply (rinvY_ks Rc R1 KS_tpHd RI pKS). vm_compute; reflexivity. exact pR25. }
  split. exact pR1. split. exact pR10. exact pR11.
Qed.

(* [comment removed for export] *)
Lemma obj_keepW LBx scr W Mc M1 o b blk : obj_at Mc o b blk -> tobj o -> 0 <= scr -> ahpres L ar LBx FF' SPA scr W Mc M1 ->
  (forall i, o <= i < o + 32 -> L5.outside W i) -> obj_at M1 o b blk.
Proof.
  intros OB TO Hs AH OUT. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  apply (obj_at_agree Mc M1 o b blk OB). clear - TO FRP V2R; unfold tobj in TO; lia. clear - TO FRP V2R V2S CLS; unfold tobj in TO; lia.
  intros i Hi. apply (proj1 AH). split. clear - Hi TO FRP V2R V2S CLS; unfold tobj in TO; lia. split. apply tcl. exact Hs. clear - Hi TO; unfold tobj in TO; lia. apply OUT. exact Hi.
Qed.
Lemma str_keepW LBx scr W Mc M1 sk : str_at Mc sk -> 0 <= scr -> ahpres L ar LBx FF' SPA scr W Mc M1 ->
  (forall i, F + 32 <= i < F + 56 -> L5.outside W i) -> str_at M1 sk.
Proof.
  intros ST Hs AH OUT. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _). apply (str_agree Mc M1 sk ST).
  intros i Hi. apply (proj1 AH). split. clear - Hi FRP; lia. split. apply tcl. exact Hs. left; clear - Hi; lia. apply OUT. exact Hi.
Qed.
Lemma out1 o i j : (j + 32 <= o \/ o + 32 <= j) -> j <= i < j + 32 -> L5.outside [(o, 32)] i.
Proof. intros H Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - H Hi X; lia. Qed.

Lemma objL_keepW LBx scr W Mc M1 o b ws blk : objL Mc o b ws blk -> F + 32 <= o -> o + 32 <= F + 504 -> 0 <= scr -> ahpres L ar LBx FF' SPA scr W Mc M1 ->
  (forall i, o <= i < o + 32 -> L5.outside W i) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBx /\ (forall i, q <= i < q + 8 * cap -> L5.outside W i)) ->
  (forall j, 0 <= j < 4 -> L5.outside W (o / 8 + SB + j)) ->
  objL M1 o b ws blk.
Proof.
  intros (OB & OL & OZ) H1 H2 Hs AH OUT OUTB OUTS. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  split. { apply (obj_keepW LBx scr W Mc M1 o b blk OB ltac:(left; split; assumption) Hs AH OUT). }
  split.
  - destruct OL as (Lws & Rws & LAT). split. exact Lws. split. exact Rws. destruct OB as [OBA _]. destruct OBA as (_ & _ & _ & OST).
    destruct (L5.bo_st b) as [v0 v1|cap q] eqn:EST. exact LAT.
    destruct OST as (_ & _ & _ & Hlc & CAPR & _ & Q4096 & Q47 & _). destruct (OUTB cap q eq_refl) as [INB OUTQ].
    eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - Q4096; lia. 2: rewrite Lws; clear - Q47 Hlc; lia.
    intros i Hi. rewrite Lws in Hi. apply (proj1 AH). split. clear - Hi Q4096 Q47 Hlc; lia. split. apply (block_client L ar LBx FF' SPA scr q (8 * cap) i INB). clear - Hi Hlc; lia.
    apply OUTQ. clear - Hi Hlc; lia.
  - intros j Hj. unfold byte_at. rewrite (proj1 AH). apply OZ. exact Hj.
    assert (E : HeapIfaceA.S o + j = o / 8 + SB + j) by reflexivity. rewrite E.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split. { clear - Hj H1 H2 FRP. unfold SB. lia. }
    split. { apply (fframe_shadow_client L ar LBx FF' SPA scr F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S.
             rewrite (proj1 (proj2 F8)). clear - Hj H1 H2 FRP. lia. }
    apply OUTS. exact Hj.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma inl_of_nodyn Mk o b : L5.big_at RSEGS Mk o b -> L5.bo_dyn b = false -> exists v0 v1, L5.bo_st b = L5.BInl v0 v1.
Proof.
  intros (_ & _ & _ & OST) D. destruct (L5.bo_st b) as [v0 v1|cap q]. exists v0, v1; reflexivity.
  exfalso. destruct OST as (BT1 & _). unfold L5.bo_dyn in D. rewrite BT1 in D. discriminate D.
Qed.

(* [comment removed for export] *)
Lemma ahpres_comp LBa LBb FFx sp s1 s2 s W1 W2 (Ma Mb Mc' : word -> option byte) :
  ahpres L ar LBa FFx sp s1 W1 Ma Mb -> ahpres L ar LBb FFx sp s2 W2 Mb Mc' ->
  (forall a, aclient L ar LBa FFx sp s a -> aclient L ar LBb FFx sp s a) ->
  0 <= s1 <= s -> 0 <= s2 <= s -> ahl_ceil ar <= sp - s -> 0 <= sp - s -> sp <= 2 ^ 47 -> L5.defined Ma (sp - s) s ->
  ahpres L ar LBa FFx sp s (W1 ++ W2) Ma Mc'.
Proof.
  intros (E1 & D1 & K1) (E2 & D2 & K2) SUB S1 S2 CE SP0 SP47 DEF.
  assert (C1 : forall a, aclient L ar LBa FFx sp s a -> aclient L ar LBa FFx sp s1 a). { intros a Hc. eapply aclient_mono. exact Hc. intros x Hx. clear - Hx S1. lia. }
  assert (C2 : forall a, aclient L ar LBa FFx sp s a -> aclient L ar LBb FFx sp s2 a). { intros a Hc. eapply aclient_mono. exact (SUB a Hc). intros x Hx. clear - Hx S2. lia. }
  split; [|split].
  - intros a (Ha & Hc & Ho). apply L5.outside_app in Ho. destruct Ho as (O1 & O2).
    rewrite (E2 a). apply (E1 a). split. exact Ha. split. exact (C1 a Hc). exact O1. split. exact Ha. split. exact (C2 a Hc). exact O2.
  - intros i Hi. set (x := sp - s + i).
    assert (STKC : forall LBx sc, x < sp - sc -> aclient L ar LBx FFx sp sc x). { intros LBx sc Hx. apply stack_client. subst x. clear - Hi CE SP47 Hx. lia. clear - Hx. lia. }
    assert (XR : 0 <= x < 2 ^ 64). { subst x. clear - Hi SP0 SP47 S1. lia. }
    assert (DB : Mb (Z_to_bv 64 x) <> None).
    { destruct (Z_lt_ge_dec x (sp - s1)) as [LT|GE]. apply (K1 x XR (STKC LBa s1 LT)). apply DEF. exact Hi.
      replace x with (sp - s1 + (x - (sp - s1))) by (clear; lia). apply D1. subst x. clear - GE Hi. lia. }
    destruct (Z_lt_ge_dec x (sp - s2)) as [LT|GE]. apply (K2 x XR (STKC LBb s2 LT)). exact DB.
    replace x with (sp - s2 + (x - (sp - s2))) by (clear; lia). apply D2. subst x. clear - GE Hi. lia.
  - intros a Ha Hc D. apply (K2 a Ha (C2 a Hc)). apply (K1 a Ha (C1 a Hc)). exact D.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section OPMODS.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> list fframe -> list fframe -> credit -> Z -> (word -> option byte) -> bvmap 5 word ->
                               list (Z * Z) -> credit -> list fframe -> Prop.
Variables (SCRo SCRf D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).
(* [comment removed for export] *)
Hypothesis Hom2 : L5BOMF.opmodf2_spec L ar HI SCRo SCRf D1 D2 D3 K2 bytes2.
Hypothesis HS_OM : 0 <= SCRo /\ 208 + SCRo <= SCRT.
Hypothesis HS_OMF : SCRo + 16 <= SCRf /\ COPY_SCR + 32 <= SCRf /\ 208 + SCRf <= SCRT.
Hypothesis HSO8 : SCRo mod 8 = 0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma spa_scro8 : (V2 - 192 - SCRo) mod 8 = 0.
Proof. clear - V2A HSO8. unfold aligned in V2A. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Hypothesis HDO : D1 <= d1 /\ D2 <= d2 /\ D3 <= d3.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.
Hypothesis IMG0 : L5.img_clear M 0x10000 0x3c000.

(* [comment removed for export] *)
Lemma img_clear_now BX Mc modelc LKc crc Ac : binv [] BX Mc modelc LKc crc Ac -> L5.img_clear Mc 0x10000 0x3c000.
Proof.
  intros (B1 & _ & _ & _ & _ & _ & B7 & _) a Ha. rewrite B7. apply IMG0. exact Ha.
  split. clear - Ha; lia. split. 2:{ intros rr []. }
  right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. clear - Ha; lia.
  intros X. pose proof (aly_static_lo L C LY a X) as Y. clear - Ha Y. lia.
Qed.

(* [comment removed for export] *)
Lemma in_lb_remove q (b : Z * Z) l : In b l -> fst b <> q -> In b (lb_remove q l).
Proof.
  induction l as [|c l IH]; intros Hin NE. destruct Hin. cbn [lb_remove]. destruct (Z.eqb_spec (fst c) q) as [E|E].
  - destruct Hin as [<-|Hin]. contradiction. exact Hin.
  - destruct Hin as [<-|Hin]. left; reflexivity. right. apply IH; assumption.
Qed.
Lemma key_not_in_tail BX : forall (LBx : list (Z * Z)) q n b, NoDup (map fst (BX ++ LBx)) -> In (q, n) BX -> In b LBx -> fst b <> q.
Proof.
  induction BX as [|c BX IH]; intros LBx q n b ND Hin Hb. destruct Hin.
  cbn [map app] in ND. inversion ND as [|x l NI ND']. subst. destruct Hin as [->|Hin].
  - cbn [fst] in NI. intros E. apply NI. rewrite <- E. apply list_elem_of_In. apply in_map. apply in_or_app. right. exact Hb.
  - apply (IH LBx q n b ND' Hin Hb).
Qed.
Lemma bx_not_client BX Mc modelc LKc crc Ac q n a :
  ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of modelc) -> In (q, n) BX -> q <= a < q + n -> ~ aclient L ar LB FF S SCRT a.
Proof.
  intros HH Hin Ha Hc.
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF.
  assert (ND : NoDup (map fst (BX ++ LB))). { clear - WF. decompose [and] WF. assumption. }
  destruct WF as (WB & _).
  destruct (WB (q, n) ltac:(apply in_or_app; left; exact Hin)) as (BR0 & _ & _ & _ & BA & BF & _). cbn [fst snd] in *.
  apply (fresh_block_not_client L ar C HI LY HIok LB FF' LK2 cr2 A M2 _ S SCRT q n a HH2 ltac:(clear - SPT; lia) BR0).
  - intros b Hb. apply BA. apply in_lb_remove. apply in_or_app; right; exact Hb. apply (key_not_in_tail BX LB q n b ND Hin Hb).
  - eapply fframes_apart_incl. exact BF. intros g0 Hg; apply in_or_app; left; exact Hg.
  - exact Ha.
  - apply aclient_cons. exact Hc.
Qed.

Lemma aobjF o : F + 32 <= o -> o + 32 <= F + 504 -> o mod 8 = 0 -> aobj FF' o 32.
Proof.
  intros H1 H2 H8. exists (F, 3, V2 - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 3) with 512.
  split. exact H1. split. clear - H2; lia. exact H8.
Qed.
Lemma F8s : F mod 8 = 0 /\ (F + 96) mod 8 = 0 /\ (F + 160) mod 8 = 0 /\ (F + 224) mod 8 = 0 /\ (F + 288) mod 8 = 0.
Proof.
  pose proof NUM as (_ & _ & _ & ALF & _). clear - ALF. unfold aligned in ALF.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma out_y BX Mc modelc LKc crc Ac (by_ : L5.bigobj) oy j i :
  ri_inv HI (BX ++ LB) FF' LKc crc Ac Mc (vml_of modelc) -> obj_at Mc (F + 288) by_ oy ->
  (forall q n, oy = Some (q, n) -> In (q, n) BX) ->
  ((F + 32 <= j /\ j + 32 <= F + 288) \/ (SPA <= j /\ j + 32 <= S)) -> j <= i < j + 32 ->
  L5.outside [(F + 288, 32); (L5.bo_data (F + 288) by_, 8 * L5.bo_cap by_)] i.
Proof.
  intros HH [OB OBLK] INB HJ Hi rr Hr X. unfold L5.in_rng in X.
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X.
  - clear - X Hi HJ SFB. lia.
  - unfold L5.bo_data, L5.bo_cap in X. destruct OB as (_ & _ & _ & OST). destruct (L5.bo_st by_) as [v0 v1|cap q].
    + clear - X Hi HJ SFB. lia.
    + pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
      destruct (WB (q, 8 * cap) ltac:(apply in_or_app; left; apply INB; exact OBLK)) as ((_ & _ & _ & _ & Q4 & _) & _ & _ & _ & _ & BF & _). cbn [fst snd] in *.
      specialize (BF (F, 3, V2 - 192 + 32) ltac:(left; reflexivity)). cbn [ff_addr ff_class fst snd] in BF. change (ff_bytes 3) with 512 in BF.
      pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
      clear - X Hi HJ BF Q4 SLO SPC. lia.
Qed.

(* [comment removed for export] *)
Lemma ph_opmod2 (fx : FPState) Rc Mc modelc LKc crc Ac sk ob oc oy by_ wy bc bb fba :
  binv [] (ostr oy ++ ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> rinvX Rc ->
  objL Mc (F + 288) by_ wy oy -> reduced wy -> (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> Z.of_nat (L5.bo_len by_) + 1 <= cap) ->
  (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
  obj_at Mc (V2 - 136) bc oc -> obj_at Mc (F + 160) bb ob ->
  L5OMA.a_ok Mc (F + 96) fba -> shadow_zero Mc (F + 96) 4 -> str_at Mc sk ->
  L5OMA.acredit_for L crc (K2 + 1) (bytes2 (L5.bo_cap by_) + 8 * Z.max (L5.bo_cap by_) 8) ->
  credit_le crmin (L5OMA.adebits L crc (K2 + 1) (bytes2 (L5.bo_cap by_) + 8 * Z.max (L5.bo_cap by_) 8)) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e334 Mc modelc) K.
Proof.
  intros BI RI (OY & OYL & OYZ) RED CAPL LEN1 CAPB OC OB AOK AZ ST CRF CRL.
  set (BX := ostr oy ++ ostr oc ++ ostr ob ++ ostr sk) in *. set (capy := L5.bo_cap by_) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26).
  pose proof (tpI_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  assert (RI1 : rinvX R1). { apply (rinvX_ks Rc R1 KS_tpI RI pKS). vm_compute; reflexivity. }
  apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e334 R1 L5OMA.OMF K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (binv_model [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  destruct HS_OMF as (HSF1 & HSF2 & HSF3).
  assert (SF0 : 0 <= SCRf) by (pose proof (proj1 HS_OM); clear - HSF1 H; lia).
  destruct (callee_pre [] BX Mc model1 LKc crc Ac SCRf BI1 SF0 ltac:(clear - HSF3; lia)) as (STK1 & R1k & R2k & R3k & RSk & A32).
  pose proof RI1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & _).
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  assert (CAP0 : 0 <= capy). { subst capy. unfold L5.bo_cap. destruct OY as [(_ & _ & _ & OST) _]. destruct (L5.bo_st by_). clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. }
  assert (INY : forall q n, oy = Some (q, n) -> In (q, n) BX). { intros q n E. subst oy BX. cbn [ostr app]. left; reflexivity. }
  destruct HK2 as [HK2a HK2b]. destruct HDO as (HDa & HDb & HDc).
  (* [comment removed for export] *)
  pose proof BI1 as (_ & _ & _ & _ & _ & B6 & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  assert (DDEF : L5.defined Mc (V2 - 168) 32).
  { pose proof B6 as (_ & _ & _ & _ & DSCR & _). intros i Hi. replace (V2 - 168 + i) with (S - SCRT + (V2 - 168 + i - (S - SCRT))) by (clear; lia). apply DSCR. clear - Hi SPC CLS. lia. }
  destruct (u8_of_defined Mc (V2 - 168) ltac:(replace (V2 - 168) with (V2 - 168 + 0) by (clear; lia); apply DDEF; clear; lia)) as (fbo & OFB & FBO).
  assert (V2M : V2 mod 8 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  assert (DM8 : (V2 - 168) mod 8 = 0 /\ (V2 - 192 - 16 - SCRo) mod 8 = 0) by (clear - V2M HSO8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (stk_shadow BX Mc model1 LKc crc Ac (V2 - 168) BI1 ltac:(clear; lia) ltac:(clear; lia) (proj1 DM8)) as DSZ.
  apply (Hom2 fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac (V2 - 168) (F + 288) (F + 96) SPA 582468 fba fbo by_ wy HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Y2.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - exact STK1.
  - apply (stksh_now BX Mc model1 LKc crc Ac (SPA - 16 - SCRo) BI1). clear - HS_OM HSF1 HSF3 CLS; lia. exact (proj2 DM8).
  - apply (ffrk_le 1 FF' LKc d1 D1 R1k HDa).
  - apply (ffrk_le 2 FF' LKc d2 D2 R2k HDb).
  - apply (ffrk_le 3 FF' LKc d3 D3 R3k HDc).
  - exact RSk.
  - apply (img_clear_now BX Mc model1 LKc crc Ac BI1).
  - split. exact (proj1 OY). split. exact OYL. split. exact RED.
    destruct OY as [OYA OYB]. destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST. exact I. split. apply in_or_app. left. apply INY. exact OYB. apply (CAPL cap q eq_refl).
  - apply aobjF. clear; lia. clear; lia. exact F8e.
  - exact OYZ.
  - exact LEN1.
  - exact CAPB.
  - exact AOK.
  - apply aobjF. clear; lia. clear; lia. exact F8b.
  - exact AZ.
  - right. clear; lia.
  - split. exact OFB. split. exact FBO. split. { split. clear; lia. split. clear - SHI CLS; lia. exact (proj1 DM8). } split. exact DDEF. exact DSZ.
  - replace (Z.max 64 (8 * L5.bo_cap by_)) with (8 * Z.max capy 8) by (subst capy; clear; lia). exact CRF.
  - (* [comment removed for export] *)
    intros fx2 R2 M1 M2' model2' LB1 LB2 cr1 cr2' LK1 LK2' A2' by' wy' g BIG' LIMBS' STM AOK' CRA AHP LKI1 POST LKI2' RT2 IA2 AM2 HH2'.
    assert (S0 : 0 <= SCRo + 16) by (pose proof (proj1 HS_OM); clear - H; lia).
    assert (SC0 : 0 <= COPY_SCR + 32) by (rewrite L5ACPS.SCR_EQ; clear; lia).
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
    assert (OC1 : obj_at M1 (V2 - 136) bc oc).
    { apply (obj_keepW _ _ _ _ _ _ _ _ OC ltac:(right; clear - CLS; lia) S0 AHP). intros i Hi. apply (out_y BX Mc model1 LKc crc Ac by_ oy (V2 - 136) i HH1 OY INY ltac:(right; clear - CLS; lia) Hi). }
    assert (OB1 : obj_at M1 (F + 160) bb ob).
    { apply (obj_keepW _ _ _ _ _ _ _ _ OB ltac:(left; clear; lia) S0 AHP). intros i Hi. apply (out_y BX Mc model1 LKc crc Ac by_ oy (F + 160) i HH1 OY INY ltac:(left; clear; lia) Hi). }
    assert (OA1 : obj_at M1 (F + 96) (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) None). { split. exact (proj1 AOK'). reflexivity. }
    assert (ST1 : str_at M1 sk).
    { apply (str_keepW _ _ _ _ _ _ ST S0 AHP). intros i Hi. apply (out_y BX Mc model1 LKc crc Ac by_ oy (F + 32) i HH1 OY INY ltac:(left; clear; lia) ltac:(clear - Hi; lia)). }
    (* [comment removed for export] *)
    assert (YBLK : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> In (q, 8 * cap) BX /\ q + 8 * cap <= ahl_ceil ar /\ (q + 8 * cap <= F \/ F + 512 <= q)
                     /\ 0 <= q /\ (q + 8 * cap <= BIGSHADOW_LO \/ BIGSHADOW_HI <= q)).
    { intros cap q E. destruct OY as [_ OYB]. rewrite E in OYB. pose proof (INY _ _ OYB) as IN1. split. exact IN1.
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB & _).
      destruct (WB (q, 8 * cap) ltac:(apply in_or_app; left; exact IN1)) as ((_ & _ & _ & _ & Q4 & (Q50 & Q51 & _)) & _ & _ & _ & _ & BF & _). cbn [fst snd] in *.
      specialize (BF (F, 3, V2 - 192 + 32) ltac:(left; reflexivity)). cbn [ff_addr ff_class fst snd] in BF. change (ff_bytes 3) with 512 in BF.
      split. exact Q4. split. exact BF. split. exact Q50. exact Q51. }
    assert (SHB : forall j, 0 <= j < 4 -> BIGSHADOW_LO <= (F + 288) / 8 + SB + j < BIGSHADOW_HI /\ F / 8 + SB <= (F + 288) / 8 + SB + j < F / 8 + SB + 64).
    { intros j Hj. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB. clear - Hj FR F8a. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (YZ1 : shadow_zero M1 (F + 288) 4).
    { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 288) + j = (F + 288) / 8 + SB + j) by reflexivity. rewrite E. destruct (SHB j Hj) as [SH1 SH2].
      rewrite (proj1 AHP). rewrite <- E. apply OYZ. exact Hj.
      split. { clear - SH1. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH1. lia. }
      split. { apply (fframe_shadow_client L ar (BX ++ LB) FF' SPA (SCRo + 16) F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S.
               rewrite (proj1 (proj2 F8)). clear - SH2. lia. }
      intros rr Hr X. unfold L5.in_rng in X. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X.
      - apply (fsh_off ((F + 288) / 8 + SB + j)). left. clear - X; lia. exact SH2.
      - unfold L5.bo_data, L5.bo_cap in X. destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST.
        + apply (fsh_off ((F + 288) / 8 + SB + j)). left. clear - X; lia. exact SH2.
        + destruct (YBLK cap q eq_refl) as (_ & _ & _ & Q0 & Q5). clear - X SH1 Q5. lia. }
    assert (CASES : exists oy', obj_at M1 (F + 288) by' oy' /\ LB1 = (ostr oy' ++ ostr oc ++ ostr ob ++ ostr sk) ++ LB /\ 0 <= L5.bo_cap by' <= Z.max capy 8
              /\ (forall cap q, L5.bo_st by' = L5.BDyn cap q -> q + 8 * cap <= ahl_ceil ar)
              /\ (forall a, aclient L ar (BX ++ LB) FF' SPA SCRf a -> aclient L ar LB1 FF' SPA SCRf a)).
    { destruct OY as [OYA OYB]. pose proof BIG' as (_ & _ & _ & OST'). subst capy. unfold L5.bo_cap.
      destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST; destruct (L5.bo_st by') as [v0' v1'|cap' q'] eqn:EST'.
      - subst oy. exists None. split. split. exact BIG'. rewrite EST'. reflexivity. split. exact STM. split. clear; lia. split. intros ? ? X; discriminate X. subst LB1. intros a X; exact X.
      - destruct STM as (E8 & ELB & FRESH). exists (Some (q', 64)). split. split. exact BIG'. rewrite EST'. rewrite E8. reflexivity. split. subst oy. rewrite ELB. reflexivity. split. rewrite E8. clear; lia.
        split. intros c0 q0 X. injection X as -> ->. destruct FRESH as ((_ & _ & _ & _ & Q4 & _) & _). rewrite E8. exact Q4.
        rewrite ELB. intros a X. apply aclient_consb. exact X.
      - contradiction.
      - destruct STM as (EC & EQ & ELB). exists oy. split. split. exact BIG'. rewrite EST'. rewrite EC, EQ. exact OYB. split. exact ELB.
        split. destruct OST' as (_ & _ & _ & _ & X & _). rewrite EC in *. clear - X; lia.
        split. intros c0 q0 X. injection X as -> ->. rewrite EC, EQ. exact (proj1 (proj2 (YBLK cap q eq_refl))). subst LB1. intros a X; exact X. }
    destruct CASES as (oy' & OY1 & ELB1 & CAPR' & YCE & CSUB). subst LB1.
    set (BX1 := ostr oy' ++ ostr oc ++ ostr ob ++ ostr sk) in *.
    (* [comment removed for export] *)
    destruct POST as (RP2 & POST).
    assert (KEEP : forall (Wd : ahpres L ar (BX1 ++ LB) FF' SPA (COPY_SCR + 32) [(V2 - 168, 32)] M1 M2'),
              objL M2' (F + 288) by' wy' oy' /\ obj_at M2' (V2 - 136) bc oc /\ obj_at M2' (F + 160) bb ob /\ obj_at M2' (F + 96) (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) None /\ str_at M2' sk).
    { intros Wd.
      split. 2:{ split. apply (obj_keepW _ _ _ _ _ _ _ _ OC1 ltac:(right; clear - CLS; lia) SC0 Wd). intros i Hi. apply (out1 _ i (V2 - 136)). clear; lia. exact Hi.
                 split. apply (obj_keepW _ _ _ _ _ _ _ _ OB1 ltac:(left; clear; lia) SC0 Wd). intros i Hi. apply (out1 _ i (F + 160)). clear - SFB'; lia. exact Hi.
                 split. apply (obj_keepW _ _ _ _ _ _ _ _ OA1 ltac:(left; clear; lia) SC0 Wd). intros i Hi. apply (out1 _ i (F + 96)). clear - SFB'; lia. exact Hi.
                 apply (str_keepW _ _ _ _ _ _ ST1 SC0 Wd). intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi SFB'; lia. }
      apply (objL_keepW _ _ _ _ _ _ _ _ _ (conj OY1 (conj LIMBS' YZ1)) ltac:(clear; lia) ltac:(clear; lia) SC0 Wd).
      - intros i Hi. apply (out1 _ i (F + 288)). clear - SFB'; lia. exact Hi.
      - intros cap q E. destruct OY1 as [_ OYB1]. rewrite E in OYB1. split. apply in_or_app. left. subst BX1. rewrite OYB1. cbn [ostr app]. left; reflexivity.
        pose proof (YCE cap q E) as Q4. intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi Q4 SLO SPC. lia.
      - intros j Hj rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X.
        assert (E : (F + 288) / 8 = F / 8 + 36). { clear - ALF. unfold aligned in ALF. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        rewrite E in X. apply (fsh_off (F / 8 + SB + (36 + j))). right. clear - X CLS; lia. clear - Hj; lia. }
    pose proof STK1 as (_ & SK2 & SK3 & SK4 & SK5 & _).
    assert (BIC : forall LKx crx Ax BXx, ahpres L ar (BX1 ++ LB) FF' SPA (COPY_SCR + 32) [(V2 - 168, 32)] M1 M2' -> ri_inv HI (BXx ++ LB) FF' LKx crx Ax M2' (vml_of model2') -> amodel_ok Ax model2' ->
              incl Ac Ax -> incl LKx LKc -> binv [] BXx M2' model2' LKx crx Ax).
    { intros LKx crx Ax BXx AHP2 HHx AMx IAx LKIx.
      pose proof (ahpres_comp (BX ++ LB) (BX1 ++ LB) FF' SPA (SCRo + 16) (COPY_SCR + 32) SCRf _ _ Mc M1 M2' AHP AHP2 CSUB ltac:(clear - S0 HSF1; lia) ltac:(clear - SC0 HSF2; lia)
                    ltac:(clear - SK2; lia) ltac:(clear - SK2 FCEIL FRP; lia) ltac:(clear - SK3 SK4; lia) SK5) as AHPC.
      apply (binv_callee [] [] BX BX BXx Mc model1 LKc crc Ac M2' model2' LKx crx Ax SCRf ([(F + 288, 32); (L5.bo_data (F + 288) by_, 8 * capy)] ++ [(V2 - 168, 32)]) BI1 AHPC HHx AMx RT2 IAx LKIx).
      - exact SF0.
      - clear - HSF3 CLS; lia.
      - intros rr a Hr X. unfold L5.in_rng in X. change (ff_bytes 3 / 8) with 64. cbn [app] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in X.
        + split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
        + subst capy. unfold L5.bo_data, L5.bo_cap in X. destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST.
          * split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
          * destruct (YBLK cap q eq_refl) as (_ & Q4 & _ & Q0 & Q5). split. unfold tocell. clear - X Q4 SLO SPC CLS; lia.
            intros Y. clear - X Y Q5 FR F8a. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          split. unfold tocell. clear - X CLS; lia. apply fsh_off. right. clear - X CLS; lia.
      - intros a Hc _ rr Hr X. unfold L5.in_rng in X. cbn [app] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in X.
        + apply (NCF a). left; clear - X; lia. exact Hc.
        + subst capy. unfold L5.bo_data, L5.bo_cap in X. destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST.
          * apply (NCF a). left; clear - X; lia. exact Hc.
          * destruct (YBLK cap q eq_refl) as (INQ & _). apply (bx_not_client BX Mc model1 LKc crc Ac q (8 * cap) a HH1 INQ X Hc).
        + apply (NCS a). clear - X CLS; lia. exact Hc.
      - intros a X. exact X. }
    assert (RI2 : rinvX R2) by (apply (rinvX_pres R1 R2 RI1 RP2)).
    assert (LKI : incl LK2' LKc) by (intros z Hz; apply LKI1, LKI2'; exact Hz).
    (* [comment removed for export] *)
    assert (CRD : credit_le crmin (adebit L cr1 (8 * L5.bo_cap by'))).
    { eapply credit_le_trans. exact CRL. rewrite <- (L5OMA.adebits_1 L cr1 (8 * L5.bo_cap by')).
      rewrite <- (L5OMA.adebits_add L crc K2 (bytes2 capy) 1 (8 * Z.max capy 8)).
      eapply credit_le_trans. apply (L5OMA.adebits_mono L _ cr1 1 (8 * Z.max capy 8) CRA). apply (L5OMA.adebits_le L cr1 1 (8 * Z.max capy 8) 1 (8 * L5.bo_cap by') LY2). clear; lia. clear - CAPR'; lia. }
    destruct g as [|q cap].
    + destruct POST as (DYNF & ELB & ECR & BIG & AHP2). subst LB2 cr2'.
      destruct (KEEP AHP2) as ((OY2 & _) & OC2 & OB2 & OA2 & ST2).
      destruct (inl_of_nodyn M1 (F + 288) by' (proj1 OY1) DYNF) as (v0 & v1 & EST).
      apply (ph_y fx2 R2 M2' model2' LK2' cr1 A2' sk ob oc oy' None by' (L5.BO (copy_fb fbo (L5.bo_fb by') false) (L5.bo_len by') (L5.bo_st by')) bc bb (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1))).
      * apply (BIC LK2' cr1 A2' BX1 AHP2 HH2' AM2 IA2 LKI).
      * eapply credit_le_trans. exact CRD. apply adebit_le. exact LY2. clear - CAPR'; lia.
      * exact RI2.
      * exact OY2.
      * split. exact BIG. cbn [L5.bo_st]. rewrite EST. reflexivity.
      * exact OC2.
      * exact OB2.
      * exact OA2.
      * exact ST2.
    + destruct POST as (DYNT & ECAP & ELB & ECR & FRESH & BIG & LIMBS & AHP2). subst LB2 cr2' cap.
      destruct (KEEP AHP2) as ((OY2 & _) & OC2 & OB2 & OA2 & ST2).
      apply (ph_y fx2 R2 M2' model2' LK2' (adebit L cr1 (8 * L5.bo_cap by')) A2' sk ob oc oy' (Some (q, 8 * L5.bo_cap by')) by'
               (L5.BO (copy_fb fbo (L5.bo_fb by') true) (L5.bo_len by') (L5.BDyn (L5.bo_cap by') q)) bc bb (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1))).
      * apply (BIC LK2' _ A2' (ostr (Some (q, 8 * L5.bo_cap by')) ++ BX1) AHP2 HH2' AM2 IA2 LKI).
      * exact CRD.
      * exact RI2.
      * exact OY2.
      * split. exact BIG. reflexivity.
      * exact OC2.
      * exact OB2.
      * exact OA2.
      * exact ST2.
Qed.

(* [comment removed for export] *)
Lemma frame_byte BX Mc modelc LKc crc Ac a : binv [] BX Mc modelc LKc crc Ac -> F <= a < F + 512 -> exists v, L5.u8_at RSEGS Mc a v /\ 0 <= v < 256.
Proof.
  intros BI Ha.
  destruct (vis_facts [] BX Mc modelc LKc crc Ac BI) as (_ & _ & (FDEFv & _) & (_ & _ & FV & _)). change (ff_bytes 3) with 512 in *.
  apply u8_of_defined. specialize (FDEFv (a - F) ltac:(clear - Ha; lia)). replace (F + (a - F)) with a in FDEFv by (clear; lia).
  unfold mrestrict in FDEFv. specialize (FV (a - F) ltac:(clear - Ha; lia)). replace (F + (a - F)) with a in FV by (clear; lia). rewrite FV in FDEFv. exact FDEFv.
Qed.
(* [comment removed for export] *)
Lemma shz_keepW LBx scr W Mc M1 o : shadow_zero Mc o 4 -> F + 32 <= o -> o + 32 <= F + 504 -> o mod 8 = 0 -> 0 <= scr -> ahpres L ar LBx FF' SPA scr W Mc M1 ->
  (forall j, 0 <= j < 4 -> L5.outside W (o / 8 + SB + j)) -> shadow_zero M1 o 4.
Proof.
  intros OZ H1 H2 H8 Hs AH OUTS j Hj. unfold byte_at. rewrite (proj1 AH). apply OZ. exact Hj.
  pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  assert (E : HeapIfaceA.S o + j = o / 8 + SB + j) by reflexivity. rewrite E.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split. { clear - Hj H1 H2 FRP. unfold SB. lia. }
  split. { apply (fframe_shadow_client L ar LBx FF' SPA scr F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S.
           rewrite (proj1 (proj2 F8)). clear - Hj H1 H2 FRP. lia. }
  apply OUTS. exact Hj.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma sh_in_F o j : F + 32 <= o -> o + 32 <= F + 504 -> 0 <= j < 4 -> F / 8 + SB <= o / 8 + SB + j < F / 8 + SB + 64.
Proof.
  intros H1 H2 Hj. pose proof NUM as (_ & FRP & _). pose proof F8s as (F8a & _). clear - H1 H2 Hj FRP F8a.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Lemma out1_sh o o' j : F + 32 <= o -> o + 32 <= F + 504 -> F <= o' -> o' + 32 <= F + 512 -> 0 <= j < 4 -> L5.outside [(o', 32)] (o / 8 + SB + j).
Proof.
  intros H1 H2 H3 H4 Hj rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X.
  apply (fsh_off (o / 8 + SB + j)). left. clear - X H3 H4; lia. apply sh_in_F; assumption.
Qed.

Lemma dyn_of_dyn Mk o b : L5.big_at RSEGS Mk o b -> L5.bo_dyn b = true -> exists cap q, L5.bo_st b = L5.BDyn cap q.
Proof.
  intros (_ & _ & _ & OST) D. destruct (L5.bo_st b) as [v0 v1|cap q]. 2:{ exists cap, q; reflexivity. }
  exfalso. destruct OST as (BT0 & _). unfold L5.bo_dyn in D. rewrite BT0 in D. discriminate D.
Qed.
Lemma a_ok_keepW LBx scr W Mc M1 fba : L5OMA.a_ok Mc (F + 96) fba -> 0 <= scr -> ahpres L ar LBx FF' SPA scr W Mc M1 ->
  (forall i, F + 96 <= i < F + 96 + 32 -> L5.outside W i) -> L5OMA.a_ok M1 (F + 96) fba.
Proof.
  intros [AB AT] Hs AH OUT. split. 2: exact AT.
  assert (OA : obj_at Mc (F + 96) (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) None) by (split; [exact AB | reflexivity]).
  exact (proj1 (obj_keepW LBx scr W Mc M1 _ _ _ OA ltac:(left; clear; lia) Hs AH OUT)).
Qed.

Section COPYY.
Hypothesis Hcp : copy_spec L ar HI.

(* [comment removed for export] *)
Lemma ph_copy_y (fx : FPState) Rc Mc modelc LKc crc Ac sk ob oc bc bb wb fba :
  binv [] (ostr oc ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> rinvX Rc ->
  objL Mc (F + 160) bb wb ob -> reduced wb -> (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  (1 <= L5.bo_len bb)%nat -> L5.bo_cap bb <= 268 ->
  obj_at Mc (V2 - 136) bc oc -> shadow_zero Mc (F + 288) 4 ->
  L5OMA.a_ok Mc (F + 96) fba -> shadow_zero Mc (F + 96) 4 -> str_at Mc sk ->
  L5OMA.acredit_for L crc (K2 + 2) (8 * L5.bo_cap bb + bytes2 (L5.bo_cap bb) + 8 * Z.max (L5.bo_cap bb) 8) ->
  credit_le crmin (L5OMA.adebits L crc (K2 + 2) (8 * L5.bo_cap bb + bytes2 (L5.bo_cap bb) + 8 * Z.max (L5.bo_cap bb) 8)) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e328 Mc modelc) K.
Proof.
  intros BI RI (OB & OBL & OBZ) RED CAPL LEN1 CAPB OC YZ AOK AZ ST CRF CRL.
  set (BX := ostr oc ++ ostr ob ++ ostr sk) in *. set (capb := L5.bo_cap bb) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X25 & X26).
  pose proof (tpH2_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  assert (RI1 : rinvX R1). { apply (rinvX_ks Rc R1 KS_tpH2 RI pKS). vm_compute; reflexivity. }
  apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e328 R1 COPY K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (binv_model [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  destruct (callee_pre [] BX Mc model1 LKc crc Ac COPY_SCR BI1 ltac:(rewrite L5ACPS.SCR_EQ; clear; lia) ltac:(clear - HS_COPY; lia)) as (STK1 & R1k & R2k & R3k & RSk & A32).
  pose proof RI1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & _).
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  assert (CAP0 : 0 <= capb). { subst capb. unfold L5.bo_cap. destruct OB as [(_ & _ & _ & OST) _]. destruct (L5.bo_st bb). clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. }
  destruct HK2 as [HK2a HK2b].
  assert (INB : forall q n, ob = Some (q, n) -> In (q, n) BX). { intros q n E. subst ob BX. apply in_or_app. right. cbn [ostr app]. left; reflexivity. }
  destruct (frame_byte BX Mc model1 LKc crc Ac (F + 288) BI1 ltac:(clear; lia)) as (fbo & OFB & FBO).
  destruct (L5OMA.acredit_for_take L crc (K2 + 2) (8 * capb + bytes2 capb + 8 * Z.max capb 8) (8 * capb) LY2 CRF ltac:(clear - HK2a; lia)
              ltac:(pose proof (HK2b capb CAP0); clear - H CAP0; lia)) as [CROK CRF1].
  replace (K2 + 2 - 1) with (K2 + 1) in CRF1 by (clear; lia). replace (8 * capb + bytes2 capb + 8 * Z.max capb 8 - 8 * capb) with (bytes2 capb + 8 * Z.max capb 8) in CRF1 by (clear; lia).
  apply (Hcp fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac (F + 288) (F + 160) SPA 582452 fbo bb wb HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - intros _. split. clear - CAPB; subst capb; lia. exact CROK.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Y2.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - exact STK1.
  - apply (proj1 (ffrk_1 FF' LKc 2)). apply (ffrk_le 1 FF' LKc d1 2 R1k). clear - HD1; lia.
  - exact RSk.
  - exact OFB.
  - exact FBO.
  - apply aobjF. clear; lia. clear; lia. exact F8e.
  - exact YZ.
  - exact (proj1 OB).
  - exact OBL.
  - apply aobjF. clear; lia. clear; lia. exact F8c.
  - exact OBZ.
  - intros cap q E. destruct OB as [_ OBB]. rewrite E in OBB. apply in_or_app. left. apply INB. exact OBB.
  - right. clear; lia.
  - intros fx2 R2 M2' model2' g LB2 cr2' LK2' A2' POST RT2 IA2 AM2 LKI2' HH2'.
    destruct POST as (RP2 & POST).
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
    pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
    assert (S0 : 0 <= COPY_SCR) by (rewrite L5ACPS.SCR_EQ; clear; lia).
    assert (KEEP : ahpres L ar (BX ++ LB) FF' SPA COPY_SCR [(F + 288, 32)] Mc M2' ->
              obj_at M2' (V2 - 136) bc oc /\ obj_at M2' (F + 160) bb ob /\ L5OMA.a_ok M2' (F + 96) fba /\ shadow_zero M2' (F + 96) 4 /\ str_at M2' sk /\ shadow_zero M2' (F + 288) 4).
    { intros Wd.
      split. apply (obj_keepW _ _ _ _ _ _ _ _ OC ltac:(right; clear - CLS; lia) S0 Wd). intros i Hi. apply (out1 _ i (V2 - 136)). clear - SFB'; lia. exact Hi.
      split. apply (obj_keepW _ _ _ _ _ _ _ _ OB ltac:(left; clear; lia) S0 Wd). intros i Hi. apply (out1 _ i (F + 160)). clear; lia. exact Hi.
      split. apply (a_ok_keepW _ _ _ _ _ _ AOK S0 Wd). intros i Hi. apply (out1 _ i (F + 96)). clear; lia. exact Hi.
      split. apply (shz_keepW _ _ _ _ _ _ AZ ltac:(clear; lia) ltac:(clear; lia) F8b S0 Wd). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
      split. apply (str_keepW _ _ _ _ _ _ ST S0 Wd). intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi; lia.
      apply (shz_keepW _ _ _ _ _ _ YZ ltac:(clear; lia) ltac:(clear; lia) F8e S0 Wd). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj. }
    assert (BIC : forall LK1 cr1 A1 BX1, ahpres L ar (BX ++ LB) FF' SPA COPY_SCR [(F + 288, 32)] Mc M2' -> ri_inv HI (BX1 ++ LB) FF' LK1 cr1 A1 M2' (vml_of model2') -> amodel_ok A1 model2' ->
              incl Ac A1 -> incl LK1 LKc -> binv [] BX1 M2' model2' LK1 cr1 A1).
    { intros LK1 cr1 A1 BX1 AHP HHx AMx IAx LKIx.
      apply (binv_callee [] [] BX BX BX1 Mc model1 LKc crc Ac M2' model2' LK1 cr1 A1 COPY_SCR [(F + 288, 32)] BI1 AHP HHx AMx RT2 IAx LKIx).
      - exact S0.
      - clear - HS_COPY CLS; lia.
      - intros rr a [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
      - intros a Hc _ rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (NCF a). left; clear - X; lia. exact Hc.
      - intros a X. exact X. }
    assert (RI2 : rinvX R2) by (apply (rinvX_pres R1 R2 RI1 RP2)).
    destruct g as [|q cap].
    + destruct POST as (DYNF & ELB & ECR & BIG & AHP). subst LB2 cr2'.
      destruct (KEEP AHP) as (OC2 & OB2 & AOK2 & AZ2 & ST2 & YZ2).
      destruct (inl_of_nodyn Mc (F + 160) bb (proj1 OB) DYNF) as (v0 & v1 & EST).
      apply (ph_opmod2 fx2 R2 M2' model2' LK2' crc A2' sk ob oc None (L5.BO (copy_fb fbo (L5.bo_fb bb) false) (L5.bo_len bb) (L5.bo_st bb)) wb bc bb fba).
      * apply (BIC LK2' crc A2' BX AHP HH2' AM2 IA2 LKI2').
      * exact RI2.
      * split. split. exact BIG. cbn [L5.bo_st]. rewrite EST. reflexivity.
        split. { destruct OBL as (Lws & Rws & LAT). split. exact Lws. split. exact Rws. cbn [L5.bo_st L5.bo_len]. rewrite EST in LAT |- *. exact LAT. } exact YZ2.
      * exact RED.
      * cbn [L5.bo_st L5.bo_len]. exact CAPL.
      * exact LEN1.
      * exact CAPB.
      * exact OC2.
      * exact OB2.
      * exact AOK2.
      * exact AZ2.
      * exact ST2.
      * change (L5.bo_cap (L5.BO (copy_fb fbo (L5.bo_fb bb) false) (L5.bo_len bb) (L5.bo_st bb))) with capb.
        apply (L5OMA.acredit_for_le L crc (K2 + 2) (8 * capb + bytes2 capb + 8 * Z.max capb 8) _ _ LY2 CRF). clear; lia. clear - CAP0; lia.
      * change (L5.bo_cap (L5.BO (copy_fb fbo (L5.bo_fb bb) false) (L5.bo_len bb) (L5.bo_st bb))) with capb.
        eapply credit_le_trans. exact CRL. apply (L5OMA.adebits_le L crc _ _ _ _ LY2). clear; lia. clear - CAP0; lia.
    + destruct POST as (DYNT & ECAP & ELB & ECR & FRESH & BIG & LIMBS & AHP). subst LB2 cr2'. fold capb in ECAP. subst cap.
      destruct (KEEP AHP) as (OC2 & OB2 & AOK2 & AZ2 & ST2 & YZ2).
      destruct (dyn_of_dyn Mc (F + 160) bb (proj1 OB) DYNT) as (cb & qb & EST).
      apply (ph_opmod2 fx2 R2 M2' model2' LK2' (adebit L crc (8 * capb)) A2' sk ob oc (Some (q, 8 * capb)) (L5.BO (copy_fb fbo (L5.bo_fb bb) true) (L5.bo_len bb) (L5.BDyn capb q)) wb bc bb fba).
      * apply (BIC LK2' _ A2' (ostr (Some (q, 8 * capb)) ++ BX) AHP HH2' AM2 IA2 LKI2').
      * exact RI2.
      * split. split. exact BIG. reflexivity. split. exact LIMBS. exact YZ2.
      * exact RED.
      * cbn [L5.bo_st L5.bo_len]. intros cap' q' E. injection E as <- <-. subst capb. unfold L5.bo_cap. rewrite EST. apply (CAPL cb qb EST).
      * exact LEN1.
      * exact CAPB.
      * exact OC2.
      * exact OB2.
      * exact AOK2.
      * exact AZ2.
      * exact ST2.
      * change (L5.bo_cap (L5.BO (copy_fb fbo (L5.bo_fb bb) true) (L5.bo_len bb) (L5.BDyn capb q))) with capb. exact CRF1.
      * change (L5.bo_cap (L5.BO (copy_fb fbo (L5.bo_fb bb) true) (L5.bo_len bb) (L5.BDyn capb q))) with capb.
        rewrite <- (L5OMA.adebits_1 L crc (8 * capb)). rewrite L5OMA.adebits_add. replace (1 + (K2 + 1)) with (K2 + 2) by (clear; lia).
        replace (8 * capb + (bytes2 capb + 8 * Z.max capb 8)) with (8 * capb + bytes2 capb + 8 * Z.max capb 8) by (clear; lia). exact CRL.
Qed.
End COPYY.

(* [comment removed for export] *)
Lemma shz_keep LBx scr Mc M1 o : shadow_zero Mc o 4 -> F + 32 <= o -> o + 32 <= F + 504 -> o mod 8 = 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> shadow_zero M1 o 4.
Proof.
  intros OZ H1 H2 H8 AG j Hj. unfold byte_at. rewrite AG. apply OZ. exact Hj.
  - pose proof (sh_in_F o j H1 H2 Hj) as X. pose proof NUM as (_ & FRP & _). pose proof F8s as (F8a & _). clear - X FRP F8a. unfold SB in *.
    assert (E : HeapIfaceA.S o + j = o / 8 + 2147450880 + j) by reflexivity. rewrite E.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
    apply (fframe_shadow_client L ar LBx FF' SPA scr F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of.
    assert (E : HeapIfaceA.S o + j = o / 8 + SB + j) by reflexivity. rewrite E. unfold HeapIfaceA.S. rewrite (proj1 (proj2 F8)).
    pose proof (sh_in_F o j H1 H2 Hj) as X. clear - X. lia.
Qed.
Lemma objL_keep LBx scr Mc M1 o b ws blk : objL Mc o b ws blk -> F + 32 <= o -> o + 32 <= F + 504 -> o mod 8 = 0 -> 0 <= scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBx) -> objL M1 o b ws blk.
Proof.
  intros (OB & OL & OZ) H1 H2 H8 Hs AG INB.
  split. { apply (obj_keep LBx scr Mc M1 o b blk OB ltac:(left; split; assumption) Hs AG). }
  split. 2:{ apply (shz_keep LBx scr Mc M1 o OZ H1 H2 H8 AG). }
  destruct OL as (Lws & Rws & LAT). split. exact Lws. split. exact Rws. destruct OB as [OBA _]. destruct OBA as (_ & _ & _ & OST).
  destruct (L5.bo_st b) as [v0 v1|cap q] eqn:EST. exact LAT.
  destruct OST as (_ & _ & _ & Hlc & CAPR & _ & Q4096 & Q47 & _).
  eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - Q4096; lia. 2: rewrite Lws; clear - Q47 Hlc; lia.
  intros i Hi. rewrite Lws in Hi. apply AG. clear - Hi Q4096 Q47 Hlc; lia. apply (block_client L ar LBx FF' SPA scr q (8 * cap) i (INB cap q eq_refl)). clear - Hi Hlc; lia.
Qed.
Lemma a_ok_keep LBx scr Mc M1 fba : L5OMA.a_ok Mc (F + 96) fba -> 0 <= scr ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBx FF' SPA scr a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) -> L5OMA.a_ok M1 (F + 96) fba.
Proof.
  intros [AB AT] Hs AG. split. 2: exact AT.
  assert (OA : obj_at Mc (F + 96) (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) None) by (split; [exact AB | reflexivity]).
  exact (proj1 (obj_keep LBx scr Mc M1 _ _ _ OA ltac:(left; clear; lia) Hs AG)).
Qed.

Section XDTOR.
Hypothesis Hcp : copy_spec L ar HI.
(* [comment removed for export] *)
Lemma ph_xdtor (fx : FPState) Rc Mc modelc LKc crc Ac sk ob ox oc bx bc bb wb fba :
  binv [] (ostr oc ++ ostr ox ++ ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> rinvY Rc ->
  obj_at Mc (F + 224) bx ox ->
  objL Mc (F + 160) bb wb ob -> reduced wb -> (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  (1 <= L5.bo_len bb)%nat -> L5.bo_cap bb <= 268 ->
  obj_at Mc (V2 - 136) bc oc -> shadow_zero Mc (F + 288) 4 ->
  L5OMA.a_ok Mc (F + 96) fba -> shadow_zero Mc (F + 96) 4 -> str_at Mc sk ->
  L5OMA.acredit_for L crc (K2 + 2) (8 * L5.bo_cap bb + bytes2 (L5.bo_cap bb) + 8 * Z.max (L5.bo_cap bb) 8) ->
  credit_le crmin (L5OMA.adebits L crc (K2 + 2) (8 * L5.bo_cap bb + bytes2 (L5.bo_cap bb) + 8 * Z.max (L5.bo_cap bb) 8)) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e304 Mc modelc) K.
Proof.
  intros BI RI OX OBJ RED CAPL LEN1 CAPB OC YZ AOK AZ ST CRF CRL.
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  apply (dtor_stage rinvY rinvX 0x8e304 0x8e328 (F + 224) run_Hi run_Hd rinvX_T rinvX_pres ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia)
           fx Rc Mc modelc (ostr oc ++ ostr ox ++ ostr ob ++ ostr sk) (ostr oc ++ ostr ob ++ ostr sk) LKc crc Ac bx ox BI RI OX).
  - pose proof (blk_second oc ox (ostr ob ++ ostr sk) Mc modelc LKc crc Ac (proj1 BI)) as X. destruct ox as [[q n]|]. exact X. reflexivity.
  - intros fx' R' M' model' A' BI' RI' IA' AG'.
    assert (S0 : 0 <= OPDEL_SCR) by (rewrite DEL_EQ; clear; lia).
    apply (ph_copy_y Hcp fx' R' M' model' LKc crc A' sk ob oc bc bb wb fba BI' RI').
    + apply (objL_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ _ OBJ ltac:(clear; lia) ltac:(clear; lia) F8c S0 AG').
      intros cap q E. destruct OBJ as ((_ & OBB) & _). rewrite E in OBB. subst ob. apply in_or_app. left. apply in_or_app. right. cbn [ostr app]. left; reflexivity.
    + exact RED.
    + exact CAPL.
    + exact LEN1.
    + exact CAPB.
    + apply (obj_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ _ _ OC). right; clear - CLS; lia. exact S0. exact AG'.
    + apply (shz_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ YZ ltac:(clear; lia) ltac:(clear; lia) F8e AG').
    + apply (a_ok_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ AOK S0 AG').
    + apply (shz_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' _ AZ ltac:(clear; lia) ltac:(clear; lia) F8b AG').
    + apply (str_keep ((ostr oc ++ ostr ob ++ ostr sk) ++ LB) OPDEL_SCR Mc M' sk ST S0 AG').
    + exact CRF.
    + exact CRL.
Qed.
End XDTOR.

(* [comment removed for export] *)
Lemma out_rf_sh o w j : F + 32 <= o -> o + 32 <= F + 504 -> SPA <= w -> w + 32 <= S -> 0 <= j < 4 -> L5.outside [(w, 32)] (o / 8 + SB + j).
Proof.
  intros H1 H2 H3 H4 Hj rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X.
  apply (fsh_off (o / 8 + SB + j)). right. clear - X H3 H4; lia. apply sh_in_F; assumption.
Qed.
Lemma objL_keep_rf BXx Mc modelc LKc crc Ac M1 scr w o b ws blk :
  ri_inv HI (BXx ++ LB) FF' LKc crc Ac Mc (vml_of modelc) -> objL Mc o b ws blk -> F + 32 <= o -> o + 32 <= F + 504 -> o mod 8 = 0 -> 0 <= scr ->
  SPA <= w -> w + 32 <= S -> ahpres L ar (BXx ++ LB) FF' SPA scr [(w, 32)] Mc M1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) (BXx ++ LB)) -> objL M1 o b ws blk.
Proof.
  intros HH OBJ H1 H2 H8 Hs W1 W2 AH INB.
  pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  apply (objL_keepW (BXx ++ LB) scr [(w, 32)] Mc M1 o b ws blk OBJ H1 H2 Hs AH).
  - intros i Hi. apply (out1 _ i o). clear - SFB' H2 W1; lia. exact Hi.
  - intros cap q E. split. exact (INB cap q E).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _). destruct (WB (q, 8 * cap) (INB cap q E)) as ((_ & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q4.
    intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi Q4 SLO SPC W1. lia.
  - intros j Hj. apply out_rf_sh; assumption.
Qed.


Section OPMOD1.
Hypothesis Hcp : copy_spec L ar HI.
Hypothesis Hom1 : L5BOMF.opmodf1_spec L ar HI XS xs_pre xs_foot e2_landed e3_landed SCRo SCRf D1 D2 D3 K1 bytes1.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
(* [comment removed for export] *)
Definition img_same (Mk : word -> option byte) : Prop :=
  (forall a, 0x10000 <= a < 0x634000 -> ~ hl_rt_static L a -> Mk (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  (forall a, ar_sptop ar <= a < 2 ^ 47 -> Mk (Z_to_bv 64 a) = M (Z_to_bv 64 a)).       (* [comment removed for export] *)
Lemma img_same_now BX Mc modelc LKc crc Ac : binv [] BX Mc modelc LKc crc Ac -> img_same Mc.
Proof.
  intros (B1 & _ & _ & _ & _ & _ & B7 & _). split.
  - intros a Ha NS. apply B7.
    split. clear - Ha; lia. split. 2:{ intros rr []. }
    right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact Ha. exact NS.
  - intros a Ha. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    apply B7. split. clear - Ha SPT; lia. split. 2:{ intros rr []. }
    right; left. split. clear - Ha SPT; lia. clear - Ha SHI; lia.
Qed.
Variable st0 : XS.
Hypothesis XSP : forall Mk, img_same Mk -> xs_pre st0 Mk.
Local Notation RESTB capb := (8 * capb + bytes2 capb + 8 * Z.max capb 8).

(* [comment removed for export] *)
Definition om1_state (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (LKk : list fframe) (crk : credit) (Ak : list (Z * Z))
           (sk ob : option (Z * Z)) (bb : L5.bigobj) (wb : list Z) (fba fbx : Z) : Prop :=
  binv [] (ostr ob ++ ostr sk) Mk modelk LKk crk Ak /\ rinvY Rk /\
  L5OMA.x_is_a Mk (F + 224) fbx /\ shadow_zero Mk (F + 224) 4 /\
  objL Mk (F + 160) bb wb ob /\ reduced wb /\ L5.bo_cap bb <= 268 /\
  shadow_zero Mk (F + 288) 4 /\ L5OMA.a_ok Mk (F + 96) fba /\ shadow_zero Mk (F + 96) 4 /\ str_at Mk sk /\
  credit_le crmin (L5OMA.adebits L crk (K1 + K2 + 3) (bytes1 (L5.bo_cap bb) + (64 + RESTB (L5.bo_cap bb)))).
(* [comment removed for export] *)
Definition E2_obl : Prop :=
  forall (fx' : FPState) Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx st R' M' model' LB' cr' LK' A',
    om1_state Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx ->
    regs_preserved Rk R' ->
    xs_pre st Mk ->                                  (* [comment removed for export] *)
    e2_landed st ((ostr ob ++ ostr sk) ++ LB) FF' LKk crk SPA M' R' LB' cr' LK' ->
    L5OMA.x_is_a M' (F + 224) fbx -> L5.big_at RSEGS M' (F + 160) bb -> L5C.obj_limbs RSEGS M' bb wb ->
    ahpres L ar ((ostr ob ++ ostr sk) ++ LB) FF' SPA (SCRo + 16) ((F + 224, 32) :: xs_foot) Mk M' ->
    model_rt modelk model' -> incl Ak A' -> amodel_ok A' model' ->
    ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
    srealizes RSEGS SCFG (cfg (fx:=fx') R' L5OMA.TOP_PAD M' model') K.
Definition E3_obl : Prop :=
  forall (fx' : FPState) Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx st R' M' model' LB' cr' LK' A' fbx' nx qx cr1,
    om1_state Rk Mk modelk LKk crk Ak sk ob bb wb fba fbx ->
    regs_preserved Rk R' ->
    xs_pre st Mk ->                                  (* [comment removed for export] *)
    L5.big_at RSEGS M' (F + 224) (L5.BO fbx' nx (L5.BDyn 8 qx)) -> afresh L ar ((ostr ob ++ ostr sk) ++ LB) (FF' ++ LK') M' qx 64 ->
    L5OMA.acredit_after L crk K1 (bytes1 (L5.bo_cap bb)) cr1 ->
    e3_landed st ((qx, 64) :: (ostr ob ++ ostr sk) ++ LB) FF' LKk cr1 SPA M' R' LB' cr' LK' ->
    L5.big_at RSEGS M' (F + 160) bb -> L5C.obj_limbs RSEGS M' bb wb ->
    ahpres L ar ((ostr ob ++ ostr sk) ++ LB) FF' SPA (SCRo + 16) ((F + 224, 32) :: xs_foot) Mk M' ->
    model_rt modelk model' -> incl Ak A' -> amodel_ok A' model' ->
    ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
    srealizes RSEGS SCFG (cfg (fx:=fx') R' L5OMA.TOP_PAD M' model') K.

(* [comment removed for export] *)
Lemma ph_opmod1 (fx : FPState) Rc Mc modelc LKc crc Ac sk ob bb wb fba fbx :
  E2_obl -> E3_obl ->
  om1_state Rc Mc modelc LKc crc Ac sk ob bb wb fba fbx ->
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
  L5OMA.acredit_for L crc (K1 + K2 + 3) (bytes1 (L5.bo_cap bb) + (64 + RESTB (L5.bo_cap bb))) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e2f4 Mc modelc) K.
Proof.
  intros E2 E3 STATE CAPL DYN3 CRF.
  pose proof STATE as (BI & RI & XA & XZ & OBJ & RED & CAPB & YZ & AOK & AZ & ST & CRL).
  set (BX := ostr ob ++ ostr sk) in *. set (capb := L5.bo_cap bb) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23 & X26).
  pose proof (tpF_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR12)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  assert (RI1 : rinvY R1). { apply (rinvY_ks Rc R1 KS_tpF RI pKS). vm_compute; reflexivity. }
  apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e2f4 R1 L5OMA.OMF K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (binv_model [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  destruct HS_OMF as (HSF1 & HSF2 & HSF3).
  assert (SF0 : 0 <= SCRf) by (pose proof (proj1 HS_OM); clear - HSF1 H; lia).
  destruct (callee_pre [] BX Mc model1 LKc crc Ac SCRf BI1 SF0 ltac:(clear - HSF3; lia)) as (STK1 & R1k & R2k & R3k & RSk & A32).
  pose proof RI1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & _).
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  destruct HK2 as [HK2a HK2b]. destruct HK1 as [HK1a HK1b]. destruct HDO as (HDa & HDb & HDc).
  assert (CAP0 : 0 <= capb). { subst capb. unfold L5.bo_cap. destruct OBJ as ((( _ & _ & _ & OST) & _) & _). destruct (L5.bo_st bb). clear; lia. destruct OST as (_ & _ & _ & _ & X & _). clear - X; lia. }
  assert (INB : forall cap q, L5.bo_st bb = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)).
  { intros cap q E. destruct OBJ as ((_ & OBB) & _). rewrite E in OBB. subst ob. apply in_or_app. left. subst BX. cbn [ostr app]. left; reflexivity. }
  assert (STATE1 : om1_state R1 Mc model1 LKc crc Ac sk ob bb wb fba fbx).
  { unfold om1_state. fold BX. fold capb. split. exact BI1. split. exact RI1. repeat (split; [assumption|]). exact CRL. }
  (* [comment removed for export] *)
  pose proof BI1 as (_ & _ & _ & _ & _ & B6 & _).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  assert (DDEF : L5.defined Mc (V2 - 136) 32).
  { pose proof B6 as (_ & _ & _ & _ & DSCR & _). intros i Hi. replace (V2 - 136 + i) with (S - SCRT + (V2 - 136 + i - (S - SCRT))) by (clear; lia). apply DSCR. clear - Hi SPC CLS. lia. }
  destruct (u8_of_defined Mc (V2 - 136) ltac:(replace (V2 - 136) with (V2 - 136 + 0) by (clear; lia); apply DDEF; clear; lia)) as (fbo & OFB & FBO).
  assert (V2M : V2 mod 8 = 0). { clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  assert (DM8 : (V2 - 136) mod 8 = 0 /\ (V2 - 192 - 16 - SCRo) mod 8 = 0) by (clear - V2M HSO8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (stk_shadow BX Mc model1 LKc crc Ac (V2 - 136) BI1 ltac:(clear; lia) ltac:(clear; lia) (proj1 DM8)) as DSZ.
  apply (Hom1 fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac (V2 - 136) (F + 224) (F + 160) SPA fbx fbo bb wb st0 HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - rewrite r12. exact pR12.
  - rewrite r1. exact pR1.
  - rewrite r2. exact Y2.
  - replace (9%bv : bv 5) with (reg 9) by (apply bv_eq; reflexivity). exact Y9.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - replace (3%bv : bv 5) with (reg 3) by (apply bv_eq; reflexivity). rewrite Y3. exact G3.
  - exact STK1.
  - apply (stksh_now BX Mc model1 LKc crc Ac (SPA - 16 - SCRo) BI1). clear - HS_OM HSF1 HSF3 CLS; lia. exact (proj2 DM8).
  - apply (ffrk_le 1 FF' LKc d1 D1 R1k HDa).
  - apply (ffrk_le 2 FF' LKc d2 D2 R2k HDb).
  - apply (ffrk_le 3 FF' LKc d3 D3 R3k HDc).
  - exact RSk.
  - apply (img_clear_now BX Mc model1 LKc crc Ac BI1).
  - exact XA.
  - apply aobjF. clear; lia. clear; lia. exact F8d.
  - exact XZ.
  - destruct OBJ as ((OBA & OBB) & OBL & _). split. exact OBA. split. exact OBL. split. exact RED.
    destruct (L5.bo_st bb) as [v0 v1|cap q] eqn:EST. exact I. apply (INB cap q eq_refl).
  - apply aobjF. clear; lia. clear; lia. exact F8c.
  - exact (proj2 (proj2 OBJ)).
  - right. clear; lia.
  - exact CAPB.
  - exact DYN3.
  - split. exact OFB. split. exact FBO. split. { split. clear; lia. split. clear - SHI CLS; lia. exact (proj1 DM8). } split. exact DDEF. exact DSZ.
  - apply (L5OMA.acredit_for_le L crc (K1 + K2 + 3) (bytes1 capb + (64 + RESTB capb)) (K1 + 1) (bytes1 capb + 64) LY2 CRF). clear - HK2a; lia.
    pose proof (HK2b capb CAP0). clear - H CAP0. lia.
  - (* [comment removed for export] *)
    intros Mo OFFW. apply XSP. destruct (img_same_now BX Mc model1 LKc crc Ac BI1) as (I1 & I2). split.
    + intros a Ha NS. rewrite OFFW. exact (I1 a Ha NS). clear - Ha; lia. clear - Ha V2R; lia.
    + intros a Ha. rewrite OFFW. exact (I2 a Ha). clear - Ha SPT; lia. clear - Ha SHI CLS; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M1 M2' model2' LB1 LB2 cr1 cr2' LK1 LK2' A2' bx wx g BIGX LIMX NEGX STX BIGB LIMB LEN1 CRA AHP LKI1 POST LKI2' RT2 IA2 AM2 HH2'.
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
    assert (S0 : 0 <= SCRo + 16) by (pose proof (proj1 HS_OM); clear - H; lia).
    assert (SC0 : 0 <= COPY_SCR + 32) by (rewrite L5ACPS.SCR_EQ; clear; lia).
    assert (CASES : exists ox, obj_at M1 (F + 224) bx ox /\ LB1 = (ostr ox ++ BX) ++ LB /\ 0 <= L5.bo_cap bx <= 8
              /\ (forall a, aclient L ar (BX ++ LB) FF' SPA SCRf a -> aclient L ar LB1 FF' SPA SCRf a)).
    { unfold L5.bo_cap. destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:EST.
      - exists None. split. split. exact BIGX. rewrite EST. reflexivity. split. exact STX. split. clear; lia. subst LB1. intros a X; exact X.
      - destruct STX as (E8 & ELB & FRESH). exists (Some (q, 64)). split. split. exact BIGX. rewrite EST. rewrite E8. reflexivity. split. rewrite ELB. reflexivity. split. rewrite E8. clear; lia.
        rewrite ELB. intros a X. apply aclient_consb. exact X. }
    destruct CASES as (ox & OX1 & ELB1 & CAPX & CSUB). subst LB1.
    destruct POST as (RP2 & POST).
    pose proof STK1 as (_ & SK2 & SK3 & SK4 & SK5 & _).
    set (WC := [(F + 224, 32)] ++ [(V2 - 136, 32)]).
    assert (COMP : ahpres L ar ((ostr ox ++ BX) ++ LB) FF' SPA (COPY_SCR + 32) [(V2 - 136, 32)] M1 M2' -> ahpres L ar (BX ++ LB) FF' SPA SCRf WC Mc M2').
    { intros AHP2. exact (ahpres_comp (BX ++ LB) ((ostr ox ++ BX) ++ LB) FF' SPA (SCRo + 16) (COPY_SCR + 32) SCRf _ _ Mc M1 M2' AHP AHP2 CSUB ltac:(clear - S0 HSF1; lia) ltac:(clear - SC0 HSF2; lia)
                    ltac:(clear - SK2; lia) ltac:(clear - SK2 FCEIL FRP; lia) ltac:(clear - SK3 SK4; lia) SK5). }
    assert (OUTC : forall i, ((F <= i < F + 512 \/ F / 8 + SB <= i < F / 8 + SB + 64) /\ ~ (F + 224 <= i < F + 256)) -> L5.outside WC i).
    { intros i (Hi & NX) rr Hr X. unfold L5.in_rng in X. subst WC. cbn [app] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X. apply NX. clear - X; lia.
      destruct Hi as [Hi|Hi]. clear - X Hi SFB' CLS; lia. apply (fsh_off i). right. clear - X CLS; lia. exact Hi. }
    assert (KEEP : ahpres L ar ((ostr ox ++ BX) ++ LB) FF' SPA (COPY_SCR + 32) [(V2 - 136, 32)] M1 M2' ->
              obj_at M2' (F + 224) bx ox /\ objL M2' (F + 160) bb wb ob /\ shadow_zero M2' (F + 288) 4 /\ L5OMA.a_ok M2' (F + 96) fba /\ shadow_zero M2' (F + 96) 4 /\ str_at M2' sk).
    { intros Wd. pose proof (COMP Wd) as Wc.
      split. apply (obj_keepW _ _ _ _ _ _ _ _ OX1 ltac:(left; clear; lia) SC0 Wd). intros i Hi. apply (out1 _ i (F + 224)). clear - SFB'; lia. exact Hi.
      split. { apply (objL_keepW _ _ _ _ _ _ _ _ _ OBJ ltac:(clear; lia) ltac:(clear; lia) SF0 Wc).
        - intros i Hi. apply OUTC. split. left. clear - Hi; lia. clear - Hi; lia.
        - intros cap q E. split. exact (INB cap q E).
          pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB & _).
          destruct (WB (q, 8 * cap) (INB cap q E)) as ((_ & _ & _ & _ & Q4 & _) & _ & _ & _ & _ & BF & _). cbn [fst snd] in *.
          specialize (BF (F, 3, V2 - 192 + 32) ltac:(left; reflexivity)). cbn [ff_addr ff_class fst snd] in BF. change (ff_bytes 3) with 512 in BF.
          intros i Hi rr Hr X. unfold L5.in_rng in X. subst WC. cbn [app] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X. clear - X Hi BF; lia. clear - X Hi Q4 SLO SPC; lia.
        - intros j Hj. apply OUTC. pose proof (sh_in_F (F + 160) j ltac:(clear; lia) ltac:(clear; lia) Hj) as Y. split. right. exact Y. intros X. apply (fsh_off ((F + 160) / 8 + SB + j)). left. clear - X; lia. exact Y. }
      split. { apply (shz_keepW _ _ _ _ _ _ YZ ltac:(clear; lia) ltac:(clear; lia) F8e SF0 Wc). intros j Hj. apply OUTC. pose proof (sh_in_F (F + 288) j ltac:(clear; lia) ltac:(clear; lia) Hj) as Y. split. right. exact Y. intros X. apply (fsh_off ((F + 288) / 8 + SB + j)). left. clear - X; lia. exact Y. }
      split. { apply (a_ok_keepW _ _ _ _ _ _ AOK SF0 Wc). intros i Hi. apply OUTC. split. left. clear - Hi; lia. clear - Hi; lia. }
      split. { apply (shz_keepW _ _ _ _ _ _ AZ ltac:(clear; lia) ltac:(clear; lia) F8b SF0 Wc). intros j Hj. apply OUTC. pose proof (sh_in_F (F + 96) j ltac:(clear; lia) ltac:(clear; lia) Hj) as Y. split. right. exact Y. intros X. apply (fsh_off ((F + 96) / 8 + SB + j)). left. clear - X; lia. exact Y. }
      apply (str_keepW _ _ _ _ _ _ ST SF0 Wc). intros i Hi. apply OUTC. split. left. clear - Hi; lia. clear - Hi; lia. }
    assert (BIC : forall LKx crx Ax BXx, ahpres L ar ((ostr ox ++ BX) ++ LB) FF' SPA (COPY_SCR + 32) [(V2 - 136, 32)] M1 M2' -> ri_inv HI (BXx ++ LB) FF' LKx crx Ax M2' (vml_of model2') -> amodel_ok Ax model2' ->
              incl Ac Ax -> incl LKx LKc -> binv [] BXx M2' model2' LKx crx Ax).
    { intros LKx crx Ax BXx AHP2 HHx AMx IAx LKIx.
      apply (binv_callee [] [] BX BX BXx Mc model1 LKc crc Ac M2' model2' LKx crx Ax SCRf WC BI1 (COMP AHP2) HHx AMx RT2 IAx LKIx).
      - exact SF0.
      - clear - HSF3 CLS; lia.
      - intros rr a Hr X. unfold L5.in_rng in X. subst WC. cbn [app] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X.
        + split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
        + split. unfold tocell. clear - X CLS; lia. apply fsh_off. right. clear - X CLS; lia.
      - intros a Hc _ rr Hr X. unfold L5.in_rng in X. subst WC. cbn [app] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X.
        + apply (NCF a). left; clear - X; lia. exact Hc.
        + apply (NCS a). clear - X CLS; lia. exact Hc.
      - intros a X. exact X. }
    assert (RI2 : rinvY R2) by (apply (rinvY_pres R1 R2 RI1 RP2)).
    assert (LKI : incl LK2' LKc) by (intros z Hz; apply LKI1, LKI2'; exact Hz).
    pose proof (L5OMA.acredit_for_split L crc (K1 + K2 + 3) (bytes1 capb + (64 + RESTB capb)) K1 (bytes1 capb) LY2 CRF ltac:(clear - HK1a HK2a; lia)
                  ltac:(pose proof (HK1b capb CAP0); pose proof (HK2b capb CAP0); clear - H H0 CAP0; lia)) as [_ CRF2].
    replace (K1 + K2 + 3 - K1) with (K2 + 3) in CRF2 by (clear; lia). replace (bytes1 capb + (64 + RESTB capb) - bytes1 capb) with (64 + RESTB capb) in CRF2 by (clear; lia).
    pose proof (L5OMA.acredit_for_mono L _ cr1 (K2 + 3) (64 + RESTB capb) CRF2 CRA) as CRF3.
    assert (CRL1 : credit_le crmin (L5OMA.adebits L cr1 (K2 + 3) (64 + RESTB capb))).
    { eapply credit_le_trans. exact CRL. replace (K1 + K2 + 3) with (K1 + (K2 + 3)) by (clear; lia).
      rewrite <- (L5OMA.adebits_add L crc K1 (bytes1 capb) (K2 + 3) (64 + RESTB capb)). apply (L5OMA.adebits_mono L _ cr1 _ _ CRA). }
    destruct (L5OMA.acredit_for_take L cr1 (K2 + 3) (64 + RESTB capb) (8 * L5.bo_cap bx) LY2 CRF3 ltac:(clear - HK2a; lia)
                ltac:(pose proof (HK2b capb CAP0); clear - H CAP0 CAPX; lia)) as [CROK CRF1].
    destruct g as [|q cap].
    + destruct POST as (DYNF & ELB & ECR & BIG & AHP2). subst LB2 cr2'.
      destruct (KEEP AHP2) as (OX2 & OBJ2 & YZ2 & AOK2 & AZ2 & ST2).
      destruct (inl_of_nodyn M1 (F + 224) bx (proj1 OX1) DYNF) as (v0 & v1 & EST).
      apply (ph_xdtor Hcp fx2 R2 M2' model2' LK2' cr1 A2' sk ob ox None bx (L5.BO (copy_fb fbo (L5.bo_fb bx) false) (L5.bo_len bx) (L5.bo_st bx)) bb wb fba).
      * apply (BIC LK2' cr1 A2' (ostr ox ++ BX) AHP2 HH2' AM2 IA2 LKI).
      * exact RI2.
      * exact OX2.
      * exact OBJ2.
      * exact RED.
      * exact CAPL.
      * exact LEN1.
      * exact CAPB.
      * split. exact BIG. cbn [L5.bo_st]. rewrite EST. reflexivity.
      * exact YZ2.
      * exact AOK2.
      * exact AZ2.
      * exact ST2.
      * apply (L5OMA.acredit_for_le L cr1 (K2 + 3) (64 + RESTB capb) _ _ LY2 CRF3). clear; lia. subst capb; clear; lia.
      * eapply credit_le_trans. exact CRL1. apply (L5OMA.adebits_le L cr1 _ _ _ _ LY2). clear; lia. subst capb; clear; lia.
    + destruct POST as (DYNT & ECAP & ELB & ECR & FRESH & BIG & LIMBS & AHP2). subst LB2 cr2' cap.
      destruct (KEEP AHP2) as (OX2 & OBJ2 & YZ2 & AOK2 & AZ2 & ST2).
      apply (ph_xdtor Hcp fx2 R2 M2' model2' LK2' (adebit L cr1 (8 * L5.bo_cap bx)) A2' sk ob ox (Some (q, 8 * L5.bo_cap bx)) bx
               (L5.BO (copy_fb fbo (L5.bo_fb bx) true) (L5.bo_len bx) (L5.BDyn (L5.bo_cap bx) q)) bb wb fba).
      * apply (BIC LK2' _ A2' (ostr (Some (q, 8 * L5.bo_cap bx)) ++ ostr ox ++ BX) AHP2 HH2' AM2 IA2 LKI).
      * exact RI2.
      * exact OX2.
      * exact OBJ2.
      * exact RED.
      * exact CAPL.
      * exact LEN1.
      * exact CAPB.
      * split. exact BIG. reflexivity.
      * exact YZ2.
      * exact AOK2.
      * exact AZ2.
      * exact ST2.
      * apply (L5OMA.acredit_for_le L _ (K2 + 3 - 1) (64 + RESTB capb - 8 * L5.bo_cap bx) _ _ LY2 CRF1). clear; lia. subst capb; clear - CAPX; lia.
      * eapply credit_le_trans. exact CRL1. rewrite <- (L5OMA.adebits_1 L cr1 (8 * L5.bo_cap bx)). rewrite L5OMA.adebits_add.
        apply (L5OMA.adebits_le L cr1 _ _ _ _ LY2). clear; lia. subst capb; clear - CAPX; lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2' model2' LB2 cr2' LK2' A2' RP2 LANDED XA' BIGB LIMB AHP RT2 IA2 AM2 HH2'.
    exact (E2 fx2 R1 Mc model1 LKc crc Ac sk ob bb wb fba fbx st0 R2 M2' model2' LB2 cr2' LK2' A2' STATE1 RP2 (XSP Mc (img_same_now BX Mc model1 LKc crc Ac BI1)) LANDED XA' BIGB LIMB AHP RT2 IA2 AM2 HH2').
  - (* [comment removed for export] *)
    intros fx2 R2 M2' model2' LB2 cr2' LK2' A2' fbx' nx qx cr1 RP2 BIGX FRESH CRA1 LANDED BIGB LIMB AHP RT2 IA2 AM2 HH2'.
    exact (E3 fx2 R1 Mc model1 LKc crc Ac sk ob bb wb fba fbx st0 R2 M2' model2' LB2 cr2' LK2' A2' fbx' nx qx cr1 STATE1 RP2 (XSP Mc (img_same_now BX Mc model1 LKc crc Ac BI1)) BIGX FRESH CRA1 LANDED BIGB LIMB AHP RT2 IA2 AM2 HH2').
Qed.

(* [comment removed for export] *)
Definition rinv2 (Rc : bvmap 5 word) : Prop := rinvT Rc /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96) /\ getr Rc (reg 23) = Z_to_bv 64 (F + 160).
Definition IDX2 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21; 23]%nat.
Lemma rinv2_keep Ra Rb : rinv2 Ra -> (forall k, In k IDX2 -> getr Rb (reg k) = getr Ra (reg k)) -> rinv2 Rb.
Proof.
  intros (XT & X21 & X23) KS. unfold rinv2. rewrite !KS by (apply L5K.in_b; vm_compute; reflexivity).
  split. { apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply KS. revert Hk. apply (L5K.incl_b TIDX IDX2). vm_compute; reflexivity. }
  split; assumption.
Qed.
Lemma rinv2_ks Ra Rb (KS : list nat) : rinv2 Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) IDX2 = true -> rinv2 Rb.
Proof. intros RI HKS HB. apply (rinv2_keep Ra Rb RI). intros k Hk. apply HKS. exact (L5K.incl_b IDX2 KS HB k Hk). Qed.
Lemma rinv2_pres Ra Rb : rinv2 Ra -> regs_preserved Ra Rb -> rinv2 Rb.
Proof.
  intros RI RP. apply (rinv2_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP).
  revert Hk. apply (L5K.incl_b IDX2 cs_all). vm_compute; reflexivity.
Qed.
Lemma copy_fb_bit1 fbo fba : Z.testbit fba 1 = false -> Z.testbit (copy_fb fbo fba false) 1 = false.
Proof.
  intros H. unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec, H.
  change (Z.testbit 252 1) with false. change (Z.testbit 0 1) with false. change (Z.testbit 2 1) with true.
  rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma ph_copy_x (fx : FPState) Rc Mc modelc LKc crc Ac sk ob bb wb fba :
  E2_obl -> E3_obl ->
  binv [] (ostr ob ++ ostr sk) Mc modelc LKc crc Ac -> rinv2 Rc ->
  shadow_zero Mc (F + 224) 4 ->
  objL Mc (F + 160) bb wb ob -> reduced wb -> L5.bo_cap bb <= 268 ->
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
  shadow_zero Mc (F + 288) 4 -> L5OMA.a_ok Mc (F + 96) fba -> shadow_zero Mc (F + 96) 4 -> str_at Mc sk ->
  L5OMA.acredit_for L crc (K1 + K2 + 3) (bytes1 (L5.bo_cap bb) + (64 + RESTB (L5.bo_cap bb))) ->
  credit_le crmin (L5OMA.adebits L crc (K1 + K2 + 3) (bytes1 (L5.bo_cap bb) + (64 + RESTB (L5.bo_cap bb)))) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e2e4 Mc modelc) K.
Proof.
  intros E2 E3 BI RI XZ OBJ RED CAPB CAPL DYN3 YZ AOK AZ ST CRF CRL.
  set (BX := ostr ob ++ ostr sk) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21 & X23).
  pose proof (tpE_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11 & pR26)).
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR). subst M1v.
  assert (RI1 : rinvY R1).
  { pose proof (rinv2_ks Rc R1 KS_tpE RI pKS ltac:(vm_compute; reflexivity)) as (Z1 & Z21 & Z23). unfold rinvY. split. exact Z1. split. exact Z21. split. exact Z23. exact pR26. }
  apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e2e4 R1 COPY K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (binv_model [] BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  destruct (callee_pre [] BX Mc model1 LKc crc Ac COPY_SCR BI1 ltac:(rewrite L5ACPS.SCR_EQ; clear; lia) ltac:(clear - HS_COPY; lia)) as (STK1 & R1k & R2k & R3k & RSk & A32).
  pose proof RI1 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & _).
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  destruct (frame_byte BX Mc model1 LKc crc Ac (F + 224) BI1 ltac:(clear; lia)) as (fbo & OFB & FBO).
  assert (INB : forall cap q, L5.bo_st bb = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)).
  { intros cap q E. destruct OBJ as ((_ & OBB) & _). rewrite E in OBB. subst ob. apply in_or_app. left. subst BX. cbn [ostr app]. left; reflexivity. }
  destruct AOK as [ABIG ABIT].
  apply (Hcp fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac (F + 224) (F + 96) SPA 582388 fbo (L5.BO fba 2 (L5.BInl L5PSA.A0 L5PSA.A1)) [L5PSA.A0; L5PSA.A1] HH1 AM1 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - intros D. exfalso. destruct ABIG as (_ & _ & _ & (BT0 & _)). unfold L5.bo_dyn in D. cbn [L5.bo_fb] in *. rewrite BT0 in D. discriminate D.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Y2.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - exact STK1.
  - apply (proj1 (ffrk_1 FF' LKc 2)). apply (ffrk_le 1 FF' LKc d1 2 R1k). clear - HD1; lia.
  - exact RSk.
  - exact OFB.
  - exact FBO.
  - apply aobjF. clear; lia. clear; lia. exact F8d.
  - exact XZ.
  - exact ABIG.
  - destruct ABIG as (_ & _ & _ & (_ & _ & _ & _ & RA0 & RA1)). split. reflexivity. split. { constructor. exact RA0. constructor. exact RA1. constructor. } reflexivity.
  - apply aobjF. clear; lia. clear; lia. exact F8b.
  - exact AZ.
  - intros cap q E. discriminate E.
  - right. clear; lia.
  - intros fx2 R2 M2' model2' g LB2 cr2' LK2' A2' POST RT2 IA2 AM2 LKI2' HH2'.
    destruct POST as (RP2 & POST).
    destruct g as [|q cap]. 2:{ exfalso. destruct POST as (DYNT & _). destruct ABIG as (_ & _ & _ & (BT0 & _)). unfold L5.bo_dyn in DYNT. cbn [L5.bo_fb] in *. rewrite BT0 in DYNT. discriminate DYNT. }
    destruct POST as (_ & ELB & ECR & BIG & AHP). subst LB2 cr2'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in BIG.
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
    pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
    change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
    assert (S0 : 0 <= COPY_SCR) by (rewrite L5ACPS.SCR_EQ; clear; lia).
    assert (BI2 : binv [] BX M2' model2' LK2' crc A2').
    { apply (binv_callee [] [] BX BX BX Mc model1 LKc crc Ac M2' model2' LK2' crc A2' COPY_SCR [(F + 224, 32)] BI1 AHP HH2' AM2 RT2 IA2 LKI2').
      - exact S0.
      - clear - HS_COPY CLS; lia.
      - intros rr a [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
      - intros a Hc _ rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (NCF a). left; clear - X; lia. exact Hc.
      - intros a X. exact X. }
    apply (ph_opmod1 fx2 R2 M2' model2' LK2' crc A2' sk ob bb wb fba (copy_fb fbo fba false) E2 E3).
    + unfold om1_state. fold BX. split. exact BI2. split. exact (rinvY_pres R1 R2 RI1 RP2).
      split. { split. exact BIG. apply copy_fb_bit1. exact ABIT. }
      split. { apply (shz_keepW _ _ _ _ _ _ XZ ltac:(clear; lia) ltac:(clear; lia) F8d S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj. }
      split. { apply (objL_keepW _ _ _ _ _ _ _ _ _ OBJ ltac:(clear; lia) ltac:(clear; lia) S0 AHP).
               - intros i Hi. apply (out1 _ i (F + 160)). clear; lia. exact Hi.
               - intros cap q E. split. exact (INB cap q E).
                 pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB & _). destruct (WB (q, 8 * cap) (INB cap q E)) as (_ & _ & _ & _ & _ & BF & _). cbn [fst snd] in BF.
                 specialize (BF (F, 3, V2 - 192 + 32) ltac:(left; reflexivity)). cbn [ff_addr ff_class fst snd] in BF. change (ff_bytes 3) with 512 in BF.
                 intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi BF. lia.
               - intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj. }
      split. exact RED. split. exact CAPB.
      split. { apply (shz_keepW _ _ _ _ _ _ YZ ltac:(clear; lia) ltac:(clear; lia) F8e S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj. }
      split. { apply (a_ok_keepW _ _ _ _ _ _ (conj ABIG ABIT) S0 AHP). intros i Hi. apply (out1 _ i (F + 96)). clear; lia. exact Hi. }
      split. { apply (shz_keepW _ _ _ _ _ _ AZ ltac:(clear; lia) ltac:(clear; lia) F8b S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj. }
      split. { apply (str_keepW _ _ _ _ _ _ ST S0 AHP). intros i Hi rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi; lia. }
      exact CRL.
    + exact CAPL.
    + exact DYN3.
    + exact CRF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits_all ds : L5PSA.digits_ok ds -> all_digits ds = true.
Proof.
  intros H. unfold all_digits. apply forallb_forall. intros x Hx. unfold is_digit.
  pose proof (proj1 (List.Forall_forall _ _) H x Hx) as X. cbn in X. apply andb_true_intro. split; apply Z.leb_le; clear - X; lia.
Qed.
Lemma nwords_cap ds : L5PSA.digits_ok ds -> (length ds <= 4999)%nat -> (nwords (dec ds) <= 260)%nat.
Proof.
  intros D Hl. eapply Nat.le_trans; [| apply num_words_est_4999; exact Hl].
  apply nwords_bound. apply dec_bound. apply digits_all. exact D.
Qed.
Lemma reduced_wlist V : 0 <= V -> reduced (wlist V (nwords V)).
Proof.
  intros HV. unfold reduced. destruct (Z.eq_dec V 0) as [->|NZ]; [left; rewrite nwords_0; reflexivity| right].
  rewrite wlist_length. pose proof (nwords_pos V ltac:(clear - HV NZ; lia)) as NP.
  change (nth (nwords V - 1) (wlist V (nwords V)) 0) with (nth_w (wlist V (nwords V)) (nwords V - 1)).
  rewrite wlist_nth by (clear - NP; lia). apply wordi_top_nonzero. clear - HV NZ; lia.
Qed.

(* [comment removed for export] *)
Definition str_full (Mk : word -> option byte) (sk : option (Z * Z)) (s : list Z) : Prop :=
  match sk with
  | None => L5.lstr_short RSEGS Mk (F + 32) s
  | Some (pd, nb) => exists w0, L5.lstr_long RSEGS Mk (F + 32) s w0 pd /\ nb = w0 - 1 /\ Z.of_nat (length s) + 1 <= w0 - 1 /\ 0 <= w0 < 2 ^ 64 /\ 4096 <= pd <= 2 ^ 47
  end.
Lemma str_full_at Mk sk s : str_full Mk sk s -> str_at Mk sk.
Proof.
  destruct sk as [[pd nb]|]; cbn [str_full str_at].
  - intros (w0 & (W0T & S0 & _ & SPD & _) & _ & _ & W0R & PDR). exists w0. split. exact S0. split. exact W0R. split. exact W0T. split. replace (F + 48) with (F + 32 + 16) by (clear; lia). exact SPD. exact PDR.
  - intros (L22 & B0 & _). exists (2 * Z.of_nat (length s)). split. exact B0. split. clear - L22; lia. apply Z.testbit_even_0.
Qed.
Lemma str_full_keepW BXx Mc modelc LKc crc Ac M1 scr w sk s :
  ri_inv HI (BXx ++ LB) FF' LKc crc Ac Mc (vml_of modelc) -> str_full Mc sk s -> (forall q n, sk = Some (q, n) -> In (q, n) (BXx ++ LB)) -> 0 <= scr ->
  F + 96 <= w -> w + 32 <= F + 504 -> ahpres L ar (BXx ++ LB) FF' SPA scr [(w, 32)] Mc M1 -> str_full M1 sk s.
Proof.
  intros HH SF INS Hs W1 W2 AH. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  assert (AGH : L5C.agree_on Mc M1 (F + 32) 24).
  { intros i Hi. apply (proj1 AH). split. clear - Hi FRP; lia. split. apply tcl. exact Hs. left; clear - Hi; lia.
    intros rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi W1; lia. }
  destruct sk as [[pd nb]|]; cbn [str_full] in *.
  - destruct SF as (w0 & (W0T & S0 & S8 & SPD & BYT & NUL) & ENB & LEN & W0R & PDR). exists w0.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
    destruct (WB (pd, nb) (INS pd nb eq_refl)) as ((_ & _ & _ & _ & Q4 & (_ & _ & Q6)) & _ & _ & _ & _ & BF & _). cbn [fst snd] in *.
    specialize (BF (F, 3, V2 - 192 + 32) ltac:(left; reflexivity)). cbn [ff_addr ff_class fst snd] in BF. change (ff_bytes 3) with 512 in BF.
    assert (AGB : L5C.agree_on Mc M1 pd (Z.of_nat (length s) + 1)).
    { intros i Hi. apply (proj1 AH). split. clear - Hi PDR Q6 LEN ENB; lia. split. apply (block_client L ar (BXx ++ LB) FF' SPA scr pd nb i (INS pd nb eq_refl)). clear - Hi LEN ENB; lia.
      intros rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. clear - X Hi BF W1 W2 LEN ENB; lia. }
    split. 2:{ split. exact ENB. split. exact LEN. split. exact W0R. exact PDR. }
    split. exact W0T.
    split. { eapply L5C.u64_at_agree. 4: exact S0. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact S8. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact SPD. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.bytes_at_agree. 4: exact BYT. intros j Hj; apply AGB; clear - Hj; lia. clear - PDR; lia. clear - PDR Q6 LEN ENB; lia. }
    eapply L5C.u8_at_agree. 4: exact NUL. intros j Hj; apply AGB; clear - Hj; lia. clear - PDR; lia. clear - PDR Q6 LEN ENB; lia.
  - eapply L5C.lstr_short_agree. 4: exact SF. exact AGH. clear - FRP; lia. clear - FRP; lia.
Qed.

Section PARSE.
Variable IL : icpt_layout.
Variable SCRs : Z.
Hypothesis Hsc : L5ASCS.strctor_norm_specB L ar IL HI SCRs.
Hypothesis HS_SC : 0 <= SCRs /\ 208 + SCRs <= SCRT.
Hypothesis HSS8 : SCRs mod 8 = 0.                 (* [comment removed for export] *)
Hypothesis HBM : (forall c c', c <= c' -> bytes1 c <= bytes1 c') /\ (forall c c', c <= c' -> bytes2 c <= bytes2 c').
Local Notation REST capb := (bytes1 capb + (64 + RESTB capb)).

(* [comment removed for export] *)
Lemma a_ok_agree Mc M1 fba : L5OMA.a_ok Mc (F + 96) fba -> (forall i, F + 96 <= i < F + 128 -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)) -> L5OMA.a_ok M1 (F + 96) fba.
Proof.
  intros [AB AT] AG. split. 2: exact AT. pose proof NUM as (_ & FRP & _).
  eapply L5C.big_at_agree. 4: exact AB. intros i Hi. apply AG. clear - Hi; lia. clear - FRP; lia. clear - FRP; lia.
Qed.
Lemma shz_agree Mc M1 o : shadow_zero Mc o 4 -> (forall j, 0 <= j < 4 -> M1 (Z_to_bv 64 (o / 8 + SB + j)) = Mc (Z_to_bv 64 (o / 8 + SB + j))) -> shadow_zero M1 o 4.
Proof. intros OZ AG j Hj. unfold byte_at. assert (E : HeapIfaceA.S o + j = o / 8 + SB + j) by reflexivity. rewrite E. rewrite AG by exact Hj. rewrite <- E. apply OZ. exact Hj. Qed.
Lemma str_full_agree BXx Mc modelc LKc crc Ac M1 sk s :
  ri_inv HI (BXx ++ LB) FF' LKc crc Ac Mc (vml_of modelc) -> str_full Mc sk s -> (forall q n, sk = Some (q, n) -> In (q, n) (BXx ++ LB)) ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + SB <= i < F / 8 + SB + 64) -> M1 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)) -> str_full M1 sk s.
Proof.
  intros HH SF INS AG. pose proof NUM as ((FRG & FLRG & V2RG) & FRP & _).
  assert (AGH : L5C.agree_on Mc M1 (F + 32) 24).
  { intros i Hi. apply AG. clear - Hi FRP; lia. apply fsh_off. left; clear - Hi; lia. }
  destruct sk as [[pd nb]|]; cbn [str_full] in *.
  - destruct SF as (w0 & (W0T & S0 & S8 & SPD & BYT & NUL) & ENB & LEN & W0R & PDR). exists w0.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
    destruct (WB (pd, nb) (INS pd nb eq_refl)) as ((_ & _ & _ & _ & Q4 & (Q50 & Q51 & Q6)) & _). cbn [fst snd] in *.
    assert (AGB : L5C.agree_on Mc M1 pd (Z.of_nat (length s) + 1)).
    { intros i Hi. apply AG. clear - Hi PDR Q6 LEN ENB; lia. intros X. pose proof F8s as (F8a & _).
      clear - X Hi Q51 LEN ENB FRP F8a. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. 2:{ split. exact ENB. split. exact LEN. split. exact W0R. exact PDR. }
    split. exact W0T.
    split. { eapply L5C.u64_at_agree. 4: exact S0. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact S8. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.u64_at_agree. 4: exact SPD. intros j Hj; apply AGH; clear - Hj; lia. clear - FRP; lia. clear - FRP; lia. }
    split. { eapply L5C.bytes_at_agree. 4: exact BYT. intros j Hj; apply AGB; clear - Hj; lia. clear - PDR; lia. clear - PDR Q6 LEN ENB; lia. }
    eapply L5C.u8_at_agree. 4: exact NUL. intros j Hj; apply AGB; clear - Hj; lia. clear - PDR; lia. clear - PDR Q6 LEN ENB; lia.
  - eapply L5C.lstr_short_agree. 4: exact SF. exact AGH. clear - FRP; lia. clear - FRP; lia.
Qed.

(* [comment removed for export] *)
Definition sc_state (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (LKk : list fframe) (crk : credit) (Ak : list (Z * Z))
           (sk : option (Z * Z)) (s : list Z) (fba : Z) : Prop :=
  binv [] (ostr sk) Mk modelk LKk crk Ak /\ rinv2 Rk /\ getr Rk (reg 1) = Z_to_bv 64 582372 /\
  L5OMA.a_ok Mk (F + 96) fba /\ shadow_zero Mk (F + 96) 4 /\ shadow_zero Mk (F + 224) 4 /\ shadow_zero Mk (F + 288) 4 /\
  str_full Mk sk s /\ shadow_zero Mk (F + 32) 3 /\ shadow_zero Mk (F + 160) 4 /\
  credit_le crmin (L5OMA.adebits L crk (2 + (K1 + K2 + 3)) (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268)) /\
  L5OMA.acredit_for L crk (2 + (K1 + K2 + 3)) (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268).     (* [comment removed for export] *)
Definition E1_obl : Prop :=
  forall (fx' : FPState) Rk Mk modelk LKk crk Ak sk s fba fbo R' M' model' cr' LK' A',
    sc_state Rk Mk modelk LKk crk Ak sk s fba ->
    L5ASCS.strctor_throw_state L ar (ostr sk ++ LB) FF' crk Mk M' Rk R' (F + 160) SPA fbo s SCRs cr' ->
    model_rt modelk model' -> incl Ak A' -> amodel_ok A' model' -> incl LK' LKk ->
    ri_inv HI (ostr sk ++ LB) FF' LK' cr' A' M' (vml_of model') ->
    srealizes RSEGS SCFG (cfg (fx:=fx') R' L5ASCS.STRCTOR_THROW M' model') K.

Definition rinv1 (Rc : bvmap 5 word) : Prop := rinvT Rc /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96).
Definition IDX1 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 27; 21]%nat.
Lemma rinv1_ks Ra Rb (KS : list nat) : rinv1 Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) IDX1 = true -> rinv1 Rb.
Proof.
  intros (XT & X21) HKS HB. unfold rinv1. rewrite (HKS 21%nat) by (apply (L5K.incl_b IDX1 KS HB); apply L5K.in_b; vm_compute; reflexivity).
  split. 2: exact X21. apply (L5ATH.rinvT_keep R V2 cls F Ra Rb XT). intros k Hk. apply HKS. apply (L5K.incl_b IDX1 KS HB). revert Hk. apply (L5K.incl_b TIDX IDX1). vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_strctor (fx : FPState) Rc Mc modelc LKc crc Ac sk s fba :
  E1_obl -> E2_obl -> E3_obl ->
  binv [] (ostr sk) Mc modelc LKc crc Ac -> rinv1 Rc ->
  L5OMA.a_ok Mc (F + 96) fba -> shadow_zero Mc (F + 96) 4 -> shadow_zero Mc (F + 224) 4 -> shadow_zero Mc (F + 288) 4 ->
  str_full Mc sk s -> shadow_zero Mc (F + 32) 3 -> (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
  L5OMA.acredit_for L crc (2 + (K1 + K2 + 3)) (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268) ->
  credit_le crmin (L5OMA.adebits L crc (2 + (K1 + K2 + 3)) (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268)) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e2c4 Mc modelc) K.
Proof.
  intros E1 E2 E3 BI RI AOK AZ XZ YZ SF SZS LEN BYTES CRF CRL.
  set (m := length (snd (L5PSA.split_sign s))) in *. set (vb := L5PSA.vblk m) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as ((X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4) & X21).
  pose proof (tpD_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR23 & C23 & C22 & C21 & C20)).
  set (W1 := fun a => F / 8 + SB + 20 <= a < F / 8 + SB + 24).
  apply (apiece L ar C HI LY HIok (ostr sk ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e2c4 R1 L5ASCS.STRCTOR M1v W1 K B1 B2 pMS MG1).
  { intros a Ha Hna. apply pFZ. exact Ha. clear - Hna; subst W1; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W1; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] (ostr sk) Mc modelc LKc crc Ac M3 model3 W1 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W1; cbn beta in Wa; lia. }
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  destruct (vis_facts [] (ostr sk) Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & _ & _ & SHV)). change (ff_bytes 3 / 8) with 64 in SHV.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (IDX : (F + 32) / 8 = F / 8 + 4 /\ (F + 96) / 8 = F / 8 + 12 /\ (F + 160) / 8 = F / 8 + 20 /\ (F + 224) / 8 = F / 8 + 28 /\ (F + 288) / 8 = F / 8 + 36) by (clear - F8a; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct IDX as (I32 & I96 & I160 & I224 & I288).
  assert (AG3 : forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + SB <= i < F / 8 + SB + 64) -> M3 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FRM3. exact Hi. intros X. apply Hn. clear - X; subst W1; cbn beta in X; lia. }
  assert (SHR : 0 <= F / 8 /\ F / 8 + SB + 64 <= 2 ^ 47). { clear - FRP F8a. unfold SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SHK : forall o k, o / 8 = F / 8 + k -> (0 <= k /\ k + 4 <= 20) \/ (24 <= k /\ k + 4 <= 64) -> shadow_zero Mc o 4 -> shadow_zero M3 o 4).
  { intros o k E Hk OZ. apply (shz_agree Mc M3 o OZ). intros j Hj. rewrite E. apply FRM3. clear - Hj Hk SHR; unfold SB in *; lia. subst W1; cbn beta. clear - Hj Hk; lia. }
  assert (AOK3 : L5OMA.a_ok M3 (F + 96) fba). { apply (a_ok_agree Mc M3 fba AOK). intros i Hi. apply AG3. clear - Hi FRP; lia. apply fsh_off. left; clear - Hi; lia. }
  pose proof (SHK (F + 96) 12 I96 ltac:(left; clear; lia) AZ) as AZ3.
  pose proof (SHK (F + 224) 28 I224 ltac:(right; clear; lia) XZ) as XZ3.
  pose proof (SHK (F + 288) 36 I288 ltac:(right; clear; lia) YZ) as YZ3.
  assert (SZS3 : shadow_zero M3 (F + 32) 3).
  { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 32) + j = F / 8 + SB + (4 + j)) by (unfold HeapIfaceA.S; rewrite I32; clear; lia). rewrite E.
    rewrite FRM3. rewrite <- E. apply SZS. exact Hj. clear - Hj SHR; unfold SB in *; lia. subst W1; cbn beta. clear - Hj; lia. }
  assert (INS : forall q n, sk = Some (q, n) -> In (q, n) (ostr sk ++ LB)). { intros q n E. subst sk. cbn [ostr app]. left; reflexivity. }
  pose proof (str_full_agree (ostr sk) Mc modelc LKc crc Ac M3 sk s B1 SF INS AG3) as SF3.
  assert (BZ3 : shadow_zero M3 (F + 160) 4).
  { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 160) + j = F / 8 + 2147450900 + j) by (unfold HeapIfaceA.S, SB; rewrite I160; clear; lia). rewrite E.
    assert (X : L5.u8_at RSEGS M1v (F / 8 + 2147450900 + j) 0).
    { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct J as [J|[J|[J|J]]]; subst j.
      replace (F / 8 + 2147450900 + 0) with (F / 8 + 2147450900) by (clear; lia). exact C20.
      replace (F / 8 + 2147450900 + 1) with (F / 8 + 2147450901) by (clear; lia). exact C21.
      replace (F / 8 + 2147450900 + 2) with (F / 8 + 2147450902) by (clear; lia). exact C22.
      replace (F / 8 + 2147450900 + 3) with (F / 8 + 2147450903) by (clear; lia). exact C23. }
    rewrite EQ3. apply (byte_of_u8 M1v _ 0 X). right. clear - Hj SHR; unfold SB in SHR; lia. clear - Hj SHR; unfold SB in SHR; lia.
    replace (F / 8 + 2147450900 + j) with (F / 8 + SB + (20 + j)) by (unfold SB; clear; lia). apply SHV. clear - Hj; lia. }
  assert (RI3 : rinv2 R1).
  { pose proof (rinv1_ks Rc R1 KS_tpD RI pKS ltac:(vm_compute; reflexivity)) as (Z1 & Z21). unfold rinv2. split. exact Z1. split. exact Z21. exact pR23. }
  destruct (callee_pre [] (ostr sk) M3 model3 LKc crc Ac SCRs BI3 (proj1 HS_SC) ltac:(clear - HS_SC; lia)) as (STK3 & R1k & R2k & R3k & RSk & A32).
  pose proof RI3 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & Y21 & Y23).
  destruct (frame_byte (ostr sk) M3 model3 LKc crc Ac (F + 160) BI3 ltac:(clear; lia)) as (fbo & OFB & FBO).
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  destruct HK2 as [HK2a HK2b]. destruct HK1 as [HK1a HK1b]. destruct HBM as [HBM1 HBM2].
  assert (VB0 : 0 <= vb). { subst vb. unfold L5PSA.vblk. destruct (m <? 39)%nat. clear; lia. unfold round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(clear; lia) ltac:(clear; lia)) as X. clear - X; lia. }
  assert (RB0 : 0 <= REST 268). { pose proof (HK1b 268 ltac:(clear; Lia.lia)). pose proof (HK2b 268 ltac:(clear; Lia.lia)). clear - H H0. lia. }
  destruct (L5OMA.acredit_for_take L crc (2 + (K1 + K2 + 3)) (2 * vb + REST 268) vb LY2 CRF ltac:(clear - HK1a HK2a; lia) ltac:(clear - VB0 RB0; lia)) as [CR1 CRFa].
  destruct (L5OMA.acredit_for_take L (adebit L crc vb) (2 + (K1 + K2 + 3) - 1) (2 * vb + REST 268 - vb) vb LY2 CRFa ltac:(clear - HK1a HK2a; lia) ltac:(clear - VB0 RB0; lia)) as [CR2 CRFb].
  replace (2 + (K1 + K2 + 3) - 1 - 1) with (K1 + K2 + 3) in CRFb by (clear; lia). replace (2 * vb + REST 268 - vb - vb) with (REST 268) in CRFb by (clear; lia).
  assert (STATE1 : sc_state R1 M3 model3 LKc crc Ac sk s fba).
  { unfold sc_state. fold m. fold vb. split. exact BI3. split. exact RI3. split. exact pR1. repeat (split; [assumption|]). exact CRF. }
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  apply (Hsc fx1 R1 M3 model3 K (ostr sk ++ LB) FF' LKc crc Ac (F + 160) (F + 32) SPA 582372 fbo s HH3 AM3 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - exact LEN.
  - exact BYTES.
  - split. exact CR1. exact CR2.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Y2.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - exact STK3.
  - refine (stksh_now (ostr sk) M3 model3 LKc crc Ac (SPA - SCRs) BI3 ltac:(clear - HS_SC CLS; lia) _).
    clear - V2A HSS8. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (proj1 (ffrk_1 FF' LKc 5)). apply (ffrk_le 1 FF' LKc d1 5 R1k). exact HD1.
  - apply (ffrk_le 2 FF' LKc d2 2 R2k). exact HD2.
  - exact RSk.
  - exact OFB.
  - exact FBO.
  - apply aobjF. clear; lia. clear; lia. exact F8c.
  - exact BZ3.
  - exists (F, 3, V2 - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 3) with 512. split. clear; lia. split. clear; lia.
    clear - F8a. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). exact SZS3.
  - right. clear; lia.
  - destruct sk as [[pd nb]|]; cbn [str_full] in SF3. 2:{ left. exact SF3. }
    right. destruct SF3 as (w0 & LL & ENB & LEN' & W0R & PDR). exists w0, pd. split. exact LL. split. rewrite <- ENB. cbn [ostr app]. left; reflexivity. split. exact LEN'. exact W0R.
  - (* [comment removed for export] *)
    intros fx2 R2 M2' model2' LB2 cr2' LK2' A2' POST RT2 IA2 AM2 LKI2' HH2'.
    destruct POST as (RP2 & (PL1 & PDG) & st' & BIG & LIMBS & STM & CRD & AHP).
    set (ds := snd (L5PSA.split_sign s)) in *. set (V := dec ds) in *. set (n := nwords V) in *.
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
    assert (S0 : 0 <= SCRs) by exact (proj1 HS_SC).
    assert (DSL : (length ds <= 4999)%nat). { subst ds. clear - LEN. destruct s as [|c t]; cbn. lia. destruct (Z.eqb c 45); cbn in *; lia. }
    assert (NW : (n <= 260)%nat) by (apply (nwords_cap ds PDG DSL)).
    assert (V0 : 0 <= V) by (apply (proj1 (dec_bound ds (digits_all ds PDG)))).
    set (bb := L5.BO (L5PSA.res_fb (Z.land fbo 252) n (fst (L5PSA.split_sign s))) n st') in *.
    assert (CASES : exists ob, obj_at M2' (F + 160) bb ob /\ LB2 = (ostr ob ++ ostr sk) ++ LB /\ 0 <= L5.bo_cap bb <= 268
                      /\ (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) /\ (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat)).
    { subst bb. unfold L5.bo_cap. cbn [L5.bo_st L5.bo_len]. destruct st' as [v0 v1|cap q].
      - destruct STM as (N2 & ELB). exists None. split. split. exact BIG. reflexivity. split. exact ELB. split. clear; lia.
        split. intros cap q E; discriminate E.
        intros D. exfalso. destruct BIG as (_ & _ & _ & (BT0 & _)). unfold L5.bo_dyn in D. cbn [L5.bo_fb] in *. rewrite BT0 in D. discriminate D.
      - destruct STM as (N3 & ECAP & ELB & FRESH). exists (Some (q, 8 * cap)). split. split. exact BIG. reflexivity. split. rewrite ELB. reflexivity.
        assert (CR : Z.of_nat n + 1 <= cap <= 268). { rewrite ECAP. unfold round_up. clear - NW. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        split. clear - CR; lia. split. intros cap' q' E. injection E as <- <-. exact (proj1 CR). intros _. exact N3. }
    destruct CASES as (ob & OB2 & ELB2 & CAPR & CAPL & DYN3). subst LB2.
    assert (BI2 : binv [] (ostr ob ++ ostr sk) M2' model2' LK2' cr2' A2').
    { apply (binv_callee [] [] (ostr sk) (ostr sk) (ostr ob ++ ostr sk) M3 model3 LKc crc Ac M2' model2' LK2' cr2' A2' SCRs [(F + 160, 32)] BI3 AHP HH2' AM2 RT2 IA2 LKI2').
      - exact S0.
      - clear - HS_SC CLS; lia.
      - intros rr a [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
      - intros a Hc _ rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (NCF a). left; clear - X; lia. exact Hc.
      - intros a X. exact X. }
    pose proof (L5OMA.acredit_for_mono L _ cr2' _ _ CRFb CRD) as CRFc.
    assert (RLE : REST (L5.bo_cap bb) <= REST 268).
    { pose proof (HBM1 (L5.bo_cap bb) 268 (proj2 CAPR)) as Q1. pose proof (HBM2 (L5.bo_cap bb) 268 (proj2 CAPR)) as Q2. clear - Q1 Q2 CAPR. lia. }
    apply (ph_copy_x fx2 R2 M2' model2' LK2' cr2' A2' sk ob bb (wlist V n) fba E2 E3 BI2 (rinv2_pres R1 R2 RI3 RP2)).
    + apply (shz_keepW _ _ _ _ _ _ XZ3 ltac:(clear; lia) ltac:(clear; lia) F8d S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + split. exact OB2. split. exact LIMBS.
      apply (shz_keepW _ _ _ _ _ _ BZ3 ltac:(clear; lia) ltac:(clear; lia) F8c S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply reduced_wlist. exact V0.
    + exact (proj2 CAPR).
    + exact CAPL.
    + exact DYN3.
    + apply (shz_keepW _ _ _ _ _ _ YZ3 ltac:(clear; lia) ltac:(clear; lia) F8e S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply (a_ok_keepW _ _ _ _ _ _ AOK3 S0 AHP). intros i Hi. apply (out1 _ i (F + 96)). clear; lia. exact Hi.
    + apply (shz_keepW _ _ _ _ _ _ AZ3 ltac:(clear; lia) ltac:(clear; lia) F8b S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply (str_full_at M2' sk s). apply (str_full_keepW (ostr sk) M3 model3 LKc crc Ac M2' SCRs (F + 160) sk s HH3 SF3 INS S0 ltac:(clear; lia) ltac:(clear; lia) AHP).
    + apply (L5OMA.acredit_for_le L cr2' (K1 + K2 + 3) (REST 268) _ _ LY2 CRFc). clear; lia. exact RLE.
    + eapply credit_le_trans. exact CRL.
      replace (2 * vb + REST 268) with ((vb + vb) + REST 268) by (clear; lia). replace (2 + (K1 + K2 + 3)) with ((1 + 1) + (K1 + K2 + 3)) by (clear; lia).
      rewrite <- (L5OMA.adebits_add L crc (1 + 1) (vb + vb) (K1 + K2 + 3) (REST 268)). rewrite <- (L5OMA.adebits_add L crc 1 vb 1 vb). rewrite !L5OMA.adebits_1.
      eapply credit_le_trans. apply (L5OMA.adebits_mono L _ cr2' _ _ CRD). apply (L5OMA.adebits_le L cr2' _ _ _ _ LY2). clear; lia. exact RLE.
  - (* [comment removed for export] *)
    intros fx2 R2 M2' model2' cr2' LK2' A2' TS RT2 IA2 AM2 LKI2' HH2'.
    exact (E1 fx2 R1 M3 model3 LKc crc Ac sk s fba fbo R2 M2' model2' cr2' LK2' A2' STATE1 TS RT2 IA2 AM2 LKI2' HH2').
Qed.

Lemma rinv1_pres Ra Rb : rinv1 Ra -> regs_preserved Ra Rb -> rinv1 Rb.
Proof.
  intros (XT & X21) RP. unfold rinv1. rewrite (cs_of_preserved Ra Rb 21 RP) by (apply L5K.in_b; vm_compute; reflexivity).
  split. 2: exact X21. apply (L5ATH.rinvT_pres R V2 cls F Ra Rb XT RP).
Qed.
Lemma land252_bit1 fbo : Z.testbit (Z.land fbo 252) 1 = false.
Proof. rewrite Z.land_spec. change (Z.testbit 252 1) with false. apply Bool.andb_false_r. Qed.

Hypothesis Hcs : L5PSB.cstr_specB L ar IL HI.
Hypothesis HS_CS : 208 + L5PSB.CSTR_SCRB <= SCRT.

(* [comment removed for export] *)
Lemma ph_cstr (fx : FPState) Rc Mc modelc LKc crc Ac sk s nsz :
  E1_obl -> E2_obl -> E3_obl ->
  binv [] (ostr sk) Mc modelc LKc crc Ac -> rinvT Rc -> getr Rc (reg 21) = Z_to_bv 64 nsz -> 0 <= nsz <= 4999 ->
  shadow_zero Mc (F + 224) 4 -> shadow_zero Mc (F + 288) 4 ->
  str_full Mc sk s -> shadow_zero Mc (F + 32) 3 -> (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
  L5OMA.acredit_for L crc (4 + (K1 + K2 + 3)) (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268)) ->
  credit_le crmin (L5OMA.adebits L crc (4 + (K1 + K2 + 3)) (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268))) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e290 Mc modelc) K.
Proof.
  intros E1 E2 E3 BI RI X21 NSZ XZ YZ SF SZS LEN BYTES CRF CRL.
  set (m := length (snd (L5PSA.split_sign s))) in *. set (vb := L5PSA.vblk m) in *.
  pose proof (pf_of_binv _ _ _ _ _ _ BI) as PF. pose proof BI as (B1 & B2 & _).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  open_pf PF. pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X27 & X3 & X4).
  assert (NSZ' : 0 <= nsz < 2 ^ 64) by (clear - NSZ; lia).
  pose proof (tpC_conc fx Rc MV (fun j => match j with 2%nat => V2 | 34%nat => nsz | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & MG1 & pFR & pFZ & (pMS & pKS & pR1 & pR10 & pR11 & pR12 & pR21 & C15 & C14 & C13 & C12)).
  set (W1 := fun a => F / 8 + SB + 12 <= a < F / 8 + SB + 16).
  apply (apiece L ar C HI LY HIok (ostr sk ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x8e290 R1 L5PSA.CSTR M1v W1 K B1 B2 pMS MG1).
  { intros a Ha Hna. apply pFZ. exact Ha. clear - Hna; subst W1; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. apply fsh_client. clear - Wa; subst W1; cbn beta in Wa; lia. }
  intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
  assert (BI3 : binv [] (ostr sk) M3 model3 LKc crc Ac).
  { apply (binv_piece [] (ostr sk) Mc modelc LKc crc Ac M3 model3 W1 BI HH3 AM3 RT3 MGM3 FRM3).
    intros a Wa. right; right. change (ff_bytes 3 / 8) with 64. clear - Wa; subst W1; cbn beta in Wa; lia. }
  pose proof F8s as (F8a & F8b & F8c & F8d & F8e).
  destruct (vis_facts [] (ostr sk) Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & _ & _ & SHV)). change (ff_bytes 3 / 8) with 64 in SHV.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (IDX : (F + 32) / 8 = F / 8 + 4 /\ (F + 96) / 8 = F / 8 + 12 /\ (F + 224) / 8 = F / 8 + 28 /\ (F + 288) / 8 = F / 8 + 36) by (clear - F8a; lia).
  assert (SHR : 0 <= F / 8 /\ F / 8 + SB + 64 <= 2 ^ 47). { clear - FRP F8a. unfold SB. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct IDX as (I32 & I96 & I224 & I288).
  assert (AG3 : forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + SB <= i < F / 8 + SB + 64) -> M3 (Z_to_bv 64 i) = Mc (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FRM3. exact Hi. intros X. apply Hn. clear - X; subst W1; cbn beta in X; lia. }
  assert (SHK : forall o k, o / 8 = F / 8 + k -> (0 <= k /\ k + 4 <= 12) \/ (16 <= k /\ k + 4 <= 64) -> shadow_zero Mc o 4 -> shadow_zero M3 o 4).
  { intros o k E Hk OZ. apply (shz_agree Mc M3 o OZ). intros j Hj. rewrite E. apply FRM3. clear - Hj Hk SHR; unfold SB in *; lia. subst W1; cbn beta. clear - Hj Hk; lia. }
  pose proof (SHK (F + 224) 28 I224 ltac:(right; clear; lia) XZ) as XZ3.
  pose proof (SHK (F + 288) 36 I288 ltac:(right; clear; lia) YZ) as YZ3.
  assert (SZS3 : shadow_zero M3 (F + 32) 3).
  { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 32) + j = F / 8 + SB + (4 + j)) by (unfold HeapIfaceA.S; rewrite I32; clear; lia). rewrite E.
    rewrite FRM3. rewrite <- E. apply SZS. exact Hj. clear - Hj SHR; unfold SB in *; lia. subst W1; cbn beta. clear - Hj; lia. }
  assert (INS : forall q n, sk = Some (q, n) -> In (q, n) (ostr sk ++ LB)). { intros q n E. subst sk. cbn [ostr app]. left; reflexivity. }
  pose proof (str_full_agree (ostr sk) Mc modelc LKc crc Ac M3 sk s B1 SF INS AG3) as SF3.
  assert (AZ3 : shadow_zero M3 (F + 96) 4).
  { intros j Hj. unfold byte_at. assert (E : HeapIfaceA.S (F + 96) + j = F / 8 + 2147450892 + j) by (unfold HeapIfaceA.S, SB; rewrite I96; clear; lia). rewrite E.
    assert (X : L5.u8_at RSEGS M1v (F / 8 + 2147450892 + j) 0).
    { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct J as [J|[J|[J|J]]]; subst j.
      replace (F / 8 + 2147450892 + 0) with (F / 8 + 2147450892) by (clear; lia). exact C12.
      replace (F / 8 + 2147450892 + 1) with (F / 8 + 2147450893) by (clear; lia). exact C13.
      replace (F / 8 + 2147450892 + 2) with (F / 8 + 2147450894) by (clear; lia). exact C14.
      replace (F / 8 + 2147450892 + 3) with (F / 8 + 2147450895) by (clear; lia). exact C15. }
    rewrite EQ3. apply (byte_of_u8 M1v _ 0 X). right. clear - Hj SHR; unfold SB in SHR; lia. clear - Hj SHR; unfold SB in SHR; lia.
    replace (F / 8 + 2147450892 + j) with (F / 8 + SB + (12 + j)) by (unfold SB; clear; lia). apply SHV. clear - Hj; lia. }
  assert (RI3 : rinv1 R1). { unfold rinv1. split. apply (L5ATH.rinvT_ks R V2 cls F Rc R1 KS_tpC RI pKS). vm_compute; reflexivity. exact pR21. }
  destruct (callee_pre [] (ostr sk) M3 model3 LKc crc Ac L5PSB.CSTR_SCRB BI3 ltac:(vm_compute; discriminate) ltac:(clear - HS_CS; lia)) as (STK3 & R1k & R2k & R3k & RSk & A32).
  pose proof RI3 as ((Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y27 & Y3 & Y4) & Y21).
  destruct (frame_byte (ostr sk) M3 model3 LKc crc Ac (F + 96) BI3 ltac:(clear; lia)) as (fbo & OFB & FBO).
  assert (LY2 : as0_layout2 L) by (exact (as0_layout2_of L C LY)).
  destruct HK2 as [HK2a HK2b]. destruct HK1 as [HK1a HK1b].
  assert (VB0 : 0 <= vb). { subst vb. unfold L5PSA.vblk. destruct (m <? 39)%nat. clear; lia. unfold round_up. pose proof (Z.div_pos (Z.of_nat (num_words_est m)) 8 ltac:(clear; lia) ltac:(clear; lia)) as X. clear - X; lia. }
  assert (RB0 : 0 <= REST 268). { pose proof (HK1b 268 ltac:(clear; Lia.lia)). pose proof (HK2b 268 ltac:(clear; Lia.lia)). clear - H H0. lia. }
  destruct (L5OMA.acredit_for_take L crc (4 + (K1 + K2 + 3)) (2 * 64 + (2 * vb + REST 268)) 64 LY2 CRF ltac:(clear - HK1a HK2a; lia) ltac:(clear - VB0 RB0; lia)) as [CR1 CRFa].
  destruct (L5OMA.acredit_for_take L (adebit L crc 64) (4 + (K1 + K2 + 3) - 1) (2 * 64 + (2 * vb + REST 268) - 64) 64 LY2 CRFa ltac:(clear - HK1a HK2a; lia) ltac:(clear - VB0 RB0; lia)) as [CR2 CRFb].
  replace (4 + (K1 + K2 + 3) - 1 - 1) with (2 + (K1 + K2 + 3)) in CRFb by (clear; lia). replace (2 * 64 + (2 * vb + REST 268) - 64 - 64) with (2 * vb + REST 268) in CRFb by (clear; lia).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SFB').
  apply (Hcs fx1 R1 M3 model3 K (ostr sk ++ LB) FF' LKc crc Ac (F + 96) SPA 582340 fbo HH3 AM3 HK).
  - rewrite r10. exact pR10.
  - rewrite r11. exact pR11.
  - split. exact CR1. exact CR2.
  - rewrite r1. exact pR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact Y2.
  - exact A32.
  - rewrite r4, Y4. exact G4.
  - exact STK3.
  - refine (stksh_now (ostr sk) M3 model3 LKc crc Ac (SPA - L5PSB.CSTR_SCRB) BI3 ltac:(clear - HS_CS CLS; lia) _).
    clear - V2A. unfold aligned in V2A. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). change L5PSB.CSTR_SCRB with 4912. lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (proj1 (ffrk_1 FF' LKc 5)). apply (ffrk_le 1 FF' LKc d1 5 R1k). exact HD1.
  - apply (ffrk_le 2 FF' LKc d2 2 R2k). exact HD2.
  - exact RSk.
  - apply (img_clear_now (ostr sk) M3 model3 LKc crc Ac BI3).
  - exact OFB.
  - exact FBO.
  - apply aobjF. clear; lia. clear; lia. exact F8b.
  - exact AZ3.
  - intros fx2 R2 M2' model2' cr2' LK2' A2' POST RT2 IA2 AM2 LKI2' HH2'.
    destruct POST as (RP2 & BIG & CRD & AHP).
    assert (S0 : 0 <= L5PSB.CSTR_SCRB) by (vm_compute; discriminate).
    assert (BI2 : binv [] (ostr sk) M2' model2' LK2' cr2' A2').
    { apply (binv_callee [] [] (ostr sk) (ostr sk) (ostr sk) M3 model3 LKc crc Ac M2' model2' LK2' cr2' A2' L5PSB.CSTR_SCRB [(F + 96, 32)] BI3 AHP HH2' AM2 RT2 IA2 LKI2').
      - exact S0.
      - clear - HS_CS CLS; lia.
      - intros rr a [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. split. unfold tocell. clear - X SFB' CLS; lia. apply fsh_off. left. clear - X; lia.
      - intros a Hc _ rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (NCF a). left; clear - X; lia. exact Hc.
      - intros a X. exact X. }
    pose proof (L5OMA.acredit_for_mono L _ cr2' _ _ CRFb CRD) as CRFc.
    apply (ph_strctor fx2 R2 M2' model2' LK2' cr2' A2' sk s (Z.land fbo 252) E1 E2 E3 BI2 (rinv1_pres R1 R2 RI3 RP2)).
    + split. exact BIG. apply land252_bit1.
    + apply (shz_keepW _ _ _ _ _ _ AZ3 ltac:(clear; lia) ltac:(clear; lia) F8b S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply (shz_keepW _ _ _ _ _ _ XZ3 ltac:(clear; lia) ltac:(clear; lia) F8d S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply (shz_keepW _ _ _ _ _ _ YZ3 ltac:(clear; lia) ltac:(clear; lia) F8e S0 AHP). intros j Hj. apply out1_sh. clear; lia. clear; lia. clear; lia. clear; lia. exact Hj.
    + apply (str_full_keepW (ostr sk) M3 model3 LKc crc Ac M2' L5PSB.CSTR_SCRB (F + 96) sk s HH3 SF3 INS S0 ltac:(clear; lia) ltac:(clear; lia) AHP).
    + intros j Hj. unfold byte_at. rewrite (proj1 AHP). apply SZS3. exact Hj.
      assert (E : HeapIfaceA.S (F + 32) + j = F / 8 + SB + (4 + j)) by (unfold HeapIfaceA.S; rewrite I32; clear; lia). rewrite E.
      split. clear - Hj SHR; unfold SB in *; lia.
      split. { apply (fframe_shadow_client L ar (ostr sk ++ LB) FF' SPA L5PSB.CSTR_SCRB F 3 (V2 - 192 + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, HeapIfaceA.S.
               rewrite (proj1 (proj2 F8)). clear - Hj. lia. }
      intros rr [<-|[]] X. unfold L5.in_rng in X; cbn [fst snd] in X. apply (fsh_off (F / 8 + SB + (4 + j))). left. clear - X; lia. clear - Hj; lia.
    + exact LEN.
    + exact BYTES.
    + exact CRFc.
    + eapply credit_le_trans. exact CRL.
      replace (2 * 64 + (2 * vb + REST 268)) with ((64 + 64) + (2 * vb + REST 268)) by (clear; lia). replace (4 + (K1 + K2 + 3)) with ((1 + 1) + (2 + (K1 + K2 + 3))) by (clear; lia).
      rewrite <- (L5OMA.adebits_add L crc (1 + 1) (64 + 64) (2 + (K1 + K2 + 3)) (2 * vb + REST 268)). rewrite <- (L5OMA.adebits_add L crc 1 64 1 64). rewrite !L5OMA.adebits_1.
      apply (L5OMA.adebits_mono L _ cr2' _ _ CRD).
Qed.

(* [comment removed for export] *)
Definition pads_ok : Prop := E1_obl /\ E2_obl /\ E3_obl.
Lemma ph_cstr_p (fx : FPState) Rc Mc modelc LKc crc Ac sk s nsz :
  pads_ok ->
  binv [] (ostr sk) Mc modelc LKc crc Ac -> rinvT Rc -> getr Rc (reg 21) = Z_to_bv 64 nsz -> 0 <= nsz <= 4999 ->
  shadow_zero Mc (F + 224) 4 -> shadow_zero Mc (F + 288) 4 ->
  str_full Mc sk s -> shadow_zero Mc (F + 32) 3 -> (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
  L5OMA.acredit_for L crc (4 + (K1 + K2 + 3)) (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268)) ->
  credit_le crmin (L5OMA.adebits L crc (4 + (K1 + K2 + 3)) (2 * 64 + (2 * L5PSA.vblk (length (snd (L5PSA.split_sign s))) + REST 268))) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x8e290 Mc modelc) K.
Proof. intros (E1 & E2 & E3). apply ph_cstr; assumption. Qed.
End PARSE.
End OPMOD1.
End OPMODS.
End DT.
End TOP.
End WithIface.
End SCFG_1.
End L5ATD.
