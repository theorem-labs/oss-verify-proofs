(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK L5DivKitA L5ADivH L5ADivT L5ADivPD.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVD.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADIVPD.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Lemma DEL_EQ : OPDEL_SCR = 4096. Proof. reflexivity. Qed.

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

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 352).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : aligned E 32.
Hypothesis HK : K [].
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 352 + 4096 <= SCRD.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation Gx := (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G).

(* [comment removed for export] *)
Definition pf (MV : word -> option byte) : Prop :=
  L5.writable RSEGS MV (E - 352) 352 /\ L5.img_clear MV 860160 880640 /\ L5.u64_at RSEGS MV 908088 2147450880 /\ L5.u32_at RSEGS MV 908096 1 /\
  L5.defined MV F 512 /\ L5.writable RSEGS MV F 512 /\ L5.writable RSEGS MV (F / 8 + SB) 64 /\ L5.u64_at RSEGS MV (F + 504) fl /\ L5.writable RSEGS MV fl 1.
Lemma NUM : (0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= E < 2 ^ 64) /\ 4096 <= F <= 140737488354816 /\ 4096 <= fl <= 140737488355327 /\ aligned F 32
  /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 512 <= fl \/ fl + 1 <= F) /\ (E - 352 + 352 <= F \/ F + 512 <= E - 352) /\ (E - 352 + 352 <= fl \/ fl + 1 <= E - 352)
  /\ (F + 512 <= E - 352 /\ fl + 1 <= E - 352).
Proof.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
  change (ff_bytes 3) with 512 in *.
  split. clear - FR FLR ER; lia. split. clear - FR; lia. split. clear - FLR; lia. split. exact F32. split. exact FBIG. split. exact FLBIG. split. exact FLA.
  assert (SFB : F + 512 <= E - 352 /\ fl + 1 <= E - 352) by (clear - FCEIL FLR SPC SLO; lia).
  split. clear - SFB; lia. split. clear - SFB; lia. exact SFB.
Qed.
Lemma pf_of_binv W BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> pf (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros BI.
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F + 512 - 8) with (F + 504) in FLCv by (clear; lia).
  unfold pf. split. { eapply L5.writable_sub. exact WSv. clear; lia. clear; lia. }
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
  (forall Rc, rout Rc -> rinvD R E Rc) -> (forall Ra Rb, rout Ra -> regs_preserved Ra Rb -> rout Rb) -> L5.ra_ok pcn ->
  ((F <= ox /\ ox + 32 <= F + 512) \/ (SPA <= ox /\ ox + 32 <= E)) ->
  forall (fx : FPState) Rc Mc modelc W BX BXn LKc crc Ac b blk,
  binv W BX Mc modelc LKc crc Ac -> rin Rc -> obj_at Mc ox b blk ->
  match blk with None => BXn = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BXn ++ LB end ->
  (forall (fx' : FPState) R' M' model' A',
      binv W BXn M' model' LKc crc A' -> rout R' -> incl Ac A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXn ++ LB) FF' SPA OPDEL_SCR a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' pcn M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros INL DYN ROT RPR RAn OXR fx Rc Mc modelc W BX BXn LKc crc Ac b blk BI RI [OB OBLK] BLK KF.
  pose proof (pf_of_binv W BX Mc modelc LKc crc Ac BI) as PF.
  destruct (Gx W BX Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & FV & SV & _)).
  change (ff_bytes 3) with 512 in FV.
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (OXN : 4096 <= ox /\ ox + 32 <= 2 ^ 47) by (clear - OXR FRP ER; lia).
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
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    apply (KF fx1 R1 Mc model1 Ac BI1 RO1 (incl_refl _)). intros a _ _. reflexivity.
  - (* [comment removed for export] *)
    subst blk. destruct BLK as [INP ELB]. destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    destruct (DYN fx Rc MV fb q cap RI PF (CELL1 _ O0) FBR BT1 (CELLV (ox + 24) q ltac:(clear; lia) ltac:(clear; lia) O24) ltac:(clear - Q4096 Q47 CAPR; lia)
                  (CELLV (ox + 16) cap ltac:(clear; lia) ltac:(clear; lia) O16) CAPR) as (fx1 & R1 & MS1 & RO1 & dR1 & dR10 & dR11).
    apply (apure (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 OPDEL_SIZED K B1 B2 MS1).
    intros model1 HH1 AM1 RT1 AH1.
    pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
    pose proof (ROT R1 RO1) as (Z2 & _ & _ & _ & Z4).
    assert (SPA16 : (E - 352) mod 16 = 0). { clear - EA. unfold aligned in EA. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (Hdel fx1 R1 Mc model1 K (BX ++ LB) FF' LKc crc Ac q (8 * cap) SPA pcn HH1 AM1 HK INP).
    + rewrite r10. exact dR10.
    + rewrite r1. exact dR1.
    + exact RAn.
    + rewrite r2. exact Z2.
    + rewrite r4, Z4. rewrite <- G4. reflexivity.
    + replace SPA with (E - 352) by (clear; lia). apply (astk_sub ar Mc Mc E SCRD 352 OPDEL_SCR B6 (mem_grows_refl Mc)).
      clear; lia. rewrite DEL_EQ; clear; lia. rewrite DEL_EQ; clear - HSCR; lia. exact SPA16.
    + intros fx3 R3 M3 model3 A3 RP3 AH3 RT3 IA3 AM3 HH3. rewrite ELB in AH3, HH3.
      assert (BI3 : binv W BXn M3 model3 LKc crc A3).
      { apply (L5AFK.binv_callee L ar C HI HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G
                 W W BX BXn BXn Mc model1 LKc crc Ac M3 model3 LKc crc A3 OPDEL_SCR [] BI1 AH3 HH3 AM3 RT3 IA3 (incl_refl _)).
        - rewrite DEL_EQ; clear; lia.
        - rewrite DEL_EQ; clear - HSCR; lia.
        - intros rr a [].
        - intros a _ _ rr [].
        - intros a X. exact X. }
      apply (KF fx3 R3 M3 model3 A3 BI3 (RPR R1 R3 RO1 RP3) IA3).
      intros a Ha Hc. apply (proj1 AH3). split. exact Ha. split. exact Hc. intros rr [].
Qed.

(* [comment removed for export] *)
Definition rinvTL (Rc : bvmap 5 word) : Prop :=
  rinvD R E Rc /\ getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 20) = Z_to_bv 64 (F + 32) /\ getr Rc (reg 21) = Z_to_bv 64 (F + 96)
  /\ getr Rc (reg 24) = Z_to_bv 64 F /\ getr Rc (reg 27) = Z_to_bv 64 F.
Definition rinvT3 (Rc : bvmap 5 word) : Prop := rinvTL Rc /\ getr Rc (reg 19) = Z_to_bv 64 18446744073709551608.
Definition TLIDX : list nat := [2; 3; 4; 8; 9; 18; 20; 21; 24; 27]%nat.
Lemma rinvTL_keep Ra Rb : rinvTL Ra -> (forall k, In k TLIDX -> getr Rb (reg k) = getr Ra (reg k)) -> rinvTL Rb.
Proof.
  intros (RD & X18 & X20 & X21 & X24 & X27) Kp. unfold rinvTL. split. { apply (rinvD_keep R E Ra Rb RD). intros k Hk. apply Kp. unfold DIDX in Hk. unfold TLIDX. cbn [In] in Hk |- *. clear - Hk. tauto. }
  rewrite (Kp 18%nat), (Kp 20%nat), (Kp 21%nat), (Kp 24%nat), (Kp 27%nat) by (unfold TLIDX; cbn [In]; tauto). repeat split; assumption.
Qed.
Lemma rinvTL_ks Ra Rb (KS : list nat) : rinvTL Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) TLIDX = true -> rinvTL Rb.
Proof. intros RI Kp HB. apply (rinvTL_keep Ra Rb RI). intros k Hk. apply Kp. exact (L5K.incl_b TLIDX KS HB k Hk). Qed.
Lemma rinvTL_pres Ra Rb : rinvTL Ra -> regs_preserved Ra Rb -> rinvTL Rb.
Proof. intros RI RP. apply (rinvTL_keep Ra Rb RI). intros k Hk. apply (cs_of_preserved Ra Rb k RP). revert Hk. apply (L5K.incl_b TLIDX); vm_compute; reflexivity. Qed.
Lemma rinvT3_ks Ra Rb (KS : list nat) : rinvT3 Ra -> (forall x, In x KS -> getr Rb (reg x) = getr Ra (reg x)) ->
  forallb (fun i => existsb (Nat.eqb i) KS) (19%nat :: TLIDX) = true -> rinvT3 Rb.
Proof.
  intros [RI X19] Kp HB. split. { apply (rinvTL_keep Ra Rb RI). intros k Hk. apply Kp. apply (L5K.incl_b (19%nat :: TLIDX) KS HB k). right; exact Hk. }
  rewrite (Kp 19%nat). exact X19. apply (L5K.incl_b (19%nat :: TLIDX) KS HB 19%nat). left; reflexivity.
Qed.
Lemma rinvT3_pres Ra Rb : rinvT3 Ra -> regs_preserved Ra Rb -> rinvT3 Rb.
Proof. intros [RI X19] RP. split. exact (rinvTL_pres Ra Rb RI RP). rewrite (cs_of_preserved Ra Rb 19 RP) by inl. exact X19. Qed.

(* [comment removed for export] *)
Local Ltac open_pf PF := destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv);
  pose proof NUM as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
Local Ltac run_inl PIECE OPEN CLOSE :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in
  intros fx Rc MV fb RI PF O0 FBR BT0; open_pf PF; OPEN RI;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & _));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | CLOSE Rc R1 RI pKS].
Local Ltac run_dyn PIECE OPEN CLOSE :=
  let fx := fresh "fx" in let Rc := fresh "Rc" in let MV := fresh "MV" in let fb := fresh "fb" in let q := fresh "q" in let cap := fresh "cap" in
  intros fx Rc MV fb q cap RI PF O0 FBR BT1 O24 QR O16 CAPR; open_pf PF; OPEN RI;
  assert (FBR' : 0 <= fb <= 255 /\ 0 <= fb < 2 ^ 64) by (clear - FBR; lia); destruct FBR' as [FBR' FBR''];
  assert (QR' : 4096 <= q <= 140737488355328 /\ 0 <= q < 2 ^ 64) by (clear - QR; lia); destruct QR' as [QR' QR''];
  assert (CR' : 1 <= cap <= 134217728 /\ 0 <= cap < 2 ^ 64) by (clear - CAPR; lia); destruct CR' as [CR' CR''];
  pose proof (PIECE fx Rc MV (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | 60%nat => fb | 61%nat => q | 62%nat => cap | _ => 0 end)) as P; cbn beta iota in P;
  feed P ltac:(first [apply UR | apply U_to | sc ]);
  destruct P as (fx1 & R1 & M1v & _ & pFR & _ & (pMS & pKS & pR1 & pR10 & pR11));
  assert (E1 : M1v = MV) by (apply mem_eq_of_agree; intros a Ha; apply pFR); subst M1v;
  exists fx1, R1; split; [exact pMS | split; [CLOSE Rc R1 RI pKS | split; [exact pR1 | split; [exact pR10 | exact pR11]]]].
Local Ltac openTL RI := pose proof RI as ((X2 & X8 & X9 & X3 & X4) & X18 & X20 & X21 & X24 & X27).
Local Ltac openT3 RI := pose proof RI as (((X2 & X8 & X9 & X3 & X4) & X18 & X20 & X21 & X24 & X27) & X19).

Lemma run_T1i : inl_run rinvTL rinvTL 0x92c3c 0x92c5c (F + 96).
Proof. run_inl v5T1i_conc openTL ltac:(fun Rc R1 RI pKS => apply (rinvTL_ks Rc R1 KS_v5T1i RI pKS); vm_compute; reflexivity). Qed.
Lemma run_T1d : dyn_run rinvTL rinvTL 0x92c3c 0x92c5c (F + 96).
Proof. unfold dyn_run. replace (F + 96 + 24) with (F + 120) by (clear; lia). replace (F + 96 + 16) with (F + 112) by (clear; lia).
  run_dyn v5T1d_conc openTL ltac:(fun Rc R1 RI pKS => apply (rinvTL_ks Rc R1 KS_v5T1d RI pKS); vm_compute; reflexivity). Qed.
Lemma run_T2i : inl_run rinvT3 rinvT3 0x92c70 0x92c90 (F + 32).
Proof. run_inl v5T2i_conc openT3 ltac:(fun Rc R1 RI pKS => apply (rinvT3_ks Rc R1 KS_v5T2i RI pKS); vm_compute; reflexivity). Qed.
Lemma run_T2d : dyn_run rinvT3 rinvT3 0x92c70 0x92c90 (F + 32).
Proof. unfold dyn_run. replace (F + 32 + 24) with (F + 56) by (clear; lia). replace (F + 32 + 16) with (F + 48) by (clear; lia).
  run_dyn v5T2d_conc openT3 ltac:(fun Rc R1 RI pKS => apply (rinvT3_ks Rc R1 KS_v5T2d RI pKS); vm_compute; reflexivity). Qed.

(* [comment removed for export] *)
Lemma div_dtors (fx : FPState) Rc Mc modelc W BX BX1 BXf LKc crc Ac bn on bd od :
  binv W BX Mc modelc LKc crc Ac -> rinvTL Rc -> obj_at Mc (F + 96) bn on -> obj_at Mc (F + 32) bd od ->
  match on with None => BX1 = BX | Some (q, n) => In (q, n) (BX ++ LB) /\ lb_remove q (BX ++ LB) = BX1 ++ LB end ->
  match od with None => BXf = BX1 | Some (q, n) => In (q, n) (BX1 ++ LB) /\ lb_remove q (BX1 ++ LB) = BXf ++ LB end ->
  (forall a, aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> aclient L ar (BX1 ++ LB) FF' SPA OPDEL_SCR a) ->
  (forall (fxf : FPState) Rf Mf modelf Af,
      regs_preserved R Rf -> incl Ac Af ->
      ahpres L ar LB FF E SCRD W M Mf ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (BXf ++ LB) FF' SPA OPDEL_SCR a -> ~ L5AFK.Wret F fl 3 a -> ~ (F / 8 + SB + 12 <= a < F / 8 + SB + 16) -> Mf (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      model_rt model modelf -> amodel_ok Af modelf ->
      ri_inv HI (BXf ++ LB) FF LKc crc Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x92c3c Mc modelc) K.
Proof.
  intros BI RI ON OD BK1 BK2 BKC KF.
  (* [comment removed for export] *)
  apply (dtor_stage rinvTL rinvTL 0x92c3c 0x92c5c (F + 96) run_T1i run_T1d (fun Rx X => proj1 X) rinvTL_pres ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia)
           fx Rc Mc modelc W BX BX1 LKc crc Ac bn on BI RI ON BK1).
  intros fx1 R1 M1 model1 A1 BI1 RI1 IA1 AG1.
  (* [comment removed for export] *)
  pose proof (pf_of_binv W _ M1 model1 LKc crc A1 BI1) as PF. open_pf PF. openTL RI1.
  set (MV1 := mrestrict (ahid A1 model1) M1) in *.
  pose proof (v5Tp_conc fx1 R1 MV1 (fun j => match j with 2%nat => E | 40%nat => F | 41%nat => fl | 58%nat => U R1 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx2 & R2 & M2v & MG2 & pFR & pFZ & (pMS & pKS & pR19 & _)).
  set (Wp := fun a => F / 8 + SB + 12 <= a < F / 8 + SB + 16).
  apply (L5DKA.bstage L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G W _ M1 model1 LKc crc A1 fx1 fx2 R1 0x92c5c R2 0x92c70 M2v Wp K BI1 pMS MG2).
  { intros a Ha Hn. apply pFZ. exact Ha. subst Wp; cbn beta in Hn. clear - Hn. unfold SB in Hn. lia. }
  { intros a Ha Wa. apply (L5DKA.wp_shadow L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G). subst Wp; cbn beta in Wa. change (ff_bytes 3 / 8) with 64. clear - Wa; lia. }
  intros M2' model2' BI2 AH2 VIS2 MGM2 FRM2.
  assert (RI2 : rinvT3 R2). { split. apply (rinvTL_ks R1 R2 KS_v5Tp RI1 pKS). vm_compute; reflexivity. exact pR19. }
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHX : F + 64 <= F / 8 + SB + 12 \/ F / 8 + SB + 16 <= F + 32). { clear - FBIG FRP. unfold SB. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (OD2 : obj_at M2' (F + 32) bd od).
  { apply (obj_at_agree Mc M2' (F + 32) bd od OD ltac:(clear - FRP; lia) ltac:(clear - FRP; lia)). intros i Hi. rewrite FRM2. apply AG1. clear - Hi FRP; lia.
    apply (fframe_client L ar _ FF' SPA OPDEL_SCR F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia. clear - Hi FRP; lia.
    subst Wp; cbn beta. clear - Hi SHX. lia. }
  apply (dtor_stage rinvT3 rinvT3 0x92c70 0x92c90 (F + 32) run_T2i run_T2d (fun Rx X => proj1 (proj1 X)) rinvT3_pres ltac:(split; [clear; lia | reflexivity]) ltac:(left; clear; lia)
           fx2 R2 M2' model2' W BX1 BXf LKc crc A1 bd od BI2 RI2 OD2 BK2).
  intros fx3 R3 M3 model3 A3 BI3 RI3 IA3 AG3.
  (* [comment removed for export] *)
  pose proof RI3 as ((RD3 & Y18 & Y20 & Y21 & Y24 & Y27) & Y19).
  apply (div_tail L ar C HI LY HIok R M model K LB FF LK A E SCRD F fl ro r LK2 M2 model2 cr2 G ER EA RA UR1 G2 fx3 R3 M3 model3 W BXf LKc crc A3 BI3 RD3 Y18 Y19 Y24 Y27).
  intros fxf Rf Mf modelf RPf FRMf AHf RTf AMf HHf.
  apply (KF fxf Rf Mf modelf A3 RPf). { intros x Hx. apply IA3. apply IA1. exact Hx. } exact AHf.
  { intros a Ha Hc Hw Hp. rewrite (FRMf a Ha Hw). rewrite (AG3 a Ha Hc). rewrite FRM2. apply AG1. exact Ha.
    apply BKC. exact Hc. exact Ha. exact Hp. }
  exact RTf. exact AMf. exact HHf.
Qed.

End DIV.
End WithIface.
End SCFG_1.
End L5ADVD.
