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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BCmp L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivLeafSpecsAB0 L5DivInnerSpecsAB0 L5BCopyAS L5BDivH L5BDivT L5BDivD L5BDivE L5BDivEA L5BDivHC L5BDivHA L5BDivHO L5BDivPG1 L5BDivPG2 L5BDivGL L5BDivGA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Bo0_code_92368_93368.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGB.
Import L5A. Import L5CA. Import L5CSA. Import L5W. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHA. Import L5ADVHO. Import L5ADIVPG1. Import L5ADIVPG2. Import L5ADVGA.
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
Lemma g6 (fx : FPState) Rc Mc modelc W W1 BX LKc crc Ac (br bn : L5.bigobj) wn :
  binv W BX Mc modelc LKc crc Ac -> rinvD R E Rc ->
  getr Rc (reg 25) = Z_to_bv 64 (F + 96) -> L5.u64_at RSEGS Mc (E - 288) ro ->
  L5.big_at RSEGS Mc ro br -> aobj FF ro 32 -> shadow_zero Mc ro 4 ->
  L5.big_at RSEGS Mc (F + 96) bn -> L5C.obj_limbs RSEGS Mc bn wn -> shadow_zero Mc (F + 96) 4 ->
  Z.of_nat (L5.bo_len bn) <= 2 ^ 23 ->
  (L5.bo_dyn br = true -> Z.of_nat (L5.bo_len bn) <= L5.bo_cap br) ->
  ((3 <= L5.bo_len bn)%nat -> L5.bo_dyn br = false -> acredit_ok L crc (8 * round_up (Z.of_nat (L5.bo_len bn)))) ->
  (forall cap q, L5.bo_st br = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) (BX ++ LB)) ->
  (forall c q c' q', L5.bo_st br = L5.BDyn c q -> L5.bo_st bn = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall a, L5.outside W1 a -> L5.outside W a /\ L5.outside [(ro, 32); (L5.bo_data ro br, 8 * Z.of_nat (L5.bo_len bn))] a) ->
  (forall (fx' : FPState) R1 R' M' model' (g : growth) LBn cr' LK' A',
      (forall x, In x KS_v5G6 -> getr R1 (reg x) = getr Rc (reg x)) -> getr R1 (reg 22) = Z_to_bv 64 ro ->
      assign_post L ar (BX ++ LB) FF' LK' crc Mc M' R1 R' ro (F + 96) SPA br bn wn g LBn cr' ->
      binv W1 (match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) M' model' LK' cr' A' ->
      incl Ac A' -> incl LK' LKc ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' 0x931d4 M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc 0x931c4 Mc modelc) K.
Proof.
  intros BI RI X25 S96 OBR AOR SZR OBN OLN SZN LEN CAPOK CROK INR INN NOAL WSUB KF.
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G W BX Mc modelc LKc crc Ac ro BI AOR SZR)
    as ((ORP & ORG & O8) & _).
  pose proof (frm_vis L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER W BX Mc modelc LKc crc Ac _ _ BI S96 ltac:(clear; lia) ltac:(clear; lia)) as S96v.
  open_ctx BI. pose proof BI as (B1 & B2 & _). pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  set (MV := mrestrict (ahid Ac modelc) Mc) in *.
  assert (ER' : 140735332487616 <= E <= 140737488355328) by (clear - ER; lia).
  assert (FR' : 4096 <= F <= 140737488354816) by (clear - FRP; lia).
  assert (ROR : 0 <= ro <= 18446744073709551615) by (clear - ORP ORG; lia).
  pose proof (v5G6_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx1 & R1 & M1v & _ & _ & pEQ & (pMS & pKS & pR1 & pR10 & pR11 & pR22)).
  assert (EQM : M1v = MV) by (apply mem_eq_of_agree; exact pEQ). rewrite EQM in pMS.
  apply (apure L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc 0x931c4 R1 ASSIGN K B1 B2 pMS).
  intros model1 HH1 AM1 RT1 AH1.
  pose proof (L5AFK.binv_model L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3 W BX Mc modelc LKc crc Ac model1 BI HH1 AM1 RT1) as BI1.
  eapply (L5ADVEA.assign_stage) with (W := W) (W1 := W1) (BX := BX) (o := ro) (k := 96) (pcn := 0x931d4) (b := br) (b' := bn) (ws' := wn);
    try first [exact LY | exact HIok | exact G | exact ER | exact EA | exact HK | exact RA | exact UR1 | exact G2 | exact G4 | exact HSCR0 | exact FFR1 | exact FFRS | exact Hdel | exact Hasg | exact BI1].
  - apply (rinvD_ks R E Rc R1 KS_v5G6 RI pKS). vm_compute; reflexivity.
  - exact pR10.
  - exact pR11.
  - exact pR1.
  - split. clear; lia. reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - exact OBR.
  - exact AOR.
  - exact SZR.
  - exact OBN.
  - exact OLN.
  - exact SZN.
  - exact LEN.
  - exact CAPOK.
  - exact CROK.
  - exact INR.
  - exact INN.
  - exact NOAL.
  - exact WSUB.
  - intros fx3 R3 M3 model3 g LBn cr3 LK3 A3 POST BI3 IA3 ILK3. apply (KF fx3 R1 R3 M3 model3 g LBn cr3 LK3 A3 pKS pR22 POST BI3 IA3 ILK3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DREGF (MV : word -> option byte) (D m : Z) : Prop :=
  (4096 <= D /\ D mod 8 = 0 /\ D + 8 * m <= ahl_ceil ar /\ D + 8 * m <= 140737479966720) /\ L5ADVGL.nsh D (8 * m) /\ L5ADVGL.oim D (8 * m)
  /\ L5KA.zeros_at MV (D / 8 + 2147450880) m /\ L5.defined MV D (8 * m) /\ L5.writable RSEGS MV D (8 * m).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma d8 x : x mod 8 = 0 -> x / 8 * 8 = x. Proof. intros H. lia. Qed.
Lemma d8j x j : x mod 8 = 0 -> (x + 8 * j) / 8 = x / 8 + j /\ (x + 8 * j) mod 8 = 0. Proof. intros H. split; lia. Qed.
Lemma d16 x : x mod 8 = 0 -> (x + 16) / 8 = x / 8 + 2 /\ (x + 16) mod 8 = 0 /\ (x + 24) / 8 = x / 8 + 3 /\ (x + 24) mod 8 = 0 /\ (x + 8) / 8 = x / 8 + 1 /\ (x + 8) mod 8 = 0. Proof. intros H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bltu_Z (x y : Z) : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros Hx Hy. unfold branch_taken, bv_ltu. rewrite !BG.unsigned_lit by lia. reflexivity. Qed.
Lemma br_92f30 fx Rx Mx : msteps RSEGS (st fx Rx 0x93284 Mx) (st fx Rx (if branch_taken BC_LTU (getr Rx (reg 24)) (getr Rx (reg 10)) then 0x93350 else 0x93288) Mx).
Proof.
  assert (r24 : (24%bv : bv 5) = Z_to_bv 5 (Z.of_nat 24)) by (apply bv_eq; reflexivity).
  rewrite <- r24, <- r10.
  apply (L5ACMP.br_site fx Rx Mx 0x93284 0x93350 (0x93284%bv : word) _ BC_LTU 24 10 _ ltac:(apply bv_eq; vm_compute; reflexivity) Bo0_code_92368_93368.F_93284 eq_refl Bo0_code_92368_93368.D_93284);
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma g7_run (fx : FPState) Rc MV sd fb (lenr : nat) sto (n l Dd vr d : Z) :
  rinvD R E Rc -> pf E F fl MV ->
  getr Rc (reg 20) = Z_to_bv 64 (n + 1) -> getr Rc (reg 22) = Z_to_bv 64 ro -> getr Rc (reg 24) = Z_to_bv 64 sd ->
  0 <= sd < 2 ^ 64 -> ARGF E F MV ro -> ro + 32 <= E - 400 -> L5.big_at RSEGS MV ro (L5.BO fb lenr sto) ->
  0 <= n <= 299 -> 0 <= l <= 298 ->
  DREGF MV (L5.bo_data ro (L5.BO fb lenr sto)) (n + 1) -> DREGF MV Dd (l + 1) ->
  L5.u64_at RSEGS MV (E - 272) (l + 1) -> L5.u64_at RSEGS MV (E - 120) Dd ->
  L5KA.zeros_at MV ((E - 384) / 8 + 2147450880) 48 -> L5.writable RSEGS MV (E - 400) 400 ->
  L5.u64_at RSEGS MV (L5.bo_data ro (L5.BO fb lenr sto) + 8 * n) vr -> 0 <= vr < 2 ^ 64 ->
  L5.u64_at RSEGS MV (Dd + 8 * l) d -> 0 <= d < 2 ^ 64 ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx Rc 0x931d4 MV) (st fx' R' 0x93284 M') /\ mem_grows MV M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (E - 376 <= a < E - 360) -> ~ (E - 240 <= a < E - 224) -> ~ (E - 392 <= a < E - 384) -> M' (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
    /\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 23; 25; 26]%nat -> getr R' (reg x) = getr Rc (reg x))
    /\ getr R' (reg 10) = Z_to_bv 64 d /\ getr R' (reg 24) = Z_to_bv 64 vr
    /\ getr R' (reg 19) = Z_to_bv 64 n /\ getr R' (reg 21) = Z_to_bv 64 ((ro + 8) / 8 + 2147450880) /\ getr R' (reg 22) = Z_to_bv 64 (ro + 8) /\ getr R' (reg 27) = Z_to_bv 64 l
    /\ L5.u64_at RSEGS M' (E - 232) (Z.of_nat lenr) /\ L5.u64_at RSEGS M' (E - 240) (L5.bo_data ro (L5.BO fb lenr sto))
    /\ L5.u64_at RSEGS M' (E - 376) sd /\ L5.u64_at RSEGS M' (E - 368) (ro / 8 + 2147450880).
Proof.
  intros RI PF X20 X22 X24 SDR ((ORP & ORG & O8) & OBIG & OZ & OW & OFR & OF & OSH & SOF & SOSH & SOFR) OLOW OB NR LR
         ((RD1 & RD8 & RDC & RD2) & RNS & ROI & RZ & RDEF & RWR) ((DD1 & DD8 & DDC & DD2) & DNS & DOI & DZ & DDEF & DWR) S112 S264 FZ FW400 CR VRR CD DRR.
  unfold pf in PF. destruct PF as (W352 & IMGC & CSB & CUAR & FDEFv & FWv & FSHWv & FLCv & FLWv).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  pose proof RI as (X2 & X8 & X9 & X3 & X4 & XSB).
  pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. clear OWNAG HH2 NCF NCS FLNC.
  assert (ER' : 140735332487632 <= E <= 140737488355328) by (clear - ER; lia).
  assert (OAL : L5ADIVPG1.aligned ro 8) by exact O8. assert (EAL : L5ADIVPG1.aligned E 32) by exact EA.
  unfold L5ADVGL.nsh, L5ADVGL.oim in *.
  destruct OB as (O0 & FBR & OL8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in *.
  assert (FBR' : 0 <= fb <= 255) by (clear - FBR; lia). assert (FBG : 0 <= fb < 2 ^ 64) by (clear - FBR; lia).
  pose proof (d8j Dd l DD8) as (DL8 & DLA). pose proof (d8 Dd DD8) as DD88.
  assert (CEIL : ahl_ceil ar + 9104 <= E) by (clear - SLO HSCR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (EDV : (E - 240) / 8 = (E - 384) / 8 + 18 /\ (E - 120) / 8 = (E - 384) / 8 + 33 /\ 17591916560912 <= (E - 384) / 8 /\ (E - 384) / 8 + 48 <= 17592186044416)
    by (clear - EA ER; unfold L5ADIVPG1.aligned in EA; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct EDV as (EDR & EDD & EDL & EDH).
  assert (VZR : L5KA.zeros_at MV ((E - 240) / 8 + 2147450880) 1). { rewrite EDR. eapply L5KA.zeros_at_sub. exact FZ. clear; lia. clear; lia. }
  assert (VZD : L5KA.zeros_at MV ((E - 120) / 8 + 2147450880) 1). { rewrite EDD. eapply L5KA.zeros_at_sub. exact FZ. clear; lia. clear; lia. }
  pose proof (d8 ro O8) as RO88.
  assert (RB : 0 <= ro / 8 /\ ro / 8 <= 17592186044412) by (clear - RO88 ORP; lia).
  assert (OFRX : E - 400 + 400 <= ro \/ ro + 32 <= E - 400) by (right; exact OLOW).
  assert (SOFRX : ro / 8 + 2147450880 + 4 <= E - 400 \/ E - 400 + 400 <= ro / 8 + 2147450880) by (left; clear - RB ER; lia).
  assert (LNR : 0 <= Z.of_nat lenr <= 18446744073709551615 /\ 0 <= Z.of_nat lenr < 2 ^ 64).
  { destruct sto; [destruct OST as (_ & _ & _ & X & _) | destruct OST as (_ & _ & _ & X & X' & _)]; clear - X + clear - X X'; lia. }
  destruct LNR as [LNR LNRG].
  assert (VR1 : 0 <= n <= 134217727 /\ 0 <= l <= 134217727 /\ 1 <= n + 1 - n <= 134217728 /\ 1 <= l + 1 - l <= 134217728 /\ 1 <= n + 1 <= 134217728 /\ 1 <= l + 1 <= 134217728
                /\ 0 <= n < 2 ^ 64 /\ 0 <= l < 2 ^ 64 /\ 0 <= n + 1 < 2 ^ 64 /\ 0 <= l + 1 < 2 ^ 64 /\ 0 <= sd <= 18446744073709551615 /\ 0 <= vr <= 18446744073709551615 /\ 0 <= d <= 18446744073709551615)
    by (clear - NR LR SDR VRR DRR; lia).
  destruct VR1 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  assert (DDR : 4096 <= Dd <= 140737488355328 /\ 0 <= Dd < 2 ^ 64 /\ 4104 <= 8 * (l + 1) + Dd <= 140737479966720 /\ L5ADIVPG1.aligned Dd 8 /\ 0 <= Dd / 8 /\ Dd / 8 <= 17592186043904)
    by (unfold L5ADIVPG1.aligned; clear - DD1 DD8 DD2 DD88 LR; lia).
  destruct DDR as (DDR1 & DDRG & DDR2 & DDAL & DDB1 & DDB2).
  assert (DAP : (Dd + 8 * (l + 1) <= Dd / 8 + 2147450880 \/ Dd / 8 + 2147450880 + (l + 1) <= Dd) /\ (E - 400 + 400 <= Dd \/ Dd + 8 * (l + 1) <= E - 400)
                /\ (E - 400 + 400 <= Dd / 8 + 2147450880 \/ Dd / 8 + 2147450880 + (l + 1) <= E - 400)).
  { split. clear - DNS DD88 DDB1 LR; lia. split. clear - DDC CEIL; lia. clear - DDB2 ER LR; lia. }
  destruct DAP as (DAP1 & DAP2 & DAP3).
  destruct sto as [v0 v1|cap q]; unfold L5.bo_data in *; cbn [L5.bo_st] in *.
  - (* [comment removed for export] *)
    destruct OST as (BT0 & _).
    pose proof (d16 ro O8) as (R16 & R16A & _).
    assert (RR : 4096 <= ro + 16 <= 140737488355328 /\ L5ADIVPG1.aligned (ro + 16) 8 /\ 4104 <= ro + 8 * (n + 1) + 16 <= 140737479966720) by (unfold L5ADIVPG1.aligned; clear - RD1 RD2 R16A ORP NR; lia).
    destruct RR as (RR1 & RRA & RR2).
    assert (RAP : (ro + 16 + 8 * (n + 1) <= (ro + 16) / 8 + 2147450880 \/ (ro + 16) / 8 + 2147450880 + (n + 1) <= ro + 16) /\ (E - 400 + 400 <= ro + 16 \/ ro + 16 + 8 * (n + 1) <= E - 400)
                  /\ (E - 400 + 400 <= (ro + 16) / 8 + 2147450880 \/ (ro + 16) / 8 + 2147450880 + (n + 1) <= E - 400)).
    { rewrite R16. split. clear - RNS RO88 RB NR; lia. split. clear - RDC CEIL; lia. clear - RB ER NR; lia. }
    destruct RAP as (RAP1 & RAP2 & RAP3).
    replace (ro + 16 + 8 * n) with (ro + 8 * n + 16) in CR by (clear; lia).
    pose proof (v5G7i_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 63%nat => sd | 64%nat => l + 1 | 65%nat => Dd
                                              | 71%nat => n + 1 | 72%nat => Z.of_nat lenr | 73%nat => n | 74%nat => l | 75%nat => d | 76%nat => vr | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & p10 & _ & _ & _ & _ & p19 & p21 & p22 & p24 & p27 & _ & pC232 & pC240 & pC376 & pC368)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG.
    split. { intros a Ha N1 N2 N3. apply pFZ. exact Ha. intros X. apply N1. clear - X; lia. intros X. apply N2. clear - X; lia. intros X. apply N3. clear - X; lia. }
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 23; 25; 26]%nat). vm_compute; reflexivity. }
    split. exact p10. split. exact p24. split. exact p19. split. exact p21. split. exact p22. split. exact p27. split. exact pC232. split. exact pC240. split. exact pC376. exact pC368.
  - (* [comment removed for export] *)
    destruct OST as (BT1 & O16 & O24 & _ & CAPR & _ & Q4096 & Q47 & _).
    pose proof (d8 q RD8) as Q88.
    assert (QB : 0 <= q / 8 /\ q / 8 <= 17592186043904) by (clear - Q88 RD1 RD2 NR; lia).
    assert (RR : 4096 <= q <= 140737488355328 /\ L5ADIVPG1.aligned q 8 /\ 4104 <= q + 8 * (n + 1) <= 140737479966720 /\ 0 <= q < 2 ^ 64) by (unfold L5ADIVPG1.aligned; clear - RD1 RD2 RD8 NR; lia).
    destruct RR as (RR1 & RRA & RR2 & QRG).
    assert (RAP : (q + 8 * (n + 1) <= q / 8 + 2147450880 \/ q / 8 + 2147450880 + (n + 1) <= q) /\ (E - 400 + 400 <= q \/ q + 8 * (n + 1) <= E - 400)
                  /\ (E - 400 + 400 <= q / 8 + 2147450880 \/ q / 8 + 2147450880 + (n + 1) <= E - 400)).
    { split. clear - RNS Q88 QB NR; lia. split. clear - RDC CEIL; lia. clear - QB ER NR; lia. }
    destruct RAP as (RAP1 & RAP2 & RAP3).
    pose proof (v5G7d_conc fx Rc MV (fun j => match j with 2%nat => E | 36%nat => ro | 40%nat => F | 58%nat => U Rc 1 | 60%nat => fb | 63%nat => sd | 64%nat => l + 1 | 65%nat => Dd | 70%nat => q
                                              | 71%nat => n + 1 | 72%nat => Z.of_nat lenr | 73%nat => n | 74%nat => l | 75%nat => d | 76%nat => vr | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1v & pMG & _ & pFZ & (pMS & pKS & _ & p10 & _ & _ & _ & _ & p19 & p21 & p22 & p24 & p27 & _ & pC232 & pC240 & pC376 & pC368)).
    exists fx1, R1, M1v. split. exact pMS. split. exact pMG.
    split. { intros a Ha N1 N2 N3. apply pFZ. exact Ha. intros X. apply N1. clear - X; lia. intros X. apply N2. clear - X; lia. intros X. apply N3. clear - X; lia. }
    split. { intros x Hx. apply pKS. revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 23; 25; 26]%nat). vm_compute; reflexivity. }
    split. exact p10. split. exact p24. split. exact p19. split. exact p21. split. exact p22. split. exact p27. split. exact pC232. split. exact pC240. split. exact pC376. exact pC368.
Qed.
End DIV.
End WithIface.
End SCFG_1.
End L5ADVGB.
