(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun Bo0_code_8e368_8f368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5BCopyS16 L5BOpModFP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5BOMF.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5OMA. Import L5BCPS16. Import L5BOMFP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Definition offw (lo hi : Z) (M M1 : word -> option byte) : Prop := forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Section Specs.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> list fframe -> list fframe -> credit -> Z -> (word -> option byte) -> bvmap 5 word ->
                               list (Z * Z) -> credit -> list fframe -> Prop.
(* [comment removed for export] *)
Variables (SCRo SCRf D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).

(* [comment removed for export] *)
Definition ret_slot (M : word -> option byte) (T co fbo : Z) : Prop :=
  L5.u8_at RSEGS M co fbo /\ 0 <= fbo < 256 /\ sobj ar T co 32 /\ L5.defined M co 32 /\ shadow_zero M co 4.

Definition opmodf1_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (co xo bo T fbx fbo : Z) (bb : L5.bigobj) (wb : list Z) (st : XS),
    let capb := L5.bo_cap bb in
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 co -> getr R 11%bv = Z_to_bv 64 xo -> getr R 12%bv = Z_to_bv 64 bo ->
    getr R 1%bv = Z_to_bv 64 OMF1_RET ->                                    (* [comment removed for export] *)
    getr R 2%bv = Z_to_bv 64 T -> getr R 9%bv = Z_to_bv 64 T -> T mod 32 = 0 ->    (* [comment removed for export] *)
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> getr R 3%bv = Z_to_bv 64 67584 ->
    astk ar M T SCRf -> stksh ar M (T - 16 - SCRo) ->
    ffrk 1 FF LK D1 -> ffrk 2 FF LK D2 -> ffrk 3 FF LK D3 -> ffrs FF T ->
    L5.img_clear M 0x10000 0x3c000 ->
    x_is_a M xo fbx -> aobj FF xo 32 -> shadow_zero M xo 4 ->
    b_ok LB M bo bb wb -> aobj FF bo 32 -> shadow_zero M bo 4 ->
    (xo + 32 <= bo \/ bo + 32 <= xo) ->
    L5.bo_cap bb <= 268 -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->
    ret_slot M T co fbo ->
    acredit_for L cr (K1 + 1) (bytes1 capb + 64) ->                          (* [comment removed for export] *)
    (forall M1 : word -> option byte, offw (T - 16) T M M1 -> xs_pre st M1) ->      (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M1 M' : word -> option byte) (model' : Model) LB1 LB' cr1 cr' (LK1 LK' : list fframe) (A' : list (Z * Z))
            (bx : L5.bigobj) (wx : list Z) (g : growth),
        L5.big_at RSEGS M1 xo bx -> L5C.obj_limbs RSEGS M1 bx wx -> L5.bo_neg bx = false ->
        match L5.bo_st bx with
        | L5.BInl _ _ => LB1 = LB
        | L5.BDyn cap q => cap = 8 /\ LB1 = (q, 64) :: LB /\ afresh L ar LB (FF ++ LK1) M1 q 64
        end ->
        L5.big_at RSEGS M1 bo bb -> L5C.obj_limbs RSEGS M1 bb wb -> (1 <= L5.bo_len bb)%nat ->
        acredit_after L cr K1 (bytes1 capb) cr1 ->
        ahpres L ar LB FF T (SCRo + 16) [(xo, 32)] M M1 -> incl LK1 LK ->
        copy_post_at 32 L ar LB1 FF LK' cr1 M1 M' R R' co xo T fbo bx wx g LB' cr' -> incl LK' LK1 ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' OMF1_RET M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        regs_preserved R R' ->
        e2_landed st LB FF LK cr T M' R' LB' cr' LK' ->
        x_is_a M' xo fbx -> L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb ->
        ahpres L ar LB FF T (SCRo + 16) ((xo, 32) :: xs_foot) M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' TOP_PAD M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z))
            fbx' nx qx cr1,
        regs_preserved R R' ->
        L5.big_at RSEGS M' xo (L5.BO fbx' nx (L5.BDyn 8 qx)) -> afresh L ar LB (FF ++ LK') M' qx 64 ->
        acredit_after L cr K1 (bytes1 capb) cr1 ->
        e3_landed st ((qx, 64) :: LB) FF LK cr1 T M' R' LB' cr' LK' ->
        L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb ->
        ahpres L ar LB FF T (SCRo + 16) ((xo, 32) :: xs_foot) M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R OMF M model) K.

Definition opmodf2_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (co yo ao T r fba fbo : Z) (by_ : L5.bigobj) (wy : list Z),
    let capy := L5.bo_cap by_ in
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 co -> getr R 11%bv = Z_to_bv 64 yo -> getr R 12%bv = Z_to_bv 64 ao ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 T -> T mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    astk ar M T SCRf -> stksh ar M (T - 16 - SCRo) ->
    ffrk 1 FF LK D1 -> ffrk 2 FF LK D2 -> ffrk 3 FF LK D3 -> ffrs FF T ->
    L5.img_clear M 0x10000 0x3c000 ->
    y_ok LB M yo by_ wy -> aobj FF yo 32 -> shadow_zero M yo 4 -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    a_ok M ao fba -> aobj FF ao 32 -> shadow_zero M ao 4 ->
    (yo + 32 <= ao \/ ao + 32 <= yo) ->
    ret_slot M T co fbo ->
    acredit_for L cr (K2 + 1) (bytes2 capy + Z.max 64 (8 * capy)) ->          (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M1 M' : word -> option byte) (model' : Model) LB1 LB' cr1 cr' (LK1 LK' : list fframe) (A' : list (Z * Z))
            (by' : L5.bigobj) (wy' : list Z) (g : growth),
        L5.big_at RSEGS M1 yo by' -> L5C.obj_limbs RSEGS M1 by' wy' ->
        match L5.bo_st by_, L5.bo_st by' with
        | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LB1 = LB
        | L5.BInl _ _, L5.BInl _ _ => LB1 = LB
        | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LB1 = (q', 64) :: LB /\ afresh L ar LB (FF ++ LK1) M1 q' 64
        | L5.BDyn _ _, L5.BInl _ _ => False
        end ->
        a_ok M1 ao fba ->
        acredit_after L cr K2 (bytes2 capy) cr1 ->
        ahpres L ar LB FF T (SCRo + 16) [(yo, 32); (L5.bo_data yo by_, 8 * L5.bo_cap by_)] M M1 -> incl LK1 LK ->
        copy_post_at 32 L ar LB1 FF LK' cr1 M1 M' R R' co yo T fbo by' wy' g LB' cr' -> incl LK' LK1 ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R OMF M model) K.
End Specs.

(* [comment removed for export] *)
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
Lemma offw_agree lo hi M M1 a n : offw lo hi M M1 -> 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= lo \/ hi <= a) -> L5C.agree_on M M1 a n.
Proof. intros AG H0 H1 FAR i Hi. apply AG. lia. lia. Qed.
Lemma offw_shz lo hi M M1 o g : offw lo hi M M1 -> shadow_zero M o g -> 0 <= o -> (S o + g <= lo \/ hi <= S o) -> S o + g <= 2 ^ 64 -> shadow_zero M1 o g.
Proof. intros AG SZ H0 FAR H1 j Hj. unfold byte_at. rewrite AG. apply SZ. exact Hj. unfold S, SB in *. pose proof (Z.div_pos o 8 H0 ltac:(lia)). lia. lia. Qed.

(* [comment removed for export] *)
Lemma ahpres_up LB FF sp fr scr W M M' :
  ahpres L ar LB FF (sp - fr) scr W M M' -> 0 <= fr -> L5.defined M (sp - fr) fr -> ahl_ceil ar <= sp - fr -> sp <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar ->
  ahpres L ar LB FF sp (scr + fr) W M M'.
Proof.
  intros (E & D & Kd) Hfr DF HC HT SPT. apply (ahpres_of L ar).
  - eapply (ek_mono L ar). exact E. intros x Hx; lia. intros a Ha; exact Ha.
  - intros i Hi. destruct (Z_lt_le_dec i scr) as [LT|GE].
    + replace (sp - (scr + fr) + i) with (sp - fr - scr + i) by lia. apply D. lia.
    + replace (sp - (scr + fr) + i) with (sp - fr + (i - scr)) by lia. apply Kd. lia. apply stack_client. lia. lia. apply DF. lia.
  - intros a Ha Hc HM. apply Kd. exact Ha. 2: exact HM. eapply aclient_mono. exact Hc. intros x Hx. lia.
Qed.

Lemma copy_post_up LB FF LKq cr M M' Rc Rc' R R' o o' T fbo b' ws' g LB' cr' :
  copy_post_at 16 L ar LB FF LKq cr M M' Rc Rc' o o' (T - 16) fbo b' ws' g LB' cr' -> regs_preserved R R' ->
  L5.defined M (T - 16) 16 -> ahl_ceil ar <= T - 16 -> T <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar ->
  copy_post_at 32 L ar LB FF LKq cr M M' R R' o o' T fbo b' ws' g LB' cr'.
Proof.
  intros (_ & P) RP DF HC HT SPT. split. exact RP.
  destruct g as [|q cap].
  - destruct P as (P1 & P2 & P3 & P4 & AH). repeat (split; [assumption|]). replace (COPY_SCR + 32) with (COPY_SCR + 16 + 16) by lia. apply ahpres_up; first [assumption | lia].
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & AH). repeat (split; [assumption|]). replace (COPY_SCR + 32) with (COPY_SCR + 16 + 16) by lia. apply ahpres_up; first [assumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma omf_tail : copy_stk16_spec L ar HI ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (co xo T r rt8 fbo : Z) (bx : L5.bigobj) (wx : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R (reg 2) = Z_to_bv 64 (T - 16) -> getr R (reg 8) = Z_to_bv 64 co -> getr R (reg 10) = Z_to_bv 64 xo -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
    T mod 32 = 0 -> astk ar M T (COPY_SCR + 32) ->
    L5.u64_at RSEGS M (T - 16) rt8 -> L5.u64_at RSEGS M (T - 8) r -> L5.ra_ok r -> 0 <= rt8 < 2 ^ 64 ->
    ffr FF LK 2 -> ffrs FF (T - 16) ->
    L5.u8_at RSEGS M co fbo -> 0 <= fbo < 256 -> sobj ar T co 32 -> L5.defined M co 32 -> shadow_zero M co 4 ->
    L5.big_at RSEGS M xo bx -> L5C.obj_limbs RSEGS M bx wx -> aobj FF xo 32 -> shadow_zero M xo 4 ->
    (forall cap q, L5.bo_st bx = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (L5.bo_dyn bx = true -> 8 * L5.bo_cap bx <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap bx)) ->
    (forall (fx' : FPState) (Rc R2 R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        copy_post_at 16 L ar LB FF LK' cr M M' Rc R2 co xo (T - 16) fbo bx wx g LB' cr' ->
        getr R' (reg 2) = Z_to_bv 64 T -> getr R' (reg 8) = Z_to_bv 64 rt8 ->
        (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg k) = getr R (reg k)) ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R OMF_INNER_RET M model) K.
Proof.
  intros Hcp fx R M model K LB FF LK cr A co xo T r rt8 fbo bx wx HH AM HK G2 G8 G10 G4 T32 STK C16 C8 RA RT8 FFR FRS CO8 FBO SOB CODEF COSZ BIGX LIMX AOX XSZ INB CRX KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold COPY_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR in SLO. cbn in SLO.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & _).
  pose proof SOB as (SO1 & SO2 & SO8).
  assert (TR : 0 <= T < 2 ^ 64 /\ 140735332487184 <= T <= 140737488355328 /\ 4096 <= co <= 140737488355296 /\ 0 <= co < 2 ^ 64 /\ ahl_ceil ar <= T - 16) by (clear - SLO SHI SPT SO1 SO2; lia).
  destruct TR as (TR0 & TR1 & COR & COR0 & TCE).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 0 0 HH AOX ltac:(clear; lia) ltac:(reflexivity)) as ((XO1 & XO2 & XO3 & _) & _).
  set (H := ahid A model) in *.
  assert (W16 : L5.writable RSEGS (mrestrict H M) (T - 16) 16).
  { apply (proj2 (writable_vis H M (T - 16) 16 (VIS (T - 16) 16 TCE ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))).
    eapply (astk_writable ar M T). exact STK. unfold COPY_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; cbn; clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (omfB_conc fx R (mrestrict H M) (fun j => match j with 2%nat => T | 33%nat => co | 36%nat => xo | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P TR0 COR0 ltac:(clear - XO1 XO3; lia) G2 G8 G10 TR1 T32 W16 COR) as (fx1 & R1 & M1v & MG1 & _ & FZ1 & (MS1 & KS1 & B1 & B10 & B11)). clear P.
  apply (apiece_ro L ar C HI LY HIok LB FF LK cr A M model fx fx1 R OMF_INNER_RET R1 COPY M1v K HH AM MS1 MG1 FZ1).
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  pose proof (mem_eq_of_agree _ _ FRM1) as EQ. subst M1. clear FRM1 MGM1.
  (* [comment removed for export] *)
  assert (T32' : (T - 32) mod 32 = 0).
  { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 32) with ((T / 32 - 1) * 32) by (clear - E; lia). apply Z_mod_mult. }
  apply (Hcp fx1 R1 M model1 K LB FF LK cr A co xo (T - 32) 0x8eb44 fbo bx wx HH1 AM1 HK).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - exact CRX.
  - rewrite r1. exact B1.
  - split. clear; lia. reflexivity.
  - replace (T - 32 + 16) with (T - 16) by (clear; lia). rewrite r2, (KS1 2%nat) by inl. exact G2.
  - exact T32'.
  - rewrite r4, (KS1 4%nat) by inl. exact G4.
  - replace (T - 32 + 16) with (T - 16) by (clear; lia). eapply (astk_sub ar M M T (COPY_SCR + 32) 16 (COPY_SCR + 16) STK). intros x Hx; exact Hx. clear; lia. unfold COPY_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; cbn; clear; lia. clear; lia.
    { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 16) with ((T / 32 * 2 - 1) * 16) by (clear - E; lia). apply Z_mod_mult. }
  - exact FFR.
  - replace (T - 32 + 16) with (T - 16) by (clear; lia). exact FRS.
  - exact CO8.
  - exact FBO.
  - split. clear - SO1; lia. split. exact SO2. exact SO8.
  - exact CODEF.
  - exact COSZ.
  - exact BIGX.
  - exact LIMX.
  - exact AOX.
  - exact XSZ.
  - exact INB.
  - intros fx2 R2 M2 model2 g LB2 cr2 LK2 A2 CP RT2 IA2 AM2 LKI2 HH2.
    replace (T - 32 + 16) with (T - 16) in CP by (clear; lia).
    pose proof CP as (RP2 & _).
    assert (AHc : ahpres L ar LB FF (T - 16) (COPY_SCR + 16) [(co, 32)] M M2).
    { destruct g; [destruct CP as (_ & _ & _ & _ & _ & X) | destruct CP as (_ & _ & _ & _ & _ & _ & _ & _ & X)]; exact X. }
    destruct AHc as (EK & _ & _).
    assert (AGF : forall i, T - 16 <= i < T -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply EK. split. clear - Hi TR0 TR1; lia. split. apply stack_client. clear - Hi TCE TR1; lia. clear - Hi; lia.
      intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi SO1; lia. }
    assert (C16_2 : L5.u64_at RSEGS M2 (T - 16) rt8).
    { eapply (L5C.u64_at_agree RSEGS M M2). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C16. }
    assert (C8_2 : L5.u64_at RSEGS M2 (T - 8) r).
    { eapply (L5C.u64_at_agree RSEGS M M2). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C8. }
    assert (DEF2 : L5.defined M2 (T - 16) 16).
    { eapply (L5C.defined_agree M M2). intros i Hi; apply AGF; clear - Hi; lia.
      intros i Hi. replace (T - 16 + i) with (T - (COPY_SCR + 32) + (COPY_SCR + 32 - 16 + i)) by (clear; lia). apply DSCR. unfold COPY_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; cbn; clear - Hi; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & _).
    set (H2 := ahid A2 model2) in *.
    assert (W16_2 : L5.writable RSEGS (mrestrict H2 M2) (T - 16) 16).
    { apply (proj2 (writable_vis H2 M2 (T - 16) 16 (VIS2 (T - 16) 16 TCE ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))).
      apply (L5C.writable_of_defined RSEGS). exact DEF2. clear - TR1; lia. clear - TR0; lia. }
    pose proof (omfC_conc fx2 R2 (mrestrict H2 M2) (fun j => match j with 2%nat => T | 37%nat => r | 38%nat => rt8 | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P TR0 ltac:(clear - RA; destruct RA; lia) RT8
                ltac:(rewrite (cs_of_preserved R1 R2 2 RP2) by (unfold cs_all; inl); rewrite (KS1 2%nat) by inl; exact G2) TR1 T32 W16_2
                ltac:(apply (proj2 (u64_at_vis H2 M2 (T - 8) r (VIS2 (T - 8) 8 ltac:(clear - TCE; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))); exact C8_2)
                ltac:(apply (proj2 (u64_at_vis H2 M2 (T - 16) rt8 (VIS2 (T - 16) 8 TCE ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))); exact C16_2))
      as (fx3 & R3 & M3v & MG3 & _ & FZ3 & (MS3 & KS3 & E1 & E2 & E8)). clear P.
    pose proof (ret_to fx3 R3 M3v 0x8eb50 W_8eb50 r F_8eb50 eq_refl D_8eb50 E1 (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ MS3 RET) as MS. clear MS3 RET.
    apply (apiece_ro L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 fx2 fx3 R2 0x8eb44 R3 r M3v K HH2 AM2 MS MG3 FZ3).
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3.
    pose proof (mem_eq_of_agree _ _ FRM3) as EQ. subst M3. clear FRM3 MGM3.
    apply (KONT fx3 R1 R2 R3 M2 model3 g LB2 cr2 LK2 A2 CP E2 E8).
    + intros k Hk. cbn [In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [ rewrite (KS3 _) by inl; rewrite (cs_of_preserved R1 R2 _ RP2) by (unfold cs_all; inl); rewrite (KS1 _) by inl; reflexivity |]). destruct Hk.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
    + exact IA2.
    + exact AM3.
    + exact LKI2.
    + exact HH3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stksh_off (M M1 : word -> option byte) lo T : stksh ar M lo -> offw (T - 16) T M M1 -> lo mod 8 = 0 -> ahl_ceil ar <= lo -> 0 <= lo ->
  ar_stack_top ar <= 2 ^ 47 -> ar_sptop ar <= 2 ^ 47 -> 2 ^ 46 <= T - 16 -> stksh ar M1 lo.
Proof.
  intros SSH AG L8 CE L0 TOP SPT HT j Hj. unfold byte_at. unfold stksh, shadow_zero, byte_at in SSH.
  set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (MX : mx <= 2 ^ 47) by (subst mx; apply Z.max_lub; assumption).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Q : 0 <= S lo + j < 2 ^ 46) by (unfold S, SB; clear - Hj L8 CE L0 MX; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  rewrite AG. apply SSH. exact Hj. clear - Q; lia. clear - Q HT; lia.
Qed.

(* [comment removed for export] *)
Lemma ahpres_friend LB FF LK cr A M M1 M' (model : Model) T scr W :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  offw (T - 16) T M M1 -> mem_grows M M1 -> ahpres L ar LB FF (T - 16) scr W M1 M' -> L5.defined M1 (T - 16) 16 ->
  ahl_ceil ar <= T - 16 - scr -> 0 <= scr -> T <= 2 ^ 47 -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  ahpres L ar LB FF T (scr + 16) W M M'.
Proof.
  intros HH OFF MG AHP DF HC Hs HT SPT.
  pose proof (ahpres_up LB FF T 16 scr W M1 M' AHP ltac:(lia) DF ltac:(lia) HT (proj1 SPT)) as (E & D & Kd).
  apply (ahpres_of L ar).
  - eapply (ek_trans L ar). 2: exact E. apply (ek_piece L ar LB FF T (scr + 16) W M M1 _ OFF). intros a Ha Hc _ X.
    destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ T (scr + 16) a HH SPT Hc) as [Y|Y]. { clear - X Y Hs. destruct Y as (_ & Y). apply Y. Lia.lia. } { clear - X Y HC Hs. Lia.lia. }
  - exact D.
  - eapply (dk_trans L ar). apply (dk_grows L ar). exact MG. exact Kd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Proofs.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> list fframe -> list fframe -> credit -> Z -> (word -> option byte) -> bvmap 5 word ->
                               list (Z * Z) -> credit -> list fframe -> Prop.
Variables (SCRo SCRf D1 D2 D3 K1 K2 : Z) (bytes1 bytes2 : Z -> Z).
Hypothesis HSo : 0 <= SCRo /\ SCRo mod 8 = 0.
Hypothesis HSf : SCRo + 16 <= SCRf /\ COPY_SCR + 32 <= SCRf.
Hypothesis HD1 : 2 <= D1.
Hypothesis HK1 : 0 <= K1 /\ forall c, 0 <= c -> 0 <= bytes1 c.
Hypothesis HK2 : 0 <= K2 /\ forall c, 0 <= c -> 0 <= bytes2 c.

(* [comment removed for export] *)
Lemma landed_to_preserved (R R1 R' : bvmap 5 word) T :
  landed_regs R1 R' (T - 16) (bv_unsigned (getr R (reg 8))) -> getr R 2%bv = Z_to_bv 64 T ->
  (forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k)) -> regs_preserved R R'.
Proof.
  intros (L2 & L8 & LK) G2 KS. apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
  destruct Hk as [<-|Hk]. { rewrite <- r2, L2, G2. f_equal. lia. }
  destruct Hk as [<-|Hk]. { rewrite <- (KS 3%nat) by inl. apply LK. vm_compute. clear. tauto. }
  destruct Hk as [<-|Hk]. { rewrite <- (KS 4%nat) by inl. apply LK. vm_compute. clear. tauto. }
  destruct Hk as [<-|Hk]. { replace (reg 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite L8. replace (8%bv : bv 5) with (reg 8) by (apply bv_eq; reflexivity). apply Z_to_bv_bv_unsigned. }
  repeat (destruct Hk as [<-|Hk]; [ rewrite <- (KS _) by inl; apply LK; vm_compute; clear; tauto |]). destruct Hk.
Qed.

Theorem opmodf1_ok :
  opmod1A_spec L ar HI XS xs_pre xs_foot e2_landed e3_landed SCRo D1 D2 D3 K1 bytes1 -> copy_stk16_spec L ar HI ->
  opmodf1_spec L ar HI XS xs_pre xs_foot e2_landed e3_landed SCRo SCRf D1 D2 D3 K1 bytes1.
Proof.
  intros Hom1 Hcp fx R M model K LB FF LK cr A co xo bo T fbx fbo bb wb st capb HH AM HK G10 G11 G12 G1 G2 G9 T32 G4 G3 STK SSH F1 F2 F3 FRS IMG XA AOX XSZ BOK AOB BSZ APART CAPB DYN3 RS CRF XSP KN KE2 KE3.
  destruct RS as (CO8 & FBO & SOB & CODEF & COSZ). destruct HSo as (HSo0 & HSo8). destruct HSf as (HSf1 & HSf2).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (CSV : COPY_SCR = 4256) by reflexivity.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _ & ND & _).
  pose proof SOB as (SO1 & SO2 & SO8).
  assert (TR : 0 <= T < 2 ^ 64 /\ 140735332487184 <= T <= 140737488355328 /\ 4096 <= co <= 140737488355296 /\ 0 <= co < 2 ^ 64 /\ ahl_ceil ar <= T - 16 - SCRo /\ 2 ^ 46 <= T - 16)
    by (clear - SLO SHI SPT SO1 SO2 HSo0 HSf1 HSf2 CSV; lia).
  destruct TR as (TR0 & TR1 & COR & COR0 & TCE & T46).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 0 0 HH AOX ltac:(clear; lia) ltac:(reflexivity)) as ((XO1 & XO2 & XO3 & XO8 & _) & XOSH & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model bo 32 0 0 HH AOB ltac:(clear; lia) ltac:(reflexivity)) as ((BO1 & BO2 & BO3 & BO8 & _) & BOSH & _).
  set (H := ahid A model) in *.
  assert (W16 : L5.writable RSEGS (mrestrict H M) (T - 16) 16).
  { apply (proj2 (writable_vis H M (T - 16) 16 (VIS (T - 16) 16 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))).
    eapply (astk_writable ar M T). exact STK. clear - HSf2 CSV; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (omfA_conc fx R (mrestrict H M) (fun j => match j with 2%nat => T | 33%nat => co | 34%nat => xo | 35%nat => bo | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P TR0 COR0 ltac:(clear - XO1 XO3; lia) ltac:(clear - BO1 BO3; lia) ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r10; exact G10) ltac:(rewrite <- r11; exact G11) ltac:(rewrite <- r12; exact G12)
              TR1 T32 W16 ltac:(clear - XO1 XO3; lia) XO8)
    as (fx1 & R1 & M1v & MG1 & _ & FZ1 & (MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & AC16 & AC8)). clear P.
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R OMF R1 OPMOD M1v (fun a => T - 16 <= a < T) K HH AM MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa TCE HSo0 TR1; lia. clear; lia. clear - Wa TCE HSo0 SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (OFF : offw (T - 16) T M M1) by exact FRM1.
  set (rt8 := bv_unsigned (getr R (reg 8))) in *.
  assert (C16 : L5.u64_at RSEGS M1 (T - 16) rt8).
  { apply (proj1 (u64_at_vis H M1 (T - 16) rt8 (VIS (T - 16) 8 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))). unfold H. rewrite VIS1. exact AC16. }
  assert (C8 : L5.u64_at RSEGS M1 (T - 8) OMF1_RET).
  { apply (proj1 (u64_at_vis H M1 (T - 8) OMF1_RET (VIS (T - 8) 8 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))). unfold H. rewrite VIS1.
    replace OMF1_RET with (bv_unsigned (getr R (reg 1))). exact AC8. rewrite <- r1, G1. apply L5.unsigned_lit. unfold OMF1_RET; clear; lia. }
  assert (DEF16 : L5.defined M1 (T - 16) 16).
  { eapply L5.defined_grows. exact MGM1. intros i Hi. replace (T - 16 + i) with (T - SCRf + (SCRf - 16 + i)) by (clear; lia). apply DSCR. clear - Hi HSf1 HSo0; lia. }
  assert (KS13 : forall k, In k [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k)).
  { intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [apply KS1; inl|]). destruct Hk. }
  assert (T16 : (T - 16) mod 32 = 16).
  { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 16) with (16 + (T / 32 - 1) * 32) by (clear - E; lia). rewrite Z_mod_plus_full. reflexivity. }
  assert (T16' : (T - 16) mod 16 = 0).
  { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 16) with ((T / 32 * 2 - 1) * 16) by (clear - E; lia). apply Z_mod_mult. }
  assert (XA1 : x_is_a M1 xo fbx).
  { destruct XA as (B & TB). split. 2: exact TB. eapply (L5C.big_at_agree RSEGS M M1). 4: exact B. apply (offw_agree _ _ _ _ _ _ OFF). clear - XO1; lia. clear - XO3; lia. left; clear - XO2 TCE HSo0; lia. clear - XO1; lia. clear - XO3; lia. }
  assert (SHF : forall o, 0x634000 <= o -> o + 32 <= 2 ^ 47 -> S o + 4 <= T - 16 /\ S o + 4 <= 2 ^ 64).
  { intros o Ho1 Ho2. unfold S, SB. assert (o / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Ho2; lia). change (2 ^ 47 / 8) with 17592186044416 in H0. clear - H0 T46. lia. }
  assert (XSZ1 : shadow_zero M1 xo 4).
  { destruct (SHF xo XO1 XO3). apply (offw_shz _ _ _ _ _ _ OFF XSZ). clear - XO1; lia. left; assumption. assumption. }
  assert (BSZ1 : shadow_zero M1 bo 4).
  { destruct (SHF bo BO1 BO3). apply (offw_shz _ _ _ _ _ _ OFF BSZ). clear - BO1; lia. left; assumption. assumption. }
  assert (BOK1 : b_ok LB M1 bo bb wb).
  { destruct BOK as (BB & BL & RED & BLK). split.
    { eapply (L5C.big_at_agree RSEGS M M1). 4: exact BB. apply (offw_agree _ _ _ _ _ _ OFF). clear - BO1; lia. clear - BO3; lia. left; clear - BO2 TCE HSo0; lia. clear - BO1; lia. clear - BO3; lia. }
    split. 2: split; [exact RED | exact BLK].
    destruct BL as (L1 & L2 & L3). split. exact L1. split. exact L2.
    destruct BB as (_ & _ & _ & BST). destruct (L5.bo_st bb) as [v0 v1|cap q] eqn:EST. exact L3.
    destruct BST as (_ & _ & _ & LENC & CAPR & Q8 & Q4 & Q47 & _).
    pose proof (proj1 (WB (q, 8 * cap) BLK)) as (_ & _ & _ & _ & QC & _). cbn [fst snd] in QC.
    eapply (L5C.limbs_at_agree RSEGS M M1). 4: exact L3. apply (offw_agree _ _ _ _ _ _ OFF). clear - Q4; lia. rewrite L1; clear - Q47 LENC; lia. left; rewrite L1; clear - QC LENC TCE HSo0; lia.
    clear - Q4; lia. rewrite L1; clear - Q47 LENC; lia. }
  apply (Hom1 fx1 R1 M1 model1 K LB FF LK cr A xo bo (T - 16) 0x8eb34 fbx rt8 bb wb st HH1 AM1 HK).
  - rewrite r10. exact A10.
  - rewrite r11. exact A11.
  - rewrite r1. exact A1.
  - split. clear; lia. reflexivity.
  - reflexivity.
  - replace (T - 16 + 16) with T by (clear; lia). replace (9%bv : bv 5) with (reg 9) by (apply bv_eq; reflexivity). rewrite (KS1 9%nat) by inl. replace (reg 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact G9.
  - exact C16.
  - replace (T - 16 + 8) with (T - 8) by (clear; lia). exact C8.
  - rewrite r2. exact A2.
  - exact T16.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - apply (astk_sub ar M M1 T SCRf 16 SCRo STK MGM1). clear; lia. exact HSo0. clear - HSf1; lia. exact T16'.
  - replace (3%bv : bv 5) with (reg 3) by (apply bv_eq; reflexivity). rewrite (KS1 3%nat) by inl. replace (reg 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact G3.
  - apply (stksh_off M M1 (T - 16 - SCRo) T SSH OFF).
    { pose proof (Z_div_mod_eq_full (T - 16) 16) as E1. pose proof (Z_div_mod_eq_full SCRo 8) as E2. rewrite T16' in E1. rewrite HSo8 in E2.
      replace (T - 16 - SCRo) with (((T - 16) / 16 * 2 - SCRo / 8) * 8) by (clear - E1 E2; lia). apply Z_mod_mult. }
    exact TCE. clear - TCE SPT; lia. exact TOP47. clear - SPT; lia. exact T46.
  - exact F1.
  - exact F2.
  - exact F3.
  - eapply ffrs_le. exact FRS. clear; lia.
  - intros a Ha. rewrite OFF. apply IMG. exact Ha. clear - Ha; lia. clear - Ha T46; lia.
  - exact XA1.
  - exact AOX.
  - exact XSZ1.
  - exact BOK1.
  - exact AOB.
  - exact BSZ1.
  - exact APART.
  - exact CAPB.
  - exact DYN3.
  - pose proof (as0_layout2_of L C LY) as LY2. destruct HK1 as (HK10 & HKB).
    assert (B0 : 0 <= bytes1 capb). { apply HKB. unfold capb, L5.bo_cap. destruct BOK as (BB & _). destruct BB as (_ & _ & _ & BST). destruct (L5.bo_st bb). clear; lia. clear - BST; lia. }
    exact (proj1 (acredit_for_split L cr (K1 + 1) (bytes1 capb + 64) K1 (bytes1 capb) LY2 CRF ltac:(clear - HK10; lia) ltac:(clear - B0; lia))).
  - apply XSP. exact OFF.
  - (* [comment removed for export] *)
    intros fx' R' M' model' LB' cr' LK' A' RP A10' XAF BB' BL' LEN1 CRA AHP RT IA AM' LKI HH'.
    destruct XAF as (bx & wx & BX & LX & NEG & XST).
    pose proof AHP as (EK & _ & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND' & _).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (T - 16) SCRo a -> ~ (xo <= a < xo + 32) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hc Hx. apply EK. split. exact Ha. split. exact Hc. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. exact Hx. }
    pose proof (sobj_facts L ar C HI LY HIok LB FF LK cr A M model co 32 T (T - 16) SCRo HH SOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - TCE HSo0; lia) ltac:(clear; lia))
      as ((CO1 & _ & CO3 & _) & _ & _ & _ & _ & COCL & COSHCL).
    pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 (T - 16) SCRo HH AOX ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & _ & _ & _ & XOSHCL).
    change (32 / 8) with 4 in COSHCL, XOSHCL.
    assert (SHR : forall o j, 0x634000 <= o -> o + 32 <= 2 ^ 47 -> 0 <= j < 4 -> 0 <= o / 8 + SB + j < 2 ^ 64 /\ ~ (xo <= o / 8 + SB + j < xo + 32) /\ ~ (T - 16 <= o / 8 + SB + j < T)).
    { intros o j Ho1 Ho2 Hj. assert (o / 8 + 4 <= 2 ^ 47 / 8). { replace (o / 8 + 4) with ((o + 32) / 8). apply Z.div_le_mono; clear - Ho2; lia. replace (o + 32) with (o + 4 * 8) by (clear; lia). apply Z.div_add. clear; lia. }
      change (2 ^ 47 / 8) with 17592186044416 in H0. pose proof (Z.div_pos o 8 ltac:(clear - Ho1; lia) ltac:(clear; lia)). unfold SB. clear - H0 H1 Hj XOSH XO3 T46. lia. }
    assert (AGF : forall i, T - 16 <= i < T -> M' (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
    { intros i Hi. apply KEEP. clear - Hi TR0 TR1; lia. apply stack_client. clear - Hi TCE HSo0 TR1; lia. clear - Hi; lia. clear - Hi XO2 TCE HSo0; lia. }
    assert (AGco : forall i, co <= i < co + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. rewrite KEEP. apply OFF. clear - Hi COR0 CO3; lia. clear - Hi SO1; lia. clear - Hi COR0 CO3; lia.
      replace i with (co + (i - co)) by (clear; lia). apply COCL. clear - Hi; lia. clear - Hi XO2 TCE HSo0 SO1; lia. }
    assert (AGcs : forall j, 0 <= j < 4 -> M' (Z_to_bv 64 (S co + j)) = M (Z_to_bv 64 (S co + j))).
    { intros j Hj. destruct (SHR co j CO1 CO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite KEEP. apply OFF. exact Q1. exact Q3. exact Q1. apply COSHCL. exact Hj. exact Q2. }
    assert (C16' : L5.u64_at RSEGS M' (T - 16) rt8).
    { eapply (L5C.u64_at_agree RSEGS M1 M'). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C16. }
    assert (C8' : L5.u64_at RSEGS M' (T - 8) OMF1_RET).
    { eapply (L5C.u64_at_agree RSEGS M1 M'). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C8. }
    assert (STK' : astk ar M' T (COPY_SCR + 32)).
    { pose proof (astk_after L ar C HI HIok LB FF LK cr A M M1 M' _ T SCRf (T - 16) SCRo _ HH STK MGM1 AHP ltac:(clear - HSf1; lia) ltac:(clear; lia) ltac:(clear - HSf1 HSo0; lia)) as X.
      pose proof (astk_sub ar M' M' T SCRf 0 (COPY_SCR + 32) X ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear - CSV; lia) ltac:(clear - HSf2; lia)) as Y.
      replace (T - 0) with T in Y by (clear; lia). apply Y. exact A16. }
    assert (XSZ' : shadow_zero M' xo 4).
    { intros j Hj. unfold byte_at. destruct (SHR xo j XO1 XO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite KEEP. apply XSZ1. exact Hj. exact Q1. apply XOSHCL. exact Hj. exact Q2. }
    apply (omf_tail Hcp fx' R' M' model' K LB' FF LK' cr' A' co xo T OMF1_RET rt8 fbo bx wx HH' AM' HK).
    + rewrite (cs_of_preserved R1 R' 2 RP) by (unfold cs_all; inl). exact A2.
    + rewrite (cs_of_preserved R1 R' 8 RP) by (unfold cs_all; inl). exact A8.
    + rewrite <- r10. exact A10'.
    + rewrite (cs_of_preserved R1 R' 4 RP) by (unfold cs_all; inl). rewrite (KS1 4%nat) by inl. rewrite <- r4. exact G4.
    + exact T32.
    + exact STK'.
    + exact C16'.
    + exact C8'.
    + split. unfold OMF1_RET; clear; lia. reflexivity.
    + unfold rt8. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X.
    + apply (ffrk_le 1 FF LK' D1 2). apply (ffrk_shrink 1 FF LK LK' D1 F1 LKI ND'). exact HD1.
    + eapply ffrs_le. exact FRS. clear; lia.
    + eapply (L5C.u8_at_agree RSEGS M M'). intros i Hi; apply AGco; clear - Hi; lia. clear - COR0; lia. clear - CO3; lia. exact CO8.
    + exact FBO.
    + exact SOB.
    + eapply (L5C.defined_agree M M'). intros i Hi; apply AGco; exact Hi. exact CODEF.
    + intros j Hj. unfold byte_at. rewrite AGcs by exact Hj. apply COSZ. exact Hj.
    + exact BX.
    + exact LX.
    + exact AOX.
    + exact XSZ'.
    + intros cap q EST. rewrite EST in XST. destruct XST as (-> & -> & _). left. reflexivity.
    + intros DYN. destruct BX as (_ & _ & _ & BST). unfold L5.bo_dyn in DYN. unfold L5.bo_cap. destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:EST.
      { destruct BST as (TB & _). rewrite TB in DYN. discriminate DYN. }
      destruct XST as (-> & _ & _). split. clear; lia.
      pose proof (as0_layout2_of L C LY) as LY2. destruct HK1 as (HK10 & HKB).
      assert (B0 : 0 <= bytes1 capb). { apply HKB. unfold capb, L5.bo_cap. destruct BOK as (BB & _). destruct BB as (_ & _ & _ & BST'). destruct (L5.bo_st bb). clear; lia. clear - BST'; lia. }
      pose proof (proj2 (acredit_for_split L cr (K1 + 1) (bytes1 capb + 64) K1 (bytes1 capb) LY2 CRF ltac:(clear - HK10; lia) ltac:(clear - B0; lia))) as X.
      replace (K1 + 1 - K1) with 1 in X by (clear; lia). replace (bytes1 capb + 64 - bytes1 capb) with 64 in X by (clear; lia).
      pose proof (acredit_for_mono L _ _ 1 64 X CRA) as X'.
      exact (proj1 (acredit_for_take L cr' 1 64 64 LY2 X' ltac:(clear; lia) ltac:(clear; lia))).
    + intros fx3 Rc R2 R3 M3 model3 g LB3 cr3 LK3 A3 CP E2 E8 KS RT3 IA3 AM3 LKI3 HH3.
      apply (KN fx3 R3 M' M3 model3 LB' LB3 cr' cr3 LK' LK3 A3 bx wx g).
      * exact BX.
      * exact LX.
      * exact NEG.
      * exact XST.
      * exact BB'.
      * exact BL'.
      * exact LEN1.
      * exact CRA.
      * apply (ahpres_friend LB FF LK cr A M M1 M' model T SCRo _ HH OFF MGM1 AHP DEF16 TCE HSo0). clear - TR1; lia. exact SPT.
      * exact LKI.
      * apply (copy_post_up LB' FF LK3 cr' M' M3 Rc R2 R R3 co xo T fbo bx wx g LB3 cr3 CP).
        { apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
          destruct Hk as [<-|Hk]. { rewrite E2. rewrite <- r2. symmetry. exact G2. }
          destruct Hk as [<-|Hk]. { rewrite (KS 3%nat) by inl. rewrite (cs_of_preserved R1 R' 3 RP) by (unfold cs_all; inl). apply KS13. inl. }
          destruct Hk as [<-|Hk]. { rewrite (KS 4%nat) by inl. rewrite (cs_of_preserved R1 R' 4 RP) by (unfold cs_all; inl). apply KS13. inl. }
          destruct Hk as [<-|Hk]. { rewrite E8. unfold rt8. apply Z_to_bv_bv_unsigned. }
          repeat (destruct Hk as [<-|Hk]; [ rewrite (KS _) by inl; rewrite (cs_of_preserved R1 R' _ RP) by (unfold cs_all; inl); apply KS13; inl |]). destruct Hk. }
        { eapply (L5C.defined_agree M1 M'). intros i Hi; apply AGF; clear - Hi; lia. exact DEF16. }
        { clear - TCE HSo0; lia. } { clear - TR1; lia. } { exact (proj1 SPT). }
      * exact LKI3.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT. exact RT3.
      * intros x Hx. apply IA3. apply IA. exact Hx.
      * exact AM3.
      * exact HH3.
  - (* [comment removed for export] *)
    intros fx' R' M' model' LB' cr' LK' A' LR E2L XA' BB' BL' AHP RT IA AM' HH'.
    apply (KE2 fx' R' M' model' LB' cr' LK' A').
    + exact (landed_to_preserved R R1 R' T LR G2 KS13).
    + replace (T - 16 + 16) with T in E2L by (clear; lia). exact E2L.
    + exact XA'.
    + exact BB'.
    + exact BL'.
    + apply (ahpres_friend LB FF LK cr A M M1 M' model T SCRo _ HH OFF MGM1 AHP DEF16 TCE HSo0). clear - TR1; lia. exact SPT.
    + eapply L5LZ.model_rt_trans. exact RT1. exact RT.
    + exact IA.
    + exact AM'.
    + exact HH'.
  - (* [comment removed for export] *)
    intros fx' R' M' model' LB' cr' LK' A' fbx' nx qx cr1 LR BX' FRQ CRA E3L BB' BL' AHP RT IA AM' HH'.
    apply (KE3 fx' R' M' model' LB' cr' LK' A' fbx' nx qx cr1).
    + exact (landed_to_preserved R R1 R' T LR G2 KS13).
    + exact BX'.
    + exact FRQ.
    + exact CRA.
    + replace (T - 16 + 16) with T in E3L by (clear; lia). exact E3L.
    + exact BB'.
    + exact BL'.
    + apply (ahpres_friend LB FF LK cr A M M1 M' model T SCRo _ HH OFF MGM1 AHP DEF16 TCE HSo0). clear - TR1; lia. exact SPT.
    + eapply L5LZ.model_rt_trans. exact RT1. exact RT.
    + exact IA.
    + exact AM'.
    + exact HH'.
Qed.

Theorem opmodf2_ok :
  opmod2A_spec L ar HI SCRo D1 D2 D3 K2 bytes2 -> copy_stk16_spec L ar HI ->
  opmodf2_spec L ar HI SCRo SCRf D1 D2 D3 K2 bytes2.
Proof.
  intros Hom2 Hcp fx R M model K LB FF LK cr A co yo ao T r fba fbo by_ wy capy HH AM HK G10 G11 G12 G1 RA G2 T32 G4 STK SSH F1 F2 F3 FRS IMG YOK AOY YSZ LEN1 CAPY AOK AOA ASZ APART RS CRF KN.
  destruct RS as (CO8 & FBO & SOB & CODEF & COSZ). destruct HSo as (HSo0 & HSo8). destruct HSf as (HSf1 & HSf2).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (CSV : COPY_SCR = 4256) by reflexivity.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _ & _ & _ & _ & _ & _ & _ & _ & TOP47 & _ & ND & _).
  pose proof SOB as (SO1 & SO2 & SO8).
  assert (TR : 0 <= T < 2 ^ 64 /\ 140735332487184 <= T <= 140737488355328 /\ 4096 <= co <= 140737488355296 /\ 0 <= co < 2 ^ 64 /\ ahl_ceil ar <= T - 16 - SCRo /\ 2 ^ 46 <= T - 16)
    by (clear - SLO SHI SPT SO1 SO2 HSo0 HSf1 HSf2 CSV; lia).
  destruct TR as (TR0 & TR1 & COR & COR0 & TCE & T46).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model yo 32 (T - 16) SCRo HH AOY ltac:(clear; lia) ltac:(reflexivity)) as ((YO1 & YO2 & YO3 & YO8 & _) & YOSH & _ & _ & _ & _ & YOSHCL).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model ao 32 0 0 HH AOA ltac:(clear; lia) ltac:(reflexivity)) as ((AO1 & AO2 & AO3 & AO8 & _) & AOSH & _).
  change (32 / 8) with 4 in YOSHCL.
  set (H := ahid A model) in *.
  assert (W16 : L5.writable RSEGS (mrestrict H M) (T - 16) 16).
  { apply (proj2 (writable_vis H M (T - 16) 16 (VIS (T - 16) 16 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))).
    eapply (astk_writable ar M T). exact STK. clear - HSf2 CSV; lia. clear; lia. clear; lia. }
  pose proof (omfA_conc fx R (mrestrict H M) (fun j => match j with 2%nat => T | 33%nat => co | 34%nat => yo | 35%nat => ao | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P TR0 COR0 ltac:(clear - YO1 YO3; lia) ltac:(clear - AO1 AO3; lia) ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r10; exact G10) ltac:(rewrite <- r11; exact G11) ltac:(rewrite <- r12; exact G12)
              TR1 T32 W16 ltac:(clear - YO1 YO3; lia) YO8)
    as (fx1 & R1 & M1v & MG1 & _ & FZ1 & (MS1 & KS1 & A1 & A2 & A8 & A10 & A11 & AC16 & AC8)). clear P.
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R OMF R1 OPMOD M1v (fun a => T - 16 <= a < T) K HH AM MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa TCE HSo0 TR1; lia. clear; lia. clear - Wa TCE HSo0 SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (OFF : offw (T - 16) T M M1) by exact FRM1.
  set (rt8 := bv_unsigned (getr R (reg 8))) in *.
  assert (C16 : L5.u64_at RSEGS M1 (T - 16) rt8).
  { apply (proj1 (u64_at_vis H M1 (T - 16) rt8 (VIS (T - 16) 8 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))). unfold H. rewrite VIS1. exact AC16. }
  assert (C8 : L5.u64_at RSEGS M1 (T - 8) r).
  { apply (proj1 (u64_at_vis H M1 (T - 8) r (VIS (T - 8) 8 ltac:(clear - TCE HSo0; lia) ltac:(clear - TR0; lia)) ltac:(clear - TR1; lia) ltac:(clear - TR0; lia))). unfold H. rewrite VIS1.
    assert (ER : bv_unsigned (getr R (reg 1)) = r) by (rewrite <- r1, G1; apply L5.unsigned_lit; clear - RA; destruct RA; lia). rewrite ER in AC8. exact AC8. }
  assert (DEF16 : L5.defined M1 (T - 16) 16).
  { eapply L5.defined_grows. exact MGM1. intros i Hi. replace (T - 16 + i) with (T - SCRf + (SCRf - 16 + i)) by (clear; lia). apply DSCR. clear - Hi HSf1 HSo0; lia. }
  assert (T16 : (T - 16) mod 32 = 16).
  { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 16) with (16 + (T / 32 - 1) * 32) by (clear - E; lia). rewrite Z_mod_plus_full. reflexivity. }
  assert (T16' : (T - 16) mod 16 = 0).
  { pose proof (Z_div_mod_eq_full T 32) as E. rewrite T32 in E. replace (T - 16) with ((T / 32 * 2 - 1) * 16) by (clear - E; lia). apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (SHR : forall o j, 0x634000 <= o -> o + 32 <= 2 ^ 47 -> 0 <= j < 4 -> 0 <= o / 8 + SB + j < 2 ^ 64 /\ 2147450880 <= o / 8 + SB + j < 2147450880 + 17592186044416 /\ ~ (T - 16 <= o / 8 + SB + j < T)).
  { intros o j Ho1 Ho2 Hj. assert (o / 8 + 4 <= 2 ^ 47 / 8). { replace (o / 8 + 4) with ((o + 32) / 8). apply Z.div_le_mono; clear - Ho2; lia. replace (o + 32) with (o + 4 * 8) by (clear; lia). apply Z.div_add. clear; lia. }
    change (2 ^ 47 / 8) with 17592186044416 in H0. pose proof (Z.div_pos o 8 ltac:(clear - Ho1; lia) ltac:(clear; lia)). unfold SB. clear - H0 H1 Hj T46. lia. }
  assert (YSZ1 : shadow_zero M1 yo 4).
  { intros j Hj. unfold byte_at. destruct (SHR yo j YO1 YO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite OFF. apply YSZ. exact Hj. exact Q1. exact Q3. }
  assert (ASZ1 : shadow_zero M1 ao 4).
  { intros j Hj. unfold byte_at. destruct (SHR ao j AO1 AO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite OFF. apply ASZ. exact Hj. exact Q1. exact Q3. }
  assert (AOK1 : a_ok M1 ao fba).
  { destruct AOK as (B & TB). split. 2: exact TB. eapply (L5C.big_at_agree RSEGS M M1). 4: exact B. apply (offw_agree _ _ _ _ _ _ OFF). clear - AO1; lia. clear - AO3; lia. left; clear - AO2 TCE HSo0; lia. clear - AO1; lia. clear - AO3; lia. }
  (* [comment removed for export] *)
  assert (YBLK : match L5.bo_st by_ with L5.BInl _ _ => True | L5.BDyn cap q => 4096 <= q /\ q + 8 * cap <= ahl_ceil ar /\ (q + 8 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= q) /\ Z.of_nat (L5.bo_len by_) <= cap /\ 0 < cap end).
  { destruct YOK as (BB & _ & _ & BLK). destruct BB as (_ & _ & _ & BST). destruct (L5.bo_st by_) as [v0 v1|cap q]. exact I.
    destruct BST as (_ & _ & _ & LENC & CAPR & _). destruct BLK as (BLK & _).
    pose proof (proj1 (WB (q, 8 * cap) BLK)) as (Q0 & _ & _ & _ & QC & QA). cbn [fst snd] in Q0, QC, QA. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QA.
    split. exact Q0. split. exact QC. split. clear - QA; lia. split. exact LENC. clear - CAPR; lia. }
  assert (YOK1 : y_ok LB M1 yo by_ wy).
  { destruct YOK as (BB & BL & RED & BLK). split.
    { eapply (L5C.big_at_agree RSEGS M M1). 4: exact BB. apply (offw_agree _ _ _ _ _ _ OFF). clear - YO1; lia. clear - YO3; lia. left; clear - YO2 TCE HSo0; lia. clear - YO1; lia. clear - YO3; lia. }
    split. 2: split; [exact RED | exact BLK].
    destruct BL as (L1 & L2 & L3). split. exact L1. split. exact L2.
    destruct (L5.bo_st by_) as [v0 v1|cap q] eqn:EST. exact L3. destruct YBLK as (Q0 & QC & _ & LENC & _).
    eapply (L5C.limbs_at_agree RSEGS M M1). 4: exact L3. apply (offw_agree _ _ _ _ _ _ OFF). clear - Q0; lia. rewrite L1; clear - QC LENC TCE HSo0 TR0; lia. left; rewrite L1; clear - QC LENC TCE HSo0; lia.
    clear - Q0; lia. rewrite L1; clear - QC LENC TCE HSo0 TR0; lia. }
  apply (Hom2 fx1 R1 M1 model1 K LB FF LK cr A yo ao (T - 16) 0x8eb34 fba by_ wy HH1 AM1 HK).
  - rewrite r10. exact A10.
  - rewrite r11. exact A11.
  - rewrite r1. exact A1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact A2.
  - exact T16.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - apply (astk_sub ar M M1 T SCRf 16 SCRo STK MGM1). clear; lia. exact HSo0. clear - HSf1; lia. exact T16'.
  - apply (stksh_off M M1 (T - 16 - SCRo) T SSH OFF).
    { pose proof (Z_div_mod_eq_full (T - 16) 16) as E1. pose proof (Z_div_mod_eq_full SCRo 8) as E2. rewrite T16' in E1. rewrite HSo8 in E2.
      replace (T - 16 - SCRo) with (((T - 16) / 16 * 2 - SCRo / 8) * 8) by (clear - E1 E2; lia). apply Z_mod_mult. }
    exact TCE. clear - TCE SPT; lia. exact TOP47. clear - SPT; lia. exact T46.
  - exact F1.
  - exact F2.
  - exact F3.
  - eapply ffrs_le. exact FRS. clear; lia.
  - intros a Ha. rewrite OFF. apply IMG. exact Ha. clear - Ha; lia. clear - Ha T46; lia.
  - exact YOK1.
  - exact AOY.
  - exact YSZ1.
  - exact LEN1.
  - exact CAPY.
  - exact AOK1.
  - exact AOA.
  - exact ASZ1.
  - exact APART.
  - pose proof (as0_layout2_of L C LY) as LY2. destruct HK2 as (HK20 & HKB).
    assert (B0 : 0 <= bytes2 capy). { apply HKB. unfold capy, L5.bo_cap. destruct (L5.bo_st by_). clear; lia. clear - YBLK; lia. }
    exact (proj1 (acredit_for_split L cr (K2 + 1) (bytes2 capy + Z.max 64 (8 * capy)) K2 (bytes2 capy) LY2 CRF ltac:(clear - HK20; lia) ltac:(clear - B0; lia))).
  - intros fx' R' M' model' LB' cr' LK' A' RP A10' YAF AOK' CRA AHP RT IA AM' LKI HH'.
    destruct YAF as (by' & wy' & BY & LY' & YST).
    pose proof AHP as (EK & _ & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND' & _).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (T - 16) SCRo a -> ~ (yo <= a < yo + 32) ->
                   match L5.bo_st by_ with L5.BInl _ _ => True | L5.BDyn cap q => ~ (q <= a < q + 8 * cap) end -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hc Hy Hq. apply EK. split. exact Ha. split. exact Hc. intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. exact Hy.
      unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st by_) as [v0 v1|cap q]. clear - Hy; lia. exact Hq. }
    pose proof (sobj_facts L ar C HI LY HIok LB FF LK cr A M model co 32 T (T - 16) SCRo HH SOB ltac:(clear; lia) ltac:(reflexivity) SPT ltac:(clear - TCE HSo0; lia) ltac:(clear; lia))
      as ((CO1 & _ & CO3 & _) & _ & _ & _ & _ & COCL & COSHCL).
    change (32 / 8) with 4 in COSHCL.
    assert (AGF : forall i, T - 16 <= i < T -> M' (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)).
    { intros i Hi. apply KEEP. clear - Hi TR0 TR1; lia. apply stack_client. clear - Hi TCE HSo0 TR1; lia. clear - Hi; lia. clear - Hi YO2 TCE HSo0; lia.
      destruct (L5.bo_st by_). exact I. clear - Hi YBLK TCE HSo0; lia. }
    assert (AGco : forall i, co <= i < co + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. rewrite KEEP. apply OFF. clear - Hi COR0 CO3; lia. clear - Hi SO1; lia. clear - Hi COR0 CO3; lia.
      replace i with (co + (i - co)) by (clear; lia). apply COCL. clear - Hi; lia. clear - Hi YO2 TCE HSo0 SO1; lia.
      destruct (L5.bo_st by_). exact I. clear - Hi YBLK TCE HSo0 SO1; lia. }
    assert (AGcs : forall j, 0 <= j < 4 -> M' (Z_to_bv 64 (S co + j)) = M (Z_to_bv 64 (S co + j))).
    { intros j Hj. destruct (SHR co j CO1 CO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite KEEP. apply OFF. exact Q1. exact Q3. exact Q1. apply COSHCL. exact Hj. clear - Q2 YOSH YO3; lia.
      destruct (L5.bo_st by_). exact I. clear - Q2 YBLK; lia. }
    assert (C16' : L5.u64_at RSEGS M' (T - 16) rt8).
    { eapply (L5C.u64_at_agree RSEGS M1 M'). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C16. }
    assert (C8' : L5.u64_at RSEGS M' (T - 8) r).
    { eapply (L5C.u64_at_agree RSEGS M1 M'). intros i Hi; apply AGF; clear - Hi; lia. clear - TR1; lia. clear - TR0; lia. exact C8. }
    assert (STK' : astk ar M' T (COPY_SCR + 32)).
    { pose proof (astk_after L ar C HI HIok LB FF LK cr A M M1 M' _ T SCRf (T - 16) SCRo _ HH STK MGM1 AHP ltac:(clear - HSf1; lia) ltac:(clear; lia) ltac:(clear - HSf1 HSo0; lia)) as X.
      pose proof (astk_sub ar M' M' T SCRf 0 (COPY_SCR + 32) X ltac:(intros x Hx; exact Hx) ltac:(clear; lia) ltac:(clear - CSV; lia) ltac:(clear - HSf2; lia)) as Y.
      replace (T - 0) with T in Y by (clear; lia). apply Y. exact A16. }
    assert (YSZ' : shadow_zero M' yo 4).
    { intros j Hj. unfold byte_at. destruct (SHR yo j YO1 YO3 Hj) as (Q1 & Q2 & Q3). unfold S. rewrite KEEP. apply YSZ1. exact Hj. exact Q1. apply YOSHCL. exact Hj. clear - Q2 YOSH YO3; lia.
      destruct (L5.bo_st by_). exact I. clear - Q2 YBLK; lia. }
    apply (omf_tail Hcp fx' R' M' model' K LB' FF LK' cr' A' co yo T r rt8 fbo by' wy' HH' AM' HK).
    + rewrite (cs_of_preserved R1 R' 2 RP) by (unfold cs_all; inl). exact A2.
    + rewrite (cs_of_preserved R1 R' 8 RP) by (unfold cs_all; inl). exact A8.
    + rewrite <- r10. exact A10'.
    + rewrite (cs_of_preserved R1 R' 4 RP) by (unfold cs_all; inl). rewrite (KS1 4%nat) by inl. rewrite <- r4. exact G4.
    + exact T32.
    + exact STK'.
    + exact C16'.
    + exact C8'.
    + exact RA.
    + unfold rt8. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X.
    + apply (ffrk_le 1 FF LK' D1 2). apply (ffrk_shrink 1 FF LK LK' D1 F1 LKI ND'). exact HD1.
    + eapply ffrs_le. exact FRS. clear; lia.
    + eapply (L5C.u8_at_agree RSEGS M M'). intros i Hi; apply AGco; clear - Hi; lia. clear - COR0; lia. clear - CO3; lia. exact CO8.
    + exact FBO.
    + exact SOB.
    + eapply (L5C.defined_agree M M'). intros i Hi; apply AGco; exact Hi. exact CODEF.
    + intros j Hj. unfold byte_at. rewrite AGcs by exact Hj. apply COSZ. exact Hj.
    + exact BY.
    + exact LY'.
    + exact AOY.
    + exact YSZ'.
    + intros cap' q' EST'. rewrite EST' in YST. destruct YOK as (_ & _ & _ & BLK). destruct (L5.bo_st by_) as [v0 v1|cap q].
      { destruct YST as (-> & -> & _). left. reflexivity. }
      { destruct YST as (-> & -> & ->). exact (proj1 BLK). }
    + intros DYN. destruct BY as (_ & _ & _ & BST). unfold L5.bo_dyn in DYN. unfold L5.bo_cap. destruct (L5.bo_st by') as [v0' v1'|cap' q'] eqn:EST'.
      { destruct BST as (TB & _). rewrite TB in DYN. discriminate DYN. }
      pose proof (as0_layout2_of L C LY) as LY2. destruct HK2 as (HK20 & HKB).
      assert (B0 : 0 <= bytes2 capy). { apply HKB. unfold capy, L5.bo_cap. destruct (L5.bo_st by_). clear; lia. clear - YBLK; lia. }
      pose proof (proj2 (acredit_for_split L cr (K2 + 1) (bytes2 capy + Z.max 64 (8 * capy)) K2 (bytes2 capy) LY2 CRF ltac:(clear - HK20; lia) ltac:(clear - B0; lia))) as X.
      replace (K2 + 1 - K2) with 1 in X by (clear; lia). replace (bytes2 capy + Z.max 64 (8 * capy) - bytes2 capy) with (Z.max 64 (8 * capy)) in X by (clear; lia).
      pose proof (acredit_for_mono L _ _ 1 _ X CRA) as X'.
      assert (CB : 0 < cap' /\ 8 * cap' <= Z.max 64 (8 * capy) /\ 8 * cap' <= 2 ^ 27).
      { unfold capy, L5.bo_cap in *. destruct (L5.bo_st by_) as [v0 v1|cap q]. destruct YST as (-> & _). clear; lia. destruct YST as (-> & _). clear - YBLK CAPY; lia. }
      split. exact (proj2 (proj2 CB)).
      exact (proj1 (acredit_for_take L cr' 1 (Z.max 64 (8 * capy)) (8 * cap') LY2 X' ltac:(clear; lia) ltac:(clear - CB; lia))).
    + intros fx3 Rc R2 R3 M3 model3 g LB3 cr3 LK3 A3 CP E2 E8 KS RT3 IA3 AM3 LKI3 HH3.
      apply (KN fx3 R3 M' M3 model3 LB' LB3 cr' cr3 LK' LK3 A3 by' wy' g).
      * exact BY.
      * exact LY'.
      * exact YST.
      * exact AOK'.
      * exact CRA.
      * apply (ahpres_friend LB FF LK cr A M M1 M' model T SCRo _ HH OFF MGM1 AHP DEF16 TCE HSo0). clear - TR1; lia. exact SPT.
      * exact LKI.
      * apply (copy_post_up LB' FF LK3 cr' M' M3 Rc R2 R R3 co yo T fbo by' wy' g LB3 cr3 CP).
        { apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
          destruct Hk as [<-|Hk]. { rewrite E2. rewrite <- r2. symmetry. exact G2. }
          destruct Hk as [<-|Hk]. { rewrite (KS 3%nat) by inl. rewrite (cs_of_preserved R1 R' 3 RP) by (unfold cs_all; inl). apply KS1. inl. }
          destruct Hk as [<-|Hk]. { rewrite (KS 4%nat) by inl. rewrite (cs_of_preserved R1 R' 4 RP) by (unfold cs_all; inl). apply KS1. inl. }
          destruct Hk as [<-|Hk]. { rewrite E8. unfold rt8. apply Z_to_bv_bv_unsigned. }
          repeat (destruct Hk as [<-|Hk]; [ rewrite (KS _) by inl; rewrite (cs_of_preserved R1 R' _ RP) by (unfold cs_all; inl); apply KS1; inl |]). destruct Hk. }
        { eapply (L5C.defined_agree M1 M'). intros i Hi; apply AGF; clear - Hi; lia. exact DEF16. }
        { clear - TCE HSo0; lia. } { clear - TR1; lia. } { exact (proj1 SPT). }
      * exact LKI3.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT. exact RT3.
      * intros x Hx. apply IA3. apply IA. exact Hx.
      * exact AM3.
      * exact HH3.
Qed.

End Proofs.
End WithIface.

End SCFG_1.
End L5BOMF.
