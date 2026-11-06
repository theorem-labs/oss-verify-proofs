(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun AsanPlanCore AsanPlanSound As0PlanKit As0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5AResizeP L5AResize L5DivLeafSpecsA L5DivSpecsA L5OpmodSpecsA L5DivInnerSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5ARzHugeP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ARZH.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ARZHP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
Lemma byte_of_u8 M a v : L5.u8_at RSEGS M a v -> (a < 0x10000 \/ 0x633000 <= a) -> 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros U0 HA Ha. unfold L5.u8_at in U0. cbn [rdn] in U0.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  - inversion U0. reflexivity.
  - exfalso. unfold seg_rom in U0. unfold memory_read in U0. change (Z.of_N 1) with 1 in U0.
    rewrite (as0_in_hull (Z_to_bv 64 a)) in U0. discriminate U0.
    rewrite L5.unsigned_lit by lia. unfold APS.in_hull. cbn. destruct HA; [apply andb_false_intro1 | apply andb_false_intro2]; apply Z.leb_gt || apply Z.ltb_ge; lia.
Qed.
Lemma u8_of_byte (Mk : word -> option byte) a v : byte_at Mk a v -> L5.u8_at RSEGS Mk a v.
Proof. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.

Theorem resize_huge_ok : L5DIA.resize_hugeA_spec L ar HI.
Proof.
  intros fx R M model K LB FF LK cr A o sp r n b HH AM HK G10 G11 Hn G1 RA G2 A32 G4 STK ROOM RS OB DYN AOB SZ KONT.
  unfold L5DIA.MAX_SIZE in Hn.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487296 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA16 : (sp - 128) mod 16 = 0 /\ (sp - 128) mod 32 = 0).
  { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (L5ARZ.statics_vis L ar C HI LY HIok LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp RESIZE_SCR HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  assert (LENB : (len <= 2)%nat \/ exists cap q, sto = L5.BDyn cap q /\ Z.of_nat len <= cap <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. left. exact (proj1 (proj2 (proj2 (proj2 OST)))). right. exists cap, q. split. reflexivity. clear - OST. decompose [and] OST. lia. }
  assert (LEN : 0 <= Z.of_nat len <= 2 ^ 27) by (clear - LENB; destruct LENB as [X|(c & q & _ & X)]; lia).
  assert (W128 : L5.writable RSEGS MV (sp - 128) 128).
  { apply (proj2 (writable_vis H M (sp - 128) 128 (VIS (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (L5ARZP.rzA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1v & MG1 & AFR & AFZ & (AMS & AKS & AR1 & AR2 & AR8 & AR9 & AR10 & AR11 & AR12 & AR19 & AR20 & AR24 & AQ_V2nat & AQ_V2nat_1 & AQ_V2nat_2 & AQ_V2nat_3 & AQ_V2nat_4 & AQ_V2nat_5 & AQ_V2nat_6 & AQ_V2nat_7 & AQ_V2nat_8 & AQ_V2nat_9 & AQ_V2nat_10 & AQ_V2nat_11 & AQ_V2nat_12)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R RESIZE R1 SM1 M1v (fun a => sp - 128 <= a < sp) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sp - 128). { rewrite r2, AR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, AR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 sp RESIZE_SCR 128 512 STK MGM1). clear; lia. clear; lia. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
    exact (proj1 SA16).
  - clear - ROOM. unfold ffr in ROOM. unfold ff_room. lia.
  - intros f Hf. rewrite U2. specialize (RS f Hf). clear - RS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, AR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (sp - 128 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp RESIZE_SCR).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sp - 128) 512 HH STK MGM1 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _ & _ & VFSSH2 & _).
    pose proof (L5ARZ.statics_vis L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    set (FF' := (F, 1, sp - 128 + 32) :: FF) in *.
    pose proof (aobj_facts L ar C HI LY HIok LB FF' LK2 cr A M2 model2 o 32 0 0 HH2 (aobj_cons FF _ o 32 AOB) ltac:(clear; lia) ltac:(reflexivity))
      as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _). change (32 / 8) with 4 in OVSH2. fold H2 in OVIS2, OVSH2.
    assert (AG2 : forall a, (sp - 128 <= a < sp \/ o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV2 (Z_to_bv 64 a) = (if (sp - 128 <=? a) then M1v (Z_to_bv 64 a) else M (Z_to_bv 64 a))).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      unfold MV2. rewrite (mrestrict_visible H2 M2).
      2:{ destruct Ra as [Ra|[Ra|Ra]]. replace a with ((sp - 128) + (a - (sp - 128))) by (clear; lia). apply (VIS2 (sp - 128) 128). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia. }
      rewrite (proj1 PRES2 a Ha).
      2:{ destruct Ra as [Ra|[Ra|Ra]]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. apply (obj_client L ar LB FF _ _ o 32 a AOB). exact Ra.
          apply (aclient_narrow L ar LB FF sp RESIZE_SCR). replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia.
          clear - Ra OR SLO SPT; unfold SB in *; lia. }
      destruct (Z.leb_spec (sp - 128) a) as [Hs|Hs].
      - rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with ((sp - 128) + (a - (sp - 128))) by (clear; lia). apply (VIS (sp - 128) 128). clear - SLO; lia. clear - SPR; lia.
        clear - Ra Hs OR SLO SPT OBIG; unfold SB in *; lia.
      - apply FRM1. exact Ha. clear - Hs; lia. }
    assert (XC2 : forall a v, sp - 128 <= a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj. rewrite AG2. 2: clear - Ha Hj; lia.
      destruct (Z.leb_spec (sp - 128) j) as [Hs|Hs]. reflexivity. exfalso; clear - Ha Hj Hs; lia. }
    assert (XO2 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Ha OR; lia. intros j Hj. rewrite AG2. 2: clear - Ha Hj; lia.
      destruct (Z.leb_spec (sp - 128) j) as [Hs|Hs]. exfalso; clear - Ha Hj Hs OR SLO SPT; lia. reflexivity. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4).
    { intros i Hi. rewrite AG2. 2: clear - Hi; lia. destruct (Z.leb_spec (sp - 128) (o / 8 + SB + i)) as [Hs|Hs]. exfalso; clear - Hi Hs OR OBIG SLO SPT; unfold SB in *; lia.
      unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
    assert (OW2 : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    assert (W128b : L5.writable RSEGS MV2 (sp - 128) 128).
    { apply (proj2 (writable_vis H2 M2 (sp - 128) 128 (VIS2 (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 sp). exact ASTK2. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp RESIZE_SCR o 32 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp 0 (sp - 128) 128 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in OF, SF. change (ff_bytes 1 / 8) with 16 in OFSH, SFSH.
    assert (OSHF : o / 8 + SB + 4 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) by (clear - OF F8 OR; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    assert (RS2 : forall k, In k [18; 21; 22; 23; 25; 26; 27]%nat -> getr R2 (reg k) = getr R (reg k)).
    { intros k Hk. rewrite (cs_of_preserved R1 R2 k RP2). apply AKS. revert Hk; apply (L5K.incl_b _ L5ARZP.KS_rzA); vm_compute; reflexivity.
      revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
    Local Ltac rwB RS := rewrite ?(RS 18%nat), ?(RS 21%nat), ?(RS 22%nat), ?(RS 23%nat), ?(RS 25%nat), ?(RS 26%nat), ?(RS 27%nat) by inl.
    pose proof (rhZ_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => Z.of_nat len | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R2 1 | 48%nat => U R 24 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XC2; [clear; lia | unfold U; rwB RS2; sc]) | (apply XO2; [clear; lia | sc]) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & BFR & BFZ & (BMS & BKS & BR1 & BR10 & BR11 & BR12 & BR13 & BR14 & BR15 & BR18 & BR21 & BR22 & BR23 & BR25 & BR26 & BC104
                   & BS11 & BS10 & BS9 & BS8 & BS7 & BS6 & BS5 & BS4 & BS3 & BS2 & BS1 & BS0 & BH16 & BH8 & BH0 & BDF)).
    apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M2 model2 fx1 fx3 R2 0x8f880 R3 RESERVE M3v
             (fun a => sp - 104 <= a < sp - 96 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 12) K HH2 (conj Hh2 MI2) BMS MG3).
    { intros a Ha Hna. apply BFZ. exact Ha. all: clear - Hna; unfold SB in Hna; lia. }
    { intros a Ha [Wa|[Wa|Wa]].
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      - split. apply (fframe_client L ar LB FF' 0 0 F 1 (sp - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB FF' 0 0 F 1 (sp - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp RESIZE_SCR). { eapply astk_grows. exact ASTK2. exact MGM3. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
    assert (ND2 : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
    (* [comment removed for export] *)
    destruct sto as [v0 v1|cap q]. { exfalso. destruct OST as (B0 & _). unfold L5.bo_dyn in DYN. cbn [L5.bo_fb] in DYN. rewrite B0 in DYN. discriminate DYN. }
    destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & Qlo & Qhi & _).
    assert (EMV3 : mrestrict (ahid A model3) M3 = M3v). { rewrite AH3. exact VIS3. }
    assert (AG3 : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> M3v (Z_to_bv 64 a) = MV2 (Z_to_bv 64 a)).
    { intros a Ra. apply BFZ. clear - Ra OR; unfold SB in *; lia. all: clear - Ra OR OBIG SLO SPT OF OSHF OFSH FBIG F8 FR; unfold SB in *; lia. }
    assert (XO0 : L5.u8_at RSEGS MV2 o fb).
    { eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. rewrite AG2. 2: clear - Hj; lia.
      destruct (Z.leb_spec (sp - 128) j) as [Hs|Hs]. exfalso; clear - Hj Hs OR SLO SPT; lia. reflexivity. }
    assert (YO : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M3v a v).
    { intros a v Ha Hc. pose proof (XO2 a v Ha Hc) as Hc2. xfer AG3 Hc2. }
    assert (YO0 : L5.u8_at RSEGS M3v o fb). { xfer AG3 XO0. }
    assert (OZ3 : L5KA.zeros_at M3v (o / 8 + SB) 4). { xfer AG3 OZ2. }
    assert (OW3 : L5.writable RSEGS M3v o 32). { eapply L5.writable_grows. exact MG3. exact OW2. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M3 model3 HH3) as (HOFF3 & VISs3 & _).
    pose proof (L5ARZ.statics_vis L ar C HI LY HIok LB _ LK2 cr A M3 model3 HH3) as (IMGC3 & CSB3 & CUAR3). cbv zeta in IMGC3, CSB3, CUAR3. rewrite EMV3 in IMGC3, CSB3, CUAR3.
    assert (W112 : L5.writable RSEGS M3v (sp - 240) 112).
    { rewrite <- EMV3. apply (proj2 (writable_vis (ahid A model3) M3 (sp - 240) 112 (VISs3 (sp - 240) 112 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M3 sp). exact ASTK3. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
    destruct SA16 as (SA16a & SA32a).
    assert (G3_2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 128)) by rk.
    pose proof (rhR_conc fx3 R3 M3v (fun j => match j with 2%nat => sp - 128 | 33%nat => o | 34%nat => n | 35%nat => fb | 36%nat => Z.of_nat len | 37%nat => cap | 38%nat => q | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply YO; [clear; lia | sc]) ]).
    destruct P as (fx4 & R4 & M4v & MG4 & RFR & RFZ & (RMS & RKS & RR12 & _)).
    rewrite <- EMV3 in RMS, MG4, RFZ.
    apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M3 model3 fx3 fx4 R3 RESERVE R4 ARESERVE M4v (fun a => sp - 240 <= a < sp - 128) K HH3 AM3 RMS MG4).
    { intros a Ha Hna. apply RFZ. exact Ha. clear - Hna; lia. }
    { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M4 model4 HH4 AM4 RT4 AH4 VIS4 MGM4 FRM4 EQ4.
    (* [comment removed for export] *)
    assert (EMV4 : mrestrict (ahid A model4) M4 = M4v). { rewrite AH4. exact VIS4. }
    assert (ASTK4 : astk ar M4 sp RESIZE_SCR). { eapply astk_grows. exact ASTK3. exact MGM4. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M4 model4 HH4) as (HOFF4 & VISs4 & _).
    pose proof (L5ARZ.statics_vis L ar C HI LY HIok LB _ LK2 cr A M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4). cbv zeta in IMGC4, CSB4, CUAR4. rewrite EMV4 in IMGC4, CSB4, CUAR4.
    assert (W128d : L5.writable RSEGS M4v (sp - 256) 128).
    { rewrite <- EMV4. apply (proj2 (writable_vis (ahid A model4) M4 (sp - 256) 128 (VISs4 (sp - 256) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M4 sp). exact ASTK4. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
    assert (G4_2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 128)) by rk.
    assert (G4_10 : getr R4 (reg 10) = Z_to_bv 64 o) by rk.
    assert (G4_11 : getr R4 (reg 11) = Z_to_bv 64 n) by rk.
    pose proof (rhA_conc fx4 R4 M4v (fun j => match j with 2%nat => sp - 128 | 33%nat => o | 34%nat => n | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx5 & R5 & M5v & MG5 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR19 & aR20 & aR25
                   & aC96 & aC88 & aC80 & aC72 & aC64 & aC56 & aC48 & aC40 & aC32 & aC24 & aC16 & aC8 & aC128)).
    rewrite <- EMV4 in aMS, MG5, aFZ.
    apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M4 model4 fx4 fx5 R4 ARESERVE R5 SM1 M5v (fun a => sp - 256 <= a < sp - 128) K HH4 AM4 aMS MG5).
    { intros a Ha Hna. apply aFZ. exact Ha. clear - Hna; lia. }
    { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
    intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
    (* [comment removed for export] *)
    pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
    rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
    assert (U5 : bv_unsigned (getr R5 2%bv) = sp - 256). { rewrite r2, aR2. replace (sp - 128 - 128) with (sp - 256) by (clear; lia). apply L5.unsigned_lit. clear - SPR SLO; lia. }
    assert (FFR3 : ffr FF' LK2 3). { apply (ffr_push FF LK LK2 (F, 1, sp - 128 + 32) 4 3 ROOM LKI2 ND2). clear; lia. clear; lia. }
    assert (FFRS3 : ffrs FF' (sp - 128)). { apply (ffrs_push FF sp). exact RS. clear; lia. clear; lia. }
    eapply (SM fx5 R5 M5 model5 LB FF' LK2 cr A K HH5 (proj1 AM5) (proj2 AM5)); clear SM.
    + rewrite r4. rk.
    + rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    + rewrite U5.
      apply (astack_ok_of_astk L ar C LY M3 M5 sp RESIZE_SCR 256 512 ASTK3 ltac:(eapply mem_grows_trans; [exact MGM4 | exact MGM5])). clear; lia. clear; lia.
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
      clear - SA16a. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      clear - FFR3. unfold ffr in FFR3. unfold ff_room. lia.
    + intros f Hf. rewrite U5. specialize (FFRS3 f Hf). clear - FFRS3. lia.
    + exact HK.
    + (* [comment removed for export] *)
      intros R6 M6 model6 Fd fld LK6 B10d RP6 (FS1d & FS2d & FALd & FAPPd & FCEILd) FIMGd FAPARTd FBLKd LKI6 FDEFd FLCd FLPd FLNCd FLAd FLWd FSHd PRES6 RT6 MI6 HH6.
      rewrite U5 in FLNCd. rewrite U5 in PRES6. rewrite U5 in HH6. rewrite ?U5. rewrite r1, aR1.
      pose proof (sm_facts L ar C HI LY HIok LB FF' LK6 cr A M6 model6 Fd 1 (sp - 256 + 32) fld HH6 ltac:(left; reflexivity) FS1d FS2d FALd FAPPd FCEILd FDEFd FLCd FLPd FLNCd FLAd FSHd)
        as (FRd & FFLd & F32d & F8d & _ & FDEFvd & FWvd & FBIGd & FSHWd & FSHZd & FLCvd & FLRd & FLWvd & FLBIGd & VFd & VSHd & VFLd).
      change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
      assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM5). }
      assert (MG35 : mem_grows M3 M5). { eapply mem_grows_trans; [exact MGM4 | exact MGM5]. }
      assert (ASTK6 : astk ar M6 sp RESIZE_SCR).
      { apply (astk_after_rt L ar C HI HIok LB FF' LK2 cr A M3 M5 M6 _ sp _ (sp - 256) 512 HH3 ASTK3 MG35 PRES6). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
        unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB _ LK6 cr A M6 model6 HH6) as (HOFF6 & VISs6 & _).
      pose proof (L5ARZ.statics_vis L ar C HI LY HIok LB _ LK6 cr A M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
      set (H6 := ahid A model6) in *. set (MV6 := mrestrict H6 M6) in *.
      set (FF'' := (Fd, 1, sp - 256 + 32) :: FF') in *.
      assert (W128e : L5.writable RSEGS MV6 (sp - 256) 128).
      { apply (proj2 (writable_vis H6 M6 (sp - 256) 128 (VISs6 (sp - 256) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M6 sp). exact ASTK6. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
      (* [comment removed for export] *)
      pose proof (sm_apart L ar C HI LY HIok LB FF' LK6 cr A M6 _ Fd 1 _ fld sp 0 (sp - 256) 256 HH6 SPT ltac:(left; reflexivity)
                    ltac:(clear - FRd; lia) FCEILd FAPPd FALd FAPARTd FBLKd FLNCd
                    ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SFd & SFSHd & SFLd).
      change (ff_bytes 1) with 128 in SFd. change (ff_bytes 1 / 8) with 16 in SFSHd.
      assert (FFd : Fd + 128 <= F \/ F + 128 <= Fd). { exact (FAPARTd (F, 1, sp - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)). }
      (* [comment removed for export] *)
      assert (G6_2 : getr R6 (reg 2) = Z_to_bv 64 (sp - 128 - 128)) by rk.
      assert (G6_8 : getr R6 (reg 8) = Z_to_bv 64 (sp - 128)) by rk.
      assert (G6_9 : getr R6 (reg 9) = Z_to_bv 64 (sp - 128 - 128)) by rk.
      assert (G6_19 : getr R6 (reg 19) = Z_to_bv 64 o) by rk.
      assert (G6_20 : getr R6 (reg 20) = Z_to_bv 64 n) by rk.
      assert (G6_25 : getr R6 (reg 25) = Z_to_bv 64 2147450880) by rk.
      pose proof (rhB_conc fx5 R6 MV6 (fun j => match j with 2%nat => sp - 128 | 33%nat => o | 34%nat => n | 40%nat => Fd | 41%nat => fld | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx7 & R7 & M7v & MG7 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR12 & bR13 & bR14 & bR18 & bR20 & bR23 & bR24
                     & bS11 & bS10 & bS9 & bS8 & bS7 & bS6 & bS5 & bS4 & bS3 & bS2 & bS1 & bS0 & bH16 & bH8 & bH0 & bC104 & bDF)).
      apply (apiece L ar C HI LY HIok LB FF'' LK6 cr A M6 model6 fx5 fx7 R6 0x9009c R7 0x902d0 M7v
               (fun a => sp - 232 <= a < sp - 224 \/ Fd <= a < Fd + 24 \/ Fd / 8 + SB <= a < Fd / 8 + SB + 12) K HH6 (conj Hh6 MI6) bMS MG7).
      { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; unfold SB in Hna; lia. }
      { intros a Ha [Wa|[Wa|Wa]].
        - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
        - split. apply (fframe_client L ar LB FF'' 0 0 Fd 1 (sp - 256 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FRd; lia.
        - split. apply (fframe_shadow_client L ar LB FF'' 0 0 Fd 1 (sp - 256 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8d. unfold SB in *.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          clear - Wa FRd; unfold SB in Wa; lia. }
      intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
      (* [comment removed for export] *)
      assert (ASTK7 : astk ar M7 sp RESIZE_SCR). { eapply astk_grows. exact ASTK6. exact MGM7. }
      (* [comment removed for export] *)
      assert (K57s : forall a, sp - 256 <= a < sp -> ~ (sp - 232 <= a < sp - 224) -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros a Ra Na. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR SLO; lia).
        rewrite (FRM7 a Ha). 2:{ clear - Ra Na SFd SFSHd; unfold SB in *; lia. }
        apply (proj1 PRES6 a Ha). apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. }
      assert (K37s : forall a, sp - 128 <= a < sp -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR; lia).
        rewrite (K57s a). 2: clear - Ra; lia. 2: clear - Ra; lia.
        rewrite (FRM5 a Ha). 2: clear - Ra; lia. apply (FRM4 a Ha). clear - Ra; lia. }
      assert (K17s : forall a, sp - 128 <= a < sp -> ~ (sp - 104 <= a < sp - 96) -> M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ra Na. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR; lia).
        rewrite (K37s a Ra). rewrite (FRM3 a Ha). 2:{ clear - Ra Na SF SFSH; unfold SB in *; lia. }
        apply (proj1 PRES2 a Ha). apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. }
      assert (K37f : forall a, (F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 16) -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra FR F8; unfold SB in *; lia).
        rewrite (FRM7 a Ha). 2:{ clear - Ra SFd SFSHd FFd F8 F8d FBIG FBIGd FR FRd SLO SPT; unfold SB in *; lia. }
        rewrite (proj1 PRES6 a Ha).
        2:{ destruct Ra as [Ra|Ra].
            - apply (fframe_client L ar LB FF' _ _ F 1 (sp - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia.
            - apply (fframe_shadow_client L ar LB FF' _ _ F 1 (sp - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S.
              rewrite (proj1 FQ15). clear - Ra. unfold SB in *. lia. }
        rewrite (FRM5 a Ha). 2:{ clear - Ra FR F8 FCEIL SLO SPT; unfold SB in *; lia. }
        apply (FRM4 a Ha). clear - Ra FR F8 FCEIL SLO SPT; unfold SB in *; lia. }
      (* [comment removed for export] *)
      assert (SAVE7 : forall a v, sp - 128 <= a <= sp - 8 -> ~ (sp - 112 < a < sp - 96) -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M7 a v).
      { intros a v Ra Na Hc. eapply (L5C.u64_at_agree RSEGS M1 M7). intros j Hj. apply K17s. clear - Ra Hj; lia. clear - Na Hj; lia. clear - Ra SPR; lia. clear - Ra SPR; lia.
        apply (proj1 (u64_at_vis (ahid A model) M1 a v ltac:(eapply avis_sub; [exact (VIS (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) | clear - Ra; lia | clear - Ra; lia])
                        ltac:(clear - Ra SPR; lia) ltac:(clear - Ra SPR; lia))). rewrite VIS1. exact Hc. }
      assert (SAVE7d : forall a v, sp - 256 <= a <= sp - 136 -> ~ (sp - 240 < a < sp - 224) -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M7 a v).
      { intros a v Ra Na Hc. eapply (L5C.u64_at_agree RSEGS M5 M7). intros j Hj. apply K57s. clear - Ra Hj; lia. clear - Na Hj; lia. clear - Ra SPR SLO; lia. clear - Ra SPR; lia.
        apply (proj1 (u64_at_vis (ahid A model4) M5 a v ltac:(eapply avis_sub; [exact (VISs4 (sp - 256) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) | clear - Ra; lia | clear - Ra; lia])
                        ltac:(clear - Ra SPR SLO; lia) ltac:(clear - Ra SPR; lia))). rewrite VIS5. exact Hc. }
      assert (C104 : L5.u64_at RSEGS M7 (sp - 104) F).
      { eapply (L5C.u64_at_agree RSEGS M3 M7). intros j Hj. apply K37s. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia.
        apply (proj1 (u64_at_vis H2 M3 (sp - 104) F ltac:(eapply avis_sub; [exact (VIS2 (sp - 128) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) | clear; lia | clear; lia])
                        ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))). unfold H2. rewrite VIS3. exact BC104. }
      assert (C232 : L5.u64_at RSEGS M7 (sp - 232) Fd).
      { apply (proj1 (u64_at_vis H6 M7 (sp - 232) Fd ltac:(eapply avis_sub; [exact (VISs6 (sp - 256) 128 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) | clear; lia | clear; lia])
                        ltac:(clear - SPR SLO; lia) ltac:(clear - SPR; lia))). unfold H6. rewrite VIS7. replace (sp - 232) with (sp - 128 - 104) by (clear; lia). exact bC104. }
      assert (HDR7 : L5.u64_at RSEGS M7 F L5DSA.FRAME_MAGIC).
      { eapply (L5C.u64_at_agree RSEGS M3 M7). intros j Hj. apply K37f. left; clear - Hj; lia. clear - FR; lia. clear - FR; lia.
        apply (proj1 (u64_at_vis H2 M3 F _ ltac:(eapply avis_sub; [exact VF | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). unfold H2. rewrite VIS3. exact BH0. }
      assert (HDR7d : L5.u64_at RSEGS M7 Fd L5DSA.FRAME_MAGIC).
      { apply (proj1 (u64_at_vis H6 M7 Fd _ ltac:(eapply avis_sub; [exact VFd | clear; lia | clear; lia]) ltac:(clear - FRd; lia) ltac:(clear - FRd; lia))). unfold H6. rewrite VIS7. exact bH0. }
      (* [comment removed for export] *)
      assert (SHB : forall k v, 0 <= k < 16 -> L5.u8_at RSEGS M3 (F / 8 + SB + k) v -> byte_at M7 (S F + k) v).
      { intros k v Hk Hc. unfold byte_at, S. rewrite K37f. 2: right; clear - Hk; lia.
        apply byte_of_u8. exact Hc. right; clear - Hk FR F8; unfold SB; lia. clear - Hk FR F8; unfold SB; lia. }
      assert (SH3 : forall k v, 0 <= k < 12 -> L5.u8_at RSEGS M3v (F / 8 + SB + k) v -> L5.u8_at RSEGS M3 (F / 8 + SB + k) v).
      { intros k v Hk Hc. apply (proj1 (u8_at_vis H2 M3 (F / 8 + SB + k) v ltac:(eapply avis_sub; [exact VSH | clear - Hk; lia | clear - Hk; lia]) ltac:(clear - Hk FR F8; unfold SB; lia) ltac:(clear - Hk FR F8; unfold SB; lia))).
        unfold H2. rewrite VIS3. exact Hc. }
      assert (SZ3 : forall k, 12 <= k < 16 -> L5.u8_at RSEGS M3 (F / 8 + SB + k) 0).
      { intros k Hk. apply u8_of_byte. unfold byte_at. rewrite (FRM3 (F / 8 + SB + k)). 2: clear - Hk FR F8; unfold SB; lia. 2:{ clear - Hk SF SFSH FBIG FR F8; unfold SB in *; lia. }
        exact (FSH k ltac:(clear - Hk; lia)). }
      assert (SHBd : forall k v, 0 <= k < 12 -> L5.u8_at RSEGS M7v (Fd / 8 + SB + k) v -> byte_at M7 (S Fd + k) v).
      { intros k v Hk Hc. unfold byte_at, S. apply byte_of_u8. 2: right; clear - Hk FRd F8d; unfold SB; lia. 2: clear - Hk FRd F8d; unfold SB; lia.
        apply (proj1 (u8_at_vis H6 M7 (Fd / 8 + SB + k) v ltac:(eapply avis_sub; [exact VSHd | clear - Hk; lia | clear - Hk; lia]) ltac:(clear - Hk FRd F8d; unfold SB; lia) ltac:(clear - Hk FRd F8d; unfold SB; lia))).
        unfold H6. rewrite VIS7. exact Hc. }
      assert (SZ7d : forall k, 12 <= k < 16 -> byte_at M7 (S Fd + k) 0).
      { intros k Hk. unfold byte_at, S. rewrite (FRM7 (Fd / 8 + SB + k)). 2: clear - Hk FRd F8d; unfold SB; lia. 2:{ clear - Hk SFd SFSHd FBIGd FRd F8d; unfold SB in *; lia. }
        exact (FSHd k ltac:(clear - Hk; lia)). }
      (* [comment removed for export] *)
      assert (INF7 : In (F, 1, sp - 128 + 32) FF''). { right; left; reflexivity. }
      assert (INFd7 : In (Fd, 1, sp - 256 + 32) FF''). { left; reflexivity. }
      pose proof (flagptr_now L ar C HI LY HIok LB FF' LK2 cr A M2 _ LB FF'' LK6 cr A M7 model7 F 1 _ _ fl HH2 HH7 ltac:(left; reflexivity) INF7 ltac:(left; reflexivity) FLC) as (FLC7 & _).
      pose proof (flagptr_now L ar C HI LY HIok LB FF'' LK6 cr A M6 _ LB FF'' LK6 cr A M7 model7 Fd 1 _ _ fld HH6 HH7 INFd7 INFd7 ltac:(left; reflexivity) FLCd) as (FLC7d & _).
      assert (LIVE_d : L5DSA.fr_live L ar LB ((F, 1, sp - 96) :: FF) M7 1 Fd fld (sp - 224)).
      { replace (sp - 96) with (sp - 128 + 32) by (clear; lia). replace (sp - 224) with (sp - 256 + 32) by (clear; lia).
        constructor. exact FLC7d. exact FLPd. exact FLNCd. exact FLAd. exact HDR7d. }
      assert (LIVE_c : L5DSA.fr_live L ar LB FF M7 1 F fl (sp - 96)).
      { replace (sp - 96) with (sp - 128 + 32) by (clear; lia). constructor. exact FLC7. exact FLP. exact FLNC. exact FLA. exact HDR7. }
      (* [comment removed for export] *)
      assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF sp RESIZE_SCR a).
      { intros a Ha'. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp RESIZE_SCR F 128 a HH SPT).
        clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ15). clear; lia. reflexivity.
        eapply fframes_apart_incl. exact FAPART. intros g Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha'. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (FQ15d : (Fd + 128 - 1) / 8 = Fd / 8 + 15 /\ Fd mod 8 = 0) by (clear - F8d; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (NCFd : forall a, (Fd <= a < Fd + 128 \/ S Fd <= a <= S (Fd + 128 - 1)) -> ~ aclient L ar LB FF sp RESIZE_SCR a).
      { intros a Ha'. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp RESIZE_SCR Fd 128 a HH SPT).
        clear - FRd; lia. exact FCEILd. exact FAPPd. exact (proj2 FQ15d). clear; lia. reflexivity.
        eapply fframes_apart_incl. exact FAPARTd. intros g Hg; apply in_or_app; left; right; exact Hg. exact FBLKd. exact Ha'. }
      assert (STKP : forall (Ma Mb : word -> option byte) (lo hi : Z), sp - RESIZE_SCR <= lo -> hi <= sp ->
                (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> ek L ar LB FF sp RESIZE_SCR [] Ma Mb).
      { intros Ma Mb lo hi Hlo Hhi FRMx. apply (ek_piece L ar LB FF sp RESIZE_SCR [] Ma Mb _ FRMx). intros a Ha Hc _ X.
        destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESIZE_SCR a HH SPT Hc) as [Y|Y].
        clear - X Y Hlo Hhi; lia. clear - X Y SLO Hlo; unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in *; lia. }
      assert (EK7 : ek L ar LB FF sp RESIZE_SCR [] M M7).
      { eapply ek_trans. { apply (STKP M M1 (sp - 128) sp). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. exact FRM1. }
        eapply ek_trans. { apply (ek_rt L ar LB FF [] sp RESIZE_SCR (sp - 128) 512 [] M1 M2 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        eapply ek_trans. { apply (ek_piece L ar LB FF sp RESIZE_SCR [] M2 M3 _ FRM3). intros a Ha Hc _ [X|[X|X]].
            + destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESIZE_SCR a HH SPT Hc) as [Y|Y].
              unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
            + apply (NCF a). left. clear - X; lia. exact Hc.
            + apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc. }
        eapply ek_trans. { apply (STKP M3 M4 (sp - 240) (sp - 128)). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. exact FRM4. }
        eapply ek_trans. { apply (STKP M4 M5 (sp - 256) (sp - 128)). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. exact FRM5. }
        eapply ek_trans. { apply (ek_rt L ar LB FF [(F, 1, sp - 128 + 32)] sp RESIZE_SCR (sp - 256) 512 [] M5 M6 PRES6). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        apply (ek_piece L ar LB FF sp RESIZE_SCR [] M6 M7 _ FRM7). intros a Ha Hc _ [X|[X|X]].
        + destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp RESIZE_SCR a HH SPT Hc) as [Y|Y].
          unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
        + apply (NCFd a). left. clear - X; lia. exact Hc.
        + apply (NCFd a). right. unfold S. rewrite (proj1 FQ15d). clear - X. unfold SB in X |- *. lia. exact Hc. }
      assert (DK7 : dk L ar LB FF sp RESIZE_SCR M M7).
      { eapply dk_trans. apply dk_grows; exact MGM1.
        eapply dk_trans. { apply (dk_rt L ar LB FF [] sp RESIZE_SCR (sp - 128) 512 M1 M2 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        eapply dk_trans. apply dk_grows; exact MGM3. eapply dk_trans. apply dk_grows; exact MGM4. eapply dk_trans. apply dk_grows; exact MGM5.
        eapply dk_trans. { apply (dk_rt L ar LB FF [(F, 1, sp - 128 + 32)] sp RESIZE_SCR (sp - 256) 512 M5 M6 PRES6). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        apply dk_grows; exact MGM7. }
      (* [comment removed for export] *)
      assert (V4_1 : U R4 1 = L5DSA.RESERVE_RET). { apply U_of. rk. unfold L5DSA.RESERVE_RET; clear; lia. }
      assert (V4_8 : U R4 8 = sp). { apply U_of. rk. clear - SPR; lia. }
      assert (V4_9 : U R4 9 = sp - 128). { apply U_of. rk. clear - SPR; lia. }
      assert (V4_18 : U R4 18 = F). { apply U_of. rk. clear - FR; lia. }
      assert (V4_19 : U R4 19 = n). { apply U_of. rk. clear - Hn; lia. }
      assert (V4_20 : U R4 20 = o). { apply U_of. rk. clear - OR; lia. }
      assert (V4_21 : U R4 21 = o + 8). { apply U_of. rk. clear - OR; lia. }
      assert (V4_22 : U R4 22 = S F). { apply U_of. unfold S, SB. rk. clear - FR F8; unfold S, SB; lia. }
      assert (V4_23 : U R4 23 = F). { apply U_of. rk. clear - FR; lia. }
      assert (V4_24 : U R4 24 = SB). { apply U_of. unfold SB. rk. unfold SB; clear; lia. }
      assert (V4_25 : U R4 25 = Z.of_nat len). { apply U_of. rk. clear - LEN; lia. }
      assert (V4_26 : U R4 26 = S (o + 8)). { apply U_of. unfold S, SB. rk. clear - OR; unfold S, SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      unfold U in V4_1, V4_8, V4_9, V4_18, V4_19, V4_20, V4_21, V4_22, V4_23, V4_24, V4_25, V4_26.
      rewrite V4_1 in aC8. rewrite V4_8 in aC16. rewrite V4_9 in aC24. rewrite V4_18 in aC32. rewrite V4_19 in aC40. rewrite V4_20 in aC48.
      rewrite V4_21 in aC56. rewrite V4_22 in aC64. rewrite V4_23 in aC72. rewrite V4_24 in aC80. rewrite V4_25 in aC88. rewrite V4_26 in aC96.
      assert (X2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 256)) by rk.
      assert (X3 : getr R7 (reg 3) = getr R (reg 3)) by rk.
      assert (X4 : getr R7 (reg 4) = getr R (reg 4)) by rk.
      assert (X8 : getr R7 (reg 8) = Z_to_bv 64 (sp - 128)) by rk.
      assert (X9 : getr R7 (reg 9) = Z_to_bv 64 (sp - 256)) by rk.
      assert (X19 : getr R7 (reg 19) = Z_to_bv 64 o) by rk.
      assert (X21 : getr R7 (reg 21) = Z_to_bv 64 (o + 8)) by rk.
      assert (X22 : getr R7 (reg 22) = Z_to_bv 64 (S F)) by (unfold S, SB; rk).
      assert (X23 : getr R7 (reg 23) = Z_to_bv 64 (S Fd)) by (unfold S, SB; rk).
      assert (X25 : getr R7 (reg 25) = Z_to_bv 64 SB) by (unfold SB; rk).
      assert (X26 : getr R7 (reg 26) = Z_to_bv 64 (S (o + 8))) by (unfold S, SB; rk).
      assert (X27 : getr R7 (reg 27) = getr R (reg 27)) by rk.
      apply (KONT fx7 R7 M7 model7 LK6 A F fl Fd fld).
      * unfold L5DIA.resize_huge_atA. cbn [L5.bo_len].
        split. exact X2. split. exact X3. split. exact X4. split. exact bR10. split. exact X8. split. exact X9.
        split. exact bR18. split. exact X19. split. exact bR20. split. exact X21. split. exact X22. split. exact X23.
        split. exact bR24. split. exact X25. split. exact X26. split. exact X27.
        split. { unfold L5DIA.rsaves.
          split. apply (SAVE7 (sp - 8) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_11). split. apply (SAVE7 (sp - 16) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_10).
          split. apply (SAVE7 (sp - 24) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_9). split. apply (SAVE7 (sp - 32) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_8).
          split. apply (SAVE7 (sp - 40) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_7). split. apply (SAVE7 (sp - 48) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_6).
          split. apply (SAVE7 (sp - 56) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_5). split. apply (SAVE7 (sp - 64) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_4).
          split. apply (SAVE7 (sp - 72) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_3). split. apply (SAVE7 (sp - 80) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_2).
          split. apply (SAVE7 (sp - 88) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat_1). apply (SAVE7 (sp - 96) _ ltac:(clear; lia) ltac:(clear; lia) AQ_V2nat). }
        split. exact C104.
        split. { replace (sp - 136) with (sp - 128 - 8) by (clear; lia). apply (SAVE7d (sp - 128 - 8) _ ltac:(clear; lia) ltac:(clear; lia) aC8). }
        split. { replace (sp - 144) with (sp - 128 - 16) by (clear; lia). apply (SAVE7d (sp - 128 - 16) _ ltac:(clear; lia) ltac:(clear; lia) aC16). }
        split. { replace (sp - 152) with (sp - 128 - 24) by (clear; lia). apply (SAVE7d (sp - 128 - 24) _ ltac:(clear; lia) ltac:(clear; lia) aC24). }
        split. { replace (sp - 160) with (sp - 128 - 32) by (clear; lia). apply (SAVE7d (sp - 128 - 32) _ ltac:(clear; lia) ltac:(clear; lia) aC32). }
        split. { replace (sp - 168) with (sp - 128 - 40) by (clear; lia). apply (SAVE7d (sp - 128 - 40) _ ltac:(clear; lia) ltac:(clear; lia) aC40). }
        split. { replace (sp - 176) with (sp - 128 - 48) by (clear; lia). apply (SAVE7d (sp - 128 - 48) _ ltac:(clear; lia) ltac:(clear; lia) aC48). }
        split. { replace (sp - 184) with (sp - 128 - 56) by (clear; lia). apply (SAVE7d (sp - 128 - 56) _ ltac:(clear; lia) ltac:(clear; lia) aC56). }
        split. { replace (sp - 192) with (sp - 128 - 64) by (clear; lia). apply (SAVE7d (sp - 128 - 64) _ ltac:(clear; lia) ltac:(clear; lia) aC64). }
        split. { replace (sp - 200) with (sp - 128 - 72) by (clear; lia). apply (SAVE7d (sp - 128 - 72) _ ltac:(clear; lia) ltac:(clear; lia) aC72). }
        split. { replace (sp - 208) with (sp - 128 - 80) by (clear; lia). apply (SAVE7d (sp - 128 - 80) _ ltac:(clear; lia) ltac:(clear; lia) aC80). }
        split. { replace (sp - 216) with (sp - 128 - 88) by (clear; lia). apply (SAVE7d (sp - 128 - 88) _ ltac:(clear; lia) ltac:(clear; lia) aC88). }
        split. { replace (sp - 224) with (sp - 128 - 96) by (clear; lia). apply (SAVE7d (sp - 128 - 96) _ ltac:(clear; lia) ltac:(clear; lia) aC96). }
        split. exact C232.
        split. { unfold L5DIA.sh_rz, L5DSA.sh_run. unfold SB in BS0, BS1, BS2, BS3, BS4, BS5, BS6, BS7, BS8, BS9, BS10, BS11.
          split. { intros j Hj. replace (S F + 0 + j) with (S F + j) by (clear; lia). apply SHB. clear - Hj; lia. apply SH3. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct Ej as [->|[->|[->| ->]]]; unfold SB; sc. }
          split. { intros j Hj. replace (S F + 4 + j) with (S F + (4 + j)) by (clear; lia). apply SHB. clear - Hj; lia. apply SH3. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia). destruct Ej as [->|[->| ->]]; unfold SB; sc. }
          split. { intros j Hj. replace (S F + 7 + j) with (S F + 7) by (clear - Hj; lia). apply SHB. clear; lia. apply SH3. clear; lia. unfold SB; sc. }
          split. { intros j Hj. replace (S F + 8 + j) with (S F + (8 + j)) by (clear; lia). apply SHB. clear - Hj; lia. apply SH3. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct Ej as [->|[->|[->| ->]]]; unfold SB; sc. }
          intros j Hj. replace (S F + 12 + j) with (S F + (12 + j)) by (clear; lia). apply SHB. clear - Hj; lia. apply SZ3. clear - Hj; lia. }
        split. { unfold L5DIA.sh_rz, L5DSA.sh_run.
          split. { intros j Hj. replace (S Fd + 0 + j) with (S Fd + j) by (clear; lia). apply SHBd. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct Ej as [->|[->|[->| ->]]]; unfold SB; sc. }
          split. { intros j Hj. replace (S Fd + 4 + j) with (S Fd + (4 + j)) by (clear; lia). apply SHBd. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia). destruct Ej as [->|[->| ->]]; unfold SB; sc. }
          split. { intros j Hj. replace (S Fd + 7 + j) with (S Fd + 7) by (clear - Hj; lia). apply SHBd. clear; lia. unfold SB; sc. }
          split. { intros j Hj. replace (S Fd + 8 + j) with (S Fd + (8 + j)) by (clear; lia). apply SHBd. clear - Hj; lia.
                   assert (Ej : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). destruct Ej as [->|[->|[->| ->]]]; unfold SB; sc. }
          intros j Hj. replace (S Fd + 12 + j) with (S Fd + (12 + j)) by (clear; lia). apply SZ7d. clear - Hj; lia. }
        split. exact LIVE_d. split. exact LIVE_c.
        apply ahpres_of. exact EK7. eapply astk_defined. exact ASTK7. clear; lia. clear; lia. exact DK7.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4.
        eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. exact RT7.
      * apply incl_refl.
      * exact AM7.
      * intros f Hf. apply LKI2. apply LKI6. exact Hf.
      * unfold L5DIA.ff_rz. replace (sp - 224) with (sp - 256 + 32) by (clear; lia). replace (sp - 96) with (sp - 128 + 32) by (clear; lia). exact HH7.
Qed.
End WithIface.
End SCFG_1.
End L5ARZH.
