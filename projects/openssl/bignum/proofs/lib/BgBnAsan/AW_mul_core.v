(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnA Require W_mul_core.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA BnIfaceA BnRepDefs AsStruct ImplA RtCallA BnCallsA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_rec_top AW_mul_part_recursive AW_kara_closedA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition MULC_TAIL : Z := 0x22ac6c.

Section Core.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variables (sp gp tp : word).
  Variables (m : word -> option byte) (lo R A B Dr Da Db CST : Z) (br : bignum bptr) (la lb : list Z).
  Notation SP := (bv_unsigned sp).
  Notation al := (Z.of_nat (length la)).
  Notation bl := (Z.of_nat (length lb)).
  Notation dmx := (Z.of_nat (bn_dmax br)).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).

  Definition mulc_preA : Prop :=
    limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP <= 140737488355328)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z /\
    (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z /\

    ((A + 8 <= R \/ R + 24 <= A) /\ (B + 8 <= R \/ R + 24 <= B))%Z /\

    (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z /\
    ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo /\
     (Dr + 8 * dmx <= 65536 \/ 12345344 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12345344 <= R))%Z.
  Hypothesis PRE : mulc_preA.

  Lemma P_lists : limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z.
  Proof. destruct PRE as (H1 & H2 & H3 & H4 & _). auto. Qed.
  Lemma P_rng : (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP <= 140737488355328)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_sarr : (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.
  Lemma P_disj : (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). auto. Qed.
  Lemma P_structs : ((A + 8 <= R \/ R + 24 <= A) /\ (B + 8 <= R \/ R + 24 <= B))%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_al : (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
  Lemma P_sh : ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo /\
     (Dr + 8 * dmx <= 65536 \/ 12345344 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12345344 <= R))%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Definition mulc_memA : Prop :=
    rw_cells bgasegs m R (bn_cells Dr br) /\ u64arr bgasegs m Dr (wlimbs (bn_buf br)) /\
    rw_cells bgasegs m A [C8 (wz Da)] /\ rw_cells bgasegs m B [C8 (wz Db)] /\
    limbs_at bgasegs m Da la /\ limbs_at bgasegs m Db lb /\
    stk bgasegs m lo (SP + -112) /\ mem_inv bgasegs m /\
    shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m /\
    acc bgasegs m R 24 /\ acc bgasegs m A 8 /\ acc bgasegs m B 8 /\
    acc bgasegs m Dr (8 * dmx) /\ acc bgasegs m Da (8 * al) /\ acc bgasegs m Db (8 * bl).
  Hypothesis MEM : mulc_memA.

  Definition mulc_postA (F : bvmap 5 word) (fc : bv 32) (x8 x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 : word) (W : list (Z * Z)) (topn : nat) (w : list Z)
      (Q : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 SHB) x25 x26 x27 t3 t4 t5 t6)
               F (Z_to_bv 64 MULC_TAIL) fc None m' (seg_rom bgasegs)
      /\ munch W m m' /\ wmono bgasegs m m' /\ mem_inv bgasegs m'
      /\ rw_cells bgasegs m' R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]
      /\ limbs_at bgasegs m' Dr w /\ stk bgasegs m' lo (SP + -112) /\ Q m'.

  Notation ST F fc pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 x27 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
             (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 SHB) x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Lemma P_off : forall len, (0 <= len)%Z -> (len <= 8 * dmx)%Z -> offshW [(Dr, Dr + len); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z.
  Proof.
    intros len H0 H1. pose proof P_sh as (S1 & S2 & S3 & _). pose proof P_rng as RNG.
    cbn [offshW]. unfold SHLO, SHHI in *. repeat split; lia.
  Qed.

  Lemma mulc_normalA : forall F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 t3 t4 t5 t6,
    (length la + length lb <= bn_dmax br)%nat -> (208 <= CST)%Z ->
    evt bgasegs (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) x25 x26 (Z_to_bv 64 (al + bl))
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True))
      (ST F fc 0x22ab64 m x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 (Z_to_bv 64 (al + bl)) t3 t4 t5 t6).
  Proof.
    intros until t6. intros HD HCST.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB). pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & SHDr & SHL & OFI & _). pose proof P_structs as (SRA & SRB).
    pose proof (munch_refl [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (P_off (8 * (al + bl)) ltac:(clear; lia) ltac:(clear - HD; unfold bn_dmax in *; lia)) as OFF.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at bgasegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgasegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.

    do 3 zstep. shl. chk0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.

    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 3 zstep. do 2 zstep.
    assert (HLA0 : limbs_at bgasegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at bgasegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    pose proof (acc_munch bgasegs _ m m0 Dr (8 * dmx) ACDr MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDr0.
    pose proof (acc_munch bgasegs _ m m0 Da (8 * al) ACDa MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDa0.
    pose proof (acc_munch bgasegs _ m m0 Db (8 * bl) ACDb MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDb0.
    pose proof P_sh as (_ & _ & _ & _ & _ & _ & _ & OFIR).
    pose proof (shb_cells_munch bgasegs _ _ _ m m0 SHBC MUt ltac:(cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell; clear - OFIR; lia)
                  ltac:(cbn [disjoint_from]; unfold g_shadow_memory_dynamic_address; clear - OFIR; lia)) as SHBC0.
    clear HLA HLB.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_mul_normalA (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) x25 x26 (Z_to_bv 64 (al + bl))
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True)))
      with (a := la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -112)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact SHBC0
      | exact LLA | exact LLB | clear - AL23 BL23; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - AL23; lia
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - BL23; lia
      | exact HLA0 | exact HLB0
      | replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | clear - DA HD; unfold bn_dmax in *; lia | clear - DB HD; unfold bn_dmax in *; lia
      | clear - RNG HCST; lia | clear - RNG HD HCST; unfold bn_dmax in *; lia | clear - RNG HCST; lia | clear - RNG HCST; lia
      | split; [replace Dr with (Dr + 0)%Z by (clear; lia); eapply acc_sub; [exact ACDr0 | clear; lia | clear - HD; unfold bn_dmax in *; lia]|];
        split; [exact ACDa0|]; split; [exact ACDb0|];
        split; [unfold aptrs3; split; [exact ALDr|]; split; [exact ALDa|]; split; [exact ALDb|];
                split; [clear - SHDr HD; unfold bn_dmax in *; lia | exact SHL] | clear - OFI HD; unfold bn_dmax in *; lia]
      | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    zstep. apply evt_done.
    unfold mulc_postA. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCST. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [| exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCST; unfold bn_dmax in *; lia].
             unfold wz. rewrite Nat2Z.inj_add. exact SR. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.

  Lemma mulc_comba8A : forall CS8 F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 x27 t3 t4 t5 t6,
    comba8_aspec CS8 -> (CS8 <= CST)%Z -> length la = 8%nat -> length lb = 8%nat -> (16 <= bn_dmax br)%nat ->
    evt bgasegs (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) x25 x26 x27
                 [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z 16 (mul_comba8 la lb) (fun _ => True))
      (ST F fc 0x22a9f8 m x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x26 x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros C8 HCS LA8 LB8 HD.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB). pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & SHDr & SHL & OFI & PDr & PDa & PDb & OFIR). pose proof P_structs as (SRA & SRB).
    pose proof (munch_refl [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    pose proof (P_off (8 * 16) ltac:(clear; lia) ltac:(clear - HD; unfold bn_dmax in *; lia)) as OFF.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at bgasegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgasegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.

    do 3 zstep. shl. chk0.
    do 2 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.

    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 3 zstep.
    assert (HLA0 : limbs_at bgasegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at bgasegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    pose proof (acc_munch bgasegs _ m m0 Dr (8 * dmx) ACDr MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDr0.
    pose proof (acc_munch bgasegs _ m m0 Da (8 * al) ACDa MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDa0.
    pose proof (acc_munch bgasegs _ m m0 Db (8 * bl) ACDb MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDb0.
    pose proof (shb_cells_munch bgasegs _ _ _ m m0 SHBC MUt ltac:(cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell; clear - OFIR; lia)
                  ltac:(cbn [disjoint_from]; unfold g_shadow_memory_dynamic_address; clear - OFIR; lia)) as SHBC0.
    clear HLA HLB.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.
    eapply (call_comba8A (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 bl) x25 x26 x27
                 [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z 16 (mul_comba8 la lb) (fun _ => True)))
      with (CS8 := CS8) (a := la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -112)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact SHBC0 | exact C8
      | exact LLA | exact LLB | exact LA8 | exact LB8
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | exact HLA0 | exact HLB0
      | replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | clear - DA HD LA8; unfold bn_dmax in *; lia | clear - DB HD LB8; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG HCS LA8; lia | clear - RNG HCS LB8; lia
      | split; [replace Dr with (Dr + 0)%Z by (clear; lia); eapply acc_sub; [exact ACDr0 | clear; lia | clear - HD; unfold bn_dmax in *; lia]|];
        split; [replace 64%Z with (8 * al)%Z by (rewrite LA8; reflexivity); exact ACDa0|];
        split; [replace 64%Z with (8 * bl)%Z by (rewrite LB8; reflexivity); exact ACDb0|];
        split; [unfold aptrs3; split; [exact ALDr|]; split; [exact ALDa|]; split; [exact ALDb|];
                split; [clear - SHDr HD; unfold bn_dmax in *; lia | exact SHL] |];
        split; [exact PDr|]; split; [exact PDa|]; split; [exact PDb|]; clear - OFI HD; unfold bn_dmax in *; lia
      | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    zstep. apply evt_done.
    unfold mulc_postA. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCS. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCS; unfold bn_dmax in *; lia]. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.

  Definition mulc_tpreA (TT Dt : Z) (Tl : list Z) : Prop :=
    limbs Tl /\ rw_cells bgasegs m TT [C8 (wz Dt)] /\ limbs_at bgasegs m Dt Tl /\ wr_at bgasegs m Dt (8 * Z.of_nat (length Tl)) /\
    (0 <= Dt /\ Dt + 8 * Z.of_nat (length Tl) <= lo)%Z /\
    (R + 24 <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= R)%Z /\
    (Dt + 8 * Z.of_nat (length Tl) <= Da \/ Da + 8 * al <= Dt)%Z /\ (Dt + 8 * Z.of_nat (length Tl) <= Db \/ Db + 8 * bl <= Dt)%Z /\
    (Dr + 8 * dmx <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= Dr)%Z /\

    acc bgasegs m TT 8 /\ (TT mod 8 = 0 /\ 0 < TT /\ TT + 8 <= lo)%Z.

  Lemma mulc_recA : forall (Σ : rts RT) (Q : config -> Prop) (OW LB : list block) (bR bT bA bB : block)
      (k da db : nat) (TT Dt : Z) (Tl : list Z) F fc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    (rec_stackA CS8A k <= CST)%Z -> mulc_tpreA TT Dt Tl ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat -> length la = (Nat.pow 2 k - da)%nat -> length lb = (Nat.pow 2 k - db)%nat ->
    (2 * Nat.pow 2 k <= bn_dmax br)%nat -> (scratch_rec k <= length Tl)%nat ->
    rw_cells bgasegs m (SP + -112) [C8 (Z_to_bv 64 (al + bl))] ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB Dr Dt Da Db (2 * Nat.pow 2 k) (length Tl) (length la) (length lb) /\
     (ACEIL <= lo)%Z /\ (SP + -112 + 16 <= USTACK_TOP)%Z /\ ((SP + -112) mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) (SP + -112) x /\ ~ (Dr <= x < Dr + 8 * Z.of_nat (2 * Nat.pow 2 k))%Z
                          /\ ~ (Dt <= x < Dt + 8 * Z.of_nat (length Tl))%Z) m m2 ->
       wmono bgasegs m m2 -> mem_inv bgasegs m2 ->
       limbs_at bgasegs m2 Dr (fst (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       limbs_at bgasegs m2 Dt (snd (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       stk bgasegs m2 lo (SP + -112) ->
       evt bgasegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 0x22ab50) SPF gp tp u0 u1 u2 sp x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
                  (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) (Z_to_bv 64 (al + bl)) u3 u4 u5 u6)
             F2 (Z_to_bv 64 0x22ab50) fc2 None m2 (seg_rom bgasegs))) ->
    evt bgasegs (kpost Σ Q) (ST F fc 0x22aaec m x1 t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HCS TPRE HK HDA HDB ELA ELB HD HSC FRs (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).

    destruct TPRE as (LLT & HTd & HLT & HWT & RT' & TREST).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 TREST))))) as ACT.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 TREST))))) as (ALT & PT & TLO).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & _ & SHL & _).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (2 * Nat.pow 2 k) (bn_buf br)) in *.
    assert (LRl : length Rl = (2 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    assert (HLR : limbs_at bgasegs m Dr Rl) by (subst Rl; apply (BnKaraMem.limbs_at_firstn bgasegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at bgasegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgasegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    pose proof (munch_refl [(R, R + 24)]%Z m) as MU.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR; lia). clear SHR.

    do 2 zstep. shl. chk0.
    do 2 zstep. shl. zstep. chk0.
    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 4 zstep.
    zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 ELA HDA P2; lia).
    zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 ELB HDB P2; lia).
    zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.

    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    destruct TREST as (ST1 & DTA & DTB & DTR & _).
    eapply call_recA with (CS8 := CS8A) (k := k) (a := la) (b := lb) (da := da) (db := db) (R := Rl) (T := Tl)
        (RP := Dr) (AP := Da) (BP := Db) (TQ := Dt) (lo := lo) (SPz := (SP + -112)%Z) (bR := bR) (bT := bT) (bA := bA) (bB := bB);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact (bn_mul_recursive_closedA k)
      | exact LLA | exact LLB | subst Rl; apply limbs_firstn; exact LBR | exact LLT
      | exact HK | exact HDA | exact HDB | exact ELA | exact ELB | exact LRl | exact HSC
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | apply unsigned_lit; clear - P2 AL23 ELA HDA; lia
      | f_equal; clear - ELA P2 HDA; lia | f_equal; clear - ELB P2 HDB; lia
      | apply unsigned_lit; clear - RT' RNG; lia
      | exact HLA | exact HLB | exact HLR | exact HLT
      | rewrite LRl; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | exact HWT
      | rewrite LRl; clear - DA HD; unfold bn_dmax in *; lia | rewrite LRl; clear - DB HD; unfold bn_dmax in *; lia
      | clear - DTA; lia | clear - DTB; lia
      | rewrite LRl; clear - DTR HD; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | rewrite LRl; clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG RT' HCS; lia
      | clear - RNG HCS; lia | clear - RNG HCS; lia
      | split; [exact HEAP|]; split; [rewrite LRl; exact KBL|]; split; [exact CEIL|]; split; [exact SPT|]; split; [exact SP16 | exact ETP]
      | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HRc HTc STc.
    eapply K; [exact HEAPc | exact AGc | exact WMc | exact MIc | exact HRc | exact HTc | exact STc].
  Qed.

  Lemma mulc_partA : forall (Σ : rts RT) (Q : config -> Prop) (OW LB : list block) (bR bT bA bB : block)
      (fuel k tna tnb : nat) (TT Dt : Z) (Tl : list Z) F fc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    (part_stackA CS8A k <= CST)%Z -> mulc_tpreA TT Dt Tl ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length la = (Nat.pow 2 k + tna)%nat -> length lb = (Nat.pow 2 k + tnb)%nat ->
    (4 * Nat.pow 2 k <= bn_dmax br)%nat -> (8 * Nat.pow 2 k <= length Tl)%nat ->
    rw_cells bgasegs m (SP + -112) [C8 (Z_to_bv 64 (al + bl))] ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB Dr Dt Da Db (4 * Nat.pow 2 k) (length Tl) (length la) (length lb) /\
     (ACEIL <= lo)%Z /\ (SP + -112 + 16 <= USTACK_TOP)%Z /\ ((SP + -112) mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) (SP + -112) x /\ ~ (Dr <= x < Dr + 8 * Z.of_nat (4 * Nat.pow 2 k))%Z
                          /\ ~ (Dt <= x < Dt + 8 * Z.of_nat (length Tl))%Z) m m2 ->
       wmono bgasegs m m2 -> mem_inv bgasegs m2 ->
       limbs_at bgasegs m2 Dr (fst (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       limbs_at bgasegs m2 Dt (snd (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       stk bgasegs m2 lo (SP + -112) ->
       evt bgasegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 0x22ac54) SPF gp tp u0 u1 u2 sp x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 R)
                  (Z_to_bv 64 al) (Z_to_bv 64 bl) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) (Z_to_bv 64 (al + bl)) u3 u4 u5 u6)
             F2 (Z_to_bv 64 0x22ac54) fc2 None m2 (seg_rom bgasegs))) ->
    evt bgasegs (kpost Σ Q) (ST F fc 0x22abf0 m x1 t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HCS TPRE HK3 HKF HK26 HTA HTB HD1 HD2 ELA ELB HD HSC FRs (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    destruct TPRE as (LLT & HTd & HLT & HWT & RT' & TREST).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 TREST))))) as ACT.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 TREST))))) as (ALT & PT & TLO).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & _ & SHL & _).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (4 * Nat.pow 2 k) (bn_buf br)) in *.
    assert (LRl : length Rl = (4 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    assert (HLR : limbs_at bgasegs m Dr Rl) by (subst Rl; apply (BnKaraMem.limbs_at_firstn bgasegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at bgasegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgasegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    pose proof (munch_refl [(R, R + 24)]%Z m) as MU.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR; lia). clear SHR.

    do 2 zstep. shl. chk0.
    do 2 zstep. shl. zstep. chk0.
    do 2 zstep. shl. chk0.
    do 2 zstep. shl. chk0.
    do 4 zstep.
    zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 ELA P2; lia).
    zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 ELB P2; lia).
    zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    zstep.

    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB).
    destruct TREST as (ST1 & DTA & DTB & DTR & _).
    eapply call_partA with (CS8 := CS8A) (fuel := fuel) (k := k) (a := la) (b := lb) (tna := tna) (tnb := tnb) (R := Rl) (T := Tl)
        (RP := Dr) (AP := Da) (BP := Db) (TQ := Dt) (lo := lo) (SPz := (SP + -112)%Z) (bR := bR) (bT := bT) (bA := bA) (bB := bB);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact (bn_mul_part_recursive_closedA fuel)
      | exact LLA | exact LLB | subst Rl; apply limbs_firstn; exact LBR | exact LLT
      | exact HK3 | exact HKF | exact HK26 | exact HTA | exact HTB | exact HD1 | exact HD2 | exact ELA | exact ELB | exact LRl | exact HSC
      | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia | apply unsigned_lit; clear - RNG; lia
      | apply unsigned_lit; clear - P2 AL23 ELA; lia
      | rewrite unsigned_lit by (clear - ELA AL23; lia); clear - ELA; lia | rewrite unsigned_lit by (clear - ELB BL23; lia); clear - ELB; lia
      | apply unsigned_lit; clear - RT' RNG; lia
      | exact HLA | exact HLB | exact HLR | exact HLT
      | rewrite LRl; replace Dr with (Dr + 0)%Z by lia; eapply wr_at_sub; [exact HW | lia | lia | clear - HD; unfold bn_dmax in *; lia]
      | exact HWT
      | rewrite LRl; clear - DA HD; unfold bn_dmax in *; lia | rewrite LRl; clear - DB HD; unfold bn_dmax in *; lia
      | clear - DTA; lia | clear - DTB; lia
      | rewrite LRl; clear - DTR HD; unfold bn_dmax in *; lia
      | clear - RNG HCS; lia | rewrite LRl; clear - RNG HD HCS; unfold bn_dmax in *; lia | clear - RNG RT' HCS; lia
      | clear - RNG HCS; lia | clear - RNG HCS; lia
      | split; [exact HEAP|]; split; [rewrite LRl; exact KBL|]; split; [exact CEIL|]; split; [exact SPT|]; split; [exact SP16 | exact ETP]
      | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HRc HTc STc.
    eapply K; [exact HEAPc | exact AGc | exact WMc | exact MIc | exact HRc | exact HTc | exact STc].
  Qed.
End Core.
