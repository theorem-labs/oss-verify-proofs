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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require BnKaraMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnA Require W_mul_core.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require AW_mul_core.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnIfaceA BnRepDefs AsStruct ImplA RtCallA BnCallsA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_rec_top AW_mul_part_recursive AW_kara_closedA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2268436 => 2
  | 2268448 => 1
  | 2268452 => 2
  | 2268496 => 2
  | 2268500 => 1
  | 2268504 => 2
  | 2268548 => 1
  | 2268552 => 2
  | 2268596 => 1
  | 2268600 => 2
  | 2268632 => 2
  | 2268636 => 1
  | 2268640 => 2
  | 2268800 => 2
  | 2268804 => 1
  | 2268808 => 2
  | 2268824 => 1
  | 2268828 => 2
  | 2268856 => 1
  | 2268860 => 1
  | 2268864 => 2
  | 2268904 => 2
  | 2268908 => 1
  | 2268912 => 1
  | 2268916 => 2
  | 2269036 => 2
  | 2269040 => 1
  | 2269044 => 2
  | 2269148 => 1
  | 2269152 => 2
  | 2269192 => 2
  | 2269196 => 1
  | 2269200 => 1
  | 2269204 => 2
  | 2269328 => 1
  | 2269332 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Definition MULC_TAIL : Z := 0x22a090.

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
     (Dr + 8 * dmx <= 65536 \/ 12554240 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12554240 <= R))%Z.
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
     (Dr + 8 * dmx <= 65536 \/ 12554240 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12554240 <= R))%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  Definition mulc_memA : Prop :=
    rw_cells bgbsegs m R (bn_cells Dr br) /\ u64arr bgbsegs m Dr (wlimbs (bn_buf br)) /\
    ro_cells bgbsegs m A [C8 (wz Da)] /\ rw_cells bgbsegs m B [C8 (wz Db)] /\
    limbs_at bgbsegs m Da la /\ limbs_at bgbsegs m Db lb /\
    stk bgbsegs m lo (SP + -112) /\ mem_inv bgbsegs m /\
    shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m /\
    acc bgbsegs m R 24 /\ acc bgbsegs m A 8 /\ acc bgbsegs m B 8 /\
    acc bgbsegs m Dr (8 * dmx) /\ acc bgbsegs m Da (8 * al) /\ acc bgbsegs m Db (8 * bl).
  Hypothesis MEM : mulc_memA.

  Definition mulc_postA (F : bvmap 5 word) (fc : bv 32) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (W : list (Z * Z)) (topn : nat) (w : list Z)
      (Q : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
               F (Z_to_bv 64 MULC_TAIL) fc None m' (seg_rom bgbsegs)
      /\ munch W m m' /\ wmono bgbsegs m m' /\ mem_inv bgbsegs m'
      /\ rw_cells bgbsegs m' R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]
      /\ limbs_at bgbsegs m' Dr w /\ stk bgbsegs m' lo (SP + -112) /\ Q m'.

  Notation ST F fc pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R)
             (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).

  Lemma P_off : forall len, (0 <= len)%Z -> (len <= 8 * dmx)%Z -> offshW [(Dr, Dr + len); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z.
  Proof.
    intros len H0 H1. pose proof P_sh as (S1 & S2 & S3 & _). pose proof P_rng as RNG.
    cbn [offshW]. unfold SHLO, SHHI in *. repeat split; lia.
  Qed.

  Ltac ubp P A := unfold ub_ptr_ok; intros _; split; [exact P | exact A].

  Lemma mulc_normalA : forall F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6,
    (length la + length lb <= bn_dmax br)%nat -> (240 <= CST)%Z ->
    evt bgbsegs (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 x27
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True))
      (ST F fc 0x229f6c m x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HD HCST.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB). pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & SHDr & SHL & OFI & PDr & PDa & PDb & _). pose proof P_structs as (SRA & SRB).
    pose proof (munch_refl [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
    pose proof (P_off (8 * (al + bl)) ltac:(clear; lia) ltac:(clear - HD; unfold bn_dmax in *; lia)) as OFF.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at bgbsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bgbsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.

    do 3 (ub; zstep). ub; shl. ub; chk0.
    ub; zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.

    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 3 (ub; zstep). do 2 (ub; zstep).
    assert (HLA0 : limbs_at bgbsegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at bgbsegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    pose proof (acc_munch bgbsegs _ m m0 Dr (8 * dmx) ACDr MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDr0.
    pose proof (acc_munch bgbsegs _ m m0 Da (8 * al) ACDa MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDa0.
    pose proof (acc_munch bgbsegs _ m m0 Db (8 * bl) ACDb MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDb0.
    pose proof P_sh as (_ & _ & _ & _ & _ & _ & _ & OFIR).
    pose proof (shb_cells_munch bgbsegs _ _ _ m m0 SHBC MUt ltac:(cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell; clear - OFIR; lia)
                  ltac:(cbn [disjoint_from]; unfold g_shadow_memory_dynamic_address; clear - OFIR; lia)) as SHBC0.
    clear HLA HLB.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    ub; zstep.
    eapply (call_mul_normalA (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 x27
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True)))
      with (a := la) (b := lb) (RP := Dr) (AP := Da) (BP := Db) (lo := lo) (SPz := (SP + -112)%Z);
      [ exact ESPF | apply ret_pc_even; [lia | reflexivity] | exact ST | exact MI | exact SHBC0 | exact mul_normal_okA
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
      | ubp PDr ALDr | ubp PDa ALDa | ubp PDb ALDb | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HRc STc.
    ub; zstep. apply evt_done.
    unfold mulc_postA. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCST. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [| exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCST; unfold bn_dmax in *; lia].
             unfold wz. rewrite Nat2Z.inj_add. exact SR. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.
End Core.

