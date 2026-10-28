(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require BnKaraMem W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require Import BnAPure.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnA Require W_mul_core.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA BnRepDefs AsStruct ImplA RtCallA BnCallsA BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_rec_top AW_mul_part_recursive AW_kara_closedA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2418040 => 2
  | 2418052 => 1
  | 2418056 => 2
  | 2418100 => 2
  | 2418104 => 1
  | 2418108 => 2
  | 2418152 => 1
  | 2418156 => 2
  | 2418200 => 1
  | 2418204 => 2
  | 2418236 => 2
  | 2418240 => 1
  | 2418244 => 2
  | 2418404 => 2
  | 2418408 => 1
  | 2418412 => 2
  | 2418428 => 1
  | 2418432 => 2
  | 2418460 => 1
  | 2418464 => 1
  | 2418468 => 2
  | 2418508 => 2
  | 2418512 => 1
  | 2418516 => 1
  | 2418520 => 2
  | 2418640 => 2
  | 2418644 => 1
  | 2418648 => 2
  | 2418752 => 1
  | 2418756 => 2
  | 2418796 => 2
  | 2418800 => 1
  | 2418804 => 1
  | 2418808 => 2
  | 2418932 => 1
  | 2418936 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
(* [comment removed for export] *)
Definition MULC_TAIL : Z := 0x24e8f4.

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

  (* [comment removed for export] *)
  Definition mulc_preA : Prop :=
    limbs la /\ limbs lb /\ bn_okm br /\ (al < 8388608 /\ bl < 8388608)%Z /\
    (0 < R /\ R + 24 <= lo /\ 0 < A /\ A + 8 <= lo /\ 0 < B /\ B + 8 <= lo /\
     0 <= Dr /\ Dr + 8 * dmx <= lo /\ 0 <= Da /\ Da + 8 * al <= lo /\ 0 <= Db /\ Db + 8 * bl <= lo /\
     0 <= CST /\ lo <= SP - 112 - CST /\ SP <= 140737488355328)%Z /\
    (R + 24 <= Dr \/ Dr + 8 * dmx <= R)%Z /\ (R + 24 <= Da \/ Da + 8 * al <= R)%Z /\ (R + 24 <= Db \/ Db + 8 * bl <= R)%Z /\
    (Dr + 8 * dmx <= Da \/ Da + 8 * al <= Dr)%Z /\ (Dr + 8 * dmx <= Db \/ Db + 8 * bl <= Dr)%Z /\
    (* [comment removed for export] *)
    ((A + 8 <= R \/ R + 24 <= A) /\ (B + 8 <= R \/ R + 24 <= B))%Z /\
    (* [comment removed for export] *)
    (R mod 8 = 0 /\ A mod 8 = 0 /\ B mod 8 = 0 /\ Dr mod 8 = 0 /\ Da mod 8 = 0 /\ Db mod 8 = 0)%Z /\
    ((R + 24 <= SHLO \/ SHHI <= R) /\ (Dr + 8 * dmx <= SHLO \/ SHHI <= Dr) /\ SHHI <= lo /\
     (Dr + 8 * dmx <= 65536 \/ 12570624 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12570624 <= R))%Z.
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
     (Dr + 8 * dmx <= 65536 \/ 12570624 <= Dr) /\ 0 < Dr /\ 0 < Da /\ 0 < Db /\ (R + 24 <= 65536 \/ 12570624 <= R))%Z.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  Definition mulc_memA : Prop :=
    rw_cells bsegs m R (bn_cells Dr br) /\ u64arr bsegs m Dr (wlimbs (bn_buf br)) /\
    rw_cells bsegs m A [C8 (wz Da)] /\ rw_cells bsegs m B [C8 (wz Db)] /\
    limbs_at bsegs m Da la /\ limbs_at bsegs m Db lb /\
    stk bsegs m lo (SP + -112) /\ mem_inv bsegs m /\
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m /\
    acc bsegs m R 24 /\ acc bsegs m A 8 /\ acc bsegs m B 8 /\
    acc bsegs m Dr (8 * dmx) /\ acc bsegs m Da (8 * al) /\ acc bsegs m Db (8 * bl).
  Hypothesis MEM : mulc_memA.

  (* [comment removed for export] *)
  Definition mulc_postA (F : bvmap 5 word) (fc : bv 32) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x27 : word) (W : list (Z * Z)) (topn : nat) (w : list Z)
      (Q : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
               F (Z_to_bv 64 MULC_TAIL) fc None m' (seg_rom bsegs)
      /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' R [C8 (wz Dr); C4 (wz (Z.of_nat topn)); C4 (wz dmx); C4 (wz (Z.b2z (bn_neg br))); C4 (wz (bn_flags br))]
      /\ limbs_at bsegs m' Dr w /\ stk bsegs m' lo (SP + -112) /\ Q m'.

  (* [comment removed for export] *)
  Notation ST F fc pc mm x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6 :=
    (MS (mkR x1 SPF gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R)
             (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma P_off : forall len, (0 <= len)%Z -> (len <= 8 * dmx)%Z -> offshW [(Dr, Dr + len); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z.
  Proof.
    intros len H0 H1. pose proof P_sh as (S1 & S2 & S3 & _). pose proof P_rng as RNG.
    cbn [offshW]. unfold SHLO, SHHI in *. repeat split; lia.
  Qed.

  Ltac ubp P A := unfold ub_ptr_ok; intros _; split; [exact P | exact A].
  (* [comment removed for export] *)
  Lemma mulc_normalA : forall F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6,
    (length la + length lb <= bn_dmax br)%nat -> (240 <= CST)%Z ->
    evt bsegs (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 x27
                 [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z (length la + length lb) (mul_normal la lb) (fun _ => True))
      (ST F fc 0x24e7d0 m x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HD HCST.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB). pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & SHDr & SHL & OFI & PDr & PDa & PDb & _). pose proof P_structs as (SRA & SRB).
    pose proof (munch_refl [(Dr, Dr + 8 * (al + bl)); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (P_off (8 * (al + bl)) ltac:(clear; lia) ltac:(clear - HD; unfold bn_dmax in *; lia)) as OFF.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at bsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    (* [comment removed for export] *)
    do 3 (ub; zstep). ub; shl. ub; chk0.
    ub; zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    (* [comment removed for export] *)
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 3 (ub; zstep). do 2 (ub; zstep).
    assert (HLA0 : limbs_at bsegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at bsegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    pose proof (acc_munch bsegs _ m m0 Dr (8 * dmx) ACDr MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDr0.
    pose proof (acc_munch bsegs _ m m0 Da (8 * al) ACDa MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDa0.
    pose proof (acc_munch bsegs _ m m0 Db (8 * bl) ACDb MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDb0.
    pose proof P_sh as (_ & _ & _ & _ & _ & _ & _ & OFIR).
    pose proof (shb_cells_munch bsegs _ _ _ m m0 SHBC MUt ltac:(cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell; clear - OFIR; lia)
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

  (* [comment removed for export] *)
  Lemma mulc_comba8A : forall CS8 F fc x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6,
    comba8_aspec CS8 -> (CS8 <= CST)%Z -> length la = 8%nat -> length lb = 8%nat -> (16 <= bn_dmax br)%nat ->
    evt bsegs (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 x27
                 [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z 16 (mul_comba8 la lb) (fun _ => True))
      (ST F fc 0x24e63c m x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x25 x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros C8 HCS LA8 LB8 HD.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_sarr as (SA1 & SA2 & SA3). pose proof P_disj as (DA & DB). pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & SHDr & SHL & OFI & PDr & PDa & PDb & OFIR). pose proof P_structs as (SRA & SRB).
    pose proof (munch_refl [(Dr, Dr + 8 * 16); (R, R + 24); (SP - 112 - CST, SP + -112)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (P_off (8 * 16) ltac:(clear; lia) ltac:(clear - HD; unfold bn_dmax in *; lia)) as OFF.
    pose proof (munch_refl [(R, R + 24)]%Z m) as MUt.
    assert (HW : wr_at bsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    (* [comment removed for export] *)
    do 3 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    (* [comment removed for export] *)
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 3 (ub; zstep).
    assert (HLA0 : limbs_at bsegs m0 Da la) by (eapply limbs_at_transport; [exact HLA | exact MUt | cbn [disjoint_from]; clear - SA2; lia]).
    assert (HLB0 : limbs_at bsegs m0 Db lb) by (eapply limbs_at_transport; [exact HLB | exact MUt | cbn [disjoint_from]; clear - SA3; lia]).
    pose proof (acc_munch bsegs _ m m0 Dr (8 * dmx) ACDr MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDr0.
    pose proof (acc_munch bsegs _ m m0 Da (8 * al) ACDa MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDa0.
    pose proof (acc_munch bsegs _ m m0 Db (8 * bl) ACDb MUt ltac:(cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR RNG; lia) ltac:(clear - RNG; lia) ltac:(clear - RNG; lia)) as ACDb0.
    pose proof (shb_cells_munch bsegs _ _ _ m m0 SHBC MUt ltac:(cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell; clear - OFIR; lia)
                  ltac:(cbn [disjoint_from]; unfold g_shadow_memory_dynamic_address; clear - OFIR; lia)) as SHBC0.
    clear HLA HLB.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    ub; zstep.
    eapply (call_comba8A (mulc_postA F fc x8 x9 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R) (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) x25 x27
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
    ub; zstep. apply evt_done.
    unfold mulc_postA. do 16 eexists. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx HCS. lia. }
    split; [eapply wmono_trans; [exact WM | exact WMc]|]. split; [exact MIc|].
    split. { eapply rw_cells_transport; [exact SR | exact MUc | exact WMc | cbn; clear - SA1 RNG HD HCS; unfold bn_dmax in *; lia]. }
    split; [exact HRc|]. split; [exact STc | exact I].
  Qed.
  (* [comment removed for export] *)
  Definition mulc_tpreA (TT Dt : Z) (Tl : list Z) : Prop :=
    limbs Tl /\ rw_cells bsegs m TT [C8 (wz Dt)] /\ limbs_at bsegs m Dt Tl /\ wr_at bsegs m Dt (8 * Z.of_nat (length Tl)) /\
    (0 <= Dt /\ Dt + 8 * Z.of_nat (length Tl) <= lo)%Z /\
    (R + 24 <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= R)%Z /\
    (Dt + 8 * Z.of_nat (length Tl) <= Da \/ Da + 8 * al <= Dt)%Z /\ (Dt + 8 * Z.of_nat (length Tl) <= Db \/ Db + 8 * bl <= Dt)%Z /\
    (Dr + 8 * dmx <= Dt \/ Dt + 8 * Z.of_nat (length Tl) <= Dr)%Z /\
    (* [comment removed for export] *)
    acc bsegs m TT 8 /\ (TT mod 8 = 0 /\ 0 < TT /\ TT + 8 <= lo)%Z /\ (Dt mod 8 = 0 /\ 0 < Dt)%Z.

  (* [comment removed for export] *)
  Lemma mulc_recA : forall (Σ : rts RT) (Q : config -> Prop) (OW LB : list block) (bR bT bA bB : block)
      (k da db : nat) (TT Dt : Z) (Tl : list Z) F fc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    (rec_stackA CS8A k <= CST)%Z -> mulc_tpreA TT Dt Tl ->
    (1 <= k <= 26)%nat -> (da <= 1)%nat -> (db <= 1)%nat -> length la = (Nat.pow 2 k - da)%nat -> length lb = (Nat.pow 2 k - db)%nat ->
    (2 * Nat.pow 2 k <= bn_dmax br)%nat -> (scratch_rec k <= length Tl)%nat ->
    rw_cells bsegs m (SP + -112) [C8 (Z_to_bv 64 TT)] ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB Dr Dt Da Db (2 * Nat.pow 2 k) (length Tl) (length la) (length lb) /\
     (ACEIL <= lo)%Z /\ (SP + -112 + 16 <= USTACK_TOP)%Z /\ ((SP + -112) mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) (SP + -112) x /\ ~ (Dr <= x < Dr + 8 * Z.of_nat (2 * Nat.pow 2 k))%Z
                          /\ ~ (Dt <= x < Dt + 8 * Z.of_nat (length Tl))%Z) m m2 ->
       wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 Dr (fst (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       limbs_at bsegs m2 Dt (snd (mul_recursive k la lb da db (firstn (2 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       stk bsegs m2 lo (SP + -112) ->
       evt bsegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 0x24e7bc) SPF gp tp u0 u1 u2 sp x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R)
                  (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 SHB) x27 u3 u4 u5 u6)
             F2 (Z_to_bv 64 0x24e7bc) fc2 None m2 (seg_rom bsegs))) ->
    evt bsegs (kpost Σ Q) (ST F fc 0x24e748 m x1 t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HCS TPRE HK HDA HDB ELA ELB HD HSC FRs (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    (* [comment removed for export] *)
    destruct TPRE as (LLT & HTd & HLT & HWT & RT' & TREST).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 TREST))))) as ACT.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 TREST))))) as ((ALT & PT & TLO) & ALDt & PDt).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & _ & SHL & _).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (2 * Nat.pow 2 k) (bn_buf br)) in *.
    assert (LRl : length Rl = (2 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    assert (HLR : limbs_at bsegs m Dr Rl) by (subst Rl; apply (BnKaraMem.limbs_at_firstn bsegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at bsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    pose proof (munch_refl [(R, R + 24)]%Z m) as MU.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR; lia). clear SHR.
    (* [comment removed for export] *)
    ub; zstep.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 4 (ub; zstep).
    ub; zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 ELB HDB P2; lia).
    ub; zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 ELA HDA P2; lia).
    ub; zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    ub; zstep.
(* [comment removed for export] *)
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
      | pose proof P_sh as (_ & _ & _ & _ & PDr & PDa & PDb & _);
        unfold kara_ub; split; [ubp PDr ALDr|]; split; [ubp PDa ALDa|]; split; [ubp PDb ALDb | ubp PDt ALDt]
      | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HRc HTc STc.
    eapply K; [exact HEAPc | exact AGc | exact WMc | exact MIc | exact HRc | exact HTc | exact STc].
  Qed.
  (* [comment removed for export] *)
  Lemma mulc_partA : forall (Σ : rts RT) (Q : config -> Prop) (OW LB : list block) (bR bT bA bB : block)
      (fuel k tna tnb : nat) (TT Dt : Z) (Tl : list Z) F fc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x27 t3 t4 t5 t6,
    (part_stackA CS8A k <= CST)%Z -> mulc_tpreA TT Dt Tl ->
    (3 <= k)%nat -> (k <= fuel)%nat -> (k <= 26)%nat ->
    (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
    length la = (Nat.pow 2 k + tna)%nat -> length lb = (Nat.pow 2 k + tnb)%nat ->
    (4 * Nat.pow 2 k <= bn_dmax br)%nat -> (8 * Nat.pow 2 k <= length Tl)%nat ->
    rw_cells bsegs m (SP + -112) [C8 (Z_to_bv 64 TT)] ->
    (AHEAP Σ OW LB m /\ kara_blocks OW LB bR bT bA bB Dr Dt Da Db (4 * Nat.pow 2 k) (length Tl) (length la) (length lb) /\
     (ACEIL <= lo)%Z /\ (SP + -112 + 16 <= USTACK_TOP)%Z /\ ((SP + -112) mod 16 = 0)%Z /\ tp = wz TP_A) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) (SP + -112) x /\ ~ (Dr <= x < Dr + 8 * Z.of_nat (4 * Nat.pow 2 k))%Z
                          /\ ~ (Dt <= x < Dt + 8 * Z.of_nat (length Tl))%Z) m m2 ->
       wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 Dr (fst (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       limbs_at bsegs m2 Dt (snd (mul_part_recursive fuel k la lb tna tnb (firstn (4 * Nat.pow 2 k) (bn_buf br)) Tl)) ->
       stk bsegs m2 lo (SP + -112) ->
       evt bsegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 0x24e8dc) SPF gp tp u0 u1 u2 sp x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 R)
                  (Z_to_bv 64 al) (Z_to_bv 64 (al + bl)) (Z_to_bv 64 bl) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 SHB) x27 u3 u4 u5 u6)
             F2 (Z_to_bv 64 0x24e8dc) fc2 None m2 (seg_rom bsegs))) ->
    evt bsegs (kpost Σ Q) (ST F fc 0x24e868 m x1 t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) x27 t3 t4 t5 t6).
  Proof.
    intros until t6. intros HCS TPRE HK3 HKF HK26 HTA HTB HD1 HD2 ELA ELB HD HSC FRs (HEAP & KBL & CEIL & SPT & SP16 & ETP) K.
    pose proof MEM as (SR & UR & HAd & HBd & HLA & HLB & ST & MI & SHBC & ACR & ACA & ACB & ACDr & ACDa & ACDb).
    destruct TPRE as (LLT & HTd & HLT & HWT & RT' & TREST).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 TREST))))) as ACT.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 TREST))))) as ((ALT & PT & TLO) & ALDt & PDt).
    pose proof P_lists as (LLA & LLB & OKR & (AL23 & BL23)). pose proof P_rng as RNG.
    pose proof P_al as (ALR & ALA & ALB & ALDr & ALDa & ALDb).
    pose proof P_sh as (SHR & _ & SHL & _).
    pose proof OKR as (LBR & _).
    set (Rl := firstn (4 * Nat.pow 2 k) (bn_buf br)) in *.
    assert (LRl : length Rl = (4 * Nat.pow 2 k)%nat) by (subst Rl; apply firstn_length_le; unfold bn_dmax in HD; exact HD).
    assert (HLR : limbs_at bsegs m Dr Rl) by (subst Rl; apply (BnKaraMem.limbs_at_firstn bsegs); apply limbs_at_of_u64arr; exact UR).
    assert (HW : wr_at bsegs m Dr (8 * dmx)).
    { apply (limbarr_limbs_at bsegs) in UR. destruct UR as [_ HW]. unfold bn_dmax. exact HW. }
    clear UR. unfold bn_cells in SR.
    assert (P2 : (0 < Z.of_nat (Nat.pow 2 k))%Z) by (pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia).
    pose proof (munch_refl [(R, R + 24)]%Z m) as MU.
    assert (OFF : offshW [(R, R + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - SHR; lia). clear SHR.
    (* [comment removed for export] *)
    ub; zstep.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 2 (ub; zstep). ub; shl. ub; chk0.
    do 4 (ub; zstep).
    ub; zstep. rewrite (bn_swrap32_small (bl - Z.of_nat (Nat.pow 2 k))) by (clear - BL23 ELB P2; lia).
    ub; zstep. rewrite (bn_swrap32_small (al - Z.of_nat (Nat.pow 2 k))) by (clear - AL23 ELA P2; lia).
    ub; zstep.
    assert (ESPF : bv_unsigned SPF = (SP + -112)%Z) by (apply unsigned_lit; clear - RNG; lia).
    ub; zstep.
(* [comment removed for export] *)
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
      | pose proof P_sh as (_ & _ & _ & _ & PDr & PDa & PDb & _);
        unfold kara_ub; split; [ubp PDr ALDr|]; split; [ubp PDa ALDa|]; split; [ubp PDb ALDb | ubp PDt ALDt]
      | ].
    rewrite LRl. intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F2 fc2 HEAPc AGc WMc MIc HRc HTc STc.
    eapply K; [exact HEAPc | exact AGc | exact WMc | exact MIc | exact HRc | exact HTc | exact STc].
  Qed.
End Core.
