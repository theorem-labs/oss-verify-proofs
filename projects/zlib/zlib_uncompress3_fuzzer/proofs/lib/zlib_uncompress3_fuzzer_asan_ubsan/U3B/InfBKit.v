(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface U2BGlue InfBBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma sep_ind : forall a n b k, (a + n <= b \/ b + k <= a) ->
  0 <= a -> a + n <= 2^47 -> 0 <= b -> b + k <= 2^47 ->
  exists c : Z, 0 <= c <= 1 /\ a + n <= b + c * 2^48 /\ b + k <= a + (1 - c) * 2^48.
Proof. intros a n b k [H|H] ? ? ? ?; [exists 0| exists 1]; lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section K.
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (cx : ictx) (ly : ilay).
Notation S := (c_p cx).   Notation D := (c_q cx).   Notation n := (c_n cx).
Notation OB := (c_ob cx). Notation osz := (c_osz cx). Notation Wd := (c_w cx).
Notation SP := (l_SP ly). Notation SPA := (l_SPA ly). Notation Zs := (l_Zs ly). Notation F0 := (l_F0 ly). Notation lo := (l_lo ly).

Definition blk_facts (A N : Z) : Prop :=
  6811648 <= A /\ A + N <= ATOP /\ exists b : Z, 0 <= b <= 1 /\ A + N <= 2147446784 + b * 0x7fffff800000 /\ 0x10007fff8000 * b <= A.
Lemma blk_facts_of : forall A N, ablk A (A + N) -> blk_facts A N.
Proof.
  intros A N H. pose proof (ablk_lin _ _ H) as (B1 & _ & B3 & _). unfold AIMG_HI in B1.
  destruct (ablk_ind _ _ H) as (b & Hb & H1 & H2). unfold KLS in H1.
  split; [lia|]. split; [exact B3|]. exists b. split; [exact Hb|]. split; [exact H1| exact H2].
Qed.

Definition pair_ind (A N B K : Z) : Prop :=
  exists c : Z, 0 <= c <= 1 /\ A + N <= B + c * 2^48 /\ B + K <= A + (1 - c) * 2^48.

Definition inf_lin : Prop :=
  exists Fu, Zs = Fu + 32 /\ Fu mod 256 = 0 /\ In (mkABlock (ABFake 2) Fu 256) LB
  /\ blk_facts S 7176 /\ blk_facts Fu 256 /\ blk_facts F0 64
  /\ 6341920 <= D /\ D + n <= ATOP
  /\ (exists bD : Z, 0 <= bD <= 1 /\ D + n <= 2147446784 + bD * 0x7fffff800000 /\ 0x10007fff8000 * bD <= D)
  /\ pair_ind S 7176 Fu 256 /\ pair_ind S 7176 F0 64 /\ pair_ind Fu 256 F0 64
  /\ pair_ind S 7176 D n /\ pair_ind Fu 256 D n /\ pair_ind F0 64 D n.

Lemma inf_facts : forall m, AHEAP AI L RNG stA LB m -> inf_ctx cx ly AI RNG LB -> inf_lin.
Proof.
  intros m AH CTX.
  destruct CTX as (S16 & SB & (ps & HPS & PAYH) & (Fu & HFU & ZSE & FU256 & FUB) & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                   & D1 & NR & D16 & RD & RSD & _).
  atop_facts.
  assert (DIS : forall b1 b2, In b1 LB -> In b2 LB -> b1 <> b2 ->
                 ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1)
    by (intros; eapply (AI_blocks_disjoint AI); eauto).
  pose proof (ablk_lin _ _ SB) as (SB1 & SB0 & SB3 & SB4). pose proof (ablk_lin _ _ FUB) as (UB1 & UB0 & UB3 & UB4).
  pose proof (ablk_lin _ _ F0B) as (FB1 & FB0 & FB3 & FB4). unfold AIMG_HI in *.
  exists Fu. split; [exact ZSE|]. split; [exact FU256|]. split; [exact HFU|].
  split; [apply blk_facts_of; exact SB|]. split; [apply blk_facts_of; exact FUB|]. split; [apply blk_facts_of; exact F0B|].
  assert (DB : 6341920 <= D /\ D + n <= ATOP /\
               (exists bD : Z, 0 <= bD <= 1 /\ D + n <= 2147446784 + bD * 0x7fffff800000 /\ 0x10007fff8000 * bD <= D) /\
               (forall b, In b LB -> (forall pd, b <> HB pd D n) -> 0 <= ab_addr b -> ab_addr b + ab_size b <= 2^47 -> 6811648 <= ab_addr b ->
                  pair_ind (ab_addr b) (ab_size b) D n)).
  { destruct PAYH as [(pd & HPD & NP & NEP)|[N0 DE]].
    - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HPD) as (B1 & B2 & B3). cbn [ab_addr ab_size] in *. unfold AIMG_HI in *.
      split; [lia|]. split; [lia|].
      split. { pose proof (AI_block AI _ _ _ _ _ pd D n AH HPD) as (_ & (BK & _) & _). destruct (ablk_ind _ _ BK) as (bD & Hb & H1 & H2). unfold KLS in H1. exists bD. lia. }
      intros b Hb NE A0 A47 _. apply sep_ind; try lia.
      specialize (DIS b (HB pd D n) Hb HPD (NE pd)). cbn [ab_addr ab_size] in DIS. exact DIS.
    - rewrite N0, DE. split; [lia|]. split; [lia|]. split; [exists 0; lia|]. intros b Hb _ A0 A47 AI0. exists 1. lia. }
  destruct DB as (DB1 & DB2 & DBB & DBP).
  split; [exact DB1|]. split; [exact DB2|]. split; [exact DBB|].
  split. { apply sep_ind; try lia. specialize (DIS _ _ HPS HFU ltac:(discriminate)). exact DIS. }
  split. { apply sep_ind; try lia. specialize (DIS _ _ HPS HF0 ltac:(discriminate)). exact DIS. }
  split. { apply sep_ind; try lia. specialize (DIS _ _ HFU HF0 ltac:(discriminate)). exact DIS. }
  split. { apply (DBP (HB ps S 7176) HPS); cbn [ab_addr ab_size]; try lia. intros pd' Q. inversion Q. subst pd'.
           destruct PAYH as [(pd & HPD & NP & NE)|[N0 DE]]; [| lia].
           pose proof (hb_same_id LB ps S 7176 D n (AI_hb_ids AI _ _ _ _ _ AH) HPS ltac:(rewrite <- H1, <- H2 in *; exact HPS)) as _. 
           pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND.
           assert (X : HB pd D n = HB ps D n \/ pd <> ps) by (right; exact NE).
           pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (HB pd D n) AH HPS HPD ltac:(intros Y; inversion Y; congruence)) as DD.
           cbn [ab_addr ab_size] in DD. lia. }
  split. { apply (DBP (mkABlock (ABFake 2) Fu 256) HFU); cbn [ab_addr ab_size]; try lia. intros pd Q. discriminate. }
  apply (DBP (mkABlock (ABFake 0) F0 64) HF0); cbn [ab_addr ab_size]; try lia. intros pd Q. discriminate.
Qed.

Definition inf_djs : Prop :=
     disjoint_from (inf_W cx ly) (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880))
  /\ disjoint_from (inf_W cx ly) (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880))
  /\ disjoint_from (inf_W cx ly) (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + 32768 - (Z.shiftr OB 3 + 2147450880))
  /\ disjoint_from (inf_W cx ly) (shad D) (shad (D + n - 1) + 1 - shad D)
  /\ disjoint_from (inf_W cx ly) 2147469580 (2147469836 - 2147469580) /\ disjoint_from (inf_W cx ly) 2147469900 (2147469916 - 2147469900)
  /\ disjoint_from (inf_W cx ly) 2147468552 (2147468556 - 2147468552) /\ disjoint_from (inf_W cx ly) 2147468556 (2147468557 - 2147468556)
  /\ disjoint_from (inf_W cx ly) 2147469532 (2147469576 - 2147469532).

Lemma inf_dj : inf_ctx cx ly AI RNG LB -> inf_lin -> inf_djs.
Proof.
  intros CTX (Fu & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & _ & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & _).
  destruct CTX as (S16 & SB & _ & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                   & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & _).
  atop_facts. unfold KEND in SPT. unfold inf_djs, inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
  rewrite !shad_div. unfold ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  repeat split; try exact I; Z.div_mod_to_equations; lia.
Qed.


Lemma inf_hid_step : forall LBc m0 fw saved fk fksh m m',
  inf_ctx cx ly AI RNG LB -> inf_lin ->
  inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
  munch (inf_W cx ly) m m' -> wmono bsegs m m' ->
  inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m'.
Proof.
  intros LBc m0 fw saved fk fksh m m' CTX LIN HID MU WM.
  pose proof (inf_dj CTX LIN) as (DJZ & DJS & DJO & DJP & DJLF & DJDF & DJOR & DJO6 & DJIT).
  destruct HID as (AH & SHZ & SHS & SHO & WIN & UNP & SAVED & SZ1 & FK & SZ2 & FKSH & SZ3 & SUBL & CAG & SHLF & SHDF & SHOR & SHO6 & IT1 & IT2 & IT3 & IT4 & IT5 & IT6 & GAP & (obr & OBR) & WFU).
  destruct LIN as (Fu & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & (F1 & F2 & bF & BF0 & BF1 & BF2)
                   & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & (cSU & CSU0 & CSU1 & CSU2) & (cSF & CSF0 & CSF1 & CSF2) & (cUF & CUF0 & CUF1 & CUF2)
                   & (cSD & CSD0 & CSD1 & CSD2) & (cUD & CUD0 & CUD1 & CUD2) & (cFD & CFD0 & CFD1 & CFD2)).
  destruct CTX as (S16 & SB & (ps & HPS & PAYH) & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & (iv & OCI1 & OCI2 & OCI3) & ROB & ROBS & WDC
                   & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & _).
  atop_facts. unfold KEND in SPT.
  split.
  { eapply (AI_frame AI _ _ _ _ m m' _ AH MU WM). unfold inf_W.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HFU| lia| lia]|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB ps S 7176)); [exact HPS| cbn; lia| cbn; lia]|].
    constructor; [| constructor]. cbn [fst snd]. left. right. left. exists iv. split; [exact OCI1| lia]. }
  split; [exact (sh0_mu _ _ _ _ _ SHZ MU DJZ)|]. split; [exact (sh0_mu _ _ _ _ _ SHS MU DJS)|]. split; [exact (sh0_mu _ _ _ _ _ SHO MU DJO)|].
  split.
  { intros WN. destruct (WIN WN) as (SHW & FW). destruct WDC as [W0|(W16 & WB & (pw & HPW) & RW & RSW)]; [contradiction|].
    pose proof (ablk_lin _ _ WB) as (WB1 & WB0 & WB3 & WB4). unfold AIMG_HI in WB1.
    destruct (ablk_ind _ _ WB) as (bW & BW0 & BW1 & BW2). unfold KLS in BW1.
    assert (DIS : forall b1 b2, In b1 LB -> In b2 LB -> b1 <> b2 ->
                   ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1)
      by (intros; eapply (AI_blocks_disjoint AI); eauto).
    pose proof (DIS _ _ HPW HFU ltac:(discriminate)) as DWU. cbn [ab_addr ab_size] in DWU.
    assert (DWS : Wd + 32768 <= S \/ S + 7176 <= Wd).
    { destruct (N.eq_dec pw ps) as [E|NE].
      - subst pw. pose proof (hb_same_id LB ps Wd 32768 S 7176 (AI_hb_ids AI _ _ _ _ _ AH) HPW HPS) as Q. inversion Q.
      - pose proof (DIS _ _ HPW HPS ltac:(intros Q; inversion Q; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    split.
    - eapply sh0_mu; [exact SHW| exact MU|]. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia.
    - unfold f8arr in *. eapply u8arr_transport; [exact FW| exact MU| exact WM|]. rewrite map_length, seq_length.
      unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF. repeat split; try exact I; lia. }
  split.
  { eapply unpoisoned_munch; [exact UNP| exact MU|]. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
    rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  split; [| split; [exact SZ1|]].
  { eapply rw_cells_transport; [exact SAVED| exact MU| exact WM|]. rewrite SZ1. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
    repeat split; try exact I; lia. }
  split; [| split; [exact SZ2|]].
  { eapply rw_cells_transport; [exact FK| exact MU| exact WM|]. rewrite SZ2. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
    repeat split; try exact I; lia. }
  split; [| split; [exact SZ3|]].
  { eapply rw_cells_transport; [exact FKSH| exact MU| exact WM|]. rewrite SZ3. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  split; [exact SUBL|].
  split; [| split; [exact (sh0_mu _ _ _ _ _ SHLF MU DJLF)| split; [exact (sh0_mu _ _ _ _ _ SHDF MU DJDF)|
            split; [exact (sh0_mu _ _ _ _ _ SHOR MU DJOR)| split; [exact (shc_mu _ _ _ _ _ _ SHO6 MU DJO6)|]]]]].
  2:{ assert (DJ' : forall s1 s2, 2147469532 <= s1 -> s2 <= 2147469576 -> s1 <= s2 -> disjoint_from (inf_W cx ly) s1 (s2 - s1)).
      { intros s1 s2 A1 A2 A3. unfold inf_W in *. cbn [disjoint_from] in DJIT |- *. repeat split; try exact I; lia. }
      split; [exact (shc_mu _ _ _ _ _ _ IT1 MU (DJ' 2147469532 2147469539 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split; [exact (shc_mu _ _ _ _ _ _ IT2 MU (DJ' 2147469539 2147469540 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split; [exact (shc_mu _ _ _ _ _ _ IT3 MU (DJ' 2147469544 2147469551 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split; [exact (shc_mu _ _ _ _ _ _ IT4 MU (DJ' 2147469551 2147469552 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split; [exact (shc_mu _ _ _ _ _ _ IT5 MU (DJ' 2147469556 2147469564 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split; [exact (shc_mu _ _ _ _ _ _ IT6 MU (DJ' 2147469568 2147469576 ltac:(lia) ltac:(lia) ltac:(lia)))|].
      split.
      { eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM|]. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
        repeat split; try exact I; lia. }
      split; [| eapply wr_at_transport; [exact WFU| exact WM]].
      exists obr. eapply rw_cells_transport; [exact OBR| exact MU| exact WM|].
      cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. unfold inf_W. cbn [disjoint_from]. rewrite OBE. unfold A_OUTBUF.
      repeat split; try exact I; lia. }
  eapply client_agree_trans; [exact CAG|].
  eapply (client_agree_munch AI LBc _ _ (inf_W cx ly) m m' MU WM). intros a Ha HC HN.
  assert (NZ : ~ (Zs <= a < Zs + 112)) by (intros X; apply HN; exists (Zs, Zs + 112); split; [left; reflexivity| exact X]).
  assert (NS : ~ (S <= a < S + 7176)) by (intros X; apply HN; exists (S, S + 7176); split; [right; left; reflexivity| exact X]).
  assert (NO : ~ (OB <= a < OB + osz)) by (intros X; apply HN; exists (OB, OB + osz); split; [right; right; left; reflexivity| exact X]).
  unfold inf_W. cbn [outside]. split; [| tauto].
  destruct HC as [C|[(iv' & Hiv & C)|[(b & Hb & C)|(a' & Ha' & ->)]]].
  - lia.
  - pose proof (AI_aci_img AI iv' Hiv). unfold AIMG_HI in *. lia.
  - pose proof (AI_block_bounds AI _ _ _ _ _ b AH (SUBL b Hb)) as (B1 & B2 & B3). lia.
  - assert (0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv' & Hiv & X)|(c & A & k & Hb & X)]].
      - lia.
      - pose proof (AI_aci_img AI iv' Hiv). pose proof (AI_aci_lo AI iv' Hiv). unfold AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (SUBL _ Hb)) as (B1 & B2 & B3). cbn in B1, B2, B3. unfold AIMG_HI in *. lia. }
    pose proof (shad_in_band a' H0). unfold KLS in *. lia.
Qed.

End K.
End CANSEC1.

Ltac inf_arm_open_rn :=
  lazymatch goal with
  | CTX : inf_ctx ?cx ?ly ?AI ?RNG ?LB, HID : inf_hid ?cx ?ly ?AI ?L ?RNG ?stA ?LB _ _ _ _ _ _ ?m,
    VIS : inf_vis ?cx ?ly ?st _ _ _ _ ?payload _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m,
    RNH : IDefs.RNG ?cx ?st _ _, PLEN : Z.of_nat (length ?payload) = _ |- _ =>
      pose proof CTX as CTX0;
      let AH := fresh "AH" in
      let HIDx := fresh "HIDx" in
      pose proof HID as HIDx; and_elim HIDx 19%nat;
      intros AH SHZ SHS SHO _ UNP _ _ _ _ _ _ _ _ SHLF SHDF SHOR SHO6 _;
      pose proof (inf_facts AI L RNG stA LB cx ly m AH CTX) as LIN0;
      let DJx := fresh "DJx" in
      pose proof (inf_dj AI RNG LB cx ly CTX LIN0) as DJx; and_elim DJx 9%nat; intros DJZ DJS DJO DJP DJLF DJDF DJOR DJO6 DJIT;
      let LIN := fresh "LIN" in
      pose proof LIN0 as LIN;
      destruct LIN as (Fu & LIN); and_elim LIN 15%nat;
      intros ZSE FU256 HFU (S1 & S2 & bS & BS0 & BS1 & BS2) (U1 & U2 & bU & BU0 & BU1 & BU2) (F1 & F2 & bF & BF0 & BF1 & BF2)
             DL1 DL2 (bD & BD0 & BD1 & BD2) (cSU & CSU0 & CSU1 & CSU2) (cSF & CSF0 & CSF1 & CSF2) (cUF & CUF0 & CUF1 & CUF2)
             (cSD & CSD0 & CSD1 & CSD2) (cUD & CUD0 & CUD1 & CUD2) (cFD & CFD0 & CFD1 & CFD2);
      and_elim CTX 35%nat;
      intros S16 SB _ _ RZ RSZ HF0 F064 F0B RS RSS OBE OSZ OCI ROB ROBS WDC
             D1 NR D16 RD RSD LOC LOS SPAR SPA32 SP16 SPT RSTK RI RISH RSFU TABC1 TABC2 LBABLK;
      let VF := fresh "VISf" in pose proof VIS as VF;
      and_elim VIS 13%nat; intros FRM STRM SSC LENS WORK CODES TAIL OUT PAYB STK MI MNE BKOK;
      destruct cx as [u S D n OB osz Wd cin0 cout0 W0 K0 zc]; destruct ly as [SP SPA Zs F0 lo];
      destruct st as [mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
           t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
           t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo] in *;
      let RN := fresh "RN" in
      pose proof RNH as RN; unfold IDefs.RNG in RN;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
           t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
           t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in RN;
      first [ and_elim RN 33%nat; do 32 (let F := fresh "R" in intro F); intro RN
            | repeat (let F := fresh "R" in destruct RN as [F RN]) ];
      unfold inf_locals, strm_cells, istate_cells, itail_cells, inf_W in *;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo] in *;
      atop_facts; unfold KEND in SPT; subst OB; unfold A_OUTBUF in *;
      assert (Z8 : Zs mod 8 = 0) by (clear - ZSE FU256; Z.div_mod_to_equations; lia);
      assert (S8 : S mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia);
      assert (PL : Z.of_nat (length (map (Z_to_bv 8) payload)) = n) by (rewrite length_map; exact PLEN);
      assert (RFRM : rng RNG SPA 568) by (eapply rng_sub'; [exact RSTK| lia]);
      pose proof (munch_refl [(lo, SPA + 568); (Zs, Zs + 112); (S, S + 7176); (6341952, 6341952 + osz)] m) as MU;
      pose proof (wmono_refl bsegs m) as WM;
      hide_or WDC;
      try (match goal with HF : _ = 0 \/ _ = -1 |- _ => hide_or HF end)
  end.
Ltac inf_arm_open :=
  lazymatch goal with
  | VIS : inf_vis ?cx _ ?st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SI : sinv ?cx ?st _ _ |- _ =>
      let RN0 := fresh "RN0" in
      pose proof (proj1 SI) as RN0; inf_arm_open_rn; clear RN0
  end.

Ltac inf_mode_ne :=
  first [ eassumption
        | let X := fresh "X" in intros X; lazy in X; discriminate X
        | let X := fresh "X" in intros X; cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *; lia ].
Ltac inf_back_ok :=
  first [ eassumption
        | lazymatch goal with BK : back_ok _ _ |- _ => exact BK end
        | unfold back_ok; cbn [t_mode]; split; intros E; exfalso;
          first [ discriminate E
                | cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *; lia ] ].
Ltac inf_vis_close_bk tac :=
  unfold inf_vis, inf_locals, strm_cells, istate_cells, itail_cells;
  cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
       t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo];
  do 10 (split; [eassumption|]); split; [eassumption|]; split; [inf_mode_ne| tac].
Ltac inf_vis_close :=
  unfold inf_vis, inf_locals, strm_cells, istate_cells, itail_cells;
  cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
       t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo];
  do 10 (split; [eassumption|]); split; [eassumption|]; split; [inf_mode_ne| inf_back_ok].
Ltac inf_hid_close :=
  eapply inf_hid_step;
  [ lazymatch goal with H : inf_ctx _ _ _ _ _ |- inf_ctx _ _ _ _ _ => exact H end
  | eassumption | eassumption | eassumption | eassumption ].
