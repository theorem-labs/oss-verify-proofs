From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_x2_defs huf421_kit_fill RZ_hft_x2_l1 RZ_hft_x2_l2.
Import ListNotations.
Open Scope Z_scope.

Lemma fill_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fill_epi : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : fmem)
    (SP lo DT : Z) (cw : list Z) (pos n v : Z) (fj : list byte),
  lo <= SP + -48 -> (DT + HUF_DTABLE_BYTES <= lo \/ SP <= DT) ->
  stk usegs m1 lo (SP + -48) -> rw_cells usegs m1 (SP + -48) [CB 8 fj; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
  munch [(DT + 4, DT + HUF_DTABLE_BYTES); (SP + -48, SP)] m m1 -> wmono usegs m m1 ->
  forall m' cw' n' v' (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  mem_inv usegs m' -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m1 m' -> wmono usegs m1 m' ->
  x2_cells m' DT cw' -> cells_written cw cw' pos n' v' -> n' = n -> v' = v ->
  evt usegs (huf_fillw_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP lo DT cw pos n v m)
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x259ec) fc None m' (seg_rom usegs)).
Proof.
  intros until fj. intros LOS DTS ST FR MU WM. intros until x31. intros MI MU' WM' CW CWR -> ->.
  pose proof (rw_cells_transport usegs _ _ _ _ _ FR MU' WM' ltac:(cbn; unfold HUF_DTABLE_BYTES in *; lia)) as FR'.
  pose proof (stk_transport_disjoint usegs _ _ _ _ _ ST MU' WM' ltac:(cbn; unfold HUF_DTABLE_BYTES in *; lia)) as ST'.
  clear FR ST.
  do 5 zstep. zstep. zstep.
  release_frame FR' ST' SP.
  apply evt_done. unfold huf_fillw_post.
  do 15 eexists. exists m', cw'.
  split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
    intros x Hx. cbn in Hx |- *. destruct Hx as [Hx _]. split; [exact Hx | exact I]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI|]. split; [exact ST'|]. split; [exact CW | exact CWR].
Qed.

Ltac fval :=
  rewrite ?fill_land1; shl2mul; repeat lor2add; rewrite ?Z.mod_small by lia; shr2div; rewrite ?Z.mod_small by lia;
  Z.div_mod_to_equations; lia.

Ltac fside := first [ eassumption | apply munch_refl | apply wmono_refl | (rewrite ?Z.mul_0_r; apply cells_written_refl) | reflexivity
                    | lia | fval ].

Ltac fke m1 fj :=
  lazymatch goal with |- context [KE1] => unfold KE1 | |- context [KE2] => unfold KE2 end;
  intros; eapply fill_epi with (m1 := m1) (fj := fj); first [ eassumption | lia ].

Ltac fempty m1 fj :=
  match goal with K : ?S + ?b = ?S + ?e |- _ =>
    let EB := fresh "EB" in assert (EB : e = b) by lia; subst e end;
  rewrite Z.sub_diag, Z.mul_0_r;
  eapply fill_epi with (m1 := m1) (fj := fj); fside.

Theorem huf_fillw_proof : huf_fillw_stmt.
Proof.
  unfold huf_fillw_stmt, huf_fillw_stmt_at, PHUF_FILLW.
  intros until bs. intros MI ST LO1 LO2 SPH CW DTL DTH DTE DTS SYB SYL SYH SYS DSY BGR ENR NBR TLR POSR POSH LVR BSR.
  pose proof (munch_refl [(DT + 4, DT + HUF_DTABLE_BYTES); (SP - HUF_FILLW_STACK, SP)] m) as MU.
  pose proof (munch_refl [(SP - HUF_FILLW_STACK, SP)] m) as MUF.
  pose proof (wmono_refl usegs m) as WM.
  unfold HUF_FILLW_STACK in *.
  zstep. carve_frame 48%nat ST. do 5 zstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => generalize dependent j; intros fj FR end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (CW1 : x2_cells m1 DT cw).
  { destruct CW as [CWA CWL]. split; [|exact CWL]. eapply u8arr_transport; [exact CWA | exact MUF | exact WM |].
    cbn [disjoint_from]. rewrite u16s_length, length_map. unfold HUF_DTABLE_BYTES in DTS. split; [lia | exact I]. }
  clear MUF CW. rename CW1 into CW.
  assert (NB12 : 0 <= nb <= 12) by lia.
  zstep. rewrite (swrap32_small (tl - nb)) by lia.
  zstep. zstep. rewrite (sllw_pow2 (tl - nb)) by lia.
  assert (P0 : 0 < 2 ^ (tl - nb)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2 ^ (tl - nb) <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
  assert (LENC : 2 ^ (tl - nb) = 1 \/ 2 ^ (tl - nb) = 2 \/ 2 ^ (tl - nb) = 4 \/ 2 ^ (tl - nb) = 8
                 \/ (16 <= 2 ^ (tl - nb) /\ 2 ^ (tl - nb) mod 8 = 0)).
  { assert (E : tl - nb = 0 \/ tl - nb = 1 \/ tl - nb = 2 \/ tl - nb = 3 \/ 4 <= tl - nb) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; [rewrite E; auto | rewrite E; auto | rewrite E; auto | rewrite E; auto 6 |].
    right; right; right; right. split.
    - change 16 with (2^4). apply Z.pow_le_mono_r; lia.
    - replace (tl - nb) with (3 + (tl - nb - 3)) by lia. rewrite Z.pow_add_r by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  remember (2 ^ (tl - nb)) as len eqn:ELEN. clear ELEN.
  zstep. zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit in K1 by lia.
  - zstep. zstep. if_cases K2; zify_cond K2.
    + assert (len = 4) by (destruct LENC as [E|[E|[E|[E|E]]]]; lia). subst len.
      zstep. if_cases K4; zify_cond K4.
      { fempty m1 fj. }
      do 5 zstep. zstep. if_cases K5; zify_cond K5.
      * assert (lv = 2) by lia. subst lv.
        do 6 zstep.
        eapply x2_l2_len4 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
      * assert (lv = 1) by lia. subst lv.
        do 5 zstep.
        eapply x2_l1_len4 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs) (lv := 1)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
    + zstep. zstep. if_cases K3; zify_cond K3.
      * assert (LD : 16 <= len /\ len mod 8 = 0) by (destruct LENC as [E|[E|[E|[E|E]]]]; lia).
        zstep. if_cases K4; zify_cond K4.
        { fempty m1 fj. }
        do 13 zstep.
        eapply x2_l1_def with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs) (lv := lv)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)) (L := len).
        all: first [ fke m1 fj | fside ].
      * assert (len = 8) by (destruct LENC as [E|[E|[E|[E|E]]]]; lia). subst len.
        zstep. if_cases K4; zify_cond K4.
        { fempty m1 fj. }
        do 10 zstep.
        eapply x2_l1_len8 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs) (lv := lv)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
  - zstep. if_cases K2; zify_cond K2.
    + assert (len = 1) by (destruct LENC as [E|[E|[E|[E|E]]]]; lia). subst len.
      zstep. if_cases K4; zify_cond K4.
      { fempty m1 fj. }
      do 4 zstep. zstep. if_cases K5; zify_cond K5.
      * assert (lv = 2) by lia. subst lv.
        do 5 zstep.
        eapply x2_l2_len1 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
      * assert (lv = 1) by lia. subst lv.
        do 4 zstep.
        eapply x2_l1_len1 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs) (lv := 1)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
    + zstep. zstep. if_cases K3; zify_cond K3.
      * exfalso. destruct LENC as [E|[E|[E|[E|E]]]]; lia.
      * assert (len = 2) by (destruct LENC as [E|[E|[E|[E|E]]]]; lia). subst len.
        zstep. if_cases K4; zify_cond K4.
        { fempty m1 fj. }
        do 8 zstep.
        eapply x2_l1_len2 with (m0 := m1) (cw0 := cw) (syb := syb) (pos := pos) (bg := bg) (en := en) (nb := nb) (bs := bs) (lv := lv)
          (DT := DT) (SYM := SYM) (SP := SP) (k := 0) (j := Z.to_nat (en - bg)).
        all: first [ fke m1 fj | fside ].
Qed.
