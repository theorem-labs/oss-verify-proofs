(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface
     L5Defs L5Core L5CoreSpecsU L5OpnewU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState Mem Cells Step Frame Exec Tac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Tgt Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5TopKitU L5TStrSU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TSTRU.
Import L5CSU.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Section S.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Local Ltac greg REQ k := rewrite (TKU.getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ REQ ltac:(lia)); cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add].

Lemma str_cap_eq : forall n, TSSU.str_cap n = str_cap n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma defined_of_writable : forall M a n, L5.writable rsegs M a n -> 0x92000 <= a -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros M a n W Ha Hn i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia)).
  cbn [store_ok] in W. rewrite ref_wview_overlay in W by (rewrite L5.unsigned_lit by lia; lia).
  destruct (M (Z_to_bv 64 (a + i))); [discriminate| discriminate W].
Qed.

(* [comment removed for export] *)
Lemma strinit_sso : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (s : list Z),
    (length s <= 22)%nat ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 src -> getr R 12%bv = Z_to_bv 64 (Z.of_nat (length s)) ->
    Forall (fun c => 0 <= c < 256) s ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp STRINIT_SCR ->
    o mod 8 = 0 -> sp <= o -> o + 24 <= hl_sptop L -> L5.writable RSEGS M o 24 ->
    L5.bytes_at RSEGS M src s -> L5.defined M src (Z.of_nat (length s)) ->
    (length s = 0%nat \/ (exists A m, In (A, m) LB /\ A <= src /\ src + Z.of_nat (length s) <= A + m)
                     \/ (sp <= src /\ src + Z.of_nat (length s) <= 2 ^ 47)) ->
    (o + 24 <= src \/ src + Z.of_nat (length s) <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        strinit_post L LB cr M M' R R' o sp s g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRINIT M model) K.
Proof.
  intros until s. intros SLEN HH [Mh [Ml Mm]] HK A0 A1 A2 RNG RA RAOK SP TP STK O8 SPO OHI WO SBY SDEF SLOC SEP CONT.
  unfold cfg. change Ubsan.M.loaded_segments with rsegs in *.
  destruct STK as (SP16 & SPLO & SPHI & SPTOP & SDEF2). unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in SPLO, SDEF2.
  set (n := Z.of_nat (length s)) in *.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & _).
  (* [comment removed for export] *)
  pose proof (defined_of_writable M o 24 WO ltac:(lia) ltac:(lia)) as ODEF.
  destruct (TSSU.rw_of_defined M o 24 ODEF ltac:(lia) ltac:(lia)) as [bsO OB].
  destruct (TSSU.CB_cut M o 1 23 bsO OB) as [OB0 OB1]. destruct (TSSU.C1_of_CB1 _ _ _ OB0) as [j0 O0]. clear OB OB0.
  (* [comment removed for export] *)
  assert (ST0 : stk rsegs M (sp - 8288) sp).
  { apply TKU.stk_of_defined; [| lia| lia| lia]. replace (sp - (sp - 8288)) with 8288 by lia. exact SDEF2. }
  destruct (Nat.eq_dec (length s) 0) as [L0|Lpos].
  - (* [comment removed for export] *)
    destruct (TSSU.C1CB_of_CB M (o + 1) 22 _ OB1) as (jb & j2 & OZ). clear OB1.
    eapply (TKU.srz_evt_canonMS _ R _ M model K Mh Ml).
    { unfold canon_regs. rewrite RA, SP, TP, A0, A1, A2. subst n. rewrite L0. cbn [Z.of_nat].
      eapply (TSSU.w_sso0 _ (Z_to_bv 64 sp)); rewrite ?L5.unsigned_lit by lia; [exact ST0| lia| lia| lia| lia| exact O0| exact OZ]. }
    2:{ intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & w0 & w1 & w2 & w3 & w4 & w5 & -> & _). eexists _, _, _. reflexivity. }
    intros R1c pc1 m1 R1 PO REQ1.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & w0 & w1 & w2 & w3 & w4 & w5 & E & O0' & OZ' & FR' & MU & WM & MG).
    inversion E; subst R1c pc1 m1; clear E. rewrite ?L5.unsigned_lit in MU, FR' by lia.
    rewrite (TKU.ret_pc_lit r RAOK).
    eapply (CONT fx R1 m' model Same LB cr).
    + split.
      * eapply (TKU.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R1 REQ1); try reflexivity; [exact SP| exact TP].
      * split; [exact SLEN|]. split; [reflexivity|]. split; [reflexivity|]. split; [| split].
        -- (* [comment removed for export] *) split; [exact SLEN|]. rewrite L0. cbn [Z.of_nat Z.mul]. split; [| split].
           ++ pose proof (TSSU.u8_of_cells _ _ _ _ O0') as U. exact U.
           ++ intros i Hi. rewrite L0 in Hi. lia.
           ++ rewrite Z.add_0_r. pose proof (TSSU.u8_of_cells _ _ _ _ OZ') as U. exact U.
        -- (* [comment removed for export] *) intros x OUT. apply MU. cbn. pose proof (OUT (sp - STRINIT_SCR, STRINIT_SCR) ltac:(left; reflexivity)) as X1.
           pose proof (OUT (o, 24) ltac:(right; left; reflexivity)) as X2. unfold L5.in_rng in X1, X2. cbn [fst snd] in X1, X2.
           unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in X1. lia.
        -- exact MG.
    + apply L5C.model_but_vm_refl.
    + eapply (L5C.hi_heap_client L SCFG HI LB cr M m'); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG].
      intros a Ha. destruct (Z_le_gt_dec (sp - 48) a) as [X|X]; [destruct (Z_lt_le_dec a sp) as [Y|Y]; [right; left; lia|]|].
      all: destruct (Z_le_gt_dec o a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (o + 24)) as [Z2|Z2]; [right; left; lia|]|].
      all: left; apply (MU (Z_to_bv 64 a)); rewrite L5.unsigned_lit by lia; cbn; lia.
  - (* [comment removed for export] *)
    assert (SRCB : 0 <= src /\ src + n <= 2 ^ 47 /\ (src + n <= sp - 48 \/ sp <= src)).
    { destruct SLOC as [L0|[(A & m & IN & A1' & A2')|[S1 S2]]]; [lia| | lia].
      destruct (WFB _ IN) as ((B1lo & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B1lo. cbn [fst snd] in B1, B4. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in B1. lia. }
    destruct SRCB as (SRC0 & SRCHI & SEPF).
    pose proof (TSSU.cells_of_L5bytes M src s SBY SRC0 ltac:(lia)) as SB.
    replace 23%nat with (Z.to_nat n + S (22 - Z.to_nat n))%nat in OB1 by lia.
    destruct (TSSU.CB_cut M (o + 1) _ _ _ OB1) as [OD OZ0]. clear OB1. rewrite Z2Nat.id in OZ0 by lia.
    destruct (TSSU.C1CB_of_CB M _ _ _ OZ0) as (jb & j2 & OZ). clear OZ0.
    replace (22 - Z.to_nat n)%nat with (Z.to_nat (22 - n)) in OZ by lia.
    eapply (TKU.srz_evt_canonMS _ R _ M model K Mh Ml).
    { unfold canon_regs. rewrite RA, SP, TP, A0, A1, A2.
      eapply (TSSU.w_sso _ (Z_to_bv 64 sp)) with (sbytes := map b8 s); rewrite ?L5.unsigned_lit by lia;
        [exact ST0| lia| lia| lia| lia| lia| exact SRC0| exact SRCHI| exact SEP| exact SEPF| rewrite length_map; lia| exact O0| exact OD| exact OZ| exact SB]. }
    2:{ intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & w0 & w1 & w2 & w3 & w4 & w5 & -> & _). eexists _, _, _. reflexivity. }
    intros R1c pc1 m1 R1 PO REQ1.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & w0 & w1 & w2 & w3 & w4 & w5 & E & O0' & OD' & OZ' & FR' & MU & WM & MG).
    inversion E; subst R1c pc1 m1; clear E. rewrite ?L5.unsigned_lit in MU, FR' by lia.
    rewrite (TKU.ret_pc_lit r RAOK).
    eapply (CONT fx R1 m' model Same LB cr).
    + split.
      * eapply (TKU.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R1 REQ1); try reflexivity; [exact SP| exact TP].
      * split; [exact SLEN|]. split; [reflexivity|]. split; [reflexivity|]. split; [| split].
        -- (* [comment removed for export] *) split; [exact SLEN|]. split; [| split].
           ++ pose proof (TSSU.u8_of_cells _ _ _ _ O0') as U. rewrite b8_unsigned in U by lia. replace (2 * Z.of_nat (length s)) with (n * 2) by lia. exact U.
           ++ eapply (TSSU.bytes_of_cells _ _ _ _ _ OD'). lia.
           ++ pose proof (TSSU.u8_of_cells _ _ _ _ OZ') as U. rewrite b8_unsigned in U by lia. subst n. exact U.
        -- (* [comment removed for export] *) intros x OUT. apply MU. cbn. pose proof (OUT (sp - STRINIT_SCR, STRINIT_SCR) ltac:(left; reflexivity)) as X1.
           pose proof (OUT (o, 24) ltac:(right; left; reflexivity)) as X2. unfold L5.in_rng in X1, X2. cbn [fst snd] in X1, X2.
           unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in X1. lia.
        -- exact MG.
    + apply L5C.model_but_vm_refl.
    + eapply (L5C.hi_heap_client L SCFG HI LB cr M m'); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG].
      intros a Ha. destruct (Z_le_gt_dec (sp - 48) a) as [X|X]; [destruct (Z_lt_le_dec a sp) as [Y|Y]; [right; left; lia|]|].
      all: destruct (Z_le_gt_dec o a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (o + 24)) as [Z2|Z2]; [right; left; lia|]|].
      all: left; apply (MU (Z_to_bv 64 a)); rewrite L5.unsigned_lit by lia; cbn; lia.
Qed.

Lemma str_cap_odd : forall n, 0 <= n -> Z.testbit (str_cap n + 1) 0 = true.
Proof.
  intros n Hn. unfold str_cap. destruct (Z.eqb (Z.lor n 7) 23); [reflexivity|].
  rewrite Z.bit0_odd. replace (Z.lor n 7 + 1 + 1) with (Z.lor n 7 + 2) by lia. rewrite Z.odd_add.
  assert (O : Z.odd (Z.lor n 7) = true). { rewrite <- Z.bit0_odd. rewrite Z.lor_spec. rewrite Bool.orb_true_iff. right. reflexivity. }
  rewrite O. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma strinit_long : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (s : list Z),
    (23 <= length s)%nat ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 src -> getr R 12%bv = Z_to_bv 64 (Z.of_nat (length s)) ->
    Z.of_nat (length s) < 2 ^ 26 -> Forall (fun c => 0 <= c < 256) s ->
    credit_ok L cr (str_cap (Z.of_nat (length s))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp STRINIT_SCR ->
    o mod 8 = 0 -> sp <= o -> o + 24 <= hl_sptop L -> L5.writable RSEGS M o 24 ->
    L5.bytes_at RSEGS M src s -> L5.defined M src (Z.of_nat (length s)) ->
    (length s = 0%nat \/ (exists A m, In (A, m) LB /\ A <= src /\ src + Z.of_nat (length s) <= A + m)
                     \/ (sp <= src /\ src + Z.of_nat (length s) <= 2 ^ 47)) ->
    (o + 24 <= src \/ src + Z.of_nat (length s) <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        strinit_post L LB cr M M' R R' o sp s g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRINIT M model) K.
Proof.
  intros until s. intros SLEN HH [Mh [Ml Mm]] HK A0 A1 A2 LEN RNG CRED RA RAOK SP TP STK O8 SPO OHI WO SBY SDEF SLOC SEP CONT.
  unfold cfg. change Ubsan.M.loaded_segments with rsegs in *.
  destruct STK as (SP16 & SPLO & SPHI & SPTOP & SDEF2). unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in SPLO, SDEF2.
  set (n := Z.of_nat (length s)) in *. set (cap := str_cap n) in *.
  pose proof (TKU.str_cap_bound n ltac:(lia)) as CAPB. fold cap in CAPB.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & _).
  pose proof (defined_of_writable M o 24 WO ltac:(lia) ltac:(lia)) as ODEF.
  assert (SRCB : 0 <= src /\ src + n <= 2 ^ 47 /\ (src + n <= sp - 48 \/ sp <= src) /\
                 ((exists A m, In (A, m) LB /\ A <= src /\ src + n <= A + m) \/ sp <= src)).
  { destruct SLOC as [L0|[(A & m & IN & A1' & A2')|[S1 S2]]]; [lia| | repeat split; try lia; right; lia].
    destruct (WFB _ IN) as ((B1lo & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B1lo. cbn [fst snd] in B1, B4. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in B1.
    repeat split; try lia. left. exists A, m. auto. }
  destruct SRCB as (SRC0 & SRCHI & SEPF & SLOC').
  assert (ST0 : stk rsegs M (sp - 8288) sp).
  { apply TKU.stk_of_defined; [| lia| lia| lia]. replace (sp - (sp - 8288)) with 8288 by lia. exact SDEF2. }
  (* [comment removed for export] *)
  eapply (TKU.srz_evt_canonMS _ R _ M model K Mh Ml).
  { unfold canon_regs. rewrite RA, SP, TP, A0, A1, A2.
    eapply (TSSU.w_long1 _ (Z_to_bv 64 sp)) with (n := n); rewrite ?L5.unsigned_lit by lia; [exact ST0| lia| lia| reflexivity| lia]. }
  2:{ intros ms' (m' & -> & _). eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 (m1 & E & FR1 & MU1 & WM1 & MG1 & ST1) REQ1. inversion E; subst R1c pc1 m1'; clear E.
  rewrite ?L5.unsigned_lit in FR1, MU1, ST1 by lia. rewrite str_cap_eq in REQ1. fold cap in REQ1.
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> m1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU1. cbn. rewrite L5.unsigned_lit by lia. lia. }
  assert (HH1 : hi_heap HI LB cr m1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M m1); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG1].
    intros a Ha. destruct (Z_le_gt_dec (sp - 48) a) as [X|X]; [destruct (Z_lt_le_dec a sp) as [Y|Y]; [right; left; lia|]|]; left; apply OUT1; lia. }
  (* [comment removed for export] *)
  eapply (L5NEWU.opnew_ok L HI LY HIok fx R1 m1 model K LB cr cap (sp + -48) 0x20af0).
  - exact HH1.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK.
  - greg REQ1 10. reflexivity.
  - lia.
  - exact CRED.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. unfold wz. rewrite L5.unsigned_lit by lia. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [clear -SP16; Z.div_mod_to_equations; lia|]. split; [unfold OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    unfold OPNEW_SCR, HEAP_STACK. intros i Hi. apply MG1. replace (sp + -48 - (16 + 8224) + i) with (sp - (48 + (16 + 8224)) + i) by lia. apply SDEF2. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 A RA2 RP12 FRESH HP12 MBV12 HH2. unfold L5CSU.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV12) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV12) as Ml2. rewrite Ml in Ml2.
    pose proof FRESH as [[B1lo [B1 [B2 [B3 B4]]]] [APART BDEF]]. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in B1.
    destruct HP12 as (KEPT12 & SDEF12 & CDEF12). unfold OPNEW_SCR, HEAP_STACK in SDEF12, CDEF12.
    (* [comment removed for export] *)
    assert (KS : forall a, sp - 48 <= a < 2 ^ 47 -> M2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
    { intros a Ha. apply KEPT12. apply (L5C.kept_stack L); [unfold OPNEW_SCR, HEAP_STACK; lia| unfold OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia| intros r0 []]. }
    assert (FR2 : rw_cells rsegs M2 (sp + -48) [C8 (getr R 20%bv); C8 (getr R 19%bv); C8 (getr R 18%bv); C8 (getr R 9%bv); C8 (getr R 8%bv); C8 (Z_to_bv 64 r)]).
    { eapply TKU.rw_cells_agree; [exact FR1| |]; cbn [cells_size csize Nat.add]; intros a Ha; unfold wa; [apply KS; lia|].
      rewrite KS by lia. apply (TSSU.rw_cells_defined _ _ _ a FR1); cbn [cells_size csize Nat.add]; lia. }
    assert (ODEF2 : forall i, 0 <= i < Z.of_nat 24 -> M2 (Z_to_bv 64 (o + i)) <> None).
    { intros i Hi. apply CDEF12; [lia| right; left; lia| unfold in_errno; rewrite (ly_errno L LY); lia|].
      rewrite OUT1 by lia. apply ODEF. lia. }
    destruct (TSSU.rw_of_defined M2 o 24 ODEF2 ltac:(lia) ltac:(lia)) as [junkO OB2].
    assert (PDEF : forall i, 0 <= i < Z.of_nat (Z.to_nat cap) -> M2 (Z_to_bv 64 (A + i)) <> None) by (intros i Hi; apply BDEF; lia).
    destruct (TSSU.rw_of_defined M2 A (Z.to_nat cap) PDEF ltac:(lia) ltac:(lia)) as [bsP PB0].
    replace (Z.to_nat cap) with (Z.to_nat n + S (Z.to_nat (cap - n - 1)))%nat in PB0 by lia.
    destruct (TSSU.CB_cut M2 A _ _ _ PB0) as [PB PZ0]. clear PB0. rewrite Z2Nat.id in PZ0 by lia.
    destruct (TSSU.C1CB_of_CB M2 _ _ _ PZ0) as (jb & j2 & PZ). clear PZ0.
    assert (SAG : forall a, src <= a < src + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite <- (OUT1 a) by lia. apply KEPT12. destruct SLOC' as [(Ab & mb & IN & A1' & A2')|SS].
      - destruct (WFB _ IN) as ((C1'lo & C1' & C2 & C3 & C4) & _). cbn [fst snd] in C1'lo. cbn [fst snd] in C1', C4. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in C1'.
        apply (L5C.kept_block L LB (sp + -48) OPNEW_SCR [] Ab mb); [exact IN| lia| lia| lia| rewrite (ly_errno L LY); lia| intros r0 []].
      - apply (L5C.kept_stack L); [unfold OPNEW_SCR, HEAP_STACK; lia| unfold OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia| intros r0 []]. }
    assert (SB2 : bytes_at rsegs M2 src (map b8 s)).
    { apply TSSU.cells_of_L5bytes; [| lia| lia]. eapply (L5C.bytes_at_agree rsegs M M2); [intros i Hi; apply SAG; lia| lia| lia| exact SBY]. }
    (* [comment removed for export] *)
    eapply (TKU.srz_evt_canonMS _ R2 _ M2 model2 K Mh2 Ml2).
    { rewrite (TKU.canon_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 R2 REQ1 RP12). rewrite RA2.
      eapply (TSSU.w_long2 _ (Z_to_bv 64 sp)) with (n := n) (cap := cap) (p := A) (o := o) (src := src) (sbytes := map b8 s);
        rewrite ?L5.unsigned_lit by lia;
        [lia| lia| lia| lia| lia| lia| lia| lia| lia| exact SRC0| exact SRCHI| | exact SEP| rewrite length_map; lia| exact FR2| exact OB2| exact PB| exact PZ| exact SB2].
      destruct SLOC' as [(Ab & mb & IN & A1' & A2')|SS]; [| right; lia]. pose proof (APART _ IN) as AP. cbn [fst snd] in AP. lia. }
    2:{ intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _). eexists _, _, _. reflexivity. }
    intros R3c pc3 m3' R3 PO REQ3.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & E & OB3 & PB3 & PZ3 & FR3 & MU3 & WM3 & MG3).
    inversion E; subst R3c pc3 m3'; clear E. rewrite ?L5.unsigned_lit in FR3 by lia.
    rewrite (TKU.ret_pc_lit r RAOK).
    pose proof (TSSU.rw_split m3 o [C8 (Z_to_bv 64 (cap + 1))] [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A)] OB3) as [OW0 OW12].
    pose proof (TSSU.rw_split m3 _ [C8 (Z_to_bv 64 n)] [C8 (Z_to_bv 64 A)] OW12) as [OW1 OW2]. cbn [cells_size csize Nat.add] in OW1, OW2.
    eapply (CONT fx2 R3 m3 model2 (Grown A cap) ((A, cap) :: LB) (debit L cr cap)).
    + split.
      * eapply (TKU.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R3 REQ3); try reflexivity; [exact SP| exact TP].
      * split; [exact SLEN|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [| split].
        -- (* [comment removed for export] *) split; [exact (proj1 FRESH)|]. split; [exact APART|].
           intros i Hi. destruct (Z_lt_le_dec (A + i) (A + n)).
           ++ apply (TSSU.rw_cells_defined _ _ _ (A + i) PB3); cbn [cells_size csize Nat.add]; lia.
           ++ apply (TSSU.rw_cells_defined _ _ _ (A + i) PZ3); cbn [cells_size csize Nat.add]; lia.
        -- (* [comment removed for export] *) split; [apply str_cap_odd; lia|]. split; [| split; [| split; [| split]]].
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW0) as U. rewrite L5.unsigned_lit in U by lia. exact U.
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW1) as U. rewrite L5.unsigned_lit in U by lia. subst n. exact U.
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW2) as U. rewrite L5.unsigned_lit in U by lia. replace (o + 16) with (o + 8 + 8) by lia. exact U.
           ++ eapply (TSSU.bytes_of_cells _ _ _ _ _ PB3). lia.
           ++ pose proof (TSSU.u8_of_cells _ _ _ _ PZ3) as U. rewrite b8_unsigned in U by lia. subst n. exact U.
        -- (* [comment removed for export] *) split; [| split].
           ++ intros a (Ha & CA & NE & OW). unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in CA.
              assert (NO : ~ (o <= a < o + 24)). { intros X. apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn; lia]. }
              assert (NS : ~ (sp - 8288 <= a < sp)).
              { destruct CA as [(b & Hb & Hr)|[[C1' C2]|[C1' C2]]]; [| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in C1'; lia].
                destruct (WFB b Hb) as ((D1lo & D1 & D2 & D3 & D4) & _). cbn [fst snd] in D1lo. lia. }
              assert (NB : ~ (A <= a < A + cap)).
              { destruct CA as [(b & Hb & Hr)|[[C1' C2]|[C1' C2]]]; [| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in C1'; lia].
                pose proof (APART b Hb). lia. }
              rewrite (MU3 (Z_to_bv 64 a)) by (rewrite L5.unsigned_lit by lia; cbn; lia).
              rewrite KEPT12. { apply OUT1; lia. }
              split; [exact Ha|]. split; [| split; [exact NE| intros r0 []]].
              destruct CA as [IB|[[C1' C2]|IM]]; [left; exact IB| right; left; split; [exact C1'| unfold OPNEW_SCR, HEAP_STACK; lia]| right; right; exact IM].
           ++ unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. destruct (Z_lt_le_dec (sp - (48 + (16 + 8224)) + i) (sp - 48)).
              ** rewrite (MU3 (Z_to_bv 64 _)) by (rewrite L5.unsigned_lit by lia; cbn; lia).
                 replace (sp - (48 + (16 + 8224)) + i) with (sp + -48 - (16 + 8224) + (i)) by lia. apply SDEF12. lia.
              ** apply (TSSU.rw_cells_defined _ _ _ _ FR3); cbn [cells_size csize Nat.add]; lia.
           ++ intros a Ha CA NE D0. apply MG3. apply CDEF12; [exact Ha| | exact NE| apply MG1; exact D0].
              unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in CA.
              destruct CA as [IB|[[C1' C2]|IM]]; [left; exact IB| right; left; split; [exact C1'| unfold OPNEW_SCR, HEAP_STACK; lia]| right; right; exact IM].
    + exact MBV12.
    + eapply (L5C.hi_heap_client L SCFG HI _ _ M2 m3); [exact HIok| exact HH2| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG3].
      intros a Ha. destruct (Z_le_gt_dec o a) as [X|X]; [destruct (Z_lt_le_dec a (o + 24)) as [Y|Y]; [right; left; lia|]|].
      all: destruct (Z_le_gt_dec A a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (A + cap)) as [Z2|Z2]; [right; right; exists (A, cap); split; [left; reflexivity| cbn; lia]|]|].
      all: left; apply (MU3 (Z_to_bv 64 a)); rewrite L5.unsigned_lit by lia; cbn; lia.
Qed.

(* [comment removed for export] *)
Theorem strinit_ok : strinit_spec L HI.
Proof.
  intros fx R M model K LB cr o src sp r s HH MOK HK A0 A1 A2 LEN RNG CRED RA RAOK SP TP STK O8 SPO OHI WO SBY SDEF SLOC SEP CONT.
  destruct (le_dec (length s) 22) as [SSO|LONG].
  - eapply strinit_sso; eauto.
  - eapply strinit_long; eauto; [lia| apply CRED; lia].
Qed.
End S.
End SCFG_1.

End L5TSTRU.
