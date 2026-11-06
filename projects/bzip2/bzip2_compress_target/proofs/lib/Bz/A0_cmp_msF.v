(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzTables AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msE.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WH := [(A1, A1 + ARR1_SIZE); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P)]%Z.
  Variables (s7 s11 : word).

  (* [comment removed for export] *)
  Definition incs_bytes : list byte := Eval vm_compute in (match image_bytes a0segs 139040 56 with Some bs => bs | None => [] end).
  Lemma incs_ro : forall m, mem_inv a0segs m -> bytes_at a0segs m 139040 incs_bytes.
  Proof.
    intros m MI. pose proof (ro_cells_image a0segs m 139040 incs_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ B].
    cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Lemma incs_read : forall m k, mem_inv a0segs m -> (0 <= k <= 13)%Z ->
    ov_read_bytes a0segs m (wa (139040 + 4 * k)) 4 = Some (le4 (Z_to_bv 64 (incs_at k))).
  Proof.
    intros m k MI Hk. rewrite (bytes_at_read a0segs m 139040 incs_bytes (4 * k) 4 (incs_ro m MI)) by (cbn; lia).
    assert (E : exists j, (j <= 13)%nat /\ k = Z.of_nat j) by (exists (Z.to_nat k); split; lia).
    cps_destruct E as (j & Hj & ->).
    do 14 (destruct j as [|j]; [f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity|]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_hps : forall (d lo hi : Z) (a2 : zarr) (c : Z) (q256 q264 q272 q288 : word) (e216 e224 : Z)
      (r : nat) (cnt : Z) (a1 : zarr) (b : Z) (q232 q240 q320 q328 q336 q344 q352 q360 : word)
      (x5 x6 x7 x10 x11 x12 x13 x14 x17 x18 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (Z.of_nat r = cnt)%Z -> (1 <= cnt <= c)%Z -> (c <= 13)%Z ->
    (forall k, 0 <= k < c -> incs_at k < hi - lo + 1)%Z ->
    (-2147483648 < snd (fst (mss_hps r a1 a2 qo n d lo hi (cnt - 1) b)))%Z -> (b < 2147483648)%Z ->
    (e216 = lo + 2)%Z -> (e224 = lo + 1)%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ (Z_to_bv 64 e216) (Z_to_bv 64 e224) q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360
                                   (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P -> mem_inv a0segs m ->
    munch WH me m -> wmono a0segs me m ->
    frdW a0segs WH me (P + 384) (scc_cells X) -> acoW WH me ->
    shzW a0segs WH me A1 (A1 + ARR1_SIZE) -> shzW a0segs WH me A2 (A2 + ARR2_SIZE) -> shpW a0segs WH me (P + 436) (P + 440) ->
    shzW a0segs WH me 139040 139096 ->
    (forall m' (q232' q240' q320' q328' q336' q344' q352' q360' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x20' x21' x22' x25' x26' x28' x29' x30' x31' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ (Z_to_bv 64 e216) (Z_to_bv 64 e224) q232' q240' q256 q264 q272 q288 q320' q328' q336' q344' q352' q360'
                                     (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WH me m' -> wmono a0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b' <= b)%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' cSB x20' x21' x22' s7 (Z_to_bv 64 d) x25' x26' s11
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x99508) fc None m' (seg_rom a0segs))) ->
    (forall m' (q232' q240' q320' q328' q336' q344' q352' q360' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x20' x21' x22' x25' x26' x28' x29' x30' x31' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      (b' < 0)%Z ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ (Z_to_bv 64 e216) (Z_to_bv 64 e224) q232' q240' q256 q264 q272 q288 q320' q328' q336' q344' q352' q360'
                                     (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WH me m' -> wmono a0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' cSB x20' x21' x22' s7 (Z_to_bv 64 d) x25' x26' s11
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x9a000) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 (Z_to_bv 64 lo) (Z_to_bv 64 cnt) x17
                          x18 cSB x20 x21 x22 s7 (Z_to_bv 64 d) x25 x26 s11
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99130) fc None m (seg_rom a0segs)).
  Proof.
    intros d lo hi a2 c q256 q264 q272 q288 e216 e224.
    induction r as [|r IH]; [intros; lia|].
    intros cnt a1 b q232 q240 q320 q328 q336 q344 q352 q360 x5 x6 x7 x10 x11 x12 x13 x14 x17 x18 x20 x21 x22 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR Hr Hcnt Hc INCS BL BH E216 E224 AR1 AR2 SCQ BUD STK MI MU WM VC ACW SH1 SH2 SHB SHINC K1 K2.
    msenv_open XOK. amenv_open YOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (INCS (cnt - 1)%Z ltac:(lia)) as Hh. pose proof (incs_at_pos13 (cnt - 1)%Z ltac:(lia)) as Hh1.
    set (h := incs_at (cnt - 1)) in *.
    pose proof BL as BL2. rewrite mss_hps_S in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2. fold h in K1. fold h in K2. fold h in BL2.
    pose proof (mss_hps_le_hloop r a1 a2 qo n d lo hi (cnt - 1) b) as LEH. fold h in LEH.
    (* [comment removed for export] *)
    open_scq_in SCQ.
    arun.
    pose proof (incs_read _ (cnt - 1)%Z MI ltac:(lia)) as RD. wstep. clear RD. fold h.
    try rewrite (sx32_of_Z h) by lia.
    (* [comment removed for export] *)
    arun_to 0x9917c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (A0_hloop X Y Q XOK XSEP YOK s7 s11 d h lo hi a2 (Z_to_bv 64 e216) (Z_to_bv 64 e224) (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) q256 q264 q272 q288 (Z_to_bv 64 lo)
                  (S (Z.to_nat (hi - lo + 1))) (lo + h)%Z a1 b e216 e224 lo q320 q328 q360
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| | lia| lia| lia| lia
      | exact AR1| exact AR2| exact SCQ| exact BUD| exact STK| exact MI| exact MU| exact WM| exact VC| exact ACW| exact SH1| exact SH2| exact SHB| |].
    { eapply (Z.lt_le_trans _ _ _ BL). exact LEH. }
    - (* [comment removed for export] *)
      intros m1 q320' q328' q336' q344' q352' q360' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y28 y29 y30 y31. cbv zeta.
      intros FL AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' B'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, AR1', BUD', B', K1, K2, BL2, OK', PR'. subst ex.
      open_scq_in SCQ'.
      arun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (cnt - 1)%Z a1h bh (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) q320' q328' q336' q344' q352' q360'
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| exact OK'| exact A2OK| exact PR'| lia| lia| lia| exact INCS| exact BL2| lia| lia| lia
          | exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact VC| exact ACW| exact SH1| exact SH2| exact SHB| exact SHINC| |].
        * intros m' q232'' q240'' q320'' q328'' q336'' q344'' q352'' q360''. intros until x31'. cbv zeta.
          intros AR1'' AR2'' SCQ'' BUD'' STK'' MI'' MU'' WM'' OK'' PR'' B''.
          eapply (K1 m'); [exact AR1''| exact AR2''| exact SCQ''| exact BUD''| exact STK''| exact MI''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
        * intros m' q232'' q240'' q320'' q328'' q336'' q344'' q352'' q360''. intros until x31'. cbv zeta.
          intros BN AR1'' AR2'' SCQ'' BUD'' STK'' MI'' MU'' WM'' OK'' PR'' B''.
          eapply (K2 m'); [exact BN| exact AR1''| exact AR2''| exact SCQ''| exact BUD''| exact STK''| exact MI''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
      + (* [comment removed for export] *)
        assert (r = 0)%nat by lia. subst r. cbn [mss_hps fst snd] in K1, BL2.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (K1 mm (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) q320' q328' q336' q344' q352' q360' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
    - (* [comment removed for export] *)
      intros m1 q320' q328' q336' q344' q352' q360' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y28 y29 y30 y31. cbv zeta.
      intros FL BN AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' B'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, BN, AR1', BUD', B', K1, K2, OK', PR'. subst ex.
      eapply (K2 m1 (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) q320' q328' q336' q344' q352' q360');
        [exact BN| exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_hp : forall (bigN : Z) (W : list ivl) (me : word -> option byte) (f : nat) (k : Z) (x13 : word)
      (xra x5 x6 x7 x14 x15 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
    (2 <= bigN <= (NBLOCKMAX + 20))%Z -> (0 <= k <= 13)%Z -> (13 - k < Z.of_nat f)%Z -> (forall k', 0 <= k' < k -> incs_at k' < bigN)%Z ->
    mem_inv a0segs m -> munch W me m -> shzW a0segs W me 139040 139096 ->
    (forall (c : Z) (x13' : word), c = mss_hp f bigN k -> (1 <= c <= 13)%Z -> (k <= c)%Z -> (forall k', 0 <= k' < c -> incs_at k' < bigN)%Z -> (bigN <= incs_at c)%Z ->
      evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (139040 + 4 * (c + 1))) (Z_to_bv 64 (bigN - 1)) (Z_to_bv 64 (139040 + 4 * (c + 1))) x13' x14 x15 (Z_to_bv 64 c) x17
                            x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x9911c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (139040 + 4 * k)) (Z_to_bv 64 (bigN - 1)) (Z_to_bv 64 (139040 + 4 * k)) x13 x14 x15 (Z_to_bv 64 (k - 1)) x17
                          x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98f68) fc None m (seg_rom a0segs)).
  Proof.
    intros bigN W me. induction f as [|f IH]; [intros; lia|].
    intros k x13 xra x5 x6 x7 x14 x15 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m HB Hk Hf INV MI MU SHINC K.
    msenv_open XOK.
    pose proof (incs_at_pos k ltac:(lia)) as IP.
    (* [comment removed for export] *)
    arun.
    pose proof (incs_read _ k MI ltac:(lia)) as RD. wstep. clear RD. try rewrite (sx32_of_Z (incs_at k)) by lia.
    rewrite mss_hp_S in K.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - replace (incs_at k <? bigN) with true in K by (symmetry; apply Z.ltb_lt; lia).
      assert (k < 13)%Z. { destruct (Z.eq_dec k 13) as [E|]; [| lia]. rewrite E, incs_at_13 in Kc. lia. }
      enter_with (IH (k + 1)%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m); [st_eq| lia| lia| lia| | exact MI| exact MU| exact SHINC|].
      + intros k' Hk'. destruct (Z.eq_dec k' k) as [->|]; [lia|]. apply INV. lia.
      + intros c x13' Hc H1 H2 H3 H4. eapply (K c x13'); [exact Hc| lia| lia| exact H3| exact H4].
    - replace (incs_at k <? bigN) with false in K by (symmetry; apply Z.ltb_ge; lia).
      assert (1 <= k)%Z. { destruct (Z.eq_dec k 0) as [E|]; [| lia]. rewrite E, incs_at_0 in Kc. lia. }
      wstep.
      enter_with (K k _ eq_refl ltac:(lia) ltac:(lia) INV ltac:(lia)). st_eq.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_mss : forall (d lo hi : Z) (a1 a2 : zarr) (b : Z) (q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360 : word)
      (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z -> (b < 2147483648)%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360 (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P -> mem_inv a0segs m ->
    munch WH me m -> wmono a0segs me m ->
    frdW a0segs WH me (P + 384) (scc_cells X) -> acoW WH me ->
    shzW a0segs WH me A1 (A1 + ARR1_SIZE) -> shzW a0segs WH me A2 (A2 + ARR2_SIZE) -> shpW a0segs WH me (P + 436) (P + 440) ->
    shzW a0segs WH me 139040 139096 ->
    (forall m' (q216' q224' q232' q240' q320' q328' q336' q344' q352' q360' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x20' x21' x22' x25' x26' x28' x29' x30' x31' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (0 <= b')%Z ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216' q224' q232' q240' q256 q264 q272 q288 q320' q328' q336' q344' q352' q360' (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WH me m' -> wmono a0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (b' <= b)%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' cSB x20' x21' x22' s7 (Z_to_bv 64 d) x25' x26' s11
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x99678) fc None m' (seg_rom a0segs))) ->
    (forall m' (q216' q224' q232' q240' q320' q328' q336' q344' q352' q360' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x20' x21' x22' x25' x26' x28' x29' x30' x31' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (b' < 0)%Z ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216' q224' q232' q240' q256 q264 q272 q288 q320' q328' q336' q344' q352' q360' (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WH me m' -> wmono a0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' cSB x20' x21' x22' s7 (Z_to_bv 64 d) x25' x26' s11
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x9a000) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 (hi - lo)) x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 x22 s7 (Z_to_bv 64 d) x25 x26 s11
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98f50) fc None m (seg_rom a0segs)).
  Proof.
    intros d lo hi a1 a2 b q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360
           x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR BFIN BH AR1 AR2 SCQ BUD STK MI MU WM VC ACW SH1 SH2 SHB SHINC Kge Klt.
    msenv_open XOK. amenv_open YOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof BFIN as BF2. rewrite mainSimpleSort_eq in Kge, Klt, BF2. cbv zeta in Kge. cbv zeta in Klt. cbv zeta in BF2.
    open_scq_in SCQ.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; [apply blez_taken in Kc; [|lia] | apply blez_not_taken in Kc; [|lia]].
    - (* [comment removed for export] *)
      replace (hi - lo + 1 <? 2) with true in Kge, Klt, BF2 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in Kge, Klt, BF2.
      wstep. rewrite (sx32_of_Z_signed b) by lia.
      wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Klt mm q216 q224 q232 q240 q320 q328 q336 q344 q352 q360 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact AR1| exact AR2| exact SCQ| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia].
      + wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kge mm q216 q224 q232 q240 q320 q328 q336 q344 q352 q360 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact AR1| exact AR2| exact SCQ| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia].
    - (* [comment removed for export] *)
      replace (hi - lo + 1 <? 2) with false in Kge, Klt, BF2 by (symmetry; apply Z.ltb_ge; lia).
      wstep. wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_hp (hi - lo + 1)%Z _ me 15%nat 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| lia| lia| cbn; lia| intros; lia| exact MI| exact MU| exact SHINC|].
      intros c x13' Hc C1 C2 C3 C4. rewrite <- Hc in Kge, Klt, BF2.
      (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond_z Kz; exfalso; lia|]. clear Kz.
      wstep. wstep. wstep. wstep.
      replace (Z.to_nat (c - 1 + 1)) with (Z.to_nat c) in Kge, Klt, BF2 by lia.
      assert (BL : (-2147483648 < snd (fst (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b)))%Z).
      { destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex]. cbn [fst snd] in BF2 |- *. exact BF2. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_hps d lo hi a2 c q256 q264 q272 q288 (lo + 2)%Z (lo + 1)%Z (Z.to_nat c) c a1 b q232 q240 q320 q328 q336 q344 q352 q360
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| lia| lia| exact C3| exact BL| lia| lia| lia
        | exact AR1| exact AR2| exact SCQ| exact BUD| exact STK| exact MI| assumption| assumption| exact VC| exact ACW| exact SH1| exact SH2| exact SHB| exact SHINC| |].
      + (* [comment removed for export] *)
        intros m' q232' q240' q320' q328' q336' q344' q352' q360'. intros until x31'. cbv zeta.
        intros AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        wstep. rewrite (sx32_of_Z_signed b') by lia.
        wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (Klt mm (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) q232' q240' q320' q328' q336' q344' q352' q360' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| lia| exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
        * wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (Kge mm (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) q232' q240' q320' q328' q336' q344' q352' q360' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| lia| exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
      + (* [comment removed for export] *)
        intros m' q232' q240' q320' q328' q336' q344' q352' q360'. intros until x31'. cbv zeta.
        intros BN AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        eapply (Klt m' (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) q232' q240' q320' q328' q336' q344' q352' q360');
          [exact BN| exact AR1'| exact AR2'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact B'].
  Qed.
End A0MS.

End ACeilS1.
