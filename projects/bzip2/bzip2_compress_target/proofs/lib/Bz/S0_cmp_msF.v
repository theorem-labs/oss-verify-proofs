(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzTables.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasMs2 CmpMsKit2 S0_cmp_msV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_msE.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_msE.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasMs2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMsKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msE.S0_cmp_msD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_msE.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition incs_bytes : list byte := Eval vm_compute in (match image_bytes s0segs 68984 56 with Some bs => bs | None => [] end).
  Lemma incs_ro : forall m, mem_inv s0segs m -> bytes_at s0segs m 68984 incs_bytes.
  Proof.
    intros m MI. pose proof (ro_cells_image s0segs m 68984 incs_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ B].
    cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Lemma incs_read : forall m k, mem_inv s0segs m -> (0 <= k <= 13)%Z ->
    ov_read_bytes s0segs m (wa (68984 + 4 * k)) 4 = Some (le4 (Z_to_bv 64 (incs_at k))).
  Proof.
    intros m k MI Hk. rewrite (bytes_at_read s0segs m 68984 incs_bytes (4 * k) 4 (incs_ro m MI)) by (cbn; lia).
    assert (E : exists j, (j <= 13)%nat /\ k = Z.of_nat j) by (exists (Z.to_nat k); split; lia).
    cps_destruct E as (j & Hj & ->).
    do 14 (destruct j as [|j]; [f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity|]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_hps : forall (d lo hi : Z) (a2 : zarr) (c : Z) (w144 w200 w208 w216 w224 w288 : word) (e168 e176 : Z)
      (r : nat) (cnt : Z) (a1 : zarr) (b : Z) (w184 w192 w232 w240 w248 w264 w272 : word)
      (xra x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (Z.of_nat r = cnt)%Z -> (1 <= cnt <= c)%Z -> (c <= 13)%Z ->
    (forall k, 0 <= k < c -> incs_at k < hi - lo + 1)%Z ->
    (-2147483648 < snd (fst (mss_hps r a1 a2 qo n d lo hi (cnt - 1) b)))%Z -> (b < 2147483648)%Z ->
    (e168 = lo + 2)%Z -> (e176 = lo + 1)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 144) (scb_cells X (mkSCB w144 (Z_to_bv 64 lo) (Z_to_bv 64 e168) (Z_to_bv 64 e176) w184 w192 w200 w208 w216 w224 w232 w240
                                   w248 (Z_to_bv 64 hi) w264 w272 w288)) ->
    rw_cells s0segs m (p + 292) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m -> wmono s0segs me m ->
    (forall m' (w184' w192' w232' w240' w248' w264' w272' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x23' x25' x26' x28' x29' x30' x31' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB w144 (Z_to_bv 64 lo) (Z_to_bv 64 e168) (Z_to_bv 64 e176) w184' w192' w200 w208 w216 w224 w232' w240'
                                     w248' (Z_to_bv 64 hi) w264' w272' w288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' (Z_to_bv 64 A2) x21' (Z_to_bv 64 n) x23' (Z_to_bv 64 b') x25' x26' (Z_to_bv 64 A1)
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x1a20c) fc None m' (seg_rom s0segs))) ->
    (forall m' (w184' w192' w232' w240' w248' w264' w272' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x23' x25' x26' x28' x29' x30' x31' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      (b' < 0)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB w144 (Z_to_bv 64 lo) (Z_to_bv 64 e168) (Z_to_bv 64 e176) w184' w192' w200 w208 w216 w224 w232' w240'
                                     w248' (Z_to_bv 64 hi) w264' w272' w288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' (Z_to_bv 64 A2) x21' (Z_to_bv 64 n) x23' (Z_to_bv 64 b') x25' x26' (Z_to_bv 64 A1)
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x1a554) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          x10 x11 x12 (Z_to_bv 64 cnt) x14 x15 x16 x17
                          x18 x19 (Z_to_bv 64 A2) x21 (Z_to_bv 64 n) x23 x24 x25 x26 (Z_to_bv 64 A1)
                          x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x19e30) fc None m (seg_rom s0segs)).
  Proof.
    intros d lo hi a2 c w144 w200 w208 w216 w224 w288 e168 e176.
    induction r as [|r IH]; [intros; lia|].
    intros cnt a1 b w184 w192 w232 w240 w248 w264 w272 xra x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR Hr Hcnt Hc INCS BL BH E168 E176 AR1 AR2 SCB BUD MI MU WM K1 K2.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (INCS (cnt - 1)%Z ltac:(lia)) as Hh. pose proof (incs_at_pos13 (cnt - 1)%Z ltac:(lia)) as Hh1.
    set (h := incs_at (cnt - 1)) in *.
    pose proof BL as BL2. rewrite mss_hps_S in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2. fold h in K1. fold h in K2. fold h in BL2.
    pose proof (mss_hps_le_hloop r a1 a2 qo n d lo hi (cnt - 1) b) as LEH. fold h in LEH.
    (* [comment removed for export] *)
    open_sc_in SCB.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    pose proof (incs_read _ (cnt - 1)%Z MI ltac:(lia)) as RD. wstep. clear RD. fold h.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (S0_hloop X Q XOK XSEP d h lo hi a2 w144 (Z_to_bv 64 lo) (Z_to_bv 64 e168) (Z_to_bv 64 e176) (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) w200 w208 w216 w224 w288
                  (S (Z.to_nat (hi - lo + 1))) (lo + h)%Z a1 b e168 e176 lo w232 w240
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| | lia| lia| lia| lia
      | exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| |].
    { eapply (Z.lt_le_trans _ _ _ BL). exact LEH. }
    - (* [comment removed for export] *)
      intros m1 i1 w232' w240' w248' w264' w272' xra' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y26 y28 y30 y31. cbv zeta.
      intros FL AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B' I'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, AR1', BUD', B', K1, K2, BL2, OK', PR'. subst ex.
      open_sc_in SCB'.
      wstep. wstep. wstep. wstep.
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (cnt - 1)%Z a1h bh (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) w232' w240' w248' w264' w272'
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| exact OK'| exact A2OK| exact PR'| lia| lia| lia| exact INCS| exact BL2| lia| lia| lia
          | exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| |].
        * intros m' w184'' w192'' w232'' w240'' w248'' w264'' w272''. intros until x31'. cbv zeta.
          intros AR1'' AR2'' SCB'' BUD'' MI'' MU'' WM'' OK'' PR'' B''.
          eapply (K1 m'); [exact AR1''| exact AR2''| exact SCB''| exact BUD''| exact MI''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
        * intros m' w184'' w192'' w232'' w240'' w248'' w264'' w272''. intros until x31'. cbv zeta.
          intros BN AR1'' AR2'' SCB'' BUD'' MI'' MU'' WM'' OK'' PR'' B''.
          eapply (K2 m'); [exact BN| exact AR1''| exact AR2''| exact SCB''| exact BUD''| exact MI''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
      + (* [comment removed for export] *)
        assert (r = 0)%nat by lia. subst r. cbn [mss_hps fst snd] in K1, BL2.
        wstep. rewrite (sx32_of_Z_signed bh) by lia. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (K1 mm (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) w232' w240' w248' w264' w272' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
    - (* [comment removed for export] *)
      intros m1 i1 w232' w240' w248' w264' w272' xra' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y26 y28 y29 y30 y31. cbv zeta.
      intros FL BN AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, BN, AR1', BUD', B', K1, K2, OK', PR'. subst ex.
      eapply (K2 m1 (Z_to_bv 64 cnt) (Z_to_bv 64 (cnt - 1)) w232' w240' w248' w264' w272');
        [exact BN| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_hp : forall (bigN : Z) (f : nat) (k : Z) (x12 : word)
      (xra x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
    (2 <= bigN <= (NBLOCKMAX + 20))%Z -> (0 <= k <= 13)%Z -> (13 - k < Z.of_nat f)%Z -> (forall k', 0 <= k' < k -> incs_at k' < bigN)%Z ->
    mem_inv s0segs m ->
    (forall (c : Z) (x12' : word), c = mss_hp f bigN k -> (1 <= c <= 13)%Z -> (k <= c)%Z -> (forall k', 0 <= k' < c -> incs_at k' < bigN)%Z -> (bigN <= incs_at c)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (bigN - 1)) (Z_to_bv 64 (68984 + 4 * (c + 1))) x12' (Z_to_bv 64 c) x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x19e14) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9
                          (Z_to_bv 64 (bigN - 1)) (Z_to_bv 64 (68984 + 4 * k)) x12 (Z_to_bv 64 (k - 1)) x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x19e04) fc None m (seg_rom s0segs)).
  Proof.
    intros bigN. induction f as [|f IH]; [intros; lia|].
    intros k x12 xra x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m HB Hk Hf INV MI K.
    msenv_open XOK.
    pose proof (incs_at_pos k ltac:(lia)) as IP.
    (* [comment removed for export] *)
    pose proof (incs_read _ k MI ltac:(lia)) as RD. wstep. clear RD. try rewrite (sx32_of_Z (incs_at k)) by lia.
    wstep. wstep.
    rewrite mss_hp_S in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - replace (incs_at k <? bigN) with true in K by (symmetry; apply Z.ltb_lt; lia).
      assert (k < 13)%Z. { destruct (Z.eq_dec k 13) as [E|]; [| lia]. rewrite E, incs_at_13 in Kc. lia. }
      enter_with (IH (k + 1)%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m); [st_eq| lia| lia| lia| | exact MI|].
      + intros k' Hk'. destruct (Z.eq_dec k' k) as [->|]; [lia|]. apply INV. lia.
      + intros c x12' Hc H1 H2 H3 H4. eapply (K c x12'); [exact Hc| lia| lia| exact H3| exact H4].
    - replace (incs_at k <? bigN) with false in K by (symmetry; apply Z.ltb_ge; lia).
      assert (1 <= k)%Z. { destruct (Z.eq_dec k 0) as [E|]; [| lia]. rewrite E, incs_at_0 in Kc. lia. }
      enter_with (K k _ eq_refl ltac:(lia) ltac:(lia) INV ltac:(lia)). st_eq.
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_mss : forall (d lo hi : Z) (a1 a2 : zarr) (b : Z) (w144 w152 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w288 : word)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 144) (scb_cells X (mkSCB w144 w152 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 (Z_to_bv 64 b) w288)) ->
    rw_cells s0segs m (p + 292) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m -> wmono s0segs me m ->
    (forall m' (w152' w168' w176' w184' w192' w232' w240' w248' w256' w264' w272' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x23' x25' x26' x28' x29' x30' x31' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (0 <= b')%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB w144 w152' w168' w176' w184' w192' w200 w208 w216 w224 w232' w240' w248' w256' w264' w272' w288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' (Z_to_bv 64 A2) x21' (Z_to_bv 64 n) x23' (Z_to_bv 64 b') x25' x26' (Z_to_bv 64 A1)
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x1a210) fc None m' (seg_rom s0segs))) ->
    (forall m' (w152' w168' w176' w184' w192' w232' w240' w248' w256' w264' w272' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x23' x25' x26' x28' x29' x30' x31' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (b' < 0)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB w144 w152' w168' w176' w184' w192' w200 w208 w216 w224 w232' w240' w248' w256' w264' w272' w288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 144, p + 296)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 d) (Z_to_bv 64 FT)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' (Z_to_bv 64 A2) x21' (Z_to_bv 64 n) x23' (Z_to_bv 64 b') x25' x26' (Z_to_bv 64 A1)
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x1a554) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 d) (Z_to_bv 64 FT)
                          (Z_to_bv 64 (hi - lo)) x11 x12 x13 x14 x15 x16 x17
                          x18 x19 (Z_to_bv 64 A2) x21 (Z_to_bv 64 n) x23 x24 x25 x26 (Z_to_bv 64 A1)
                          x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x19df0) fc None m (seg_rom s0segs)).
  Proof.
    intros d lo hi a1 a2 b w144 w152 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w288
           xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x28 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR BFIN BH AR1 AR2 SCB BUD MI MU WM Kge Klt.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof BFIN as BF2. rewrite mainSimpleSort_eq in Kge, Klt, BF2. cbv zeta in Kge. cbv zeta in Klt. cbv zeta in BF2.
    open_sc_in SCB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; [apply blez_taken in Kc; [|lia] | apply blez_not_taken in Kc; [|lia]].
    - (* [comment removed for export] *)
      replace (hi - lo + 1 <? 2) with true in Kge, Klt, BF2 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in Kge, Klt, BF2.
      wstep.
      wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Klt mm w152 w168 w176 w184 w192 w232 w240 w248 w256 w264 (Z_to_bv 64 b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia].
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kge mm w152 w168 w176 w184 w192 w232 w240 w248 w256 w264 (Z_to_bv 64 b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia].
    - (* [comment removed for export] *)
      replace (hi - lo + 1 <? 2) with false in Kge, Klt, BF2 by (symmetry; apply Z.ltb_ge; lia).
      wstep. wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_hp (hi - lo + 1)%Z 15%nat 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| lia| lia| cbn; lia| intros; lia| exact MI|].
      intros c x12' Hc C1 C2 C3 C4. rewrite <- Hc in Kge, Klt, BF2.
      (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond_z Kz; exfalso; lia|]. clear Kz.
      wstep. wstep. wstep. wstep. wstep. wstep.
      replace (Z.to_nat (c - 1 + 1)) with (Z.to_nat c) in Kge, Klt, BF2 by lia.
      assert (BL : (-2147483648 < snd (fst (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b)))%Z).
      { destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex]. cbn [fst snd] in BF2 |- *. exact BF2. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_hps d lo hi a2 c w144 w200 w208 w216 w224 w288 (lo + 2)%Z (lo + 1)%Z (Z.to_nat c) c a1 b _ _ _ _ _ _ _
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| lia| lia| exact C3| exact BL| lia| lia| lia
        | exact AR1| exact AR2| | exact BUD| exact MI| assumption| assumption| |].
      + match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
      + (* [comment removed for export] *)
        intros m' w184' w192' w232' w240' w248' w264' w272'. intros until x31'. cbv zeta.
        intros AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (Klt mm (Z_to_bv 64 lo) (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) w184' w192' w232' w240' w248' (Z_to_bv 64 hi) w264' w272'
                           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| lia| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
        * lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            enter_with (Kge mm (Z_to_bv 64 lo) (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) w184' w192' w232' w240' w248' (Z_to_bv 64 hi) w264' w272'
                           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| lia| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
      + (* [comment removed for export] *)
        intros m' w184' w192' w232' w240' w248' w264' w272'. intros until x31'. cbv zeta.
        intros BN AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        eapply (Klt m' (Z_to_bv 64 lo) (Z_to_bv 64 (lo + 2)) (Z_to_bv 64 (lo + 1)) w184' w192' w232' w240' w248' (Z_to_bv 64 hi) w264' w272');
          [exact BN| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| exact B'].
  Time Qed.
End S0MS.

End ACeilS1.
