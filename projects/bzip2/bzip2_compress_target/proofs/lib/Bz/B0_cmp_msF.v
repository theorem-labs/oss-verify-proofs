(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzTables AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msE B0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Notation INCS_AT := 858336%Z.

Lemma incs_read : forall m k, b0_incs m -> (0 <= k <= 13)%Z ->
  ov_read_bytes b0segs m (wa (858336 + 4 * k)) 4 = Some (le4 (Z_to_bv 64 (incs_at k))).
Proof.
  intros m k IB Hk. unfold b0_incs, B0_INCS in IB. destruct IB as [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read b0segs m 858336 BzIncs.incs_bytes (4 * k) 4 B) by (cbn; lia).
  assert (E : exists j, (j <= 13)%nat /\ k = Z.of_nat j) by (exists (Z.to_nat k); split; lia).
  cps_destruct E as (j & Hj & ->).
  do 14 (destruct j as [|j]; [f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Definition bfree_at (X : msenv) (Y : amenv) (Q : machine_state -> Prop) (pc : Z) (m : word -> option byte) : Prop :=
  forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  evt b0segs Q (MS (mkR (Z_to_bv 64 (me_A1 X)) (Z_to_bv 64 (am_P Y)) (me_gp X) (me_tp X) x5 x6 x7 (me_sp X) (Z_to_bv 64 (am_P Y))
                        x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880) x28 x29 x30 x31)
                   (me_F X) (Z_to_bv 64 pc) (me_fc X) None m (seg_rom b0segs)).

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  (* [comment removed for export] *)
  Variables (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w312 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WH := [(A1, A1 + ARR1_SIZE); (P, P + 500); (P - 32, P)]%Z.
  (* [comment removed for export] *)
  Notation SLP q240 q248 q264 q272 q328 q336 q344 q352 q392 hi lo q440 :=
    (slm_cells X Y SHF SHn (mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 q240 q248 q264 q272 w312 q328 q336 q344 q352 q392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) q440 w480)).
  (* [comment removed for export] *)
  Ltac sub_aco ACW MU := eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve].
  Ltac sub_shz SH MU := eapply (shzW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].

  (* [comment removed for export] *)
  Lemma B0_hp : forall (bigN : Z) (W : list ivl) (me : word -> option byte) (f : nat) (k : Z) (x13 : word)
      (xra x5 x6 x7 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (m : word -> option byte),
    (2 <= bigN <= (NBLOCKMAX + 20))%Z -> (0 <= k <= 13)%Z -> (13 - k < Z.of_nat f)%Z -> (forall k', 0 <= k' < k -> incs_at k' < bigN)%Z ->
    b0_incs m -> mem_inv b0segs m -> munch W me m -> shzW b0segs W me 858336 858392 ->
    (forall (c : Z) (x13' : word), c = mss_hp f bigN k -> (1 <= c <= 13)%Z -> (k <= c)%Z -> (forall k', 0 <= k' < c -> incs_at k' < bigN)%Z -> (bigN <= incs_at c)%Z ->
      evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (INCS_AT + 4 * c)) (Z_to_bv 64 bigN) (Z_to_bv 64 (INCS_AT + 4 * c)) x13' x14 (Z_to_bv 64 c) x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa3194) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (INCS_AT + 4 * k)) (Z_to_bv 64 bigN) (Z_to_bv 64 (INCS_AT + 4 * k)) x13 x14 (Z_to_bv 64 k) x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2b54) fc None m (seg_rom b0segs)).
  Proof.
    intros bigN W me. induction f as [|f IH]; [intros; lia|].
    intros k x13 xra x5 x6 x7 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m HB Hk Hf INV IB MI MU SHINC K.
    msenv_open XOK.
    pose proof (incs_at_pos k ltac:(lia)) as IP.
    (* [comment removed for export] *)
    brun.
    pose proof (incs_read _ k IB ltac:(lia)) as RD. wstep. clear RD. try rewrite (sx32_of_Z (incs_at k)) by lia.
    rewrite mss_hp_S in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - replace (incs_at k <? bigN) with false in K by (symmetry; apply Z.ltb_ge; lia).
      assert (1 <= k)%Z. { destruct (Z.eq_dec k 0) as [E|]; [| lia]. rewrite E, incs_at_0 in Kc. lia. }
      enter_with (K k _ eq_refl ltac:(lia) ltac:(lia) INV ltac:(lia)). st_eq.
    - replace (incs_at k <? bigN) with true in K by (symmetry; apply Z.ltb_lt; lia).
      assert (k < 13)%Z. { destruct (Z.eq_dec k 13) as [E|]; [| lia]. rewrite E, incs_at_13 in Kc. lia. }
      (* [comment removed for export] *)
      brun_to 0xa2b54%Z.
      enter_with (IH (k + 1)%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m); [st_eq| lia| lia| lia| | exact IB| exact MI| exact MU| exact SHINC|].
      + intros k' Hk'. destruct (Z.eq_dec k' k) as [->|]; [lia|]. apply INV. lia.
      + intros c x13' Hc H1 H2 H3 H4. eapply (K c x13'); [exact Hc| lia| lia| exact H3| exact H4].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hps : forall (d lo hi : Z) (a2 : zarr) (c : Z) (e240 e248 : Z)
      (r : nat) (cnt : Z) (a1 : zarr) (b : Z) (w264 w272 w328 w336 w344 w352 w392 w440 : word)
      (x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (Z.of_nat r = cnt)%Z -> (1 <= cnt <= c)%Z -> (c <= 13)%Z ->
    (forall k, 0 <= k < c -> incs_at k < hi - lo + 1)%Z ->
    (-2147483648 < snd (fst (mss_hps r a1 a2 qo n d lo hi (cnt - 1) b)))%Z -> (b < 2147483648)%Z ->
    (e240 = lo + 2)%Z -> (e248 = lo + 1)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells b0segs m P (SLP (Z_to_bv 64 e240) (Z_to_bv 64 e248) w264 w272 w328 w336 w344 w352 w392 hi lo w440) ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m -> b0_incs m ->
    munch WH me m -> wmono b0segs me m ->
    acoW WH me ->
    shzW b0segs WH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WH me (P + 496) (P + 500) ->
    shzW b0segs WH me 858336 858392 ->
    (forall m' (w264' w272' w328' w336' w344' w352' w392' w440' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLP (Z_to_bv 64 e240) (Z_to_bv 64 e248) w264' w272' w328' w336' w344' w352' w392' hi lo w440') ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b' <= b)%Z ->
      bfree_at X Y Q 0xa38b4 m') ->
    (forall m' (w264' w272' w328' w336' w344' w352' w392' w440' : word),
      let rr := mss_hps r a1 a2 qo n d lo hi (cnt - 1) b in let a1' := fst (fst rr) in let b' := snd (fst rr) in
      (b' < 0)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLP (Z_to_bv 64 e240) (Z_to_bv 64 e248) w264' w272' w328' w336' w344' w352' w392' hi lo w440') ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      bfree_at X Y Q 0xa3970 m') ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 (Z_to_bv 64 cnt) x16 x17
                          x18 x19 x20 x21 x22 x23 (Z_to_bv 64 d) x25 x26 cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa31ac) fc None m (seg_rom b0segs)).
  Proof.
    intros d lo hi a2 c e240 e248.
    induction r as [|r IH]; [intros; lia|].
    intros cnt a1 b w264 w272 w328 w336 w344 w352 w392 w440 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR Hr Hcnt Hc INCS BL BH E240 E248 AR1 AR2 SLB BUD STK MI IB MU WM ACW SH1 SH2 SHB SHINC K1 K2.
    msenv_open XOK. amenv_open YOK. bz_params. pose proof alloc_ceiling_range as ACR.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (INCS (cnt - 1)%Z ltac:(lia)) as Hh. pose proof (incs_at_pos13 (cnt - 1)%Z ltac:(lia)) as Hh1.
    set (h := incs_at (cnt - 1)) in *.
    pose proof BL as BL2. rewrite mss_hps_S in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2. fold h in K1. fold h in K2. fold h in BL2.
    pose proof (mss_hps_le_hloop r a1 a2 qo n d lo hi (cnt - 1) b) as LEH. fold h in LEH.
    open_slb_in SLB. unfold b0_incs, B0_INCS in IB.
    (* [comment removed for export] *)
    brun_to 0xa31d4%Z.
    lazymatch goal with |- context [Z_to_bv 64 (858336 + ?x)] => replace (858336 + x)%Z with (858336 + 4 * (cnt - 1))%Z by lia end.
    brun.
    pose proof (incs_read _ (cnt - 1)%Z IB ltac:(lia)) as RD. wstep. clear RD. try rewrite (sx32_of_Z (incs_at (cnt - 1))) by lia. fold h.
    (* [comment removed for export] *)
    brun_to 0xa321c%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0xa322c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (B0_hloop X Y SHF SHn Q XOK XSEP YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d h lo hi a2
                  (S (Z.to_nat (hi - lo + 1))) (lo + h)%Z a1 b (e240 + h)%Z (e248 + h)%Z _ _ _
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| | lia| lia| lia
      | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| apply munch_refl| apply wmono_refl
      | sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU| |].
    { eapply (Z.lt_le_trans _ _ _ BL). exact LEH. }
    all: clear AR1 AR2 SLB BUD STK MI.
    - (* [comment removed for export] *)
      intros m1 w328' w336' w344' w352' w392' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y25 y28 y29 y30 y31. cbv zeta.
      intros FL AR1' AR2' SLB' BUD' STK' MI' MU1 WM1 OK' PR' B'.
      transport_after_call b0segs mq m1 MU1 WM1. clear MU1 WM1. rename IB into IB'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, AR1', BUD', B', K1, K2, BL2, OK', PR'. subst ex.
      open_slb_in SLB'.
      brun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (cnt - 1)%Z a1h bh _ _ _ _ _ _ _ _
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| exact OK'| exact A2OK| exact PR'| lia| lia| lia| exact INCS| exact BL2| lia| exact E240| exact E248
          | exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU| exact WM| exact ACW| exact SH1| exact SH2| exact SHB| exact SHINC| |].
        * intros m' w264'' w272'' w328'' w336'' w344'' w352'' w392'' w440''. cbv zeta.
          intros AR1'' AR2'' SLB'' BUD'' STK'' MI'' IB'' MU'' WM'' OK'' PR'' B''.
          eapply (K1 m'); [exact AR1''| exact AR2''| exact SLB''| exact BUD''| exact STK''| exact MI''| exact IB''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
        * intros m' w264'' w272'' w328'' w336'' w344'' w352'' w392'' w440''. cbv zeta.
          intros BN AR1'' AR2'' SLB'' BUD'' STK'' MI'' IB'' MU'' WM'' OK'' PR'' B''.
          eapply (K2 m'); [exact BN| exact AR1''| exact AR2''| exact SLB''| exact BUD''| exact STK''| exact MI''| exact IB''| exact MU''| exact WM''| exact OK''| exact PR''| lia].
      + (* [comment removed for export] *)
        assert (r = 0)%nat by lia. subst r. cbn [mss_hps fst snd] in K1, BL2.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (K1 mm _ _ _ _ _ _ _ _ AR1' AR2' SLB' BUD' STK' MI' IB' MU WM OK' PR' ltac:(lia)) as KK end.
        unfold bfree_at in KK. enter_with KK. st_eq.
    - (* [comment removed for export] *)
      intros m1 w328' w336' w344' w352' w392' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y23 y25 y28 y29 y30 y31. cbv zeta.
      intros FL BN AR1' AR2' SLB' BUD' STK' MI' MU1 WM1 OK' PR' B'.
      transport_after_call b0segs mq m1 MU1 WM1. clear MU1 WM1. rename IB into IB'.
      destruct (mss_hloop (S (Z.to_nat (hi - lo + 1))) a1 a2 qo n d h lo hi (lo + h) b) as [[a1h bh] ex] eqn:HL.
      cbn [fst snd] in FL, BN, AR1', BUD', B', K1, K2, OK', PR'. subst ex.
      pose proof (K2 m1 _ _ _ _ _ _ _ _ BN AR1' AR2' SLB' BUD' STK' MI' IB' MU WM OK' PR' ltac:(lia)) as KK.
      unfold bfree_at in KK. enter_with KK. st_eq.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_mss_end : forall (m' : word -> option byte) (b' : Z), (-2147483648 < b' < 2147483648)%Z ->
    rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] ->
    ((0 <= b')%Z -> bfree_at X Y Q 0xa38bc m') -> ((b' < 0)%Z -> bfree_at X Y Q 0xa3970 m') -> bfree_at X Y Q 0xa38b4 m'.
  Proof.
    intros m' b' Hb BUD Kge Klt. unfold bfree_at. intros.
    msenv_open XOK.
    wstep. rewrite (sx32_of_Z_signed b') by lia.
    wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
    - eapply Klt. lia.
    - eapply Kge. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_mss : forall (d lo hi : Z) (a1 a2 : zarr) (b : Z) (w240 w248 w264 w272 w328 w336 w344 w352 w392 w440 : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z -> (b < 2147483648)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells b0segs m P (SLP w240 w248 w264 w272 w328 w336 w344 w352 w392 hi lo w440) ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m -> b0_incs m ->
    munch WH me m -> wmono b0segs me m ->
    acoW WH me ->
    shzW b0segs WH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WH me (P + 496) (P + 500) ->
    shzW b0segs WH me 858336 858392 ->
    (forall m' (w240' w248' w264' w272' w328' w336' w344' w352' w392' w440' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (0 <= b')%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLP w240' w248' w264' w272' w328' w336' w344' w352' w392' hi lo w440') ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (b' <= b)%Z ->
      bfree_at X Y Q 0xa38bc m') ->
    (forall m' (w240' w248' w264' w272' w328' w336' w344' w352' w392' w440' : word),
      let rr := mainSimpleSort a1 a2 qo n lo hi d b in let a1' := fst rr in let b' := snd rr in
      (b' < 0)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLP w240' w248' w264' w272' w328' w336' w344' w352' w392' hi lo w440') ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      bfree_at X Y Q 0xa3970 m') ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (hi - lo)) x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 (Z_to_bv 64 d) x25 x26 cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2b30) fc None m (seg_rom b0segs)).
  Proof.
    intros d lo hi a1 a2 b w240 w248 w264 w272 w328 w336 w344 w352 w392 w440
           x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 me m
           Hlo Hlh Hhi Hd A1OK A2OK PR BFIN BH AR1 AR2 SLB BUD STK MI IB MU WM ACW SH1 SH2 SHB SHINC Kge Klt.
    msenv_open XOK. amenv_open YOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof BFIN as BF2. rewrite mainSimpleSort_eq in Kge, Klt, BF2. cbv zeta in Kge. cbv zeta in Klt. cbv zeta in BF2.
    unfold b0_incs, B0_INCS in IB.
    pose proof (mss_hps_budget_le (Z.to_nat (mss_hp 15 (hi - lo + 1) 0 - 1 + 1)) a1 a2 qo n d lo hi (mss_hp 15 (hi - lo + 1) 0 - 1) b) as HBLE.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (hi - lo + 1 <? 2) with true in Kge, Klt, BF2 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in Kge, Klt, BF2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (B0_mss_end mm b ltac:(lia) BUD) as ME end.
      assert (KK : bfree_at X Y Q 0xa38b4 m).
      { apply ME.
        + intros Hb. eapply (Kge _ w240 w248 w264 w272 w328 w336 w344 w352 w392 w440);
            [lia| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact IB| exact MU| exact WM| exact A1OK| exact PR| lia].
        + intros Hb. eapply (Klt _ w240 w248 w264 w272 w328 w336 w344 w352 w392 w440);
            [lia| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact IB| exact MU| exact WM| exact A1OK| exact PR| lia]. }
      unfold bfree_at in KK. enter_with KK. st_eq.
    - replace (hi - lo + 1 <? 2) with false in Kge, Klt, BF2 by (symmetry; apply Z.ltb_ge; lia).
      (* [comment removed for export] *)
      brun_to 0xa2b54%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (B0_hp (hi - lo + 1)%Z WH me 15%nat 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
        [st_eq| lia| lia| cbn; lia| intros; lia| exact IB| exact MI| exact MU| exact SHINC|].
      intros c x13' Hc C1 C2 C3 C4. rewrite <- Hc in Kge, Klt, BF2, HBLE.
      open_slb_in SLB.
      (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond_z Kz; exfalso; lia|]. clear Kz.
      brun_to 0xa31ac%Z.
      replace (Z.to_nat (c - 1 + 1)) with (Z.to_nat c) in Kge, Klt, BF2, HBLE by lia.
      assert (BL : (-2147483648 < snd (fst (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b)))%Z).
      { destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex]. cbn [fst snd] in BF2 |- *. exact BF2. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_hps d lo hi a2 c (lo + 2)%Z (lo + 1)%Z (Z.to_nat c) c a1 b _ _ _ _ _ _ _ _
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| lia| lia| exact C3| exact BL| lia| lia| lia
        | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact IB| exact MU| exact WM| exact ACW| exact SH1| exact SH2| exact SHB| exact SHINC| |].
      + (* [comment removed for export] *)
        intros m' w264' w272' w328' w336' w344' w352' w392' w440'. cbv zeta.
        intros AR1' AR2' SLB' BUD' STK' MI' IB' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        eapply (B0_mss_end m' b' ltac:(lia) BUD').
        * intros Hb. eapply (Kge m' _ _ w264' w272' w328' w336' w344' w352' w392' w440');
            [lia| exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
        * intros Hb. eapply (Klt m' _ _ w264' w272' w328' w336' w344' w352' w392' w440');
            [lia| exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
      + (* [comment removed for export] *)
        intros m' w264' w272' w328' w336' w344' w352' w392' w440'. cbv zeta.
        intros BN AR1' AR2' SLB' BUD' STK' MI' IB' MU' WM' OK' PR' B'.
        destruct (mss_hps (Z.to_nat c) a1 a2 qo n d lo hi (c - 1) b) as [[a1' b'] ex] eqn:HPS. cbn [fst snd] in *.
        eapply (Klt m' _ _ w264' w272' w328' w336' w344' w352' w392' w440');
          [lia| exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
  Qed.
End B0MS.
End ACeilS1.
