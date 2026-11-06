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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Import BzCSewC.BzCSewB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msW B0_cmp_msX.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Lemma shiftr_bounds : forall b s, (0 <= b)%Z -> (0 <= s)%Z -> (0 <= Z.shiftr b s <= b)%Z.
Proof.
  intros b s Hb Hs. rewrite Z.shiftr_div_pow2 by lia.
  assert (P : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma shiftr_mono_l : forall a b s, (0 <= s)%Z -> (a <= b)%Z -> (Z.shiftr a s <= Z.shiftr b s)%Z.
Proof. intros. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia| assumption]. Qed.
Lemma shifts_small : forall b s, (0 <= b < 2097152)%Z -> (0 <= s)%Z -> (65534 < Z.shiftr b s)%Z -> (s <= 5)%Z.
Proof.
  intros b s Hb Hs H. destruct (Z.le_gt_cases s 5) as [L|G]; [exact L|]. exfalso.
  assert (M : (Z.shiftr b s <= Z.shiftr b 6)%Z).
  { rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_compat_l; [lia|]. split; [change (2 ^ 6)%Z with 64%Z; lia| apply Z.pow_le_mono_r; lia]. }
  rewrite (Z.shiftr_div_pow2 b 6) in M by lia. change (2 ^ 6)%Z with 64%Z in M. Z.div_mod_to_equations. lia.
Qed.
Lemma shiftr_m1 : forall s, (0 <= s)%Z -> Z.shiftr (-1) s = (-1)%Z.
Proof.
  intros s Hs. rewrite Z.shiftr_div_pow2 by lia. assert (P : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
  symmetry. apply Z.div_unique with (r := (2 ^ s - 1)%Z); [left; lia| lia].
Qed.


Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cCM := (Z_to_bv 64 18446744073707454463).
  Notation NBD := (18446744073709551615 - am_BD Y)%Z.
  Notation WQD := [(A2, A2 + ARR2_SIZE)]%Z.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma B0_shifts : forall (f : nat) (b sh : Z)
      (x2 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
    (0 <= b < 2097152)%Z -> (0 <= sh <= 6)%Z -> (6 - sh < Z.of_nat f)%Z ->
    (forall (sh' : Z), sh' = ms_shifts f b sh -> (0 <= sh' <= 6)%Z -> (Z.shiftr b sh' <= 65534)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) x2 gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (Z.shiftr b sh')) (Z_to_bv 64 sh') x12 (Z_to_bv 64 b) x14 x15 x16 x17
                            x18 (Z_to_bv 64 32) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa423c) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 65535) x2 gp tp x5 x6 x7 x8 x9
                          x10 (Z_to_bv 64 sh) x12 (Z_to_bv 64 b) x14 x15 x16 x17
                          x18 (Z_to_bv 64 32) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa4228) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; [intros; exfalso; lia|].
    intros b sh x2 x5 x6 x7 x8 x9 x10 x12 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m Hb Hsh Hf K.
    rewrite ms_shifts_S in K.
    pose proof (shiftr_bounds b sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    wstep. rewrite (Z.mod_small sh 32) by lia. rewrite swrap32_small by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - replace (65534 <? Z.shiftr b sh) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K sh) end; [st_eq| reflexivity| lia| lia].
    - pose proof (shifts_small b sh ltac:(lia) ltac:(lia) ltac:(lia)) as S5.
      replace (65534 <? Z.shiftr b sh) with true in K by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kn; zify_cond_z Kn; [| exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH b (sh + 1)%Z x2 x5 x6 x7 x8 x9 _ x12 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm) end;
        [st_eq| lia| lia| lia| exact K].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.

  (* [comment removed for export] *)
  Lemma B0_quad : forall (cnt : nat) (j bbStart sh : Z) (a1 a2 : zarr) (sq : slq)
      (x1 x5 x6 x7 x10 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (j + 1)%Z -> (0 <= j)%Z -> (0 <= bbStart)%Z -> (bbStart + j < n)%Z -> (0 <= sh <= 6)%Z -> (Z.shiftr j sh < 65536)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m ->
    munch WQD me m -> wmono b0segs me m ->
    shzW b0segs WQD me A1 (A1 + ARR1_SIZE) -> shzW b0segs WQD me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x10' x15' x16' x17' : word), let a2' := ms_quad cnt a2 a1 qo n bbStart sh j in zbok a2' ->
      u8arr b0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2' ARR2_SIZE) -> rw_cells b0segs m' P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m' ->
      munch WQD me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            x10' (Z_to_bv 64 sh) (Z_to_bv 64 bbStart) (Z_to_bv 64 0) x14 x15' x16' x17'
                            x18 x19 x20 (Z_to_bv 64 33) x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa437c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 sh) (Z_to_bv 64 bbStart) (Z_to_bv 64 (j + 1)) x14 x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 33) x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa4248) fc None m (seg_rom b0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j bbStart sh a1 a2 sq x1 x5 x6 x7 x10 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m
           Hcnt Hj Hbs Hbj Hsh Hq A1OK A2OK PR AR1 AR2 SLB MI MU WM SH1 SH2 K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite ms_quad_S in K. cbv zeta in K.
    pose proof (PR (bbStart + j)%Z ltac:(lia)) as Pu. set (u := rd32 a1 (bbStart + j)) in *.
    pose proof (shiftr_bounds j sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    wstep. try replace (j + 1 + -1)%Z with j by lia. try replace (j + 1 - 1)%Z with j by lia.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK (bbStart + j)%Z. fold u.
    (* [comment removed for export] *)
    brun_to 0xa42e0%Z.
    wstep. rewrite (Z.mod_small sh 32), swrap32_small by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO1 : store_ok b0segs mm (wa (A2 + (qo + 2 * u))) 2 = true)
        by (eapply (u8arr_storeN_ok b0segs _ A2 _ (qo + 2 * u) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      pose proof (zb8_write2 b0segs mm A2 a2 ARR2_SIZE (qo + 2 * u) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
      change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
    clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
    change (wr16 a2 (qo + 2 * u) (Z.shiftr j sh)) with (qwr a2 qo u (Z.shiftr j sh)) in AR2.
    pose proof (zbok_qwr a2 qo u (Z.shiftr j sh) A2OK) as OK1. set (a2q := qwr a2 qo u (Z.shiftr j sh)) in *.
    (* [comment removed for export] *)
    wstep; if_cases Ko; zify_cond_z Ko.
    - replace (u <? BZ_N_OVERSHOOT) with false in K by (symmetry; apply Z.ltb_ge; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kc; [apply bgtz_taken in Kc; [|lia] | apply bgtz_not_taken in Kc; [|lia]].
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2q sq x1 x5 x6 x7 _ x14 _ _ _ x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK1| exact PR| exact AR1| exact AR2| exact SLB| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact K].
        apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _) end;
          [st_eq| exact OK1| exact AR1| exact AR2| exact SLB| exact MI| exact MU| exact WM].
    - replace (u <? BZ_N_OVERSHOOT) with true in K by (symmetry; apply Z.ltb_lt; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      pose proof (zb8_length a2q ARR2_SIZE ltac:(lia)) as L2q.
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok b0segs mm (wa (A2 + (qo + 2 * (u + n)))) 2 = true)
          by (eapply (u8arr_storeN_ok b0segs _ A2 _ (qo + 2 * (u + n)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
        pose proof (zb8_write2 b0segs mm A2 a2q ARR2_SIZE (qo + 2 * (u + n)) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
        change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
      clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
      change (wr16 a2q (qo + 2 * (u + n)) (Z.shiftr j sh)) with (qwr a2q qo (u + n) (Z.shiftr j sh)) in AR2.
      pose proof (zbok_qwr a2q qo (u + n) (Z.shiftr j sh) OK1) as OK2. set (a2r := qwr a2q qo (u + n) (Z.shiftr j sh)) in *.
      (* [comment removed for export] *)
      wstep; if_cases Kc; [apply bgtz_taken in Kc; [|lia] | apply bgtz_not_taken in Kc; [|lia]].
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2r sq x1 x5 x6 x7 _ x14 _ _ _ x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK2| exact PR| exact AR1| exact AR2| exact SLB| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact K].
        apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _) end;
          [st_eq| exact OK2| exact AR1| exact AR2| exact SLB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Ltac ack_rd_saddr x s AS :=
    lazymatch goal with
    | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        let kx := az_base x in
        first
        [ match goal with
          | SH : shpW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
              let kl := az_base lo in constr_eq kx kl;
              let b := fresh "shb" in let RD := fresh "RDsh" in let OK := fresh "OKsh" in
              destruct (shpW_rd segs W m0 m lo hi x s SH MU ltac:(lia) ltac:(lia) ltac:(lia)) as (b & RD & OK);
              let E := fresh "Esh" in pose proof AS as E; unfold saddr in E; rewrite <- E in RD; clear E;
              wstep; clear RD
          end
        | fail 1 "ack_rd_saddr: no shpW region fact / munch for" x ]
    end.

  (* [comment removed for export] *)
  Lemma B0_step3 : forall (i ss SH6 SH9 : Z) (a1 a2 ftm : zarr) (sq : slq)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x28 : word) (me m : word -> option byte),
    let bbStart := clearmask (zget ftm (Z.shiftl ss 8)) in let bbEnd := clearmask (zget ftm (Z.shiftl (ss + 1) 8)) in
    let bbSize := (bbEnd - bbStart)%Z in let sh := ms_shifts 40 bbSize 0 in
    (0 <= i < 255)%Z -> (0 <= ss < 256)%Z -> ftv ftm -> (bbStart <= bbEnd)%Z -> (bbEnd <= n)%Z ->
    saddr (FT + 1024 * ss) SH6 -> saddr (FT + 1024 * ss + 1024) SH9 -> q80 sq = Z_to_bv 64 i ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m FT (zw32 ftm 65537) ->
    rw_cells b0segs m P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m ->
    munch WQD me m -> wmono b0segs me m -> mviews X Y WQD me ->
    (forall m' (y10 y11 y12 y13 y14 y15 y16 y17 : word),
      let a2' := ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) in zbok a2' ->
      u8arr b0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ftm 65537) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m' ->
      munch WQD me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (i + 1)) y11 y12 y13 y14 y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM x24
                            (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB x28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa20d0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM x24
                          (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB x28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                     F (Z_to_bv 64 0xa4200) fc None m (seg_rom b0segs)).
  Proof.
    intros i ss SH6 SH9 a1 a2 ftm sq x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x28 me m.
    intros bbStart bbEnd bbSize sh Hi Hss FTV Hle Hn AS6 AS9 E80 A1OK A2OK PR AR1 AR2 FTB SLB MI MU WM MV K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ftm 65537 ltac:(lia)) as Lft.
    mviews_open MV.
    pose proof SLB as SLBo. open_slb_in SLBo. rewrite E80 in SLBo.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as V1.
    assert (Hbs : bbStart = clearmask (zget ftm (256 * ss))) by (subst bbStart; rewrite shl8; reflexivity).
    assert (Hbe : bbEnd = clearmask (zget ftm (256 * ss + 256))) by (subst bbEnd; rewrite shl8; f_equal; f_equal; lia).
    pose proof (clearmask_bounds (zget ftm (256 * ss)) ltac:(lia)) as Bs. rewrite <- Hbs in Bs.
    pose proof (clearmask_bounds (zget ftm (256 * ss + 256)) ltac:(lia)) as Be. rewrite <- Hbe in Be.
    (* [comment removed for export] *)
    brun_to 0xa4208%Z. ack_rd_saddr (FT + 1024 * ss + 1024)%Z 4%Z AS9.
    rd32_at FTB (256 * ss)%Z. ack_merge.
    (* [comment removed for export] *)
    wstep. rd32_at FTB (256 * ss + 256)%Z.
    (* [comment removed for export] *)
    wstep. rewrite land_CM64, <- Hbs by lia. wstep. rewrite land_CM64, <- Hbe by lia.
    wstep. fold bbSize. replace (bbEnd - bbStart)%Z with bbSize by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_shifts 40 bbSize 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
      [st_eq| subst bbSize; lia| lia| cbn; lia|].
    intros sh' Esh Hsh' Hq. fold sh in Esh. subst sh'.
    (* [comment removed for export] *)
    assert (TAIL : forall m' (a2' : zarr) (y10 y12 y13 y15 y16 y17 : word),
      a2' = ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) -> zbok a2' ->
      u8arr b0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ftm 65537) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m' ->
      munch WQD me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            y10 (Z_to_bv 64 sh) y12 y13 (Z_to_bv 64 (bbSize - 1)) y15 y16 y17
                            x18 (Z_to_bv 64 32) (Z_to_bv 64 (FT + 1024 * ss)) (Z_to_bv 64 33) (Z_to_bv 64 SH9) cCM x24
                            (Z_to_bv 64 (FT + 1024 * ss + 1024)) (Z_to_bv 64 SH6) cSB x28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa437c) fc None m' (seg_rom b0segs))).
    { intros m' a2' y10 y12 y13 y15 y16 y17 Ea2 OK' AR1' AR2' FTB' SLB' MI' MU' WM'. rewrite <- Ea2 in K.
      clear AR1 AR2 FTB SLB SLBo MI MU WM. pose proof SLB' as SLBo. open_slb_in SLBo. rewrite E80 in SLBo.
      (* [comment removed for export] *)
      wstep. rewrite (Z.mod_small sh 32) by lia.
      assert (SR : (-1 <= Z.shiftr (bbSize - 1) sh <= 65534)%Z).
      { destruct (Z.eq_dec bbSize 0) as [E0|NE].
        - rewrite E0. change (0 - 1)%Z with (-1)%Z. rewrite shiftr_m1 by lia. lia.
        - pose proof (shiftr_bounds (bbSize - 1) sh ltac:(lia) ltac:(lia)). pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      try replace (bbSize + -1)%Z with (bbSize - 1)%Z by lia. rewrite swrap32_small by lia.
      wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia|]. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact OK'| exact AR1'| exact AR2'| exact FTB'| exact SLB'| exact MI'| exact MU'| exact WM']. }
    (* [comment removed for export] *)
    wstep. wstep; notrap.
    wstep; if_cases Kz; [apply bvlts0_true in Kz; [|lia] | apply bvlts0_false in Kz; [|lia]].
    - (* [comment removed for export] *)
      assert (E0 : bbSize = 0%Z) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm a2 _ _ _ _ _ _) end;
        [st_eq| rewrite E0; reflexivity| exact A2OK| exact AR1| exact AR2| exact FTB| exact SLB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (B0_quad (Z.to_nat bbSize) (bbSize - 1)%Z bbStart sh a1 a2 sq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact A2OK| exact PR| exact AR1| exact AR2| exact SLB| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]| eapply (shzW_sub b0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]|].
      { pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      intros m' y10 y15 y16 y17. cbv zeta. intros OK' AR1' AR2' SLB' MI' MU' WM'.
      clear AR1 AR2 SLB SLBo MI. transport_after_call b0segs m m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact OK'| exact AR1'| exact AR2'| exact FTB| exact SLB'| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
