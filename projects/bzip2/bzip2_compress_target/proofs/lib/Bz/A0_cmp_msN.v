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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
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

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cCM := (Z_to_bv 64 18446744073707454463).
  Notation WQD := [(A2, A2 + ARR2_SIZE)]%Z.

  (* [comment removed for export] *)
  Lemma A0_shifts : forall (f : nat) (b sh : Z)
      (x1 x2 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
    (0 <= b < 2097152)%Z -> (0 <= sh <= 6)%Z -> (6 - sh < Z.of_nat f)%Z ->
    (forall (sh' : Z) (x11' : word), sh' = ms_shifts f b sh -> (0 <= sh' <= 6)%Z -> (Z.shiftr b sh' <= 65534)%Z ->
      evt a0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9
                            x10 x11' (Z_to_bv 64 b) (Z_to_bv 64 sh') (Z_to_bv 64 65534) x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x99e7c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9
                          x10 x11 (Z_to_bv 64 b) (Z_to_bv 64 (sh - 1)) (Z_to_bv 64 65534) x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99e70) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; [intros; exfalso; lia|].
    intros b sh x1 x2 x5 x6 x7 x8 x9 x10 x11 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m Hb Hsh Hf K.
    rewrite ms_shifts_S in K.
    pose proof (shiftr_bounds b sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    wstep. wstep. replace (sh - 1 + 1)%Z with sh by lia. rewrite (Z.mod_small sh 32) by lia. rewrite swrap32_small by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - pose proof (shifts_small b sh ltac:(lia) ltac:(lia) ltac:(lia)) as S5.
      replace (65534 <? Z.shiftr b sh) with true in K by (symmetry; apply Z.ltb_lt; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH b (sh + 1)%Z x1 x2 x5 x6 x7 x8 x9 x10 _ x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm) end;
        [st_eq| lia| lia| lia| exact K].
    - replace (65534 <? Z.shiftr b sh) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K sh _) end; [st_eq| reflexivity| lia| lia].
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
  Ltac rdview V MU :=
    let RO := fresh "RO_" in pose proof (V _ MU) as RO; unfold scc_cells, sck_cells, sc0_cells, scl_cells in RO; cbn [l40 l48 l56 l72 l80 l88 l96] in RO; wstep; clear RO.

  (* [comment removed for export] *)
  Lemma A0_quad : forall (cnt : nat) (j bbStart sh : Z) (a1 a2 : zarr)
      (x5 x6 x10 x11 x12 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (j + 1)%Z -> (0 <= j)%Z -> (0 <= bbStart)%Z -> (bbStart + j < n)%Z -> (0 <= sh <= 6)%Z -> (Z.shiftr j sh < 65536)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv a0segs m ->
    munch WQD me m -> wmono a0segs me m ->
    frdW a0segs WQD me (P + 384) (scc_cells X) -> shzW a0segs WQD me A1 (A1 + ARR1_SIZE) -> shzW a0segs WQD me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x5' x10' x11' x14' x15' x16' x17' : word), let a2' := ms_quad cnt a2 a1 qo n bbStart sh j in zbok a2' ->
      u8arr a0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> mem_inv a0segs m' ->
      munch WQD me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6 (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12 (Z_to_bv 64 sh) x14' x15' x16' x17'
                            x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 33) x29 x30 x31)
                       F (Z_to_bv 64 0x99f60) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * (bbStart + j))) x11 x12 (Z_to_bv 64 sh) (Z_to_bv 64 (j + 2)) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * (bbStart + j))) x17
                          x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 33) x29 x30 x31)
                     F (Z_to_bv 64 0x99eb4) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j bbStart sh a1 a2 x5 x6 x10 x11 x12 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 me m
           Hcnt Hj Hbs Hbj Hsh Hq A1OK A2OK PR AR1 AR2 MI MU WM VCC SH1 SH2 K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite ms_quad_S in K. cbv zeta in K.
    pose proof (PR (bbStart + j)%Z ltac:(lia)) as Pu. set (u := rd32 a1 (bbStart + j)) in *.
    pose proof (shiftr_bounds j sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    arun. rdptr AR1 A1OK (bbStart + j)%Z. fold u.
    wstep. rdview VCC MU. arun.
    rewrite (Z.mod_small sh 32), swrap32_small by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO1 : store_ok a0segs mm (wa (A2 + (qo + 2 * u))) 2 = true)
        by (eapply (u8arr_storeN_ok a0segs _ A2 _ (qo + 2 * u) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      pose proof (zb8_write2 a0segs mm A2 a2 ARR2_SIZE (qo + 2 * u) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
      change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
    clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
    change (wr16 a2 (qo + 2 * u) (Z.shiftr j sh)) with (qwr a2 qo u (Z.shiftr j sh)) in AR2.
    pose proof (zbok_qwr a2 qo u (Z.shiftr j sh) A2OK) as OK1. set (a2q := qwr a2 qo u (Z.shiftr j sh)) in *.
    (* [comment removed for export] *)
    wstep; if_cases Ko; zify_cond_z Ko.
    - replace (u <? BZ_N_OVERSHOOT) with false in K by (symmetry; apply Z.ltb_ge; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2q _ x6 _ _ x12 _ x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK1| exact PR| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact VCC| exact SH1| exact SH2| exact K].
        apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact OK1| exact AR1| exact AR2| exact MI| exact MU| exact WM].
    - replace (u <? BZ_N_OVERSHOOT) with true in K by (symmetry; apply Z.ltb_lt; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      pose proof (zb8_length a2q ARR2_SIZE ltac:(lia)) as L2q.
      rdview VCC MU. wstep. wstep. rdview VCC MU. arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok a0segs mm (wa (A2 + (qo + 2 * (u + n)))) 2 = true)
          by (eapply (u8arr_storeN_ok a0segs _ A2 _ (qo + 2 * (u + n)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
        pose proof (zb8_write2 a0segs mm A2 a2q ARR2_SIZE (qo + 2 * (u + n)) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
        change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
      clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
      change (wr16 a2q (qo + 2 * (u + n)) (Z.shiftr j sh)) with (qwr a2q qo (u + n) (Z.shiftr j sh)) in AR2.
      pose proof (zbok_qwr a2q qo (u + n) (Z.shiftr j sh) OK1) as OK2. set (a2r := qwr a2q qo (u + n) (Z.shiftr j sh)) in *.
      wstep. wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2r _ x6 _ _ x12 _ x18 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK2| exact PR| exact AR1| exact AR2| exact MI| exact MU| exact WM| exact VCC| exact SH1| exact SH2| exact K].
        apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact OK2| exact AR1| exact AR2| exact MI| exact MU| exact WM].
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
  Lemma A0_step3 : forall (i ss SH6 SH9 : Z) (a1 a2 ftm : zarr)
      (x5 x6 x11 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x30 x31 : word) (me m : word -> option byte),
    let bbStart := clearmask (zget ftm (Z.shiftl ss 8)) in let bbEnd := clearmask (zget ftm (Z.shiftl (ss + 1) 8)) in
    let bbSize := (bbEnd - bbStart)%Z in let sh := ms_shifts 40 bbSize 0 in
    (0 <= i < 255)%Z -> (0 <= ss < 256)%Z -> ftv ftm -> (bbStart <= bbEnd)%Z -> (bbEnd <= n)%Z ->
    saddr (FT + 1024 * ss) SH6 -> saddr (FT + 4 * (256 * ss + 256)) SH9 ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ftm 65537) -> mem_inv a0segs m ->
    munch WQD me m -> wmono a0segs me m -> mviews X Y SHF WQD me ->
    (forall m' (y5 y6 y10 y11 y12 y13 y14 y15 y16 y17 : word),
      let a2' := ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) in zbok a2' ->
      u8arr a0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ftm 65537) -> mem_inv a0segs m' ->
      munch WQD me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 (i + 1)) cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) x24 (Z_to_bv 64 SH9) x26 x27
                            (Z_to_bv 64 33) (Z_to_bv 64 (FT + 4 * (256 * ss + 256))) x30 x31)
                       F (Z_to_bv 64 0x98730) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 255) x11 (Z_to_bv 64 (FT + 1024 * ss)) x13 x14 x15 x16 x17
                          (Z_to_bv 64 i) cSB x20 cCM (Z_to_bv 64 SH6) (Z_to_bv 64 FT) x24 (Z_to_bv 64 SH9) x26 x27
                          x28 (Z_to_bv 64 (FT + 4 * (256 * ss + 256))) x30 x31)
                     F (Z_to_bv 64 0x99e44) fc None m (seg_rom a0segs)).
  Proof.
    intros i ss SH6 SH9 a1 a2 ftm x5 x6 x11 x13 x14 x15 x16 x17 x20 x24 x26 x27 x28 x30 x31 me m.
    intros bbStart bbEnd bbSize sh Hi Hss FTV Hle Hn AS6 AS9 A1OK A2OK PR AR1 AR2 FTB MI MU WM MV K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ftm 65537 ltac:(lia)) as Lft.
    mviews_open MV.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as V1.
    assert (Hbs : bbStart = clearmask (zget ftm (256 * ss))) by (subst bbStart; rewrite shl8; reflexivity).
    assert (Hbe : bbEnd = clearmask (zget ftm (256 * ss + 256))) by (subst bbEnd; rewrite shl8; f_equal; f_equal; lia).
    pose proof (clearmask_bounds (zget ftm (256 * ss)) ltac:(lia)) as Bs. rewrite <- Hbs in Bs.
    pose proof (clearmask_bounds (zget ftm (256 * ss + 256)) ltac:(lia)) as Be. rewrite <- Hbe in Be.
    (* [comment removed for export] *)
    arun_to 0x99e4c%Z. ack_rd_saddr (FT + 4 * (256 * ss + 256))%Z 4%Z AS9.
    rd32_at FTB (256 * ss)%Z. ack_merge.
    rd32_at FTB (256 * ss + 256)%Z.
    (* [comment removed for export] *)
    wstep. rewrite land_CM64, <- Hbs by lia. wstep. rewrite land_CM64, <- Hbe by lia.
    wstep. fold bbSize. replace (bbEnd - bbStart)%Z with bbSize by reflexivity.
    wstep. rdview VC0 MU.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_shifts 40 bbSize 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
      [st_eq| subst bbSize; lia| lia| cbn; lia|].
    intros sh' v11 Esh Hsh' Hq. fold sh in Esh. subst sh'.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    assert (TAIL : forall m' (a2' : zarr) (y5 y10 y11 y14 y15 y16 y17 : word),
      a2' = ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) -> zbok a2' ->
      u8arr a0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ftm 65537) -> mem_inv a0segs m' ->
      munch WQD me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 x6 (Z_to_bv 64 1) (me_sp X) (Z_to_bv 64 P)
                            y10 y11 (Z_to_bv 64 bbSize) (Z_to_bv 64 sh) y14 y15 y16 y17
                            (Z_to_bv 64 i) cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) x24 (Z_to_bv 64 SH9) x26 x27
                            (Z_to_bv 64 33) (Z_to_bv 64 (FT + 4 * (256 * ss + 256))) x30 x31)
                       F (Z_to_bv 64 0x99f60) fc None m' (seg_rom a0segs))).
    { intros m' a2' y5 y10 y11 y14 y15 y16 y17 Ea2 OK' AR1' AR2' FTB' MI' MU' WM'. rewrite <- Ea2 in K.
      clear AR1 AR2 FTB MI MU WM.
      (* [comment removed for export] *)
      wstep. wstep. rewrite (Z.mod_small sh 32) by lia.
      assert (SR : (-1 <= Z.shiftr (bbSize - 1) sh <= 65534)%Z).
      { destruct (Z.eq_dec bbSize 0) as [E0|NE].
        - rewrite E0. change (0 - 1)%Z with (-1)%Z. rewrite shiftr_m1 by lia. lia.
        - pose proof (shiftr_bounds (bbSize - 1) sh ltac:(lia) ltac:(lia)). pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      replace (bbSize + -1)%Z with (bbSize - 1)%Z by lia. rewrite swrap32_small by lia.
      wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact OK'| exact AR1'| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM']. }
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - (* [comment removed for export] *)
      assert (E0 : bbSize = 0%Z) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm a2 _ _ _ _ _ _ _) end;
        [st_eq| rewrite E0; reflexivity| exact A2OK| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. rdview VC0 MU. wstep. wstep.
      replace (Z_to_bv 64 (18446744073709551615 - bbStart + bbEnd)) with (Z_to_bv 64 (bbSize - 1))
        by (apply Z_to_bv_eqm; subst bbSize; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_quad (Z.to_nat bbSize) (bbSize - 1)%Z bbStart sh a1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact A2OK| exact PR| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl
        | eapply (frdW_sub a0segs); [exact VCC| exact MU| sub_fp_solve]
        | eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]| eapply (shzW_sub a0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]|].
      { pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      intros m' y5 y10 y11 y14 y15 y16 y17. cbv zeta. intros OK' AR1' AR2' MI' MU' WM'.
      clear AR1 AR2 MI. transport_after_call a0segs m m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact OK'| exact AR1'| exact AR2'| exact FTB| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
