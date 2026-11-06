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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables Hh qsp l1 r1 lq nnd : Z.
  Variables SHlo SHhi : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Hypothesis ASlo : saddr (SLO + 4 * (qsp - 1)) SHlo. Hypothesis AShi : saddr (SHI + 4 * (qsp - 1)) SHhi.
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation QF ra t0 t1 t2 a0 a1 a2 a3 a4 lo a6 a7 s2 hi s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 (Z_to_bv 64 lo) a6 a7
         s2 (Z_to_bv 64 l1) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 hi) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 r1) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation cT0 := (Z_to_bv 64 SHhi). Notation cA0 := (Z_to_bv 64 (SLO + 4 * (qsp - 1))). Notation cA1 := (Z_to_bv 64 (SHI + 4 * (qsp - 1))).
  Notation cA6 := (Z_to_bv 64 (qsp - 1)). Notation cA7 := (Z_to_bv 64 SHlo).
  Definition med_idx (r3 lo hi : Z) : Z := if (r3 =? 0)%Z then lo else if (r3 =? 1)%Z then ((lo + hi) / 2)%Z else hi.
  Notation WM := [(P + 144, P + 216)]%Z.

  Ltac prep XOK XSEP fm ec :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & _ & _);
    let L1 := fresh "L1" in let L2 := fresh "L2" in
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1; pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
  Ltac rd_fm fm j AR1 FMOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 a0segs mm A1 fm ARR1_SIZE j _ AR1 ltac:(lia) ltac:(lia) FMOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac rd_ec ec x AR2 ECOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 a0segs mm A2 ec ARR2_SIZE x _ AR2 ltac:(lia) ltac:(lia) ECOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.

  (* [comment removed for export] *)
  Lemma A0_qmed : forall (hi lo rr : Z) (fm ec : zarr) (me m : word -> option byte) (ra t1 t2 a4 t3 t4 t5 t6 v144 v160 v176 v208 : word),
    (0 <= lo)%Z -> (lo + 10 <= hi < nb)%Z -> (0 <= rr < 32768)%Z -> (1 <= qsp <= 99)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells a0segs m (P + 80) (SCq X Y lq nnd v144 rr v160 Hh v176 (Z_to_bv 64 qsp) v208) -> mem_inv a0segs m ->
    munch WM me m -> wmono a0segs me m ->
    shzW a0segs WM me A1 (A1 + ARR1_SIZE) -> shzW a0segs WM me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x12 : word), let r' := ((rr * 7621 + 1) mod 32768)%Z in let med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi)) in
      u8arr a0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells a0segs m' (P + 80) (SCq X Y lq nnd v144 r' v160 Hh v176 (Z_to_bv 64 qsp) (Z_to_bv 64 (qsp - 1))) -> mem_inv a0segs m' ->
      munch WM me m' -> wmono a0segs me m' -> (0 <= med < nb)%Z ->
      evt a0segs Q (MS (QF (Z_to_bv 64 lo) cT0 t1 t2 cA0 cA1 x12 (Z_to_bv 64 lo) (Z_to_bv 64 hi) lo cA6 cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 hi) t3 t4 (Z_to_bv 64 med) t6)
                       F (Z_to_bv 64 0x9b8cc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (QF ra cT0 t1 t2 cA0 cA1 (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 9) a4 lo cA6 cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 qsp) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b80c) fc None m (seg_rom a0segs)).
  Proof.
    intros hi lo rr fm ec me m ra t1 t2 a4 t3 t4 t5 t6 v144 v160 v176 v208 Hlo Hhi Hrr Hq FMR ECR FMOK' ECOK' AR1 AR2 SC MI MU WMo SH1 SH2 K. cbv zeta in K.
    prep XOK XSEP fm ec. bz_params. unfold SCq in SC, K.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. rewrite lcg_hi15 by lia.
    set (r' := ((rr * 7621 + 1) mod 32768)%Z) in *. assert (Hr' : (0 <= r' < 32768)%Z) by (subst r'; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite lcg_div3 by lia. fold r'.
    assert (Hq3 : (0 <= r' / 3 < 10923)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.div_mod r' 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound r' 3 ltac:(lia)) as Hm3.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.div_mul (r' - r' / 3 - r' / 3 * 2) 281474976710656) by lia.
    replace (r' - r' / 3 - r' / 3 * 2)%Z with (r' mod 3)%Z by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    assert (TAIL : forall m1 (idx : Z) (x13 : word), idx = med_idx (r' mod 3) lo hi ->
      rw_cells a0segs m1 (P + 80) [C8 (Z_to_bv 64 (A1 + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
         C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 r'); C8 v160; C8 (Z_to_bv 64 Hh); C8 v176;
         C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 (Z_to_bv 64 qsp); C8 v208; C8 (Z_to_bv 64 (A1 - 4))] ->
      u8arr a0segs m1 A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m1 A2 (zb8 ec ARR2_SIZE) -> mem_inv a0segs m1 -> munch WM me m1 -> wmono a0segs me m1 ->
      evt a0segs Q (MS (QF ra cT0 t1 t2 cA0 cA1 (Z_to_bv 64 idx) x13 (Z_to_bv 64 r') lo cA6 cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 qsp) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b868) fc None m1 (seg_rom a0segs))).
    { intros m1 idx x13 Hidx SC1 AR1' AR2' MI1 MU1 WM1.
      assert (Hix : (lo <= idx <= hi)%Z).
      { subst idx. unfold med_idx. destruct (Z.eqb_spec (r' mod 3) 0); [lia|]. destruct (Z.eqb_spec (r' mod 3) 1); [|lia].
        split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]. }
      pose proof (proj2 FMR idx ltac:(lia)) as Fi. pose proof (ECR (rd32 fm idx) ltac:(lia)) as Ei.
      (* [comment removed for export] *)
      arun. rd_fm fm idx AR1' FMOK'. try rewrite (zx32_of_Z (rd32 fm idx)) by lia.
      arun. rd_ec ec (rd32 fm idx) AR2' ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm idx))) by lia.
      (* [comment removed for export] *)
      wstep. wstep. rewrite (Z.div_mul (qsp - 1) 4294967296) by lia || rewrite (Z.div_mul (qsp + -1) 4294967296) by lia || idtac.
      wstep. wstep. wstep. wstep. wstep. wstep; if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
      subst idx. enter_with (K _ _); [st_eq| exact AR1'| exact AR2'| exact SC1| exact MI1| exact MU1| exact WM1| lia]. }
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0.
    - eapply (TAIL _ lo); [unfold med_idx; rewrite K0; reflexivity| exact SC| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
    - (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      + (* [comment removed for export] *)
        wstep. eapply (TAIL _ hi); [unfold med_idx; destruct (Z.eqb_spec (r' mod 3) 0); [lia|]; destruct (Z.eqb_spec (r' mod 3) 1); [lia| reflexivity]| exact SC| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
      + (* [comment removed for export] *)
        wstep. wstep. wstep.
        replace (Z.shiftr (hi + lo) 1) with ((lo + hi) / 2)%Z by (rewrite Z.shiftr_div_pow2 by lia; f_equal; lia) || idtac.
        enter_with (TAIL _ ((lo + hi) / 2)%Z _); [st_eq| unfold med_idx; destruct (Z.eqb_spec (r' mod 3) 0); [lia|]; destruct (Z.eqb_spec (r' mod 3) 1); [reflexivity| lia]| exact SC| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
  Qed.

  Ltac st_fm fm i AR1 :=
    let SO := fresh "SO" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok a0segs mm A1 _ (4 * i) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end;
    wstep; zb8_store4 AR1 i; try clear SO.
  Notation WS := [(A1, A1 + ARR1_SIZE)]%Z.

  (* [comment removed for export] *)
  Lemma A0_vsw1 : forall (c : nat) (y1 y2 : Z) (fm : zarr) (lo hi : Z) (me m : word -> option byte) (ra t0 t2 a0 a1 a4 a7 s10 t4 t5 t6 : word),
    (1 <= c)%nat -> (0 <= y1)%Z -> (y1 + Z.of_nat c <= nb)%Z -> (0 <= y2)%Z -> (y2 + Z.of_nat c <= nb)%Z ->
    fm_range fm nb -> zbok fm ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> mem_inv a0segs m -> munch WS me m -> wmono a0segs me m ->
    shzW a0segs WS me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x6 x12 x13 x14 x16 x28 x29 : word), let fm' := fvswap c fm y1 y2 (Z.of_nat c) in
      u8arr a0segs m' A1 (zb8 fm' ARR1_SIZE) -> mem_inv a0segs m' -> munch WS me m' -> wmono a0segs me m' ->
      fm_range fm' nb -> zbok fm' ->
      evt a0segs Q (MS (QF ra t0 x6 t2 a0 a1 x12 x13 x14 lo x16 a7 (Z_to_bv 64 1) hi s10 x28 x29 t5 t6)
                       F (Z_to_bv 64 0x9bc08) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (QF ra t0 (Z_to_bv 64 (A1 + 4 * y2)) t2 a0 a1 (Z_to_bv 64 (A1 + 4 * y2)) (Z_to_bv 64 (A1 + 4 * y1)) a4 lo (Z_to_bv 64 (A1 + 4 * y1)) a7 (Z_to_bv 64 1) hi s10
                         (Z_to_bv 64 (Z.of_nat c + 1)) t4 t5 t6)
                     F (Z_to_bv 64 0x9bb9c) fc None m (seg_rom a0segs)).
  Proof.
    induction c as [|c IH]; intros y1 y2 fm lo hi me m ra t0 t2 a0 a1 a4 a7 s10 t4 t5 t6 Hc Hy1 Hy1c Hy2 Hy2c FMR FMOK' AR1 MI MU WMo SH1 K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. bz_params. pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1.
    rewrite fvswap_S in K. replace (0 <? Z.of_nat (S c))%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (proj2 FMR y1 ltac:(lia)) as F1. pose proof (proj2 FMR y2 ltac:(lia)) as F2.
    (* [comment removed for export] *)
    arun. rd_fm fm y1 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y1)) by lia.
    arun. rd_fm fm y2 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y2)) by lia.
    (* [comment removed for export] *)
    arun. st_fm fm y1 AR1. rewrite (unsigned_lit (rd32 fm y2)) in AR1 by lia.
    pose proof (zb8_length (wr32 fm y1 (rd32 fm y2)) ARR1_SIZE ltac:(lia)) as L1'.
    st_fm (wr32 fm y1 (rd32 fm y2)) y2 AR1. rewrite (unsigned_lit (rd32 fm y1)) in AR1 by lia.
    change (wr32 (wr32 fm y1 (rd32 fm y2)) y2 (rd32 fm y1)) with (fswap fm y1 y2) in AR1.
    assert (FMR1 : fm_range (fswap fm y1 y2) nb) by (apply fswap_range; [exact FMR| lia| lia]).
    assert (FMOK1 : zbok (fswap fm y1 y2)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
    (* [comment removed for export] *)
    arun. if_cases Ke; zify_cond_z Ke.
    - replace (Z.of_nat (S c) - 1)%Z with (Z.of_nat c) in K by lia.
      enter_with (IH (y1 + 1)%Z (y2 + 1)%Z (fswap fm y1 y2) lo hi me); [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1| exact MI| exact MU| exact WMo| exact SH1|].
      intros m' x6 x12 x13 x14 x16 x28 x29. cbv zeta. exact (K m' x6 x12 x13 x14 x16 x28 x29).
    - assert (c = 0)%nat by lia. subst c. cbn [fvswap Z.of_nat] in K. replace (0 <? 1 - 1)%Z with false in K by reflexivity.
      wstep.
      enter_with (K _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact MI| exact MU| exact WMo| exact FMR1| exact FMOK1].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_vsw2 : forall (c : nat) (y1 y2 : Z) (fm : zarr) (lo hi : Z) (me m : word -> option byte) (ra t0 t2 a0 a1 a4 a6 a7 s10 t5 t6 : word),
    (1 <= c)%nat -> (0 <= y1)%Z -> (y1 + Z.of_nat c <= nb)%Z -> (0 <= y2)%Z -> (y2 + Z.of_nat c <= nb)%Z ->
    fm_range fm nb -> zbok fm ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> mem_inv a0segs m -> munch WS me m -> wmono a0segs me m ->
    shzW a0segs WS me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x6 x12 x13 x14 x28 x29 x30 : word), let fm' := fvswap c fm y1 y2 (Z.of_nat c) in
      u8arr a0segs m' A1 (zb8 fm' ARR1_SIZE) -> mem_inv a0segs m' -> munch WS me m' -> wmono a0segs me m' ->
      fm_range fm' nb -> zbok fm' ->
      evt a0segs Q (MS (QF ra t0 x6 t2 a0 a1 x12 x13 x14 lo a6 a7 (Z_to_bv 64 1) hi s10 x28 x29 x30 t6)
                       F (Z_to_bv 64 0x9bcac) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (QF ra t0 (Z_to_bv 64 (A1 + 4 * y1)) t2 a0 a1 (Z_to_bv 64 (A1 + 4 * y2)) (Z_to_bv 64 (A1 + 4 * y1)) a4 lo a6 a7 (Z_to_bv 64 1) hi s10
                         (Z_to_bv 64 (A1 + 4 * y2)) (Z_to_bv 64 (Z.of_nat c + 1)) t5 t6)
                     F (Z_to_bv 64 0x9bc40) fc None m (seg_rom a0segs)).
  Proof.
    induction c as [|c IH]; intros y1 y2 fm lo hi me m ra t0 t2 a0 a1 a4 a6 a7 s10 t5 t6 Hc Hy1 Hy1c Hy2 Hy2c FMR FMOK' AR1 MI MU WMo SH1 K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. bz_params. pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1.
    rewrite fvswap_S in K. replace (0 <? Z.of_nat (S c))%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (proj2 FMR y1 ltac:(lia)) as F1. pose proof (proj2 FMR y2 ltac:(lia)) as F2.
    arun. rd_fm fm y1 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y1)) by lia.
    arun. rd_fm fm y2 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y2)) by lia.
    arun. st_fm fm y1 AR1. rewrite (unsigned_lit (rd32 fm y2)) in AR1 by lia.
    pose proof (zb8_length (wr32 fm y1 (rd32 fm y2)) ARR1_SIZE ltac:(lia)) as L1'.
    st_fm (wr32 fm y1 (rd32 fm y2)) y2 AR1. rewrite (unsigned_lit (rd32 fm y1)) in AR1 by lia.
    change (wr32 (wr32 fm y1 (rd32 fm y2)) y2 (rd32 fm y1)) with (fswap fm y1 y2) in AR1.
    assert (FMR1 : fm_range (fswap fm y1 y2) nb) by (apply fswap_range; [exact FMR| lia| lia]).
    assert (FMOK1 : zbok (fswap fm y1 y2)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
    arun. if_cases Ke; zify_cond_z Ke.
    - replace (Z.of_nat (S c) - 1)%Z with (Z.of_nat c) in K by lia.
      enter_with (IH (y1 + 1)%Z (y2 + 1)%Z (fswap fm y1 y2) lo hi me); [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1| exact MI| exact MU| exact WMo| exact SH1|].
      intros m' x6 x12 x13 x14 x28 x29 x30. cbv zeta. exact (K m' x6 x12 x13 x14 x28 x29 x30).
    - assert (c = 0)%nat by lia. subst c. cbn [fvswap Z.of_nat] in K. replace (0 <? 1 - 1)%Z with false in K by reflexivity.
      wstep.
      enter_with (K _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact MI| exact MU| exact WMo| exact FMR1| exact FMOK1].
  Qed.

  (* [comment removed for export] *)
  Definition qtail (lo hi rr' : Z) (slo shi : zarr) (pf : fpart) : fqs :=
    let fm := fp_fm pf in let unLo := fp_unLo pf in let unHi := fp_unHi pf in let ltLo := fp_ltLo pf in let gtHi := fp_gtHi pf in
    if (gtHi <? ltLo)%Z then FQS fm (qsp - 1) slo shi rr'
    else
      let n := fmin (ltLo - lo) (unLo - ltLo) in
      let fm1 := fvswap (S (Z.to_nat n)) fm lo (unLo - n) n in
      let m := fmin (hi - gtHi) (gtHi - unHi) in
      let fm2 := fvswap (S (Z.to_nat m)) fm1 unLo (hi - m + 1) m in
      let n' := (lo + unLo - ltLo - 1)%Z in
      let m' := (hi - (gtHi - unHi) + 1)%Z in
      let q2 := FQS fm2 (qsp - 1) slo shi rr' in
      if (hi - m' <? n' - lo)%Z then fpush (fpush q2 lo n') m' hi else fpush (fpush q2 m' hi) lo n'.

  (* [comment removed for export] *)
  Definition stk_def (slo shi : zarr) (k : Z) : Prop := forall i, (0 <= i < k)%Z -> zdef slo i = true /\ zdef shi i = true.

  Lemma ovw_skip_redundant : forall a J n i v j w, zdef a i = true -> zget a i = v ->
    ovw (zset (zset a i v) j w) J n = ovw (zset a j w) J n.
  Proof.
    intros a J n i v j w Hd Hg. apply ovw_ext. intros k Hk. rewrite !zdef_zset, !zget_zset.
    destruct (Z.eqb_spec k j); [split; reflexivity|]. destruct (Z.eqb_spec k i) as [->|]; [rewrite Hd, Hg; split; reflexivity| split; reflexivity].
  Qed.

  Notation WQ := [(A1, A1 + ARR1_SIZE); (P + 144, P + 216); (SLO, SLO + 400); (SHI, SHI + 400)]%Z.
  Notation SCp v144 rr' v160 v176 v208 := (SCq X Y lq nnd v144 rr' v160 Hh v176 (Z_to_bv 64 qsp) v208).

  (* [comment removed for export] *)
  Lemma A0_qpush : forall (pf : fpart) (med hi lo rr' : Z) (slo shi : zarr) (Jlo Jhi : list byte) (me m : word -> option byte) (x6 x12 x13 x28 x29 x31 v144 v160 v176 : word),
    (0 <= lo)%Z -> (lo + 10 <= hi < nb)%Z -> (1 <= qsp <= 98)%Z -> fp_ok lo hi pf -> (fp_unHi pf < fp_unLo pf)%Z ->
    fm_range (fp_fm pf) nb -> zbok (fp_fm pf) -> stk_def slo shi qsp -> zget slo (qsp - 1) = lo -> zget shi (qsp - 1) = hi ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z ->
    u8arr a0segs m A1 (zb8 (fp_fm pf) ARR1_SIZE) -> rw_cells a0segs m (P + 80) (SCp v144 rr' v160 v176 (Z_to_bv 64 (qsp - 1))) ->
    u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SLO (ovw slo Jlo 100) -> mem_inv a0segs m ->
    munch WQ me m -> wmono a0segs me m ->
    shzW a0segs WQ me A1 (A1 + ARR1_SIZE) -> shzW a0segs WQ me SLO (SLO + 400) -> shzW a0segs WQ me SHI (SHI + 400) ->
    (forall m' (x1 x5 x6' x7 x10 x11 x12' x13' x14 x15 x16 x17 x23 x26 x28' x29' x30 x31' : word), let q' := qtail lo hi rr' slo shi pf in
      u8arr a0segs m' A1 (zb8 (fq_fm q') ARR1_SIZE) -> rw_cells a0segs m' (P + 80) (SCp v144 rr' v160 v176 (Z_to_bv 64 (fq_sp q'))) ->
      u32arr a0segs m' SHI (ovw (fq_shi q') Jhi 100) -> u32arr a0segs m' SLO (ovw (fq_slo q') Jlo 100) -> mem_inv a0segs m' ->
      munch WQ me m' -> wmono a0segs me m' ->
      fm_range (fq_fm q') nb -> zbok (fq_fm q') -> stk_def (fq_slo q') (fq_shi q') (fq_sp q') -> (0 <= fq_sp q' <= qsp + 1)%Z -> fq_r q' = rr' ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6' x7 (fe_sp X) (Z_to_bv 64 P) x10 x11 x12' x13' x14 x15 x16 x17
                            (Z_to_bv 64 1) (Z_to_bv 64 l1) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB x23 (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) x26 (Z_to_bv 64 r1) x28' x29' x30 x31')
                       F (Z_to_bv 64 0x9bd40) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (QF (Z_to_bv 64 (fp_ltLo pf)) cT0 x6 (Z_to_bv 64 (fp_unLo pf)) cA0 cA1 x12 x13 (Z_to_bv 64 (fp_unHi pf)) lo cA6 cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 (fp_gtHi pf)) x28 x29 (Z_to_bv 64 med) x31)
                     F (Z_to_bv 64 0x9bb58) fc None m (seg_rom a0segs)).
  Proof.
    intros pf med hi lo rr' slo shi Jlo Jhi me m x6 x12 x13 x28 x29 x31 v144 v160 v176 Hlo Hhi Hq OK Hbr FMR FMOK' SD Glo Ghi LJlo LJhi AR1 SC SHIc SLOc MI MU WMo SH1 SHl SHh K. cbv zeta in K.
    destruct pf as [fm unLo unHi ltLo gtHi]. unfold fp_ok in OK. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *.
    fsenv_open XOK. afenv_open YOK. pose proof YSEP as SPY. unfold afenv_sep, apartv in SPY. cps_destruct SPY as (AP1B & _ & _).
    bz_params. unfold SCq in SC, K. unfold qtail in K. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kg; zify_cond_z Kg.
    { (* [comment removed for export] *)
      replace (gtHi <? ltLo)%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
      enter_with (K m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact SC| exact SHIc| exact SLOc| exact MI| exact MU| exact WMo| exact FMR| exact FMOK'| | lia| reflexivity].
      intros i Hi. apply SD. lia. }
    replace (gtHi <? ltLo)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
    set (n := fmin (ltLo - lo) (unLo - ltLo)) in K.
    assert (Hn : ((ltLo - lo < unLo - ltLo)%Z /\ n = (ltLo - lo)%Z) \/ ((unLo - ltLo <= ltLo - lo)%Z /\ n = (unLo - ltLo)%Z)) by (subst n; unfold fmin; destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia).
    set (mm := fmin (hi - gtHi) (gtHi - unHi)) in K.
    assert (Hm : ((hi - gtHi < gtHi - unHi)%Z /\ mm = (hi - gtHi)%Z) \/ ((gtHi - unHi <= hi - gtHi)%Z /\ mm = (gtHi - unHi)%Z)) by (subst mm; unfold fmin; destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia).
    set (fm1 := fvswap (S (Z.to_nat n)) fm lo (unLo - n) n) in K.
    set (fm2 := fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) mm) in K.
    set (n' := (lo + unLo - ltLo - 1)%Z) in K. set (m' := (hi - (gtHi - unHi) + 1)%Z) in K.
    clearbody n mm.
    (* [comment removed for export] *)
    assert (T3 : forall m3 (z6 z12 z13 z14 z28 z29 z30 : word),
      u8arr a0segs m3 A1 (zb8 fm2 ARR1_SIZE) -> mem_inv a0segs m3 ->
      munch WQ me m3 -> wmono a0segs me m3 -> fm_range fm2 nb -> zbok fm2 ->
      rw_cells a0segs m3 (P + 80) [C8 (Z_to_bv 64 (A1 + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
         C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 rr'); C8 v160; C8 (Z_to_bv 64 Hh); C8 v176;
         C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 (Z_to_bv 64 qsp); C8 (Z_to_bv 64 (qsp - 1)); C8 (Z_to_bv 64 (A1 - 4))] ->
      u32arr a0segs m3 SHI (ovw shi Jhi 100) -> u32arr a0segs m3 SLO (ovw slo Jlo 100) ->
      evt a0segs Q (MS (QF (Z_to_bv 64 ltLo) cT0 z6 (Z_to_bv 64 unLo) cA0 cA1 z12 z13 z14 lo (Z_to_bv 64 (gtHi - unHi)) cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 gtHi) z28 z29 z30 (Z_to_bv 64 unHi))
                       F (Z_to_bv 64 0x9bcac) fc None m3 (seg_rom a0segs))).
    { intros m3 z6 z12 z13 z14 z28 z29 z30 AR1' MI3 MU3 WM3 FMR2 FMOK2 SC3 SHI3 SLO3.
      (* [comment removed for export] *)
      assert (T4 : forall m4 (slo4 shi4 : zarr) (v2lo v2hi : Z) (w2hi : word) (u5 u6 u7 u10 u11 u13 u14 u16 u17 u26 u28 u29 u30 u31 : word),
        (bv_unsigned w2hi mod 4294967296 = v2hi mod 4294967296)%Z -> (0 <= v2lo < 4294967296)%Z ->
        u8arr a0segs m4 A1 (zb8 fm2 ARR1_SIZE) -> mem_inv a0segs m4 -> munch WQ me m4 -> wmono a0segs me m4 ->
        rw_cells a0segs m4 (P + 80) [C8 (Z_to_bv 64 (A1 + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
           C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 rr'); C8 v160; C8 (Z_to_bv 64 Hh); C8 v176;
           C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 (Z_to_bv 64 qsp); C8 (Z_to_bv 64 (qsp - 1)); C8 (Z_to_bv 64 (A1 - 4))] ->
        u32arr a0segs m4 SHI (ovw shi4 Jhi 100) -> u32arr a0segs m4 SLO (ovw slo4 Jlo 100) ->
        (forall m5 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y26 y28 y29 y30 y31 : word),
           u8arr a0segs m5 A1 (zb8 fm2 ARR1_SIZE) -> mem_inv a0segs m5 -> munch WQ me m5 -> wmono a0segs me m5 ->
           rw_cells a0segs m5 (P + 80) [C8 (Z_to_bv 64 (A1 + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
              C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 rr'); C8 v160; C8 (Z_to_bv 64 Hh); C8 v176;
              C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 (Z_to_bv 64 qsp); C8 (Z_to_bv 64 (qsp + 1)); C8 (Z_to_bv 64 (A1 - 4))] ->
           u32arr a0segs m5 SHI (ovw (zset shi4 qsp v2hi) Jhi 100) -> u32arr a0segs m5 SLO (ovw (zset slo4 qsp v2lo) Jlo 100) ->
           evt a0segs Q (MS (mkR y1 (Z_to_bv 64 P) gp tp y5 y6 y7 (fe_sp X) (Z_to_bv 64 P) y10 y11 y12 y13 y14 y15 y16 y17
                                 (Z_to_bv 64 1) (Z_to_bv 64 l1) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB y23 (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) y26 (Z_to_bv 64 r1) y28 y29 y30 y31)
                            F (Z_to_bv 64 0x9bd40) fc None m5 (seg_rom a0segs))) ->
        evt a0segs Q (MS (mkR (Z_to_bv 64 ltLo) (Z_to_bv 64 P) gp tp u5 u6 u7 (fe_sp X) (Z_to_bv 64 P) u10 u11 (Z_to_bv 64 v2lo) u13 u14 (Z_to_bv 64 lo) u16 u17
                              (Z_to_bv 64 1) (Z_to_bv 64 l1) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB w2hi (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) u26 (Z_to_bv 64 r1) u28 u29 u30 u31)
                         F (Z_to_bv 64 0x9bcf0) fc None m4 (seg_rom a0segs))).
      { intros m4 slo4 shi4 v2lo v2hi w2hi u5 u6 u7 u10 u11 u13 u14 u16 u17 u26 u28 u29 u30 u31 Ev2 Hv2 AR4 MI4 MU4 WM4 SC4 SHI4 SLO4 K5.
        pose proof (ovw_length shi4 Jhi 100 ltac:(lia)) as LH4. pose proof (ovw_length slo4 Jlo 100 ltac:(lia)) as LL4.
        (* [comment removed for export] *)
        wstep. wstep. wstep. rewrite ?slli32_srli30.
        (* [comment removed for export] *)
        arun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok a0segs mm SLO _ qsp _ SLO4 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
        wstep. ovw_store SLO4 qsp v2lo wval_lit.
        (* [comment removed for export] *)
        arun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok a0segs mm SHI _ qsp _ SHI4 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
        wstep. ovw_store SHI4 qsp v2hi (exact Ev2).
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        enter_with (K5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR4| exact MI4| exact MU4| exact WM4| exact SC4| exact SHI4| exact SLO4]. }
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. rewrite swrap32_plus_not by lia. wstep. wstep.
      (* [comment removed for export] *)
      wstep; if_cases Kp; zify_cond_z Kp.
      - (* [comment removed for export] *)
        replace (hi - m' <? n' - lo)%Z with false in K by (symmetry; apply Z.ltb_ge; subst n' m'; lia).
        (* [comment removed for export] *)
        arun.
        pose proof (u32arr_store_ok a0segs m3 SLO _ (qsp - 1) _ SLO3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
        wstep. ovw_store SLO3 (qsp - 1)%Z m' (subst m'; wval_lit).
        (* [comment removed for export] *)
        wstep. wstep.
        lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?w _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
          enter_with (T4 _ (zset slo (qsp - 1) m') shi lo n' w _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| subst n'; rewrite unsigned_lit_mod32; Z.div_mod_to_equations; lia| lia| exact AR1'| exact MI3| exact MU3| exact WM3| exact SC3| exact SHI3| exact SLO3|].
        intros m5 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y26 y28 y29 y30 y31 AR5 MI5 MU5 WM5 SC5 SHI5 SLO5.
        rewrite <- (ovw_skip_redundant shi Jhi 100 (qsp - 1) hi qsp n') in SHI5 by (try apply SD; try exact Ghi; lia).
        unfold fpush in K. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        replace (qsp + 1)%Z with (qsp - 1 + 1 + 1)%Z in SC5 by lia.
        enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR5| exact SC5| | | exact MI5| exact MU5| exact WM5| exact FMR2| exact FMOK2| | lia| reflexivity].
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SHI5.
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SLO5.
        + intros i Hi. rewrite !zdef_zset. destruct (Z.eqb_spec i (qsp - 1 + 1)); [split; reflexivity|]. destruct (Z.eqb_spec i (qsp - 1)); [split; reflexivity|]. cbn [orb]. apply SD. lia.
      - (* [comment removed for export] *)
        replace (hi - m' <? n' - lo)%Z with true in K by (symmetry; apply Z.ltb_lt; subst n' m'; lia).
        (* [comment removed for export] *)
        arun.
        pose proof (u32arr_store_ok a0segs m3 SHI _ (qsp - 1) _ SHI3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
        wstep. ovw_store SHI3 (qsp - 1)%Z n' (subst n'; rewrite unsigned_lit_mod32; Z.div_mod_to_equations; lia).
        (* [comment removed for export] *)
        wstep.
        enter_with (T4 _ slo (zset shi (qsp - 1) n') m' hi (Z_to_bv 64 hi) _ _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| rewrite unsigned_lit by lia; reflexivity| subst m'; lia| exact AR1'| exact MI3| exact MU3| exact WM3| exact SC3| exact SHI3| exact SLO3|].
        intros m5 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y26 y28 y29 y30 y31 AR5 MI5 MU5 WM5 SC5 SHI5 SLO5.
        rewrite <- (ovw_skip_redundant slo Jlo 100 (qsp - 1) lo qsp m') in SLO5 by (try apply SD; try exact Glo; lia).
        unfold fpush in K. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        replace (qsp + 1)%Z with (qsp - 1 + 1 + 1)%Z in SC5 by lia.
        enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR5| exact SC5| | | exact MI5| exact MU5| exact WM5| exact FMR2| exact FMOK2| | lia| reflexivity].
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SHI5.
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SLO5.
        + intros i Hi. rewrite !zdef_zset. destruct (Z.eqb_spec i (qsp - 1 + 1)); [split; reflexivity|]. destruct (Z.eqb_spec i (qsp - 1)); [split; reflexivity|]. cbn [orb]. apply SD. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    assert (T1 : evt a0segs Q (MS (QF (Z_to_bv 64 ltLo) cT0 x6 (Z_to_bv 64 unLo) cA0 cA1 (Z_to_bv 64 (unLo - ltLo)) (Z_to_bv 64 gtHi) (Z_to_bv 64 unHi) lo cA6 cA7
                                      (Z_to_bv 64 1) hi (Z_to_bv 64 gtHi) (Z_to_bv 64 n) x29 (Z_to_bv 64 med) (Z_to_bv 64 unHi))
                       F (Z_to_bv 64 0x9bb78) fc None m (seg_rom a0segs))).
    2:{ wstep; if_cases Kn; zify_cond_z Kn.
        - enter_with T1; st_eq.
        - wstep. enter_with T1; st_eq. }
    (* [comment removed for export] *)
    assert (T2 : forall m2 (y6 y12 y13 y14 y16 y28 y29 : word),
      u8arr a0segs m2 A1 (zb8 fm1 ARR1_SIZE) -> mem_inv a0segs m2 ->
      munch WQ me m2 -> wmono a0segs me m2 -> fm_range fm1 nb -> zbok fm1 ->
      rw_cells a0segs m2 (P + 80) [C8 (Z_to_bv 64 (A1 + 4)); C8 (Z_to_bv 64 7621); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 lq); C8 (Z_to_bv 64 nnd);
         C8 (Z_to_bv 64 (ae_SHF Y)); C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 0); C8 v144; C8 (Z_to_bv 64 rr'); C8 v160; C8 (Z_to_bv 64 Hh); C8 v176;
         C8 (Z_to_bv 64 SHI); C8 (Z_to_bv 64 SLO); C8 (Z_to_bv 64 qsp); C8 (Z_to_bv 64 (qsp - 1)); C8 (Z_to_bv 64 (A1 - 4))] ->
      u32arr a0segs m2 SHI (ovw shi Jhi 100) -> u32arr a0segs m2 SLO (ovw slo Jlo 100) ->
      evt a0segs Q (MS (QF (Z_to_bv 64 ltLo) cT0 y6 (Z_to_bv 64 unLo) cA0 cA1 y12 y13 y14 lo y16 cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 gtHi) y28 y29 (Z_to_bv 64 med) (Z_to_bv 64 unHi))
                       F (Z_to_bv 64 0x9bc08) fc None m2 (seg_rom a0segs))).
    { intros m2 y6 y12 y13 y14 y16 y28 y29 AR1' MI2 MU2 WM2 FMR1 FMOK1 SC2 SHI2 SLO2.
      pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
      (* [comment removed for export] *)
      wstep. wstep.
      assert (T2b : evt a0segs Q (MS (QF (Z_to_bv 64 ltLo) cT0 y6 (Z_to_bv 64 unLo) cA0 cA1 y12 y13 y14 lo (Z_to_bv 64 (gtHi - unHi)) cA7 (Z_to_bv 64 1) hi (Z_to_bv 64 gtHi) y28 (Z_to_bv 64 mm) (Z_to_bv 64 med) (Z_to_bv 64 unHi))
                         F (Z_to_bv 64 0x9bc18) fc None m2 (seg_rom a0segs))).
      2:{ wstep; if_cases Km; zify_cond_z Km.
          - enter_with T2b; st_eq.
          - wstep. enter_with T2b; st_eq. }
      (* [comment removed for export] *)
      wstep; if_cases Kz; zify_cond_z Kz.
      - (* [comment removed for export] *)
        assert (Efm2 : fm2 = fm1) by (subst fm2; apply fvswap_le0; lia).
        eapply (T3 m2); rewrite ?Efm2; [exact AR1'| exact MI2| exact MU2| exact WM2| exact FMR1| exact FMOK1| exact SC2| exact SHI2| exact SLO2].
      - (* [comment removed for export] *)
        arun_to 0x9bc40%Z.
        enter_with (A0_vsw2 (Z.to_nat mm) unLo (hi - mm + 1)%Z fm1 lo hi m2 m2); [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1'| exact MI2| apply munch_refl| apply wmono_refl| |].
        { eapply shzW_sub; [exact SH1| exact MU2| sub_fp_solve| lia| lia]. }
        intros m3 z6 z12 z13 z14 z28 z29 z30. cbv zeta. intros AR1'' MI3 MU3 WM3 FMR2 FMOK2. clear AR1' MI2.
        transport_after_call a0segs m2 m3 MU3 WM3.
        assert (Efm2 : fm2 = fvswap (Z.to_nat mm) fm1 unLo (hi - mm + 1) (Z.of_nat (Z.to_nat mm))).
        { subst fm2. replace (fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) mm) with (fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) (Z.of_nat (Z.to_nat mm))) by (f_equal; lia). apply fvswap_fuel. }
        rewrite <- Efm2 in AR1'', FMR2, FMOK2.
        enter_with (T3 m3 _ _ _ _ _ _ _); [st_eq| exact AR1''| exact MI3| exact MU2| exact WM2| exact FMR2| exact FMOK2| exact SC2| exact SHI2| exact SLO2]. }
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz.
    - (* [comment removed for export] *)
      assert (Efm1 : fm1 = fm) by (subst fm1; apply fvswap_le0; lia).
      eapply (T2 m); rewrite ?Efm1; [exact AR1| exact MI| exact MU| exact WMo| exact FMR| exact FMOK'| exact SC| exact SHIc| exact SLOc].
    - (* [comment removed for export] *)
      arun_to 0x9bb9c%Z.
      enter_with (A0_vsw1 (Z.to_nat n) lo (unLo - n)%Z fm lo hi m m); [st_eq| lia| lia| lia| lia| lia| exact FMR| exact FMOK'| exact AR1| exact MI| apply munch_refl| apply wmono_refl| |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      intros m2 z6 z12 z13 z14 z16 z28 z29. cbv zeta. intros AR1' MI2 MU2 WM2 FMR1 FMOK1. clear AR1 MI.
      transport_after_call a0segs m m2 MU2 WM2.
      assert (Efm1 : fm1 = fvswap (Z.to_nat n) fm lo (unLo - n) (Z.of_nat (Z.to_nat n))).
      { subst fm1. replace (fvswap (S (Z.to_nat n)) fm lo (unLo - n) n) with (fvswap (S (Z.to_nat n)) fm lo (unLo - n) (Z.of_nat (Z.to_nat n))) by (f_equal; lia). apply fvswap_fuel. }
      rewrite <- Efm1 in AR1', FMR1, FMOK1.
      enter_with (T2 m2 _ _ _ _ _ _ _); [st_eq| exact AR1'| exact MI2| exact MU| exact WMo| exact FMR1| exact FMOK1| exact SC| exact SHIc| exact SLOc].
  Qed.
End A0FS.

End ACeilS1.
