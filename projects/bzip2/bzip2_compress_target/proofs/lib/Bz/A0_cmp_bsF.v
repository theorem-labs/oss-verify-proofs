(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msW A0_cmp_bsV.
Strategy 1000 [find_orig].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSEP : amenv_sep X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WE5 := [(E + 48, E + 52); (FB, FB + 8)]%Z.

  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  Lemma A0_forig : forall (cnt : nat) (i : Z) (a1f : zarr)
      (x1 x5 x6 x7 x10 x12 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    Z.of_nat cnt = (n - i)%Z -> (0 <= i < n)%Z -> zbok a1f ->
    (exists k, i <= k < n /\ rd32 a1f k = 0)%Z ->
    u8arr a0segs m A1 (zb8 a1f ARR1_SIZE) -> munch WE5 me m -> shzW a0segs WE5 me A1 (A1 + ARR1_SIZE) ->
    (forall (k : Z) (y15 : word), (i <= k < n)%Z -> rd32 a1f k = 0%Z -> find_orig (Z.to_nat (n - i)) a1f i = k ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            x10 (Z_to_bv 64 (A1 + 4 * k)) x12 (Z_to_bv 64 k) (Z_to_bv 64 (n - k)) y15 x16 (Z_to_bv 64 (A1 + 4 * k))
                            x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x9a3f8) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 (A1 + 4 * i)) x12 (Z_to_bv 64 i) (Z_to_bv 64 (n - i)) x15 x16 (Z_to_bv 64 (A1 + 4 * i))
                          x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9a3b4) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros i a1f x1 x5 x6 x7 x10 x12 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m Hcnt Hi OK1 EX AR1 MU SH1 K.
    msenv_open1 XOK. pose proof (zb8_length a1f ARR1_SIZE ltac:(lia)) as L1. pose proof (zbok_rd32 a1f i OK1) as Bw.
    replace (Z.to_nat (n - i)) with (S (Z.to_nat (n - (i + 1)))) in K by lia. cbn [find_orig] in K.
    (* [comment removed for export] *)
    arun.
    pose proof (zb8_read4 a0segs m A1 a1f ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) OK1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD.
    wstep; if_cases Kb; zify_cond_z Kb.
    - assert (Z0 : rd32 a1f i = 0%Z) by (first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia]).
      rewrite Z0, Z.eqb_refl in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K i _ ltac:(lia) Z0 eq_refl) end; [st_eq].
    - assert (Zn : rd32 a1f i <> 0%Z) by (first [lia | intros Z0; apply Kb; apply (proj2 (sx32_zero_iff _ Bw)); exact Z0]).
      replace (rd32 a1f i =? 0)%Z with false in K by (symmetry; apply Z.eqb_neq; exact Zn).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (i + 1)%Z a1f x1 x5 x6 x7 x10 x12 _ x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me mm) end;
          [st_eq| lia| lia| exact OK1| | exact AR1| exact MU| exact SH1| ].
        { cps_destruct EX as (k & Hk & Zk). exists k. split; [| exact Zk]. destruct (Z.eq_dec k i); [subst k; exfalso; exact (Zn Zk)| lia]. }
        intros k y15 Hk Zk FO. enter_with (K k y15 ltac:(lia) Zk FO); [st_eq].
      + exfalso. cps_destruct EX as (k & Hk & Zk). destruct (Z.eq_dec k i); [subst k; exact (Zn Zk)| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Lemma A0_bs_E5 : forall (SHn : Z) (a1f : zarr) (vop vmg v384 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    saddr (E + 108) SHn -> zbok a1f -> (exists k, 0 <= k < n /\ rd32 a1f k = 0)%Z ->
    u8arr a0segs m A1 (zb8 a1f ARR1_SIZE) ->
    rw_cells a0segs m (E + 48) [C4 vop] -> rw_cells a0segs m (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells a0segs m FB [C8 vmg] ->
    rw_cells a0segs m (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] -> mem_inv a0segs m ->
    munch WE5 me m -> wmono a0segs me m ->
    shzW a0segs WE5 me E (E + 55768) -> shzW a0segs WE5 me A1 (A1 + ARR1_SIZE) ->
    (forall m' (k : Z) (y5 y6 y7 y12 y13 y14 y15 y16 y17 : word),
      (0 <= k < n)%Z -> rd32 a1f k = 0%Z -> find_orig (Z.to_nat n) a1f 0 = k ->
      u8arr a0segs m' A1 (zb8 a1f ARR1_SIZE) ->
      rw_cells a0segs m' (E + 48) [C4 (Z_to_bv 64 k)] -> rw_cells a0segs m' (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells a0segs m' FB [C8 (Z_to_bv 64 1172321806)] ->
      rw_cells a0segs m' (P + 384) [C8 v384; C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 A1)] -> mem_inv a0segs m' ->
      munch WE5 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x9a444) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 FB) (Z_to_bv 64 5216) y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 (E + 108)) cSB x20 (Z_to_bv 64 FB) x22 x23 (Z_to_bv 64 FB) (Z_to_bv 64 E) x26 (Z_to_bv 64 SHn) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x3e5c8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (E + 108)) cSB x20 (Z_to_bv 64 FB) x22 x23 (Z_to_bv 64 FB) (Z_to_bv 64 E) x26 (Z_to_bv 64 SHn) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9a37c) fc None m (seg_rom a0segs)).
  Proof.
    intros SHn a1f vop vmg v384 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 me m
           ASN OK1 EX AR1 OPC NBC MGC SCC MI MU WM SHE SH1 K.
    msenv_open1 XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & APE1 & _).
    pose proof YSEP as SPY. unfold amenv_sep, apartm in SPY. cps_destruct SPY as (APEF & AP1FB & _). box_ors.
    pose proof (zb8_length a1f ARR1_SIZE ltac:(lia)) as L1.
    (* [comment removed for export] *)
    arun_to 0x9a398%Z. wstep. lit_store.
    (* [comment removed for export] *)
    arun_to 0x9a3a8%Z.
    wstep; if_cases Kz; [apply blez_taken in Kz; [exfalso; lia| lia] | clear Kz].
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_forig (Z.to_nat n) 0%Z a1f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| exact OK1| exact EX| exact AR1| exact MU| exact SH1|].
    intros k y15 Hk Zk FO. replace (n - 0)%Z with n in FO by lia.
    (* [comment removed for export] *)
    arun_to 0x9a400%Z. wstep. wstep. wstep. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    wstep; if_cases Ks; zify_cond_z Ks; [exfalso; lia|].
    wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm k _ _ _ _ _ _ _ _ _) end;
      [st_eq| lia| exact Zk| exact FO| exact AR1| exact OPC| exact NBC| exact MGC| exact SCC| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
