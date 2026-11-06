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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsS B0_cmp_msV B0_cmp_msW B0_cmp_msS B0_cmp_msC B0_cmp_bsS B0_cmp_msO B0_cmp_msX B0_cmp_bsR B0_cmp_fsW BzCLemmasMs5 BzCFactsBs BzCLemmasMs6.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2].
(* [comment removed for export] *)

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cCM := (Z_to_bv 64 18446744073707454463).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation RO := (am_RO Y). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation NBD := (18446744073709551615 - am_BD Y)%Z.
  (* [comment removed for export] *)
  Notation WB := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400);
                  (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024); (SHF + 4, SHF + 170)]%Z.
  Notation WBODY := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400);
                     (RO, RO + 1024); (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024); (SHF + 4, SHF + 170)]%Z.
  Notation WPRE := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P, P + 536); (RO, RO + 1024); (BD, BD + 256)]%Z.
  (* [comment removed for export] *)
  Ltac sub_shz SH MU := eapply (shzW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac shc3_move H MU WM H' := pose proof (shc3_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac wsl := wstep; lit_store.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  Ltac mlmem_i AR1 AR2 FTB BDB CSB CEB SLOB SHIB SDB ROB SLB NX BUD STK SHC MI IB :=
    split; [exact AR1| split; [exact AR2| split; [exact FTB| split; [exact BDB| split; [exact CSB| split; [exact CEB| split; [exact SLOB| split; [exact SHIB|
    split; [exact SDB| split; [exact ROB| split; [do 2 eexists; split; [exact SLB| exact NX]| split; [exact BUD| split; [exact STK|
    split; [exact SHC| split; [exact MI| exact IB]]]]]]]]]]]]]]].
  Ltac open_all :=
    msenv_open XOK; amenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold msenv_sep, apartm in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F & _);
    pose proof (amsx_1_SLO X Y YSX) as AS1l; pose proof (amsx_1_SHI X Y YSX) as AS1h; pose proof (amsx_1_SD X Y YSX) as AS1d;
    pose proof (amsx_1_RO X Y YSX) as AS1r; pose proof (amsx_1_BD X Y YSX) as AS1b; pose proof (amsx_1_CS X Y YSX) as AS1c; pose proof (amsx_1_CE X Y YSX) as AS1e;
    pose proof (amsx_2_SLO X Y YSX) as AS2l; pose proof (amsx_2_SHI X Y YSX) as AS2h; pose proof (amsx_2_SD X Y YSX) as AS2d;
    pose proof (amsx_2_RO X Y YSX) as AS2r; pose proof (amsx_2_BD X Y YSX) as AS2b; pose proof (amsx_2_CS X Y YSX) as AS2c; pose proof (amsx_2_CE X Y YSX) as AS2e;
    pose proof (amsx_F_SLO X Y YSX) as ASFl; pose proof (amsx_F_SHI X Y YSX) as ASFh; pose proof (amsx_F_SD X Y YSX) as ASFd;
    pose proof (amsx_F_RO X Y YSX) as ASFr; pose proof (amsx_F_BD X Y YSX) as ASFb; pose proof (amsx_F_CS X Y YSX) as ASFc; pose proof (amsx_F_CE X Y YSX) as ASFe;
    amenv_shx_open X Y SHF YSHX;
    let H := fresh "YSFo" in pose proof YSF as H; destruct H as (?AX & ?SFL & ?SFH); unfold SH_LO, SH_HI in SFL, SFH.

  Lemma B0_bs_body : forall (q r : nat) (a1 a2 ft cs ce sl sh sd nl nh nd : zarr) (jro jbd Jlo Jhi Jd : list byte) (nx : nxt)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w408 w416 w424 w440 w472 w480 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let ft0 := ms_ftab_zero 65537 ft 65536 in
    let j0 := Z.shiftl (rd8 a2 0) 8 in
    let r1 := ms_radix1 (Z.to_nat n) a2 ft0 qo (n - 1) j0 in let a2r := fst (fst r1) in let ft1 := snd (fst r1) in
    let a2o := ms_overshoot 34 a2r qo n 0 in let ft3 := ms_accum 65536 ft1 1 in let s0' := Z.shiftl (rd8 a2o 0) 8 in
    (Z.of_nat q = n / 4)%Z -> (Z.of_nat r = n mod 4)%Z ->
    zbok a1 -> zbok a2 -> (forall v, 0 <= zget ft v < 4294967296)%Z -> (forall v, 0 <= v <= 65536 -> zget ft0 v = 0)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft3 v <= n)%Z -> r2ok n (Z.to_nat n) a1 a2o ft3 (n - 1) s0' ->
    (0 <= n * budget_q < 2147483648)%Z ->
    (* [comment removed for export] *)
    (forall (a2b ftb a1c ftc : zarr) (jb sc : Z),
      ms_radix1 (Z.to_nat n) a2 ft0 qo (n - 1) j0 = (a2b, ftb, jb) ->
      let a2o' := ms_overshoot 34 a2b qo n 0 in
      ms_radix2 (Z.to_nat n) a1 a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc) ->
      let ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364 in
      let s := MSS a1c a2o' ftc bp_bd5 cs ce (n * budget_q) 0 (MQL sl sh sd nl nh nd) false in
      (forall v, 0 <= v < 256 -> 0 <= zget ftc (v * 256) <= zget ftc ((v + 1) * 256) /\ zget ftc ((v + 1) * 256) <= n)%Z /\
      (forall k, 0 + Z.of_nat k <= 255 -> let s' := ms_bigs k ro6 qo n 0 s in s_exit s' = false -> bigF qo n ro6 (0 + Z.of_nat k) s')%Z /\
      (forall k, 0 + Z.of_nat k <= 255 -> let s' := ms_bigs k ro6 qo n 0 s in s_exit s' = false -> bigN qo n ro6 (0 + Z.of_nat k) s')%Z /\
      pr n a1c 0 (n - 1)) ->
    Z.of_nat (length jro) = 1024%Z -> Z.of_nat (length jbd) = 256%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m FT (zw32 ft 65537) ->
    u8arr b0segs m BD (ovb znew jbd 256) -> u32arr b0segs m CS (zw32 cs 256) -> u32arr b0segs m CE (zw32 ce 256) ->
    u32arr b0segs m SLO (ovw sl Jlo 100) -> u32arr b0segs m SHI (ovw sh Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    u32arr b0segs m RO (ovw znew jro 256) ->
    rw_cells b0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 (Z_to_bv 64 0); C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 (Z_to_bv 64 SHF); C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 (Z_to_bv 64 n); C8 w408; C8 w416; C8 w424; C8 (Z_to_bv 64 FT); C8 w440; C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 A1); C8 w472; C8 w480; C8 (Z_to_bv 64 FB)] ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 (n * budget_q))] -> rw_cells b0segs m (P + 500) (nxt_cells nx) -> stk b0segs m (me_lo X) P ->
    id (rw_cells b0segs m (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m -> b0_incs m ->
    munch WBODY me m -> wmono b0segs me m -> mviews X Y WBODY me ->
    (* [comment removed for export] *)
    (forall (ex : bool) m' (a2b ftb a1c ftc : zarr) (jb sc : Z) (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_radix1 (Z.to_nat n) a2 ft0 qo (n - 1) j0 = (a2b, ftb, jb) ->
      let a2o' := ms_overshoot 34 a2b qo n 0 in
      ms_radix2 (Z.to_nat n) a1 a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc) ->
      let ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364 in
      ms_bigs 256 ro6 qo n 0 (MSS a1c a2o' ftc bp_bd5 cs ce (n * budget_q) 0 (MQL sl sh sd nl nh nd) false)
        = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') ex ->
      (if ex then -2147483648 < b' < 0 else 0 <= b' <= n * budget_q)%Z ->
      zbok a1c -> zbok a2o' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z -> (forall k, 0 <= k < n -> zget a2o' k = zget a2 k)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> rook ro6 ->
      mlmem X Y SHF SHn Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro6 b' m' ->
      munch WBODY me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 0xa4450) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) y12 y13 y14 y15 y16 y17
                            y18 y19 y20 y21 y22 y23 y24 y25 y26 cSB y28 y29 y30 y31)
                       F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (E + 108)) (Z_to_bv 64 FB) (Z_to_bv 64 SHn) (Z_to_bv 64 FB) (Z_to_bv 64 (n * budget_q)) (Z_to_bv 64 E)
                          (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 (SHF + 506)) cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa1140) fc None m (seg_rom b0segs)).
  Proof.
    intros q r a1 a2 ft cs ce sl sh sd nl nh nd jro jbd Jlo Jhi Jd nx w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w408 w416 w424 w440 w472 w480
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 me m.
    intros ft0 j0 r1 a2r ft1 a2o ft3 s0' Hq Hr A1OK A2OK FTNN FT0 FACC FR2 Hb FACTS Ljro Ljbd LJlo LJhi LJd
           AR1 AR2 FTB BDB CSB CEB SLOB SHIB SDB ROB SLB BUD NX STK SHC MI IB MU WM MV K.
    open_all. mviews_open MV. unfold b0_incs, B0_INCS in IB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    pose proof (munch_refl WPRE m) as MUp. pose proof (wmono_refl b0segs m) as WMp.
    (* [comment removed for export] *)
    brun_to 0xa11c0%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (frdW_intro b0segs [(FT, FT + 262148)]%Z mm _ _ SLB ltac:(cbn [disjoint_from cells_size csize length Nat.add]; lia)) as VSL;
      pose proof (frdW_cell_at b0segs _ mm _ _ 432 _ (P + 432)%Z VSL eq_refl ltac:(reflexivity)) as V432;
      enter_with (B0_ftab_zero X Y Q XOK YOK 65537%nat 65536%Z ft _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| vm_compute; reflexivity| lia| exact FTNN| exact FTB| exact MI| apply munch_refl| apply wmono_refl| exact V432| sub_shp SHFp MU|].
    intros m3 y10 y14 y15. cbv zeta. intros FTW0 FTB0 MI3 MU3 WM3.
    clear FTB MI VSL V432.
    lazymatch type of MU3 with munch _ ?ma _ => transport_after_call b0segs ma m3 MU3 WM3 end. clear MU3 WM3.
    (* [comment removed for export] *)
    brun_to 0xa1250%Z.
    pose proof (saddr_intro A2) as ASH2. set (SHX2 := (A2 / 8 + 2147450880)%Z) in *. clearbody SHX2.
    (* [comment removed for export] *)
    brun_to 0xa1264%Z. rdblk AR2 A2OK 0%Z.
    (* [comment removed for export] *)
    brun_to 0xa1280%Z.
    (* [comment removed for export] *)
    replace (n + -1)%Z with (n - 1)%Z in SLB by lia.
    replace (FB + 4048)%Z with CE in SLB by lia. replace (FB + 2896)%Z with CS in SLB by lia. replace (FB + 2576)%Z with BD in SLB by lia.
    replace (FB + 960)%Z with SD in SLB by lia. replace (FB + 496)%Z with SHI in SLB by lia. replace (FB + 32)%Z with SLO in SLB by lia.
    replace (FB + 1424)%Z with RO in SLB by lia.
    set (sv0 := mkSLV w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w216 w224 w232 w240 w248 w256 w264 w272
                      w312 w328 w336 w344 w352 w360 w368 w376 w384 w392 w408 w416 w440 w480).
    lazymatch type of SLB with rw_cells _ ?mm _ _ => assert (SLB0 : rw_cells b0segs mm P (slb_cells X Y SHF SHn sv0)) by exact SLB end. clear SLB.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_radix X Y SHF SHn sv0 Q XOK XSEP YOK SHX2 ASH2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r a1 a2 ft0 _ _ _ _ _ _ mm mm) end;
      [st_eq| exact Hq| exact Hr| exact A1OK| exact A2OK| exact FT0| exact FTW0| exact FACC| exact FR2| exact AR1| exact AR2| exact FTB0| exact SLB0| exact MI3
      | apply munch_refl| apply wmono_refl| sub_shz SH1 MU| sub_shz SH2 MU| sub_shz SHFz MU| sub_shp SHFp MU|].
    intros m5 a2b ftb a1c ftc jb sc y5 y6 z10 z11 z12 z13 z14 z15 z16 z17 Er. cbv zeta. intros Eqn OK1c OKo FTCc LOWo AR1c AR2o FTBc SLBc MI5 MU5 WM5.
    clear AR1 AR2 FTB0 SLB0 MI3.
    lazymatch type of MU5 with munch _ ?ma _ => transport_after_call b0segs ma m5 MU5 WM5 end. clear MU5 WM5.
    destruct (FACTS a2b ftb a1c ftc jb sc Er Eqn) as (MONO & BF & BN & PRc). clear FACTS.
    set (a2o' := ms_overshoot 34 a2b qo n 0) in *.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_shell X Y SHF SHn sv0 Q XOK YOK YSX ftc jro jbd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| exact MONO| exact Ljro| exact Ljbd| exact ROB| exact BDB| exact FTBc| exact SLBc| exact MI5| apply munch_refl| apply wmono_refl
      | sub_shz SHRO MU| sub_shz SHFz MU| sub_shp SHFp MU|].
    intros m6. cbv zeta. intros RK6 RO6 BD6 FTB6 SLB6 MI6 MU6 WM6.
    set (ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ftc 364) in *.
    clear ROB BDB FTBc SLBc MI5.
    lazymatch type of MU6 with munch _ ?ma _ => transport_after_call b0segs ma m6 MU6 WM6 end. clear MU6 WM6.
    unfold bmfree_at. intros z1 z5 z6 z7 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u28 u29 u30 u31.
    (* [comment removed for export] *)
    open_slb_in SLB6. subst sv0. cbn [v80 v88 v96 v104 v112 v120 v128 v144 v152 v160 v168 v176 v184 v216 v224 v232 v240 v248 v256 v264 v272 v312 v328 v336 v344 v352 v360 v368 v376 v384 v392 v408 v416 v440 v480] in SLB6.
    (* [comment removed for export] *)
    brun_to 0xa205c%Z.
    replace (Z.land A1 3) with 0%Z by (rewrite AL1; change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2)%Z with 4%Z; clear; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wsl. brun_to 0xa20a8%Z.
    (* [comment removed for export] *)
    wsl. brun_to 0xa20bc%Z. wsl. wstep. wstep. wsl. wsl.
    replace (Z_to_bv 64 (-2097153)) with cCM by (apply Z_to_bv_eqm; reflexivity).
    (* [comment removed for export] *)
    set (sq0 := mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (ml := mm) in * end.
    assert (SLM : rw_cells b0segs ml P (slm_cells X Y SHF SHn sq0)) by exact SLB6. clear SLB6.
    shc3_move SHC MUp WMp SHC6. clear SHC MUp WMp.
    assert (ML : mlmem X Y SHF SHn Jlo Jhi Jd a1c a2o' ftc bp_bd5 cs ce sl sh sd ro6 (n * budget_q) ml).
    { mlmem_i AR1c AR2o FTB6 BD6 CSB CEB SLOB SHIB SDB RO6 SLM NX BUD STK SHC6 MI6 IB. }
    assert (MVB : mviews X Y WB ml) by (eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]).
    (* [comment removed for export] *)
    assert (TAIL : forall (ex : bool) m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z),
      ms_bigs 256 ro6 qo n 0 (MSS a1c a2o' ftc bp_bd5 cs ce (n * budget_q) 0 (MQL sl sh sd nl nh nd) false) = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') ex ->
      (if ex then -2147483648 < b' < 0 else 0 <= b' <= n * budget_q)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) ->
      mlmem X Y SHF SHn Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro6 b' m' -> munch WB ml m' -> wmono b0segs ml m' ->
      bmfree_at X Y Q 0xa4444 m').
    { intros ex m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      unfold bmfree_at. intros t1 t5 t6 t7 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t28 t29 t30 t31.
      clear ML AR1c AR2o FTB6 BD6 CSB CEB SLOB SHIB SDB RO6 SLM NX BUD STK SHC6 MI6 IB.
      transport_after_call b0segs ml m' MU' WM'.
      pose proof ML' as MLc. destruct MLc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (sq' & nx' & SLB' & _) & _). open_slb_in SLB'.
      wstep. wstep. wstep. clear SLB'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K ex mm a2b ftb a1c ftc jb sc a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact Er| exact Eqn| exact EQ| exact Hb'| exact OK1c| exact OKo| exact FTCc| exact LOWo| exact OK1| exact OK2| exact OKb| exact PR'| exact RK6
        | exact ML'| exact MU| exact WM]. }
    enter_with (B0_bigs X Y SHF SHn Q XOK XSEP YOK YSX YSF YOFF YSHX 256 0 (n * budget_q) 0 a1c a2o' ftc bp_bd5 cs ce sl sh sd nl nh nd ro6 Jlo Jhi Jd
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ml ml);
      [st_eq| reflexivity| lia| exact Hb| exact BF| exact BN| exact OK1c| exact OKo| exact bd5_zbok| exact PRc| exact LJlo| exact LJhi| exact LJd| exact ML
      | apply munch_refl| apply wmono_refl| exact MVB| |].
    - intros m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      eapply (TAIL false m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'); [exact EQ| exact Hb'| exact OK1| exact OK2| exact OKb| exact PR'| exact ML'| exact MU'| exact WM'].
    - intros m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      eapply (TAIL true m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'); [exact EQ| exact Hb'| exact OK1| exact OK2| exact OKb| exact PR'| exact ML'| exact MU'| exact WM'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
