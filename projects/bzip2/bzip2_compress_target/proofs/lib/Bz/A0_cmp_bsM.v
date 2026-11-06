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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_msS A0_cmp_msC A0_cmp_bsS A0_cmp_msO.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma rw_cells_cut11 : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cCM := (Z_to_bv 64 18446744073707454463).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation RO := (am_RO Y). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation WB := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P + 40, P + 104); (P + 184, P + 192); (P + 216, P + 384);
                  (P + 436, P + 440); (P - 16, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400);
                  (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024); (SHF + 4, SHF + 170)]%Z.
  (* [comment removed for export] *)
  Notation WMN := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P + 16, P + 104); (P + 152, P + 200); (P + 216, P + 384);
                   (P + 436, P + 440); (P - 16, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400); (RO, RO + 1024);
                   (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024); (SHF + 4, SHF + 170)]%Z.
  Notation WT0 := [(RO, RO + 1024); (P + 16, P + 104); (P + 152, P + 200)]%Z.

  (* [comment removed for export] *)
  Definition bsviews (me : word -> option byte) : Prop :=
    (frdW a0segs WMN me (P + 384) (scc_cells X) /\ frdW a0segs WMN me (P + 200) [C8 (Z_to_bv 64 (SHF + 506))] /\ acoW WMN me) /\
    (shzW a0segs WMN me A1 (A1 + ARR1_SIZE) /\ shzW a0segs WMN me A2 (A2 + ARR2_SIZE) /\
     shzW a0segs WMN me FT (FT + 262144) /\ shpW a0segs WMN me FT (FT + 262148) /\
     shpW a0segs WMN me (P + 436) (P + 440) /\ shzW a0segs WMN me 139040 139096) /\
    (shzW a0segs WMN me RO (RO + 1024) /\ shzW a0segs WMN me BD (BD + 256) /\
     shzW a0segs WMN me CS (CS + 1024) /\ shzW a0segs WMN me CE (CE + 1024)).

  Ltac shc3_move H MU WM H' := pose proof (shc3_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac open_all :=
    msenv_open XOK; amenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold msenv_sep, apartm in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F & _);
    pose proof (amsx_1_SLO X Y YSX) as AS1l; pose proof (amsx_1_SHI X Y YSX) as AS1h; pose proof (amsx_1_SD X Y YSX) as AS1d;
    pose proof (amsx_1_RO X Y YSX) as AS1r; pose proof (amsx_1_BD X Y YSX) as AS1b; pose proof (amsx_1_CS X Y YSX) as AS1c; pose proof (amsx_1_CE X Y YSX) as AS1e;
    pose proof (amsx_2_SLO X Y YSX) as AS2l; pose proof (amsx_2_SHI X Y YSX) as AS2h; pose proof (amsx_2_SD X Y YSX) as AS2d;
    pose proof (amsx_2_RO X Y YSX) as AS2r; pose proof (amsx_2_BD X Y YSX) as AS2b; pose proof (amsx_2_CS X Y YSX) as AS2c; pose proof (amsx_2_CE X Y YSX) as AS2e;
    pose proof (amsx_F_SLO X Y YSX) as ASFl; pose proof (amsx_F_SHI X Y YSX) as ASFh; pose proof (amsx_F_SD X Y YSX) as ASFd;
    pose proof (amsx_F_RO X Y YSX) as ASFr; pose proof (amsx_F_BD X Y YSX) as ASFb; pose proof (amsx_F_CS X Y YSX) as ASFc; pose proof (amsx_F_CE X Y YSX) as ASFe;
    amenv_shx_open X Y SHF YSHX.

  Lemma A0_bs_main : forall (b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd : zarr) (jro Jlo Jhi Jd : list byte)
      (v24 v32 w40 w48 w56 v64 w72 w80 w88 w96 v152 w184 v192 : word) (sq : scq)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let ro6 := ms_shell 8 (snd (ms_ro_init 256 znew znew 0)) ft 364 in
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    (forall v, 0 <= v < 256 -> 0 <= zget ft (v * 256) <= zget ft ((v + 1) * 256) /\ zget ft ((v + 1) * 256) <= n)%Z ->
    (0 <= b < 2147483648)%Z ->
    (forall k, 0 + Z.of_nat k <= 255 -> let s' := ms_bigs k ro6 qo n 0 s in s_exit s' = false -> bigF qo n ro6 (0 + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length jro) = 1024%Z -> Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) ->
    u8arr a0segs m BD (zb8 bd 256) -> u32arr a0segs m CS (zw32 cs 256) -> u32arr a0segs m CE (zw32 ce 256) ->
    u32arr a0segs m SLO (ovw sl Jlo 100) -> u32arr a0segs m SHI (ovw sh Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    u32arr a0segs m RO (ovw znew jro 256) ->
    rw_cells a0segs m (P + 16) [C8 (Z_to_bv 64 (n - 1)); C8 v24; C8 v32; C8 w40; C8 w48; C8 w56; C8 v64; C8 w72; C8 w80; C8 w88; C8 w96] ->
    rw_cells a0segs m (P + 152) [C8 v152; C8 (Z_to_bv 64 CE); C8 (Z_to_bv 64 CS); C8 (Z_to_bv 64 SHF); C8 w184; C8 v192] ->
    rw_cells a0segs m (P + 216) (scq_cells Y sq) ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P ->
    id (rw_cells a0segs m (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m ->
    munch WMN me m -> wmono a0segs me m -> bsviews me ->
    (* [comment removed for export] *)
    (forall (ex : bool) m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_bigs 256 ro6 qo n 0 s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') ex ->
      (if ex then -2147483648 < b' < 0 else 0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> rook ro6 ->
      mlmem X Y SHF Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro6 b' m' ->
      rw_cells a0segs m' (P + 16) (sc0_cells X) -> rw_cells a0segs m' (P + 152) (sck_cells X Y SHF) -> rw_cells a0segs m' (P + 192) [C8 cCM] ->
      munch WMN me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x9a26c) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 x22 (Z_to_bv 64 FT) x24 x25 x26 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x984d4) fc None m (seg_rom a0segs)).
  Proof.
    intros b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd jro Jlo Jhi Jd v24 v32 w40 w48 w56 v64 w72 w80 w88 w96 v152 w184 v192 sq
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 me m.
    intros ro6 s MONO Hb BF A1OK A2OK BDOK PR Ljro LJlo LJhi LJd AR1 AR2 FTB BDB CSB CEB SLOB SHIB SDB ROB SL0 SK0 SCQ BUD STK SHC MI MU WM BV K. subst s.
    open_all.
    destruct BV as ((VCC & V200 & ACW) & (SH1 & SH2 & SHFz & SHFp & SHBU & SHIN) & (SHRO & SHBD & SHCS & SHCE)).
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft. pose proof (ovw_length znew jro 256 ltac:(lia)) as Lro.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m0 := mm) in * end.
    enter_with (A0_bs_shell X Y Q XOK YOK YSX ft jro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 m0);
      [st_eq| exact MONO| exact Ljro| exact ROB| exact FTB| exact MI| apply munch_refl| apply wmono_refl
      | eapply (frdW_sub a0segs); [eapply (frdW_cell_at a0segs _ me (P + 384) (scc_cells X) 24 _ (P + 408)%Z); [exact VCC| reflexivity| lia]| exact MU| sub_fp_solve]
      | eapply (shzW_sub a0segs); [exact SHRO| exact MU| sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs); [exact SHFz| exact MU| sub_fp_solve| lia| lia]
      | eapply (shpW_sub a0segs); [exact SHFp| exact MU| sub_fp_solve| lia| lia]|].
    intros m5 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z28 z29 z30 z31. cbv zeta. intros RK6 RO6 FTB5 MI5 MU5 WM5. fold ro6 in RK6, RO6.
    clear ROB FTB MI. shc3_move SHC MU5 WM5 SHC5. clear SHC. transport_after_call a0segs m0 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    pose proof (munch_refl WT0 m5) as MUp. pose proof (wmono_refl a0segs m5) as WMp.
    wstep. wstep. lit_store. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. lit_store. wstep. wstep. lit_store.
    shc3_move SHC5 MUp WMp SHC6. clear SHC5 MUp WMp.
    (* [comment removed for export] *)
    replace (A1 + -4)%Z with (A1 - 4)%Z in SL0 by lia.
    destruct (rw_cells_cut11 a0segs _ _ _ 3 SL0) as [C0 SCL]. cbn [firstn skipn cells_size csize Nat.add] in C0, SCL.
    change (Z.of_nat 24) with 24%Z in SCL. replace (P + 16 + 24)%Z with (P + 40)%Z in SCL by lia. clear SL0.
    destruct (rw_cells_cut11 a0segs _ _ _ 4 SK0) as [CK SK1]. cbn [firstn skipn cells_size csize Nat.add] in CK, SK1.
    change (Z.of_nat 32) with 32%Z in SK1. replace (P + 152 + 32)%Z with (P + 184)%Z in SK1 by lia. clear SK0.
    destruct (rw_cells_cut11 a0segs _ _ _ 1 SK1) as [HIC CM]. cbn [firstn skipn cells_size csize Nat.add] in HIC, CM.
    change (Z.of_nat 8) with 8%Z in CM. replace (P + 184 + 8)%Z with (P + 192)%Z in CM by lia. clear SK1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (ml := mm) in * end.
    assert (MV : mviews X Y SHF WB ml).
    { split; [| split].
      - split; [eapply (frdW_sub a0segs); [exact VCC| exact MU| sub_fp_solve]|].
        split; [apply (frdW_intro a0segs _ ml _ _ CK); cbn [disjoint_from sck_cells cells_size csize length Nat.add]; lia|].
        split; [apply (frdW_intro a0segs _ ml _ _ C0); cbn [disjoint_from sc0_cells cells_size csize length Nat.add]; lia|].
        split; [apply (frdW_intro a0segs _ ml _ _ CM); cbn [disjoint_from cells_size csize length Nat.add]; lia|].
        eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve].
      - split; [eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub a0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub a0segs); [exact SHFz| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shpW_sub a0segs); [exact SHFp| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shpW_sub a0segs); [exact SHBU| exact MU| sub_fp_solve| lia| lia]|].
        eapply (shzW_sub a0segs); [exact SHIN| exact MU| sub_fp_solve| lia| lia].
      - split; [eapply (shzW_sub a0segs); [exact SHRO| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub a0segs); [exact SHBD| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub a0segs); [exact SHCS| exact MU| sub_fp_solve| lia| lia]|].
        eapply (shzW_sub a0segs); [exact SHCE| exact MU| sub_fp_solve| lia| lia]. }
    assert (ML : mlmem X Y SHF Jlo Jhi Jd a1 a2 ft bd cs ce sl sh sd ro6 b ml).
    { split; [exact AR1| split; [exact AR2| split; [exact FTB5| split; [exact BDB| split; [exact CSB| split; [exact CEB| split; [exact SLOB| split; [exact SHIB|
      split; [exact SDB| split; [exact RO6| split; [| split; [exact BUD| split; [exact STK| split; [exact SHC6| exact MI5]]]]]]]]]]]]]].
      exists (mkSCL w40 w48 w56 (Z_to_bv 64 0) w80 w88 w96), w184, sq. split; [exact SCL| split; [exact HIC| exact SCQ]]. }
    (* [comment removed for export] *)
    assert (TAIL : forall (ex : bool) m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_bigs 256 ro6 qo n 0 (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') ex ->
      (if ex then -2147483648 < b' < 0 else 0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) ->
      mlmem X Y SHF Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro6 b' m' -> munch WB ml m' -> wmono a0segs ml m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))).
    { intros ex m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      clear ML AR1 AR2 FTB5 BDB CSB CEB SLOB SHIB SDB RO6 SCL HIC SCQ BUD STK SHC6 MI5.
      transport_after_call a0segs ml m' MU' WM'.
      (* [comment removed for export] *)
      wstep. pose proof (V200 _ MU) as RO_. wstep. clear RO_. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K ex mm a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| exact Hb'| exact OK1| exact OK2| exact OKb| exact PR'| exact RK6| exact ML'| exact C0| exact CK| exact CM| exact MU| exact WM]. }
    enter_with (A0_bigs X Y SHF Q XOK XSEP YOK YSX YSF YOFF YSHX 256 0 b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro6 Jlo Jhi Jd
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ml ml);
      [st_eq| reflexivity| lia| lia| exact BF| exact A1OK| exact A2OK| exact BDOK| exact PR| exact LJlo| exact LJhi| exact LJd| exact ML| apply munch_refl| apply wmono_refl| exact MV| |].
    - intros m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      eapply (TAIL false m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'); [exact EQ| exact Hb'| exact OK1| exact OK2| exact OKb| exact PR'| exact ML'| exact MU'| exact WM'].
    - intros m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK1 OK2 OKb PR' ML' MU' WM'.
      eapply (TAIL true m' a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' b' nqs'); [exact EQ| exact Hb'| exact OK1| exact OK2| exact OKb| exact PR'| exact ML'| exact MU'| exact WM'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
