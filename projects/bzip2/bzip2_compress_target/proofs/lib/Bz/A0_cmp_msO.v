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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_msS A0_cmp_msL A0_cmp_msM A0_cmp_msN.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation RO := (am_RO Y). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  (* [comment removed for export] *)
  Notation WB := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (P + 40, P + 104); (P + 184, P + 192); (P + 216, P + 384);
                  (P + 436, P + 440); (P - 16, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400);
                  (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024); (SHF + 4, SHF + 170)]%Z.
  Notation WT1 := [(P + 40, P + 104)]%Z.
  Notation W2 := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (BD, BD + 256); (CS, CS + 1024); (CE, CE + 1024)]%Z.

  (* [comment removed for export] *)
  Definition mlmem (Jlo Jhi Jd : list byte) (a1 a2 ft bd cs ce sl sh sd ro : zarr) (b : Z) (m : word -> option byte) : Prop :=
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) /\ u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) /\ u32arr a0segs m FT (zw32 ft 65537) /\
    u8arr a0segs m BD (zb8 bd 256) /\ u32arr a0segs m CS (zw32 cs 256) /\ u32arr a0segs m CE (zw32 ce 256) /\
    u32arr a0segs m SLO (ovw sl Jlo 100) /\ u32arr a0segs m SHI (ovw sh Jhi 100) /\ u32arr a0segs m SD (ovw sd Jd 100) /\
    u32arr a0segs m RO (zw32 ro 256) /\
    (exists (sc : scl) (w184 : word) (sq : scq),
       rw_cells a0segs m (P + 40) (scl_cells X sc) /\ rw_cells a0segs m (P + 184) [C8 w184] /\ rw_cells a0segs m (P + 216) (scq_cells Y sq)) /\
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] /\ stk a0segs m (me_lo X) P /\
    id (rw_cells a0segs m (SHF + 4) (shc3 f8b)) /\ mem_inv a0segs m.

  Ltac mlmem_i AR1 AR2 FTB BDB CSB CEB SLOB SHIB SDB ROB SCL HIC SCQ BUD STK SHC MI :=
    split; [exact AR1| split; [exact AR2| split; [exact FTB| split; [exact BDB| split; [exact CSB| split; [exact CEB| split; [exact SLOB| split; [exact SHIB|
    split; [exact SDB| split; [exact ROB| split; [do 3 eexists; split; [exact SCL| split; [exact HIC| exact SCQ]]| split; [exact BUD| split; [exact STK|
    split; [exact SHC| exact MI]]]]]]]]]]]]]].
  Ltac shc3_move H MU WM H' := pose proof (shc3_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.
  Ltac rdview V MU :=
    let RO := fresh "RO_" in pose proof (V _ MU) as RO; unfold scc_cells, sck_cells, sc0_cells, scl_cells in RO; cbn [l40 l48 l56 l72 l80 l88 l96] in RO; wstep; clear RO.
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

  (* [comment removed for export] *)
  Lemma A0_big : forall (i b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd ro : zarr) (Jlo Jhi Jd : list byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in let ss := zget ro i in
    (0 <= i <= 255)%Z -> (0 <= b < 2147483648)%Z -> bigF qo n ro i s ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    mlmem Jlo Jhi Jd a1 a2 ft bd cs ce sl sh sd ro b m -> munch WB me m -> wmono a0segs me m -> mviews X Y SHF WB me ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y25 y26 y28 y29 y30 y31 : word),
      (i < 255)%Z ->
      ms_big ro qo n i s = MSS a1' a2' ft' (zset bd ss 1) csF ceB b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> pr n a1' 0 (n - 1) ->
      mlmem Jlo Jhi Jd a1' a2' ft' (zset bd ss 1) csF ceB sl' sh' sd' ro b' m' -> munch WB me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 (i + 1)) cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x98730) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      (i = 255)%Z ->
      ms_big ro qo n i s = MSS a1' a2' ft' (zset bd ss 1) csF ceB b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> pr n a1' 0 (n - 1) ->
      mlmem Jlo Jhi Jd a1' a2' ft' (zset bd ss 1) csF ceB sl' sh' sd' ro b' m' -> munch WB me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_big ro qo n i s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      mlmem Jlo Jhi Jd a1' a2 ft' bd cs ce sl' sh' sd' ro b' m' -> munch WB me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 i) cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) x24 x25 x26 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98730) fc None m (seg_rom a0segs)).
  Proof.
    intros i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 me m.
    intros s ss Hi Hb BF A1OK A2OK BDOK PR LJlo LJhi LJd ML MU WM MV Kn Kl Kx. subst s.
    open_all.
    destruct ML as (AR1 & AR2 & FTB & BDB & CSB & CEB & SLOB & SHIB & SDB & ROB & (sc & w184 & sq & SCL & HIC & SCQ) & BUD & STK & SHC & MI).
    destruct sc as [w40 w48 w56 w72 w80 w88 w96]. open_scl_in SCL.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft. pose proof (zw32_length ro 256 ltac:(lia)) as Lro.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    cps_destruct BF as (Hss & F1 & F23). fold ss in Hss, F1, F23.
    pose proof (munch_refl WT1 m) as MUp. pose proof (wmono_refl a0segs m) as WMp.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (zw32_read a0segs m RO ro 256 i _ ROB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. wstep. clear RD. fold ss.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    replace (FT + ss * 256 * 4)%Z with (FT + 1024 * ss)%Z in * by lia. replace (ss * 256)%Z with (256 * ss)%Z in SCL by lia.
    shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mq := mm) in * end.
    enter_with (A0_step1 X Y SHF Q XOK XSEP YOK YSX YSF YOFF YSHX 256 0 ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd
                  w40 w48 w56 w72 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 i) w184 sq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| intros k Hk; apply F1; lia| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd| exact AR1| exact AR2| exact FTB
      | exact SLOB| exact SHIB| exact SDB| exact SCL| exact HIC| exact SCQ| exact BUD| exact STK| exact SHC1| exact MI| apply munch_refl| apply wmono_refl
      | eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]| |].
    - (* [comment removed for export] *)
      intros m1 a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184 sq' y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31.
      intros EQ1 Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SCL HIC SCQ BUD STK SHC1 MI. bz_params.
      transport_after_call a0segs mq m1 MU' WM'. clear MU' WM'.
      cps_destruct (F23 ltac:(rewrite EQ1; reflexivity)) as (BD0 & FTV & FWF & FWfin & BWF & BWfin & A1007 & F3). clear F23.
      rewrite EQ1 in BD0, FTV, FWF, FWfin, BWF, BWfin, A1007, F3. cbn [s_ft s_a1 s_a2 s_bd s_cs s_ce] in BD0, FTV, FWF, FWfin, BWF, BWfin, A1007, F3.
      assert (VSL : frdW a0segs W2 m1 (P + 40) (scl_cells X (mkSCL v40 v48 v56 v72 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 i) (Z_to_bv 64 (FT + 1024 * ss)))))
        by (apply (frdW_intro a0segs _ m1 _ _ SCL'); cbn [disjoint_from scl_cells cells_size csize length Nat.add]; lia).
      assert (VBD : frdW a0segs W2 m1 (P + 280) [C8 (Z_to_bv 64 BD)]).
      { eapply (frdW_cell_at a0segs _ m1 (P + 216) (scq_cells Y sq') 64 _ (P + 280)%Z); [| reflexivity| lia].
        apply (frdW_intro a0segs _ m1 _ _ SCQ'). cbn [disjoint_from scq_cells cells_size csize length Nat.add]. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mr := mm) in * end.
      enter_with (A0_step2 X Y SHF Q XOK XSEP YOK YSX i ss a1' a2 ft' bd cs ce v40 v48 v56 v72 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mr mr);
        [st_eq| lia| lia| exact BD0| exact FTV| exact FWF| exact FWfin| exact BWF| exact BWfin| exact A1007| exact OK'| exact A2OK| exact BDOK| exact PR'
        | exact AR1'| exact AR2'| exact FTB'| exact BDB| exact CSB| exact CEB| exact MI'| apply munch_refl| apply wmono_refl
        | eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]| exact VSL| exact VBD|].
      intros last m2 SH6 SH9 u5 u6 u11 u13 u14 u15 u16 u17. cbv zeta.
      intros Elast AS6 AS9 OKB PRB FTVm CSR CER AR1'' AR2'' FTB'' BD'' CS'' CE'' MI2 MU2 WM2.
      clear AR1' AR2' FTB' BDB CSB CEB MI' VSL VBD. shc3_move SHC' MU2 WM2 SHC2. clear SHC'.
      transport_after_call a0segs mr m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      pose proof (ms_big_eq ro qo n i (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false)) as EB. cbv zeta in EB. fold ss in EB.
      rewrite EQ1 in EB. cbn [s_exit s_ft s_a1 s_a2 s_bd s_cs s_ce s_budget s_nqs s_mql] in EB.
      destruct (ms_copy_init 256 cs ce ft' ss 0) as [cs0 ce0] eqn:Eci. cbn [fst snd] in *.
      destruct (ms_copy_fwd (S (Z.to_nat n)) a1' cs0 a2 bd n ss (clearmask (zget ft' (Z.shiftl ss 8)))) as [[a1F csF] jF] eqn:Erf. cbn [fst snd] in *.
      destruct (ms_copy_bwd (S (Z.to_nat n)) a1F ce0 a2 bd n ss (clearmask (zget ft' (Z.shiftl (ss + 1) 8)) - 1)) as [[a1B ceB] jB] eqn:Erb. cbn [fst snd] in *.
      destruct (Z.eqb_spec i 255) as [E255|N255].
      + (* [comment removed for export] *)
        subst last. replace (i <? 255) with false in EB by (symmetry; apply Z.ltb_ge; lia).
        mviews_open MV. open_scq_in SCQ'.
        wstep. rdview VCK MU. astep. astep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kl mm a1B a2 (ms_mark 256 ft' ss 0) sl' sh' sd' nl' nh' nd' csF ceB b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact EB| lia| exact OKB| exact A2OK| exact PRB| | exact MU| exact WM].
        mlmem_i AR1'' AR2'' FTB'' BD'' CS'' CE'' SLO' SHI' SD' ROB SCL' HIC' SCQ' BUD' STK' SHC2 MI2.
      + subst last. replace (i <? 255) with true in EB by (symmetry; apply Z.ltb_lt; lia). cbv zeta in EB.
        destruct (F3 ltac:(lia)) as [Ble Bn].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mt := mm) in * end.
        enter_with (A0_step3 X Y SHF Q XOK XSEP i ss SH6 SH9 a1B a2 (ms_mark 256 ft' ss 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mt mt);
          [st_eq| lia| lia| exact FTVm| exact Ble| exact Bn| exact AS6| exact AS9| exact OKB| exact A2OK| exact PRB| exact AR1''| exact AR2''| exact FTB''| exact MI2
          | apply munch_refl| apply wmono_refl| eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]|].
        intros m3 z5 z6 z10 z11 z12 z13 z14 z15 z16 z17. cbv zeta. intros OKQ AR1q AR2q FTBq MIq MUq WMq.
        clear AR1'' AR2'' FTB'' MI2. shc3_move SHC2 MUq WMq SHC3. clear SHC2.
        transport_after_call a0segs mt m3 MUq WMq. clear MUq WMq.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kn mm a1B _ (ms_mark 256 ft' ss 0) sl' sh' sd' nl' nh' nd' csF ceB b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact EB| lia| exact OKB| exact OKQ| exact PRB| | exact MU| exact WM].
        mlmem_i AR1q AR2q FTBq BD'' CS'' CE'' SLO' SHI' SD' ROB SCL' HIC' SCQ' BUD' STK' SHC3 MIq.
    - (* [comment removed for export] *)
      intros m1 a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184 sq' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EQ1 Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SCL HIC SCQ BUD STK SHC1 MI. bz_params.
      transport_after_call a0segs mq m1 MU' WM'. clear MU' WM'.
      pose proof (ms_big_eq ro qo n i (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false)) as EB. cbv zeta in EB. fold ss in EB.
      rewrite EQ1 in EB. cbn [s_exit] in EB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kx mm a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EB| lia| exact OK'| exact PR'| | exact MU| exact WM].
      mlmem_i AR1' AR2' FTB' BDB CSB CEB SLO' SHI' SD' ROB SCL' HIC' SCQ' BUD' STK' SHC' MI'.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_bigs : forall (cnt : nat) (i b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd ro : zarr) (Jlo Jhi Jd : list byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - i)%Z -> (0 <= i <= 255)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, i + Z.of_nat k <= 255 -> let s' := ms_bigs k ro qo n i s in s_exit s' = false -> bigF qo n ro (i + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    mlmem Jlo Jhi Jd a1 a2 ft bd cs ce sl sh sd ro b m -> munch WB me m -> wmono a0segs me m -> mviews X Y SHF WB me ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) ->
      mlmem Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro b' m' -> munch WB me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) ->
      mlmem Jlo Jhi Jd a1' a2' ft' bd' cs' ce' sl' sh' sd' ro b' m' -> munch WB me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 i) cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) x24 x25 x26 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98730) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 me m.
    intros s Hcnt Hi Hb BF A1OK A2OK BDOK PR LJlo LJhi LJd ML MU WM MV Klast Kexit. subst s.
    pose proof (BF 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_bigs] in F0. rewrite Z.add_0_r in F0.
    rewrite ms_bigs_S in Klast, Kexit. cbv zeta in Klast. cbv zeta in Kexit.
    eapply (A0_big i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 me m);
      [lia| lia| exact F0| exact A1OK| exact A2OK| exact BDOK| exact PR| exact LJlo| exact LJhi| exact LJd| exact ML| exact MU| exact WM| exact MV| | |].
    - (* [comment removed for export] *)
      intros m' a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y25 y26 y28 y29 y30 y31.
      intros Hlt EB Hb' OK1 OK2 PR' ML' MU' WM'.
      rewrite EB in Klast, Kexit. cbn [s_exit] in Klast, Kexit.
      assert (BDOK' : zbok (zset bd (zget ro i) 1)).
      { apply zbok_zset; [exact BDOK|]. unfold bigF in F0. cbv zeta in F0. lia. }
      eapply (IH (i + 1)%Z b' nqs' a1' a2' ft' _ csF ceB sl' sh' sd' nl' nh' nd' ro Jlo Jhi Jd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me m');
        [lia| lia| lia| | exact OK1| exact OK2| exact BDOK'| exact PR'| exact LJlo| exact LJhi| exact LJd| exact ML'| exact MU'| exact WM'| exact MV| | ].
      + intros k Hk. pose proof (BF (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. rewrite ms_bigs_S in Fk. cbv zeta in Fk. rewrite EB in Fk. cbn [s_exit] in Fk. cbv zeta.
        rewrite Nat2Z.inj_succ in Fk. replace (i + 1 + Z.of_nat k)%Z with (i + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
      + intros *. intros EQ2 Hb2. eapply Klast; [exact EQ2| lia].
      + intros *. intros EQ2 Hb2. eapply Kexit; [exact EQ2| lia].
    - (* [comment removed for export] *)
      intros m' a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros E255 EB Hb' OK1 OK2 PR' ML' MU' WM'.
      rewrite EB in Klast, Kexit. cbn [s_exit] in Klast, Kexit.
      assert (BDOK' : zbok (zset bd (zget ro i) 1)).
      { apply zbok_zset; [exact BDOK|]. unfold bigF in F0. cbv zeta in F0. lia. }
      assert (cnt = 0%nat) as -> by lia. cbn [ms_bigs] in Klast.
      eapply (Klast m' a1' a2' ft' _ csF ceB sl' sh' sd' nl' nh' nd' b' nqs');
        [reflexivity| lia| exact OK1| exact OK2| exact BDOK'| exact PR'| exact ML'| exact MU'| exact WM'].
    - intros m' a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EB Hb' OK1 PR' ML' MU' WM'.
      rewrite EB in Kexit. cbn [s_exit] in Kexit.
      eapply (Kexit m' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' b' nqs');
        [reflexivity| lia| exact OK1| exact A2OK| exact BDOK| exact PR'| exact ML'| exact MU'| exact WM'].
  Qed.
End A0MS.

End ACeilS1.
