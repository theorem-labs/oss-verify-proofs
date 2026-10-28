(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_msMa U0_msMb.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.

  Definition W2 : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 340, p + 2644)]%Z.

  (* [comment removed for export] *)
  Lemma S0_step2 : forall (i ss : Z) (a1 a2 ft bd cs ce : zarr) (w64 w72 w96 w104 w112 : word) (sb : scb)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let ci := ms_copy_init 256 cs ce ft ss 0 in let cs0 := fst ci in let ce0 := snd ci in
    let j0 := clearmask (zget ft (Z.shiftl ss 8)) in
    let rf := ms_copy_fwd (S (Z.to_nat n)) a1 cs0 a2 bd n ss j0 in let a1F := fst (fst rf) in let csF := snd (fst rf) in
    let j1 := (clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1)%Z in
    let rb := ms_copy_bwd (S (Z.to_nat n)) a1F ce0 a2 bd n ss j1 in let a1B := fst (fst rb) in let ceB := snd (fst rb) in
    let ftm := ms_mark 256 ft ss 0 in
    (0 <= i <= 255)%Z -> (0 <= ss < 256)%Z ->
    zget bd ss = 0%Z -> ftv ft ->
    (forall k, let '(r, jk) := ms_copy_fwd k a1 cs0 a2 bd n ss j0 in fwdF a2 bd n ss (fst r) (snd r) jk) ->
    (zget csF ss <= snd rf)%Z ->
    (forall k, let '(r, jk) := ms_copy_bwd k a1F ce0 a2 bd n ss j1 in bwdF a2 bd n ss (fst r) (snd r) jk) ->
    (snd rb <= zget ceB ss)%Z ->
    (zget csF ss - 1 = zget ceB ss \/ (zget csF ss = 0 /\ zget ceB ss = n - 1))%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u8arr s0segs m (p + 2388) (zb8 bd 256) -> u32arr s0segs m (p + 1364) (zw32 cs 256) -> u32arr s0segs m (p + 340) (zw32 ce 256) ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112)) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) ->
    mem_inv s0segs m -> munch W2 me m -> wmono s0segs me m ->
    (forall (last : bool) m' (x5' x6' x9' x10' x11' x12' x13' x14' x15' x16' x17' x19' : word),
      last = (i =? 255)%Z ->
      zbok a1B -> pr n a1B 0 (n - 1) -> ftv ftm ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ceB c < n)%Z ->
      u8arr s0segs m' A1 (zb8 a1B ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ftm 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 (zset bd ss 1) 256) -> u32arr s0segs m' (p + 1364) (zw32 csF 256) -> u32arr s0segs m' (p + 340) (zw32 ceB 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) ->
      mem_inv s0segs m' -> munch W2 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5' x6' x7 x8 x9' x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) x19' (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 1024 * ss)) x22 (Z_to_bv 64 (p + 2388)) x24
                            (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (if last then 0x22104 else 0x21fd4)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 ss) (Z_to_bv 64 A2) (Z_to_bv 64 (256 * ss)) x22 (Z_to_bv 64 (p + 2388)) x24
                          (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21cc4) fc None m (seg_rom s0segs)).
  Proof.
    intros i ss a1 a2 ft bd cs ce w64 w72 w96 w104 w112 sb x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x26 x27 x28 x29 x30 x31 me m.
    intros ci cs0 ce0 j0 rf a1F csF j1 rb a1B ceB ftm Hi Hss BD0 FTV FWF FWfin BWF BWfin A1007 A1OK A2OK BDOK PR AR1 AR2 FTB BD CS CE SCA SCB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold W2 in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    unfold sca_cells in SCA. unfold scb_cells in SCB.
    cbn [k40 k48 k64 k72 k96 k104 k112] in SCA.
    (* [comment removed for export] *)
    wstep. wstep. notrap.
    wstep. wstep. wstep. notrap.
    wstep. wstep. rdblk BD BDOK ss. rewrite BD0.
    wstep. notrap.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_cinit X Q XOK 256 0 ss ft cs ce sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CS| exact CE| exact SCB| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1 z15 z16. cbv zeta. intros FTB1 CS1 CE1 SCB1 MI1 MU1 WM1. fold ci in CS1, CE1. fold cs0 in CS1. fold ce0 in CE1.
    clear FTB CS CE MI SCB. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename m into m0; rename mm into m end.
    transport_after_call s0segs m0 m MU1 WM1. clear MU1 WM1.
    unfold scb_cells in SCB1.
    pose proof (zw32_length cs0 256 ltac:(lia)) as Lcs0. pose proof (zw32_length ce0 256 ltac:(lia)) as Lce0.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_fwd fst snd] in F0. destruct F0 as [CSR _]. pose proof (CSR ss ltac:(lia)) as Css.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as Vs0.
    assert (Hj0 : j0 = clearmask (zget ft (256 * ss))) by (subst j0; rewrite shl8; reflexivity).
    pose proof (clearmask_bounds (zget ft (256 * ss)) ltac:(lia)) as J0r. rewrite <- Hj0 in J0r.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. notrap.
    wstep. wstep. wstep. wstep. wstep.
    rd32_at FTB1 (256 * ss)%Z. rd32_at CS1 ss. wstep. wstep. rewrite land_CM64, <- Hj0 by lia.
    (* [comment removed for export] *)
    assert (JOINB : forall m' (a1'' ce' : zarr) (jB : Z) (y5 y6 y11 y12 y13 y14 y16 y17 : word),
      rb = (a1'', ce', jB) -> zbok a1'' -> pr n a1'' 0 (n - 1) ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ce' c < n)%Z ->
      u8arr s0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd 256) -> u32arr s0segs m' (p + 1364) (zw32 csF 256) -> u32arr s0segs m' (p + 340) (zw32 ce' 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) ->
      mem_inv s0segs m' -> munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 340, p + 2644)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp y5 y6 x7 x8 (Z_to_bv 64 (p + 2388 + ss))
                            (Z_to_bv 64 (zget csF ss)) y11 y12 y13 y14 (Z_to_bv 64 (zget ce' ss)) y16 y17
                            (Z_to_bv 64 A1) (Z_to_bv 64 (4 * ss)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 1024 * ss)) x22 (Z_to_bv 64 (p + 2388)) x24
                            (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21f74) fc None m' (seg_rom s0segs))).
    { intros m' a1'' ce' jB y5 y6 y11 y12 y13 y14 y16 y17 Erb OK'' PR'' CSR' CER' AR1' AR2' FTB' BD' CS' CE' SCA' SCB' MI' MU' WM'.
      clear AR1 AR2 FTB1 BD CS1 CE1 SCA SCB1 MI1 MU WM. unfold sca_cells in SCA'. unfold scb_cells in SCB'.
      cbn [k40 k48 k64 k72 k96 k104 k112] in SCA'.
      assert (EceB : ceB = ce') by (subst ceB; rewrite Erb; reflexivity). rewrite EceB in A1007.
      pose proof (CSR' ss ltac:(lia)) as Cs1. pose proof (CER' ss ltac:(lia)) as Ce1.
      assert (EaB : a1B = a1'') by (subst a1B; rewrite Erb; reflexivity).
      (* [comment removed for export] *)
      assert (OKK : forall m'' (z10 z11 : word), m'' = m' ->
        evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp y5 y6 x7 x8 (Z_to_bv 64 (p + 2388 + ss))
                            z10 z11 y12 y13 y14 (Z_to_bv 64 (zget ce' ss)) y16 y17
                            (Z_to_bv 64 A1) (Z_to_bv 64 (4 * ss)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 1024 * ss)) x22 (Z_to_bv 64 (p + 2388)) x24
                            (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21f94) fc None m'' (seg_rom s0segs))).
      { intros m'' z10 z11 ->.
        (* [comment removed for export] *)
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (S0_mark X Q XOK 256 0 ss ft sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
          [st_eq| lia| lia| lia| exact FTV| exact FTB'| exact SCB'| exact MI'| apply munch_refl| apply wmono_refl|].
        intros m2 v11 v12. cbv zeta. intros FTVm FTB2 SCB2 MI2 MU2 WM2. fold ftm in FTVm, FTB2.
        clear FTB' MI' SCB'. unfold scb_cells in SCB2. transport_after_call s0segs m' m2 MU2 WM2. clear MU2 WM2.
        (* [comment removed for export] *)
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (SOb : store_ok s0segs mm (wa (p + 2388 + ss)) 1 = true)
            by (eapply (u8arr_storeN_ok s0segs _ (p + 2388) _ ss 1 _ BD'); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
          change bs with (le1 (Z_to_bv 64 1));
          pose proof (zb8_write1 s0segs mm (p + 2388) bd 256 ss (Z_to_bv 64 1) BD' ltac:(lia)) as BDw end.
        clear BD'. store_done. rename BDw into BD'. change (wr8 bd ss (bv_unsigned (Z_to_bv 64 1))) with (zset bd ss 1) in BD'.
        wstep. wstep. wstep; if_cases Kl; zify_cond_z Kl.
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K true mm _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_eq; lia| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SCA'| exact SCB2| exact MI2| exact MU'| exact WM'].
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K false mm _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_neq; lia| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SCA'| exact SCB2| exact MI2| exact MU'| exact WM']. }
      wstep. wstep. notrap.
      wstep; if_cases K7.
      { enter_with (OKK m' _ _); [st_eq| reflexivity]. }
      lazymatch type of K7 with ?c = false => first [apply bveqb_lit_false in K7 | idtac "K7?"] | _ => idtac end.
      wstep; if_cases K8; zify_cond_z K8; [exfalso; Z.div_mod_to_equations; lia|].
      wstep. wstep; if_cases K9; [| first [apply bveqb_lit_false in K9 | idtac "K9?"]; exfalso; Z.div_mod_to_equations; lia].
      enter_with (OKK m' _ _); [st_eq| reflexivity]. }
    (* [comment removed for export] *)
    assert (JOINF : forall m' (a1' cs' : zarr) (jF : Z) (y5 y6 y12 y13 y14 y15 y16 y17 : word),
      rf = (a1', cs', jF) -> zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> 0 <= zget cs' c <= n)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd 256) -> u32arr s0segs m' (p + 1364) (zw32 cs' 256) -> u32arr s0segs m' (p + 340) (zw32 ce0 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) ->
      mem_inv s0segs m' -> munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 340, p + 2644)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x1 (Z_to_bv 64 p) gp tp y5 y6 x7 x8 (Z_to_bv 64 (p + 2388 + ss))
                            (Z_to_bv 64 (zget cs' ss)) (Z_to_bv 64 (4 * ss)) y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) (Z_to_bv 64 (4 * ss)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 1024 * ss)) x22 (Z_to_bv 64 (p + 2388)) x24
                            (Z_to_bv 64 2097152) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x21e70) fc None m' (seg_rom s0segs))).
    { intros m' a1' cs' jF y5 y6 y12 y13 y14 y15 y16 y17 Erf OK' PR' CSR' AR1' AR2' FTB' BD' CS' CE' SCA' SCB' MI' MU' WM'.
      clear AR1 AR2 FTB1 BD CS1 CE1 SCA SCB1 MI1 MU WM.
      unfold sca_cells in SCA'. unfold scb_cells in SCB'. cbn [k40 k48 k64 k72 k96 k104 k112] in SCA'.
      assert (EaF : a1F = a1') by (subst a1F; rewrite Erf; reflexivity). assert (EcF : csF = cs') by (subst csF; rewrite Erf; reflexivity).
      pose proof (BWF 0%nat) as B0. cbn [ms_copy_bwd fst snd] in B0. destruct B0 as [CER _]. pose proof (CER ss ltac:(lia)) as Ces.
      pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as Vs1.
      assert (Hj1 : j1 = (clearmask (zget ft (256 * ss + 256)) - 1)%Z) by (subst j1; rewrite shl8; f_equal; f_equal; f_equal; lia).
      pose proof (clearmask_bounds (zget ft (256 * ss + 256)) ltac:(lia)) as J1r.
      (* [comment removed for export] *)
      wstep. wstep. notrap.
      rd32_at FTB' (256 * ss + 256)%Z. wstep. wstep. rd32_at CE' ss. wstep. wstep. rewrite land_CM64 by lia. wstep.
      replace (clearmask (zget ft (256 * ss + 256)) + -1)%Z with j1 by lia.
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        assert (Erb : rb = (a1', ce0, j1)) by (subst rb; rewrite EaF; apply ms_copy_bwd_stop; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm a1' ce0 j1 _ _ _ _ _ _ _ _) end;
          [st_eq| exact Erb| exact OK'| exact PR'| rewrite EcF; exact CSR'| exact CER| exact AR1'| exact AR2'| exact FTB'| exact BD'| rewrite EcF; exact CS'| exact CE'| exact SCA'| exact SCB'| exact MI'| exact MU'| exact WM'].
        rewrite EcF. reflexivity.
      - (* [comment removed for export] *)
        wstep. wstep. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
        enter_with (S0_cbwd X Q XOK XSEP (S (Z.to_nat n)) j1 ss a1' a2 bd ce0 (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112) sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
          [st_eq| lia| lia| rewrite <- EaF; exact BWF| rewrite <- EaF; fold rb; subst ceB; destruct rb as [[? ?] ?]; exact BWfin
          | exact OK'| exact A2OK| exact BDOK| exact PR'| exact AR1'| exact AR2'| exact BD'| exact CE'| exact SCA'| exact SCB'| exact MI'| apply munch_refl| apply wmono_refl|].
        intros m2 a1'' ce' jB u5 u6 u11 u12 u13 u14 u16 u17 Erb2 OK'' PR'' CER'' AR1'' AR2'' BD'' CE'' SCA2 SCB2 MI2 MU2 WM2.
        clear AR1' AR2' BD' CE' MI' SCA' SCB'. unfold sca_cells in SCA2. unfold scb_cells in SCB2. unfold WCB in MU2. transport_after_call s0segs mq m2 MU2 WM2. clear MU2 WM2.
        assert (Erb : rb = (a1'', ce', jB)) by (subst rb; rewrite EaF; exact Erb2).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm a1'' ce' jB _ _ _ _ _ _ _ _) end;
          [st_eq| exact Erb| exact OK''| exact PR''| rewrite EcF; exact CSR'| exact CER''| exact AR1''| exact AR2''| exact FTB'| exact BD''| rewrite EcF; exact CS'| exact CE''| exact SCA2| exact SCB2| exact MI2| exact MU'| exact WM'].
        rewrite EcF. reflexivity. }
    clear JOINB.
    wstep; if_cases Kf; zify_cond_z Kf.
    - (* [comment removed for export] *)
      assert (Erf : rf = (a1, cs0, j0)) by (subst rf; apply ms_copy_fwd_stop; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1 cs0 j0 _ _ _ _ _ _ _ _) end;
        [st_eq| exact Erf| exact A1OK| exact PR| exact CSR| exact AR1| exact AR2| exact FTB1| exact BD| exact CS1| exact CE1| exact SCA| exact SCB1| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
      enter_with (S0_cfwd X Q XOK XSEP (S (Z.to_nat n)) j0 ss a1 a2 bd cs0 (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) w64 w72 w96 w104 w112) sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
        [st_eq| lia| lia| exact FWF| fold rf; subst csF; destruct rf as [[? ?] ?]; exact FWfin
        | exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BD| exact CS1| exact SCA| exact SCB1| exact MI1| apply munch_refl| apply wmono_refl|].
      intros m2 a1' cs' jF u5 u6 u12 u13 u14 u15 u16 u17 Erf OK' PR' CSR' AR1' AR2' BD' CS' SCA2 SCB2 MI2 MU2 WM2.
      clear AR1 AR2 BD CS1 MI1 SCA SCB1. unfold sca_cells in SCA2. unfold scb_cells in SCB2. unfold WCF in MU2. transport_after_call s0segs mq m2 MU2 WM2. clear MU2 WM2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1' cs' jF _ _ _ _ _ _ _ _) end;
        [st_eq| exact Erf| exact OK'| exact PR'| exact CSR'| exact AR1'| exact AR2'| exact FTB1| exact BD'| exact CS'| exact CE1| exact SCA2| exact SCB2| exact MI2| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
