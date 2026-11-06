(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed BothHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 rds2_cert_ok (p : constr) : bool :=
  match Constr.Unsafe.check p with Val _ => true | Err _ => false end.
Ltac2 rds2_prove (t : constr) : constr := constr:(ltac2:(ltac1:(intros; lia)) : $t).
Ltac2 rec rds2_relia (c : constr) : bool * constr :=
  let rec claimed (t : constr) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Cast _ _ ty => ty
    | Constr.Unsafe.Lambda b body => Constr.Unsafe.make (Constr.Unsafe.Prod b (claimed body))
    | Constr.Unsafe.LetIn b v body => Constr.Unsafe.make (Constr.Unsafe.LetIn b v (claimed body))
    | _ => Constr.type t
    end in
  let moved := { contents := false } in
  let walk (t : constr) : constr :=
    let (hit, u) := rds2_relia t in (if hit then moved.(contents) := true else ()); u in
  if Constr.Unsafe.is_closed c then
    if rds2_cert_ok c then (false, c) else
    let inner := Constr.Unsafe.map walk c in
    if rds2_cert_ok inner then (moved.(contents), inner) else
    match Control.case (fun () => rds2_prove (claimed inner)) with
    | Val pr => let (fresh, _) := pr in (true, fresh)
    | Err _ => (moved.(contents), inner)
    end
  else
    let rebuilt := Constr.Unsafe.map walk c in
    if moved.(contents) then (true, rebuilt) else (false, c).
Ltac2 rec rds2_sub (f : constr -> constr option) (c : constr) : bool * constr :=
  match f c with
  | Some r => (true, r)
  | None =>
    let touched := { contents := false } in
    let d := Constr.Unsafe.map
      (fun x => let (k, y) := rds2_sub f x in (if k then touched.(contents) := true else ()); y) c in
    if touched.(contents) then (true, d) else (false, c)
  end.
Ltac2 rec rds2_lit (subs : (constr * constr) list) (c : constr) : constr option :=
  match subs with [] => None | (a, b) :: r => if Constr.equal c a then Some b else rds2_lit r c end.
Ltac2 rds2_fix (subs : (constr * constr) list) (c : constr) : constr :=
  let (_, c) := rds2_relia c in
  match subs with [] => c | _ => let (_, c) := rds2_sub (rds2_lit subs) c in c end.
Ltac2 rds2_run (subs : (constr * constr) list) (tab : string) (secs : string list) (s : string) : unit :=
  KReplay.kr_revert ();
  let ph := { contents := [] } in
  let c := KReplay.decode_ph (Some ph) tab (KReplay.kr_secs secs) s in
  Std.exact_no_check (rds2_fix subs c);
  List.iter (fun (e, b) => Control.new_goal e; Control.enter (fun () => Std.exact_no_check (rds2_fix subs b))) (ph.(contents)).
Ltac2 rds2_run1 (tab : string) (secs : string list) (s : string) : unit := rds2_run [] tab secs s.
Ltac2 kr_t_ARepInit_B () := "C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS:MainExport:mimg_coverC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsBoth>asan_mem_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K59OSSVerify5KrLib2AS:MainExport4zexp01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K59OSSVerify5KrLib2AS:MainExport5mfact01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport9mfact_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport:mfact_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8mfact_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib5BothW<ARepInit_kitEbytes_eq_of_unsigned'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ARepInit_kit;rw_cells_tlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW<ARepInit_kit;rw_cells_hdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ARepInit_kit=rw_cells_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib5BothW<ARepInit_kit9img_chunkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ARepInit_B<flags85_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ARepInit_B=cflags34_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW7ACanaryApremap_canary_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW5ABase4al_VC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ARepInit_A3ST0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC59OSSVerify5KrLib5BothW<ARepInit_kit9byte_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4div2C59OSSVerify5KrLib5BothW<ARepInit_kit6zscanNC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N3subC47Corelib7Strings:PrimString6stringI47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3powC56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N2ltK47Corelib4Init9Datatypes6option01C56Stdlib6NArith6BinNat1N8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6NArith6BinNat1N7add_0_rC56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;hex_byte_atC46Stdlib9micromega;ZifyClasses9not_morphC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib5BothW:ARepInit_B8zscanN_SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6NArith6BinNat1N3divC56Stdlib6NArith6BinNat1N4succC56Stdlib6NArith4Nnat5Nat2N8inj_succC56Stdlib6NArith6BinNat1N3mulC56Stdlib6NArith6BinNat1N;pow_succ_r'C56Stdlib6NArith6BinNat1N7div_modC56Stdlib6NArith6BinNat1N6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3remC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6NArith6BinNat1N6mod_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6NArith6BinNat1N9add_assocC47Corelib4Init9Datatypes?andb_true_introC56Stdlib6NArith6BinNat1N8div2_divC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_powC56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat3N2Z7inj_mulC56Stdlib6ZArith4Znat3N2Z7inj_divC56Stdlib6ZArith4Znat3N2Z7inj_remC56Stdlib6ZArith4Znat3N2Z7inj_addC56Stdlib6ZArith4Znat3N2Z;inj_sub_maxI47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS;AsanHexScan6zscanZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrImgGTgt_huf_decompress_bothUTgt_huf_decompress_both_seg_bytes_003C1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ARepInit_kit4SEG3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N3lebC56Stdlib6NArith6BinNat1N6leb_leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib2AS;AsanHexScan<zscanZ_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ARepInit_B?zscanN_completeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib5BothW:ARepInit_B:aia_scan63C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_N_ZI47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8zexp_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8mwr_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport2zvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3Z2N2idC59OSSVerify5KrLib5BothW<ARepInit_kit<img_zero_stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ARepInit_kit9wr_at_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW:ARepInit_B8aia_scanC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
Proof.
  unfold arelro.
  apply (mimg_cover bsegs V m asan_mem_facts ARELRO_LO ARELRO_HI HM).
  vm_compute. reflexivity.
Qed.

  (* [comment removed for export] *)
  Lemma flags85_init : rw_cells bsegs m 0xb7b4d [C1 (Z_to_bv 8 1)].
Proof.
  assert (qw_b7b48 : rw_cells bsegs m 752456 [C8 (Z_to_bv 64 72340172838010881)]).
  { apply (mfact_find bsegs V m asan_mem_facts (MCell (ZLit 752456) 8 (ZLit 72340172838010881)) HM).
    vm_compute. reflexivity. }
  assert (cut_at_5 : rw_cells bsegs m 752456
    ([CB 5 (firstn 5 (le8 (Z_to_bv 64 72340172838010881)))] ++ [C1 (Z_to_bv 8 1)]
       ++ [CB 2 (skipn 6 (le8 (Z_to_bv 64 72340172838010881)))])).
  { apply (rw_cells_recast bsegs m 752456 _ _ qw_b7b48).
    - vm_compute. repeat split.
    - apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
    - reflexivity. }
  apply rw_cells_app in cut_at_5 as [_ from_5].
  apply rw_cells_app in from_5 as [only_5 _].
  exact only_5.
Qed.

  Lemma cflags34_init : rw_cells bsegs m 0x14be4a [C1 (Z_to_bv 8 1)].
Proof.
  pose proof (mfact_find bsegs V m asan_mem_facts (MCell (ZLit 1359432) 8 (ZLit 128849084416)) HM)
    as qw_14be48.
  cbn [mfact_ok zv cellw] in qw_14be48.
  specialize (qw_14be48 ltac:(vm_compute; reflexivity)).
  assert (byte_2_isolated : rw_cells bsegs m 1359432
    ([CB 2 (firstn 2 (le8 (Z_to_bv 64 128849084416)))] ++ [C1 (Z_to_bv 8 1)]
       ++ [CB 5 (skipn 3 (le8 (Z_to_bv 64 128849084416)))])).
  { apply (rw_cells_recast _ _ _ _ _ qw_14be48); [vm_compute; repeat split | | reflexivity].
    apply bytes_eq_of_unsigned'. vm_compute. reflexivity. }
  destruct (proj1 (rw_cells_app _ _ _ _ _) byte_2_isolated) as [low_pair rest].
  destruct (proj1 (rw_cells_app _ _ _ _ _) rest) as [the_flag high_five].
  exact the_flag.
Qed.

  Theorem arep_rt_init : arep_rt L m.
Proof.
  pose proof (fun f => mfact_find bsegs V m asan_mem_facts f HM) as handoff.
  (* three cells whose address or value comes from the layout *)
  assert (tsd_slot : rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]).
  { unfold L. rewrite LV_ctx.
    apply (handoff (MCell (ZLit 6350392) 8 (ZMul (ZLit 4096) (ZV 228)))). vm_compute. reflexivity. }
  assert (ctx_plus8 : rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)]).
  { unfold L. rewrite LV_ctx.
    apply (handoff (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0))). vm_compute. reflexivity. }
  assert (ctx_plus152 : rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]).
  { unfold L. rewrite LV_ctx, LV_t.
    apply (handoff (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227)))).
    vm_compute. reflexivity. }
  (* 0xb7b24: one handoff word, then the two halves of the quad word at 0xb7b28 *)
  assert (trio_b7b24 : rw_cells bsegs m 0xb7b24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]).
  { apply rw_cells_cons.
    - apply (handoff (MCell (ZLit 752420) 4 (ZLit 4096))). vm_compute. reflexivity.
    - change (0xb7b24 + Z.of_nat (csize (C4 (Z_to_bv 64 0x1000)))) with 752424.
      assert (qw_b7b28 : rw_cells bsegs m 752424 [C8 (Z_to_bv 64 816043786240)])
        by (apply (handoff (MCell (ZLit 752424) 8 (ZLit 816043786240))); vm_compute; reflexivity).
      apply (rw_cells_recast _ _ _ _ _ qw_b7b28); [vm_compute; repeat split | | reflexivity].
      apply bytes_eq_of_unsigned'. vm_compute. reflexivity. }
  pose proof flags85_init as flag_b7b4d.
  pose proof cflags34_init as flag_14be4a.
  unfold arep_rt.
  repeat match goal with |- _ /\ _ => split end.
  all: let rec fill :=
    first
    [ match goal with known : rw_cells _ _ ?a ?cs |- rw_cells _ _ ?a ?cs => exact known end
    | lazymatch goal with |- context [L] => fail | _ => idtac end;
      first
      [ apply (img_chunk V m asan_mem_facts);
          [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
          | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ]
      | lazymatch goal with
        | |- rw_cells _ _ ?a [C8 (Z_to_bv _ ?v)] => apply (handoff (MCell (ZLit a) 8 (ZLit v)))
        | |- rw_cells _ _ ?a [C4 (Z_to_bv _ ?v)] => apply (handoff (MCell (ZLit a) 4 (ZLit v)))
        | |- rw_cells _ _ ?a [C2 (Z_to_bv _ ?v)] => apply (handoff (MCell (ZLit a) 2 (ZLit v)))
        | |- rw_cells _ _ ?a [C1 (Z_to_bv _ ?v)] => apply (handoff (MCell (ZLit a) 1 (ZLit v)))
        end; vm_compute; reflexivity
      | lazymatch goal with |- rw_cells _ _ _ (_ :: _ :: _) => idtac end;
        apply rw_cells_cons;
          [ fill
          | lazymatch goal with |- rw_cells _ _ ?a _ => let a' := eval vm_compute in a in change a with a' end;
            fill ] ] ]
  in fill.
Qed.

  Theorem arep_rt2_init : arep_rt2 m.
Proof.
  pose proof (fun f => mfact_find bsegs V m asan_mem_facts f HM) as handoff.
  assert (byte_14bf2c : rw_cells bsegs m 0x14bf2c [C1 (Z_to_bv 8 0)]).
  { assert (qw_14bf28 : rw_cells bsegs m 1359656 [C8 (Z_to_bv 64 16843009)])
      by (apply (handoff (MCell (ZLit 1359656) 8 (ZLit 16843009))); vm_compute; reflexivity).
    assert (split_4_1_3 : rw_cells bsegs m 1359656
      ([CB 4 (firstn 4 (le8 (Z_to_bv 64 16843009)))] ++ [C1 (Z_to_bv 8 0)]
         ++ [CB 3 (skipn 5 (le8 (Z_to_bv 64 16843009)))])).
    { apply (rw_cells_recast _ _ _ _ _ qw_14bf28); [| | exact eq_refl].
      + vm_compute. repeat split.
      + apply bytes_eq_of_unsigned'. vm_compute. reflexivity. }
    apply rw_cells_app, proj2, rw_cells_app, proj1 in split_4_1_3.
    exact split_4_1_3. }
  unfold arep_rt2. split; [exact byte_14bf2c | split].
  - apply (handoff (MCell (ZLit 0x14beb8) 8 (ZLit 0))). vm_compute. reflexivity.
  - apply (img_chunk V m asan_mem_facts);
      [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
      | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ].
Qed.

  Theorem arep_rt3_init : arep_rt3 m.
Proof.
  unfold arep_rt3.
  repeat match goal with |- _ /\ _ => split end.
  all: try first
    [ apply (img_chunk V m asan_mem_facts);
        [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
        | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ]
    | lazymatch goal with
      | |- rw_cells _ _ ?at_ [C8 (Z_to_bv _ ?val)] =>
          apply (mfact_find bsegs V m asan_mem_facts (MCell (ZLit at_) 8 (ZLit val)) HM)
      | |- rw_cells _ _ ?at_ [C4 (Z_to_bv _ ?val)] =>
          apply (mfact_find bsegs V m asan_mem_facts (MCell (ZLit at_) 4 (ZLit val)) HM)
      | |- rw_cells _ _ ?at_ [C1 (Z_to_bv _ ?val)] =>
          apply (mfact_find bsegs V m asan_mem_facts (MCell (ZLit at_) 1 (ZLit val)) HM)
      end; vm_compute; reflexivity ].
  (* the eight bytes at 0x60d2d0 hold a value only known as V 45 *)
  pose proof (mfact_find bsegs V m asan_mem_facts (MRo (ZLit 0x60d2d0) 8 (ZV 45)) HM) as seen_v45.
  specialize (seen_v45 ltac:(vm_compute; reflexivity)).
  cbn [mfact_ok zv] in seen_v45.
  assert (open_for_writes : wr_at bsegs m 0x60d2d0 8).
  { split; [lia | split; [lia |]].
    intros k k_span. apply BothPlanImages.asan_rw_window.
    rewrite wa_unsigned; lia. }
  exists (word_to_le_bytes 8 (Z_to_bv 64 (V 45))).
  apply rw_cells_of_parts; [split; [reflexivity | exact I] | | exact open_for_writes].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact seen_v45.
Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
Proof.
  pose proof (fun f => mfact_find bsegs V m asan_mem_facts f HM) as handoff.
  assert (space_lo : al_space_beg L = 4096 * V 208 + -4096 * V 209 + 65536)
    by (unfold L; rewrite LV_space_beg; ring).
  assert (space_hi : al_space_beg L + K_SPACE_SIZE = 4096 * V 208 + -4096 * V 209 + 137439019008)
    by (rewrite space_lo; unfold K_SPACE_SIZE; lia).
  assert (ptrs : al_ptr_array L = 4096 * V 226) by (unfold L; apply LV_ptr_array).
  (* cells the handoff wrote, in address order *)
  assert (c32 : rw_cells bsegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 (al_space_beg L))]).
  { rewrite space_lo.
    apply (handoff (MCell (ZLit 748728) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536)))).
    vm_compute. reflexivity. }
  assert (c40 : rw_cells bsegs m (AINSTANCE + 40) [C4 (Z_to_bv 64 4294967295)]).
  { assert (all_ones : rw_cells bsegs m 748736 [C4 (Z_to_bv 64 18446744073709551615)])
      by (apply (handoff (MCell (ZLit 748736) 4 (ZLit 18446744073709551615))); vm_compute; reflexivity).
    apply (rw_cells_recast _ _ _ _ _ all_ones); [exact (conj I I) | | reflexivity].
    apply bytes_eq_of_unsigned'. vm_compute. reflexivity. }
  assert (c48 : rw_cells bsegs m (AINSTANCE + 48) [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]).
  { rewrite space_hi.
    apply (handoff (MCell (ZLit 748744) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)))).
    vm_compute. reflexivity. }
  assert (c56 : rw_cells bsegs m (AINSTANCE + 56) [C1 (Z_to_bv 8 0)])
    by (apply (handoff (MCell (ZLit 748752) 1 (ZLit 0))); vm_compute; reflexivity).
  assert (c64 : rw_cells bsegs m (AINSTANCE + 64) [C8 (Z_to_bv 64 4096)])
    by (apply (handoff (MCell (ZLit 748760) 8 (ZLit 4096))); vm_compute; reflexivity).
  assert (c72 : rw_cells bsegs m (AINSTANCE + 72) [C8 (Z_to_bv 64 (al_ptr_array L))]).
  { rewrite ptrs. apply (handoff (MCell (ZLit 748768) 8 (ZMul (ZLit 4096) (ZV 226)))). vm_compute. reflexivity. }
  assert (c680 : rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)])
    by (apply (handoff (MCell (ZLit 749376) 1 (ZLit 0))); vm_compute; reflexivity).
  (* cells still as the image left them *)
  assert (counts : rw_cells bsegs m (AINSTANCE + 112) [C8 (Z_to_bv 64 (a_nres (ST0 V))); C8 (Z_to_bv 64 (a_nsec (ST0 V)))]).
  { change (a_nres (ST0 V)) with 0. change (a_nsec (ST0 V)) with 0.
    apply (img_chunk V m asan_mem_facts);
      [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
      | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ]. }
  assert (c984 : rw_cells bsegs m (AINSTANCE + 984) [C1 (Z_to_bv 8 0)]).
  { apply (img_chunk V m asan_mem_facts);
      [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
      | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ]. }
  exact (conj c32 (conj c48 (conj c64 (conj c72 (conj counts (conj c680 (conj c984 (conj c40 c56)))))))).
Qed.

  (* [comment removed for export] *)
  Theorem aquar_glob_const_init : aquar_glob_const m.
Proof.
  pose proof (fun f => mfact_find bsegs V m asan_mem_facts f HM) as handoff.
  assert (limits : rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)]).
  { apply rw_cells_cons; [apply (handoff (MCell (ZLit 749488) 8 (ZLit Q_MAX))); vm_compute; reflexivity |].
    change (AQ_MAX + Z.of_nat (csize (C8 (Z_to_bv 64 Q_MAX)))) with 749496.
    apply rw_cells_cons; [apply (handoff (MCell (ZLit 749496) 8 (ZLit Q_MIN))); vm_compute; reflexivity |].
    change (749496 + Z.of_nat (csize (C8 (Z_to_bv 64 Q_MIN)))) with 749504.
    apply (handoff (MCell (ZLit 749504) 8 (ZLit Q_CACHE))). vm_compute. reflexivity. }
  assert (lock_bytes : rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply rw_cells_cons; [apply (handoff (MCell (ZLit 749576) 1 (ZLit 0))); vm_compute; reflexivity |].
    change (AQ_MUTEX + Z.of_nat (csize (C1 (Z_to_bv 8 0)))) with 749577.
    apply rw_cells_cons; [apply (handoff (MCell (ZLit 749577) 1 (ZLit 0))); vm_compute; reflexivity |].
    change (749577 + Z.of_nat (csize (C1 (Z_to_bv 8 0)))) with 749578.
    apply (img_chunk V m asan_mem_facts);
      [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
      | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ]. }
  exact (conj limits lock_bytes).
Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
Proof.
  unfold aqcache. split.
  2: exact I.
  apply (img_chunk V m asan_mem_facts); [exact HM | | | | |].
  4, 5: vm_compute; congruence.
  all: vm_compute; try reflexivity; repeat split.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zscanN_S : forall s f base n, zscanN s (Datatypes.S f) base n =
    (if N.eqb n 0 then true else if N.eqb n 1 then byte_zero s base
     else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool).
Proof. reflexivity. Qed.
  Lemma zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) -> zscanN s (Datatypes.S f) base n = true.
Proof.
    intros s f. induction f as [|f IH]; intros base n Hn Hz; rewrite zscanN_S;
      (destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|]); destruct (N.eqb_spec n 1) as [E1|N1].
    1, 3: (pose proof (Hz 0%N ltac:(lia)) as Z0; rewrite N.add_0_r in Z0; unfold byte_zero; rewrite Z0; reflexivity).
    - exfalso. change (2 ^ N.of_nat 0)%N with 1%N in Hn. lia.
    - cbv iota zeta. rewrite N.div2_div. rewrite Nat2N.inj_succ, N.pow_succ_r' in Hn.
      pose proof (N.div_mod n 2 ltac:(lia)) as DM. pose proof (N.mod_lt n 2 ltac:(lia)) as ML.
      set (h := (n / 2)%N) in *. set (r := (n mod 2)%N) in *. set (p := (2 ^ N.of_nat f)%N) in *. clearbody h r p.
      apply andb_true_intro. split; apply IH.
      + lia.
      + intros i Hi. apply Hz. lia.
      + lia.
      + intros i Hi. rewrite <- N.add_assoc. apply Hz. lia.
  Qed.
  Lemma aia_scan63 : zscanZ AsanUbsan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
Proof.
    apply (zscanN_complete _ 63).
    - apply N.leb_le. vm_compute. reflexivity.
    - intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. lia.
  Qed.

  Theorem aintal_init : aintal false m.
Proof.
  assert (no_overlay : forall i, AIA_BASE <= i < AIA_BASE + Z.of_N (Z.to_N AIA_SIZE) -> m (wa i) = None).
  { apply (mimg_cover bsegs V m asan_mem_facts _ _ HM). vm_compute. reflexivity. }
  assert (writable_seg : wr_at bsegs m 724992 5620432).
  { apply (mfact_find bsegs V m asan_mem_facts (MWr (ZLit 724992) 5620432) HM). vm_compute. reflexivity. }
  assert (writable_aia : wr_at bsegs m AIA_BASE (Z.of_N (Z.to_N AIA_SIZE))).
  { apply (wr_at_sub m 724992 5620432 _ _ writable_seg); vm_compute; congruence. }
  pose proof (img_zero_stk _ _ m AIA_BASE aia_scan ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; congruence) no_overlay writable_aia) as aia_stack.
  unfold aintal. split; [| split].
  - apply (img_chunk V m asan_mem_facts);
      [ exact HM | vm_compute; reflexivity | vm_compute; repeat split
      | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence ].
  - exact aia_stack.
  - intro never. discriminate never.
Qed.
End B.
End CANSEC1.
(* [comment removed for export] *)
