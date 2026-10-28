(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_bitlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_core_bitlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_BITLEN_STACK_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_bitlen_postA"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.log2"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen_rec"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"].


Definition A_MPI_CORE_BITLEN : Z := 0xa34b0.
Definition MPI_CORE_BITLEN_STACK_A : Z := 16.

Definition mpi_core_bitlen_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O17.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O15.)$12.)(11.&40.O15.))(13.(=.$>.$>.)))O1.R1.)(4.(14.O17.O1.R1.)(4.(15.O17.R1.)(4.(5.(2.&40.)R=.(16.&40.(17.O4.O3.)))(18.O17.R1.O2.(11.&40.O15.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_bitlen_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Pn,$>.Plo,$>.Pxs,(1:.(2.&40.))P,(1;.O3.R5.R4.(1<.R1.))P,(4.(1=.=R4.)(1=.R4.+2710.))P,(1=.R5.(1>.(1?.(2.&40.)R3.)))P,(5.$>.(20.R7.+4.)=)P,(21.=R8.)P,(15.O3.R:.)P,(22.O2.)P,(23.O2.R2>.)P,(24.O3.O2.R=.)P,(25.O3.O2.R30.R>.R=.(26.+4.R<.))P,(18.O3.R?.R<.(11.&40.R2?.))P,(1=.R=.(10.(11.&40.R30.)$12.))P,(5.$>.(20.(11.&40.R31.)+10.)=)P,(27.R34.R?.(10.(11.&40.R32.)R?.))P,(28.(1=.(29.R12.(26.+4.(1>.(1?.(2.&40.)R?.))))(10.(11.&40.R33.)$12.))(1=.(11.&40.R33.)R12.))P,(5.(2.&40.)R2<.(16.&40.R13.))P,(5.(2.&40.)R2<.(16.&40.R13.))(2:.O3.O2.R38.(2;.O3.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R12.R14.R13.R16.)(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(16.&40.O1.)R17.(9.(2.&40.))R16.(:.O3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_core_bitlen_z_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_bitlen ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Plo,$>.P,(15.O3.R3.)P,(4.(1=.=R3.)(21.R3.(2<.+2.+40.)))P,(22.O2.)P,(23.O2.R28.)P,(24.O3.O2.R7.)P,(18.O3.R8.R6.(11.&40.R28.))P,(1=.R7.(10.(11.&40.R29.)$12.))P,(5.$>.(20.(11.&40.R2:.)+10.)=)P,(27.R2=.R9.(10.(11.&40.R2;.)R9.))P,(5.(2.&40.)R24.(16.&40.R;.))P,(5.(2.&40.)R24.(16.&40.=))(2:.O3.O2.R30.(2;.O3.R2?.R2>.R2=.R2<.R28.R27.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R10.R?.(13.(2.&40.))=R<.R>.)(6.(7.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(16.&40.O1.)R?.(9.(2.&40.))R>.(:.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n lo : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SA : A + 4 * Z.of_nat (length xs) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_bitlen_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(bv_unsigned sp - 16, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L14935779467.66L15475369355.68L31399144472.68L32049487064.69L3830364018.69 L46933721732.69L59589536811.66Q15643391633.69Q9843295730.69 00000100=00H00S00e01:01B01L01ZFS1A2xs1w1r1bS2sp1A2xs1wS2sp1A2xs1wS2sp1A2lo2xs3SLO1wS1A1n2xs2Hn2XB1w1r2HrS1A2xs1wS2sp2lo2xsS2sp2lo2xs3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK A Hn Ln XB LO0 SLO SCS SPR"] Lemma clz_walk : forall (w : word) (x r : Z) (x10 x13 x14 x15 x16 x17 w11 : word) (junk : list (bv 8)) (mm : mem),
    x = bv_unsigned w mod 2 ^ 32 -> x <> 0 -> 1 <= r <= n ->
    core_bitlen xs n = 32 * (r - 1) + Z.log2 x + 1 ->
    w11 = Z_to_bv 64 (r - 1) ->
    rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 x10 w11 (sx32 w) x13 x14 x15 x16 x17
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa353c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros w x r x10 x13 x14 x15 x16 x17 w11 junk mm Hx Hnz Hr HBL -> FR ST MU WM MI. al_facts.
    do 12 zstep.
    destruct (smear_chain w x (Z.log2 x) Hx Hnz eq_refl) as [SM Bb]. cbv zeta in SM.
    rewrite SM. clear SM.
    set (b := Z.log2 x) in *. clearbody b.
    do 19 step.
    (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) =>
      let raw := get_x10 R in
        assert (HR : bv_unsigned raw = 31 - b)
          by (clear -b Bb; pattern b;
              lazymatch goal with |- ?P b =>
                unshelve refine (enum32 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b Bb) end;
              cbv beta; vm_compute; reflexivity)
    end.
    step. step. step.
    rewrite HR. clear HR. rewrite (unsigned_lit (r - 1)) by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish. f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
    rewrite Z.mod_small by lia. rewrite HBL. lia.
    all: match goal with |- ?g => idtac "CLZ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0?L20378331621.74L23917391152.74L26773890077.72L29010565666.65L31399144472.61L31889232343.74L32049487064.62L35909905322.69L37798226539.68L37801064254.72L3834405561.62 L42468625771.72L44663269934.70L54425554183.69L55310445663.65L56834433586.74L58496276083.65L58829635818.75L59164244479.75L59308628179.66L66138855315.63L8658395247.64 Q10827307447.72Q15647499098.62Q23447478054.70Q25485674942.72Q25486628167.73Q25488363986.70Q26295627581.73Q26463039879.73Q45164787272.73Q50458135125.73Q8945570098.70 Q9839185977.62 00000?00T00i01A01M01d02002K04O04j05=05L05Y05i06A06P06]07807S08508H08`09509B09W09g0:70:G0:R0:e0;:0;G0;R0;cS1A2xs1k1r2Hk1wS1A2xs2XB1k1r2Hk1w2K1S1A2xs2XB1k1r2Hk2K11wS1A1n2xs2Ln2XB1k1r2Hk2HrS2sp1A2xs2HkS1A1n2xs1k1r2Hk2Hr1w2K1S2sp1A2xs2HkS1A1n2xs2Ln2XB1k1r2Hk2Hr2K1S2AL2CS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1A1n2lo2xs2Ln2XB1k1r3x153x163x172mm2Hk2Hr2K12NXS1A1n2xs2Ln2XB1k1r2Hk2Hr2K1S2sp1A2lo2xs3SLO2HkS1A2xs1k1r2Hk1wS1A2xs1k1r2HkS1A2xs1k1r2Hk2K1S1A1n2xs2Hn2XB1k1r2Hk2HrS1A2xs1k1r2Hk1wS1A2xs1k1r2HkS1A1n2xs2XB1k1r2Hk1w3HBL2K1S1A1n2xs1k1r2Hk2Hr1w3HBL2K1S2sp1A1n2xs2Ln2XB3SPR1k1r2Hk2Hr2K0S1A1n2xs2XB1r2Hk2HrS1A1n2xs2Ln2XB1k1r2Hk2HrS1A1n2xs1k1r2Hk2Hr2K1S2sp2lo2xs2HkS1A1n2xs1k1r2Hk2Hr2K1S1A2xs1k1r2Hk2K1S1A2xs1k1r2Hk2K1S1A2xs1k1r2Hk2K1S2xs1k1r2HkS1A2xs2XB1k1r2Hk2K1S1A1n2xs1k1r2Hk2Hr2K1S1A2xs1k1r2HkS2xs1k1r2HkS2sp2lo2xs3SLO2Hk". (* [comment removed for export] *)
  Lemma zsw32_zero_iff : forall u, zswrap 32 (zlow 32 u) = 0 <-> u mod 2 ^ 32 = 0.
  Proof.
    intros u. unfold zswrap, zlow. change (2 ^ (32 - 1)) with (2 ^ 31).
    pose proof (Z.mod_pos_bound u (2 ^ 32) ltac:(lia)) as R.
    set (y := u mod 2 ^ 32) in *. clearbody y.
    destruct (Z.ltb_spec y (2 ^ 31)).
    - rewrite (Z.mod_small (y + 2 ^ 31)) by lia. lia.
    - replace (y + 2 ^ 31) with ((y - 2 ^ 31) + 1 * 2 ^ 32) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia.
  Qed.
  Lemma loop_walk : forall (k : nat) (r : Z) (x12 x15 x16 x17 : word) (junk : list (bv 8)) (mm : mem) (er : Z),
    Z.to_nat r = k -> 1 <= r <= n -> er = r ->
    core_bitlen xs n = core_bitlen_rec xs (Z.to_nat r) ->
    bytes_at asegs mm A (u32s xs) -> aobj asegs AL CS mm A (4 * n) ->
    rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -16) ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 er) x12 SB (Z_to_bv 64 1)
      x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xa34d8) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r x12 x15 x16 x17 junk mm er Hk Hr Er HBL HA OA FR ST MU WM MI; [exfalso; clear - Hk Hr; lia|]. al_facts.
    (* [comment removed for export] *)
    destruct (nth_error xs (Z.to_nat (r - 1))) as [w|] eqn:NX; [| exfalso; apply nth_error_None in NX; clear - NX Hr Ln; lia].
    (* [comment removed for export] *)
    pose proof (u32ro_cell_at mm A xs (r - 1) (A + 4 * (er - 1)) w HA NX ltac:(clear - Hr; lia) ltac:(clear - Er; lia)) as CSx.
    (* [comment removed for export] *)
    lx_hide HBL. lx_spell. lx_run_tac (PLAN [0xa34d8; 0xa353c] [(0xa350c, DJoin)] 80%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear CSx; lx_unhide.
    (* [comment removed for export] *)
    all: assert (L32 : limb32 xs (Z.to_nat (r - 1)) = bv_unsigned w mod 2^32) by (unfold limb32; rewrite (nth_error_nth _ _ _ NX); reflexivity);
         replace (Z.to_nat r) with (S (Z.to_nat (r - 1))) in HBL by lia; cbn [core_bitlen_rec] in HBL; rewrite L32 in HBL.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa34d8) _ _ _ _) =>
             assert (V0 : zswrap 32 (zlow 32 (bv_unsigned w)) = 0) by lia;
             apply zsw32_zero_iff in V0; rewrite V0, Z.eqb_refl in HBL;
             eapply (IH (r - 1)); [clear - Hk Hr; lia | lia | clear - Er; lia | exact HBL | exact HA | exact OA
               | exact FR | exact ST | exact MU | exact WM | exact MI]
         | |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 0xa353c) _ _ _ _) =>
             assert (V1 : bv_unsigned w mod 2^32 <> 0) by (rewrite <- zsw32_zero_iff; lia);
             rewrite (proj2 (Z.eqb_neq _ _) V1) in HBL; rewrite lx_sx32;
             eapply (clz_walk w (bv_unsigned w mod 2^32) r); [reflexivity | exact V1 | lia | rewrite HBL; lia | f_equal; lia
               | exact FR | exact ST | exact MU | exact WM | exact MI]
         | |- _ =>
             assert (V0 : zswrap 32 (zlow 32 (bv_unsigned w)) = 0) by lia;
             apply zsw32_zero_iff in V0; rewrite V0, Z.eqb_refl in HBL;
             assert (CB : core_bitlen xs n = 0) by (rewrite HBL; replace (Z.to_nat (r - 1)) with O by lia; reflexivity);
             lx_post; first [rewrite CB; reflexivity | idtac]
         end.
    (* [comment removed for export] *)
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00[0?K49615311099.68L11616173489.65L1167583876.66 L1169664276.64 L1685717371.0  L17912843979.65L18873397548.65L18926591958.65L20433961190.64L22331926039.65L25960813796.65L32049487064.64L3227376625.65 L41872764395.67L43061775753.62L44015132812.65L44301797884.65L46748113268.64L47039734445.65L49618833658.3 L53395299452.65L58304640849.65L58796926075.65L60194088209.65L61931962912.66Q11801279589.68Q1219017780.67 Q15643324129.64Q21798041355.67Q23150033886.67Q25513505925.67Q31394594844.67Q40688494363.67Q41126203749.67Q44034257392.67Q45914037331.65Q49698585326.66Q53519952433.67Q54057591853.67Q58146298210.67Q63037100374.67Q66715549212.67Q9843367298.64 00000N00O00P00Q00R00S00\00e00n00o01:01C01S01_01n02702802A02W02X02a02l03:03E03S03l04904C04D04Q04m05105205305?05I05]05j05k06J06V06b06oS2ra2sp1A2xs2SA2HB5Ha_st5Hl_stFFFSFS2sp1A2xsS2sp1A2xsS2sp1A2xsFS2sp1A1n2xsS2sp1A2xsS2sp1A2xs3NZA2XBS2AL2sp1A2xsS2sp1A2lo2xs2LOS2sp1A2xsFS2sp1A2xsS2sp1A1n2xs2Hn3NZA3SPRFS2sp1A2xsS2sp1A1n2xsS2sp1A1n2xs2HnS2sp1A1n2xsS2sp1A1n2xs2HnS2ra2sp2xs2HB5Ha_st5Hl_stS2AL2xs5ALWF'S2sp2lo2xsFS2AL2xs5ALWF'S2ra2sp2lo2xs2HB5Ha_st5Hl_stS2xsFFS2AL2xs4IMG'S2sp2xs2HBS2sp2xs3SPR2HB5Ha_stS2AL2xs5ALWF'FS2ra2sp2lo2xs2LO2HB5Ha_st5Hl_stS2AL2xs4IMG'S2AL2xs4IMG'S2sp2lo2xs2LO". (* [comment removed for export] *)
Lemma A_mpi_core_bitlen_spec : forall AL, asan_img_ok AL -> mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
Proof.
  intros AL IMG. unfold mpi_core_bitlen_stmtA, A_MPI_CORE_BITLEN.
  intros until xs. intros HA Hn LX ALA NZA MI ALWF CSOK ABS OA ST LO SPA SCS SA -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_BITLEN_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB. pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  lx_spell. lx_run_tac (PLAN [0xa34d8] [] 40%N). lx_tree.
  (* [comment removed for export] *)
  all: lx_gc.
  all: lazymatch goal with
       | |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
           assert (N0 : n = 0) by lia; subst n; lx_post; first [reflexivity | idtac]
       | |- _ =>
           lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_ro32 A HA'; lx_rn_aobj A OA';
           eapply (loop_walk AL IMG ALWF CS CSOK) with (A := A) (n := n) (lo := lo) (xs := xs) (k := Z.to_nat n) (r := n);
           first [ assumption | reflexivity | eassumption | klia ]
       end.
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L1685717371.0  L20433961190.55L31399144472.55L32049487064.56L32049487064.57L3830427394.56 L41872764395.59L43061775753.53L46748113268.56Q11801279589.59Q1219017780.58 Q15643324129.55Q15643324129.56Q21798041355.58Q23150033886.58Q25513505925.58Q31394594844.58Q41126203749.58Q44034257392.58Q45914037331.56Q49698585326.57Q53519952433.58Q58146298210.58Q63037100374.58Q66715549212.58Q9843367298.55 Q9843367298.56 00000100500900=00A00K00R00\00`01601@01G01N01O01Y02202302402=02D02U02_03;03D03M03W03aSS2spS2spS2spS2spS2sp2lo2LOS2AL2spS2sp2lo2LOS2spS2ra2sp2HB5Ha_st5Hl_stS2AL5ALWF'S2sp2loS2sp2loFS2AL5ALWF'S2ra2sp2lo2HB5Ha_st5Hl_stSFS2AL4IMG'S2sp2HBS2sp3SPR2HB5Ha_stS2AL5ALWF'S2ra2sp2lo2LO2HB5Ha_st5Hl_stS2AL4IMG'S2AL4IMG'S2sp2lo2LOS2sp2lo2LO". (* [comment removed for export] *)
Lemma A_mpi_core_bitlen_z_spec : forall AL, asan_img_ok AL -> mpi_core_bitlen_z_stmtA asegs AL A_MPI_CORE_BITLEN.
Proof.
  intros AL IMG. unfold mpi_core_bitlen_z_stmtA, A_MPI_CORE_BITLEN.
  intros until lo. intros MI HA ALWF CSOK ABS ST LO SPA SCS -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_BITLEN_STACK_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  lx_spell. lx_run_tac (PLAN [] [] 30%N). lx_tree.
  (* [comment removed for export] *)
  all: lx_post; first [reflexivity | idtac].
  all: match goal with |- ?g => idtac "Z-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
