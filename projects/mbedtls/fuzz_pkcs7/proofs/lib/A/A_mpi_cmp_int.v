(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_cmp_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_mpi_cmp_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_cmp_int () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.A.A_mpi_cmp_mpi.mpi_cmp_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.abs"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition A_MPI_CMP_INT_E : Z := 0x09d8bc.   (* [comment removed for export] *)
Notation MPI_CMP_INT_STACK_A := 16 (only parsing).

Definition mpi_cmp_int_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PLB,(4.$5.)PdX,$6.Pz,$0.Plo,$0.P,(7.O3.R5.R4.R3.)P,P,(8.$9.(:.R4.)$;.)(<.=(=.R5.))P,(>.(?.(10.(11.+2.+1?.))R4.)(<.R4.(11.+2.+1?.)))P,(12.O3.R8.)P,(13.O2.)P,(14.O2.R2<.)P,(15.O3.O2.R;.)P,(16.O3.O2.R2>.R<.(17.R:.)+10.)P,P,(?.+1.(18.R;.))(16.O3.O2.R30.R>.(=.R<.)(19.+4.(18.R<.)))P,(1:.O3.R>.R:.(1;.&40.R2>.))P,(?.=R;.)P,(?.R<.(1<.(1;.&40.R30.)+10.))P,(8.$0.(1=.(1;.&40.R31.)+10.)=)P,(1>.R34.R>.(1<.(1;.&40.R32.)R>.))P,(1?.(?.(20.(17.R11.)+10.)R?.)(?.(1;.&40.R33.)(17.R11.)))P,P,(?.+1.(18.R12.))(1?.(?.(20.(=.R13.)(19.+4.(18.R13.)))R11.)(?.(1;.&40.R35.)(=.R13.)))P,(8.(1.&40.)R2=.(21.&40.(17.R13.)))P,(8.(1.&40.)R2=.(21.&40.R13.))(22.O3.O2.R39.(23.O3.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.(24.(1<.(25.R15.)R14.))R13.R17.)(26.(27.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(21.&40.O1.)R18.(28.(1.&40.))R17.(29.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m mm : mem) (lo : Z) (junk : list byte).
  Variables (X P n sg : Z) (xs : list word) (pad : word) (z : Z).
  Hypothesis CX : rw_cells asegs mm X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at asegs mm P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis Hz : -2^31 <= z < 2^31.
  Hypothesis MI : mem_inv asegs mm.
  Hypothesis ALX : X mod 8 = 0.
  Hypothesis OX : aobj asegs AL CS mm X 16.
  Hypothesis OP : 1 <= n -> aobj asegs AL CS mm P (4 * n).
  Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk asegs mm lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(lo, bv_unsigned sp)] m mm.
  Hypothesis WM : wmono asegs m mm.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis PBB : 0 <= P /\ P + 4 * n <= 2^64.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation ABSZ := (Z_to_bv 64 (bv_swrap 32 (Z.abs z))).
  Notation S30 := (Z_to_bv 64 (z ≫ 30)).
  Let POST := mpi_cmp_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (sg * lval xs n - z)) lo m.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L31399144472.75L32049487064.75L3832275385.76 Q15641501786.76Q9840988985.76 00000;00D00V00`00nS2sp1X1P2xsS2sp1X2xsS2sp2lo1X1P2xs3SLOS2sp2lo2xsS2sp2lo2xs3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk X P MI FR ST MU WM LO0 SLO SCS SPR"] Lemma i_ret : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Pxt0,(1.&40.)Pxt1,(1.&40.)Pxt2,(1.&40.)Pxa1,(1.&40.)Pxa2,(1.&40.)Pxa3,(1.&40.)Pxa4,(1.&40.)Pxa5,(1.&40.)Pxa6,(1.&40.)Pxa7,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(21.&40.(24.(1<.(19.Vsg,(2;.Vxs,Vn,))Vz,)))R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(21.&40.+9=9:4.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    intros. al_facts. pose proof FR as FR'. pose proof MU as MU'. pose proof WM as WM'.
    zstep. zstep. release_frame FR' ST (bv_unsigned sp). zstep.
    apply evtA_done. subst POST. unfold mpi_cmp_postA. deexists 15. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI| assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L21565147537.3 L37952971835.2 L38570215867.73L52526760875.73L59589536811.7300000800=00>00D00JS1z2NE1HS1z1HFS1X2xsS1X2xs". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk X P Hz MI FR ST MU WM LO0 SLO SCS SPR"] Lemma i_negsign : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Pxt0,(1.&40.)Pxt1,(1.&40.)Pxt2,(1.&40.)Pxa0,(1.&40.)Pxa1,(1.&40.)Pxa2,(1.&40.)Pxa3,(1.&40.)Pxa4,(1.&40.)Pxa5,(1.&40.)Pxa6,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)P,(2<.(8.$0.Vz,=))P,(8.$0.(2;.Vxs,Vn,)=)(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R10.R?.R>.Vs0,Vs1,R=.R<.R;.R:.R9.R8.R7.(21.&40.(2=.Vz,+1>.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(21.&40.+9=99<.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros NE V0. al_facts.
    zstep. zstep. rewrite to_sign64 by exact Hz.
    match goal with |- context [Z_to_bv 64 (0 - ?v)] =>
      replace (Z_to_bv 64 (0 - v)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret|] end.
    rewrite V0, Z.mul_0_r. apply Z_to_bv_eqm. destruct (Z.ltb_spec z 0); [rewrite Z.sgn_pos by (clear - H; lia)| rewrite Z.sgn_neg by (clear - H NE; lia)]; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L11447730086.127L11668836897.79 L11668954808.82 L14948324624.83 L14948324753.82 L2211643683.1   L23100341967.80 L23881756466.2  L27376338525.5  L28984363690.6  L30436581548.83 L31073374752.6  L36571201320.0  L36699230869.5  L37000197732.85 L39280637297.0  L41790136718.5  L57857825604.85 L57995725721.85 L59308546259.3  L59308551419.5  L61876316679.2  L7355979690.5   Q12370813529.82 Q17207247366.81 Q18685009588.81 Q1954359180.84  Q26295627581.84 Q27852559322.84 Q29604973977.84 Q29651637810.82 Q35962453809.85 Q37625444836.81 Q39698791082.81 Q46138256361.81 Q47203011511.84 Q47203114201.81 Q47204945698.84 Q5485174314.82  Q5485443065.81  Q57549000273.81 Q6143569392.82  Q62204707499.84 Q63571230453.81 Q8943731401.81  00000100J00c00d00e00h01501;01G01V01W01f01g02302402502A02B02O02X02g02m03903M03X03h04904B04R04b04c04d04o05:05J05U05`05k06606A06L06W06b07207;FS1X1P1n2xs1z2XB3PBB2N12wxS1X1P1n2xs1z2XB3PBB2N12wxFFS1PS1X1P2xs1z2wxS1z2HzS1z2SS2wx2K1S1z2SS2wx2K12K2FS1z2SS2wx2K12K2SS1z2SS2wx2K1FSS1z2SS2wx2K2FS1X1P2xs1z2wxS1n2N12N0S1n2xs2LX2N12NXS2xs1ES1z2SS2wx2K2S1X1P2xs1z2XB3ALX2wxS1X2xs1z2wxS1P1n2xs1z2N12wxS1P1n2xs1z3PBB2wxS2xs1z2wxS1P1n2xs1z2N12wxS1P1n2xs1z2N12wxFFS1X2xs1z2wxS1P2xs1z2wxS1P1n2xs1z2N12wxS1P2xs1z2wxS1P2xs1z2wxS1P2xs1z2wxS1X2xs1z2wxS1X2xs1z2wxS1P2xs1z2wxS1X2xs1z2wxS1P2xs1z2wxS1P1n2xs1z2N12wxS2xs1z2wx". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad CX HX LX SG XB PB Hz MI ALX OX OP FR ST MU WM LO0 SLO SCS SPR PBB"] Lemma i_tail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Ps,$0.Pxt0,(1.&40.)Pxt1,(1.&40.)Pxt2,(1.&40.)Pxa1,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)P,(8.$0.R9.Vsg,)P,(8.$0.(2;.Vxs,Vn,)(2;.Vxs,+1.))P,(?.+1.Vn,)P,(2<.(8.$0.Vz,=))P,(<.=(19.Vsg,Vz,))(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(21.&40.VX,)R:.(21.&40.R>.)(21.&40.(2>.VAL,))(21.&40.(20.(2=.VX,+3.)(2>.VAL,)))(21.&40.(2?.&20.(30.Vz,)))(21.&40.+1.)(21.&40.(2=.Vz,+1>.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(21.&40.+9=9=4.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Es IV N1 NE SS. subst s. al_facts.
    pose proof (OP N1) as OPn. destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    pose proof (swrap32_mod64 (Z.abs z)) as AZ. rewrite (Z.mod_small (Z.abs z)) in AZ by (clear - Hz; lia). change (2^64)%Z with 18446744073709551616%Z in AZ.
    destruct (nth_error xs 0%nat) as [wx|] eqn:NX; [| apply nth_error_None in NX; cbn in NX; exfalso; clear - NX N1 LX; lia].
    pose proof (limb32_of_read xs 1 wx NX) as LXr. change (Z.to_nat (1 - 1)) with 0%nat in LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    assert (V1 : lval xs 1 = limb32 xs 0).
    { pose proof (lval_succ xs 0 ltac:(clear; lia)) as E. rewrite lval_0 in E. change (2 ^ (32 * 0)) with 1 in E. change (Z.to_nat 0) with 0%nat in E. change (0 + 1) with 1 in E. clear - E. lia. }
    assert (Ba : 0 <= Z.abs z < 2^32) by (clear - Hz; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (P + (4 * 1 - 4)) 4 || shadow_chk OPn (P + 0) 4 || shadow_chk OPn P 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs mm P xs 0 wx _ HX NX ltac:(clear; lia) eq_refl) as RDX.
    replace (P + 4 * 0) with (P + 0) in RDX by (clear; lia).
    zstep || (replace (P + 0) with P in RDX by (clear; lia); zstep). clear RDX.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32, ?AZ in K1.
    - apply (proj1 (sxz_lt_iff _ _ Ba Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
      rewrite IV, V1, LXr. destruct SG as [-> | ->]; [apply Z.sgn_pos; clear - K1 SS Hz; lia| apply Z.sgn_neg; clear - K1 SS Hz; lia].
    - apply (proj1 (sxz_le_iff _ _ Bx Ba)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32, ?AZ in K2.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_le_iff _ _ Ba Bx)) in K2.
        zstep. zstep. zstep. zstep.
        replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
        rewrite IV, V1, LXr. destruct SG as [-> | ->]; apply Z.sgn_null; clear - K1 K2 SS Hz; lia.
      + apply (proj1 (sxz_lt_iff _ _ Bx Ba)) in K2.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        replace (Z_to_bv 64 (0 - sg mod 18446744073709551616)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret|].
        apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_r. f_equal.
        rewrite IV, V1, LXr. destruct SG as [-> | ->]; [apply Z.sgn_neg; clear - K2 SS Hz; lia| apply Z.sgn_pos; clear - K2 SS Hz; lia].
    all: match goal with |- ?g => idtac "ITAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00n0?L10351590514.3 L2424315261.2  L27374205926.4 L27376689812.4 L29074168500.80L29074168500.84L29074177661.77L29074259581.81L29872086579.4 L29971605727.2 L32954672704.78L32954672833.77L33263794707.3 L36692897582.4 L36699230482.4 L37584535605.6 L38557321885.74L38557611298.75L38557611814.85L39220637093.0 L41250042025.2 L45130434338.1 L46074207724.2 L487262474.5   L49913194515.3 L53519152530.75L55588686165.0 L57261330391.3 L57467543336.3 L57718878797.2 L59308586764.3 L59308628304.4 L59308668168.3 L59308668297.3 L59314873579.4 L59576979634.75L62338422136.8 L65271643703.0 L66184348993.2 L66253710909.77L66253711036.78L935128771.3   Q22285549238.83Q22285598390.81Q22285631880.84Q22285631880.86Q22286196081.83Q22286196081.85Q39212284437.84Q39212284437.86Q4926406185.84 Q4926406185.86 Q54253886744.83Q54253886744.85Q56761401107.84Q56761401107.86Q60511567613.84Q60511567613.86Q63231384938.83Q63231434090.81Q9538382329.83 Q9538464249.81 00000800>00H00T00a00l01901D01O01U01V01W01`01j02602F02G02H02I02J02P02T02Z02e02m03503603>03G03M03V03\03e03m04504?04Q04R04Y05105I05Q05Y05a05i06106906A06I06Q06Y06a06i07107<07G07M07S07[07c07i07oS1n1i2I1S1z2K4S2xs1z1i1HS2xs1z2I32PzS1X2xs2XB1i1jS1X2xs2XB1iS1X2xs2XB1i1jS1X2xs2XB1iS2xs1i2I31HS1n2I1FFS1i2K22K1S2xs1z1i1HS2xs1z2R12K4S2xs1z2Hz1i2I31HFFFSS1i2K1S2sgS1i2K1S1n1i2I12K1S1z2Hl1HS1X2xs1iSS1z2Hz1HS1z2NE2HlS1z2PzS1z2K42HmS1j2K1S1i2I32EiS1j1H2EjS1z2Hz1ES1X2xs1z1iS1n1z1i2I11j2Hj2K2SS2sg2SGS1X1P1n2xs2XB3PBB1i2I11jS1X1P1n2xs2XB3PBB1i2I11jS1z2Hz1HS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs1iS1X2xs2XB1iS1X2xs2XB1iS2xs1iS2xs1iS1X2xs1iS1X2xs1iS2xs1iS2xs1i". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad CX HX LX SG XB PB Hz MI ALX OX OP FR ST MU WM LO0 SLO SCS SPR PBB"] Lemma i_stage2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Pi,$0.Pxt,(1.&40.)Pw5,(1.&40.)Pw12,(1.&40.)Pxt2,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)P,(31.Vxs,Vn,R9.)P,P,(8.$0.(1;.&40.R9.)=)(8.$0.R;.=)P,P,(2<.(8.$0.(1;.&40.R:.)=))(2<.(8.$0.R<.=))(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R:.R;.R8.Vs0,Vs1,(21.&40.VX,)(21.&40.Vz,)R9.(21.&40.(2>.VAL,))(21.&40.(20.(2=.VX,+3.)(2>.VAL,)))(21.&40.(2?.&20.(30.Vz,)))(21.&40.R<.)(21.&40.(2=.Vz,+1>.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(21.&40.+9=960.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros SX XT0 XT1. al_facts. dpose SX as (I1 & I2 & I3).
    pose proof (lval_range xs i ltac:(clear - I1; lia)) as RX.
    pose proof (bv_unsigned_in_range 64 xt) as XTR. unfold bv_modulus in XTR. cbn [Z.pow Z.of_N Pos.pow] in XTR.
    assert (ZM : z mod 18446744073709551616 = 0 <-> z = 0).
    { split; intros E; [| rewrite E; reflexivity]. destruct (Z.lt_ge_cases z 0).
      - replace (z mod 18446744073709551616) with (z + 2^64) in E by (symmetry; rewrite <- (Z.mod_add z 1 18446744073709551616) by (clear; lia); apply Z.mod_small; clear - H Hz; lia). exfalso; clear - E H Hz; lia.
      - rewrite Z.mod_small in E by (clear - H Hz; lia). exact E. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0; rewrite ?(Z.mod_small (bv_unsigned xt)) in K0 by exact XTR.
    - (* [comment removed for export] *)
      apply Z.lor_eq_0_iff in K0. destruct K0 as [Kz Kt]. apply (proj1 ZM) in Kz. pose proof (XT0 Kt) as Ei.
      zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
      rewrite I2, Ei, lval_0, Kz. clear; lia.
    - (* [comment removed for export] *)
      zstep. set (j := Z.b2z (0 <? z mod 18446744073709551616)) in *.
      assert (Hj : (j = 0 /\ z = 0) \/ (j = 1 /\ z <> 0)).
      { subst j. destruct (Z.eq_dec z 0) as [->|NE]; [left; split; reflexivity| right; split; [| exact NE]].
        destruct (Z.ltb_spec 0 (z mod 18446744073709551616)) as [Hl|Hl]; [reflexivity|]. exfalso. apply NE. apply (proj1 ZM).
        pose proof (Z.mod_pos_bound z 18446744073709551616 ltac:(clear; lia)). clear - Hl H. lia. }
      clearbody j.
      assert (NZ : ~ (i = 0 /\ z = 0)).
      { intros [Ei Ez]. apply K0. rewrite Ez. change (0 mod 18446744073709551616) with 0. rewrite Z.lor_0_l.
        destruct (Z.eq_dec (bv_unsigned xt) 0) as [E|E]; [exact E| exfalso; exact (XT1 E Ei)]. }
      clear K0.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - I1 Hn Hj; lia).
      2: { (* [comment removed for export] *)
        zstep. zstep. zstep. shadow_chk OX (X + 8) 2. zstep. rewrite sx16_small by (clear - SG; lia). zstep.
        replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
        destruct I3 as [->|I3]; [exfalso; clear - K1 Hj; lia|]. rewrite I2.
        assert (Z.abs z < lval xs i).
        { destruct Hj as [[-> ->]|[-> NE]]; [pose proof (pow32_pos (i - 1) ltac:(clear - K1; lia)); clear - H I3; lia|].
          pose proof (pow32_le 1 (i - 1) ltac:(clear - K1; lia)). clear - H I3 Hz. change (2 ^ (32 * 1)) with 4294967296 in H. lia. }
        destruct SG as [-> | ->]; [apply Z.sgn_pos; clear - H; lia| apply Z.sgn_neg; clear - H; lia]. }
      (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - I1 Hn Hj; lia).
      2: { (* [comment removed for export] *)
        assert (i = 0 /\ j = 1) as [Ei Ej] by (clear - K1 K2 I1 Hj; lia).
        destruct Hj as [[? ?]|[_ NE]]; [exfalso; clear - Ej H; lia|].
        apply i_negsign; [exact NE| rewrite I2, Ei; apply lval_0]. }
      assert (i = 1 /\ j = 1) as [Ei Ej] by (destruct Hj as [[-> ->]|[-> NE]]; [exfalso; apply NZ; split; [clear - K1 K2 I1; lia| reflexivity]| clear - K1 K2; lia]).
      destruct Hj as [[? _]|[_ NE]]; [exfalso; clear - Ej H; lia|]. clear K1 K2 NZ.
      destruct I3 as [I3|I3]; [exfalso; clear - I3 Ei; lia|]. rewrite Ei in I1, I2, I3. change (2 ^ (32 * (1 - 1))) with 1 in I3.
      pose proof (lval_range xs 1 ltac:(clear; lia)) as R1. assert (N1 : 1 <= n) by (clear - I1; lia).
      rewrite Ei.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX (X + 8) 2. zstep. rewrite !sx16_small by (clear - SG; lia). zstep.
      destruct SG as [Es|Es]; rewrite Es.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K4; zify_cond K4.
        * (* [comment removed for export] *) apply (proj1 (shr30_neg_iff z Hz)) in K4.
          zstep. zstep. replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
          rewrite I2, Es. apply Z.sgn_pos. clear - K4 R1; lia.
        * assert (Pz : 0 < z) by (destruct (Z.lt_ge_cases z 0) as [Hl|Hl]; [exfalso; pose proof (proj2 (shr30_neg_iff z Hz) Hl) as Hm; clear - K4 Hm; lia| clear - Hl NE; lia]). clear K4.
          apply (i_tail 1); [symmetry; exact Es| exact I2| exact N1| exact NE| rewrite Es; clear - Pz; lia].
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K4; zify_cond K4.
        * apply (proj1 (shr30_neg_iff z Hz)) in K4.
          apply (i_tail (-1)); [symmetry; exact Es| exact I2| exact N1| exact NE| rewrite Es; clear - K4; lia].
        * assert (Pz : 0 < z) by (destruct (Z.lt_ge_cases z 0) as [Hl|Hl]; [exfalso; pose proof (proj2 (shr30_neg_iff z Hz) Hl) as Hm; clear - K4 Hm; lia| clear - Hl NE; lia]). clear K4.
          (* [comment removed for export] *)
          zstep. zstep. zstep. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal].
          rewrite I2, Es. apply Z.sgn_neg. clear - Pz I3; lia.
    all: match goal with |- ?g => idtac "ISTAGE2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L11014210082.3 L1546378976.3  L16475646230.75L16475699316.78L21007906567.2 L23917405863.3 L23970764156.81L29971580958.3 L31326834835.4 L33397803794.4 L36571201320.0 L42164753195.3 L45380526330.2 L54425655405.3 L55166369148.2 L56393850587.4 L59308546259.3 L59308551419.6 L59308587409.4 L64930767917.4 Q24418024571.80Q26295627581.80Q39944472214.80Q42426514348.80Q50458135125.80Q57547169194.80Q57549166911.80Q57549198250.77Q63571026702.77Q8943673138.77 00000800@00[01601<01D01e01m02802902:02B02G02O02T02_02h03903D03O03a03l04>04T04a05305E05W05i064S1n1r2HrS1n1r2HrS1X1P1n2xs2XB3PBB1k1r2Hk2HrS1X1P1n2xs2XB3PBB1k1r2Hk2HrS1n2HnS1k1r2HkS1X1P1n2xs2XB3PBB1k1r2Hk2Hr2PP2wxS1n1r2HrS1n1r2Hr2K2FSS1n1r2HrS1P1rS1n1r2HrS1P1rS1n1r2Hr2K2S1n2N12N0S1n2xs2LX1r2Hr2NXS1n1r2Hk2HrS1n1r2Hr2K2S1P1n2xs1k1r2Hk2HrS2xs1k1r2HkS1P1n2xs1k1r2Hk2HrS1P1n2xs3PBB1k1r2Hk2HrS1P2xs1k1r2HkS1P1n2xs1k1r2Hk2HrS1P1n2xs1k1r2Hk2HrS1P1n2xs1k1r2Hk2HrS1P1n2xs1k1r2Hk2HrS2xs1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk pad CX HX LX Hn SG XB PB Hz MI ALX OX OP FR ST MU WM LO0 SLO SCS SPR PBB"] Lemma i_loop1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Pk,$32.Pr,$0.Pw12,(1.&40.)Pxt,(1.&40.)Pxt2,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)P,(8.$32.(33.R8.)R9.)P,(>.(?.+1.R9.)(?.R9.Vn,))P,(8.$0.(2;.Vxs,Vn,)(2;.Vxs,R:.))P,(8.(1.&40.)R:.(21.&40.(20.VP,(1<.(19.+4.R;.)+4.))))(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R;.R:.R9.Vs0,Vs1,(21.&40.VX,)(21.&40.Vz,)R;.(21.&40.(2>.VAL,))(21.&40.(20.(2=.VX,+3.)(2>.VAL,)))(21.&40.(2?.&20.(30.Vz,)))(21.&40.R<.)(21.&40.(2=.Vz,+1>.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(21.&40.+9=920.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w12 xt xt2 xt3 xt4 xt5 xt6 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= n) by (clear - Hr; lia). pose proof (OP N1) as OPn.
    destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hr LX; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs mm P xs (r - 1) wx _ HX NX ltac:(clear - Hr; lia) eq_refl) as RDX.
    replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply i_stage2.
      + split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
      + intros KF. exfalso. apply K1. rewrite bv_unsigned_sx32 in KF. exact KF.
      + intros _. clear - Hr; lia.
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LXr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        apply i_stage2.
        * split; [clear - Hn; lia|]. split; [| left; reflexivity]. rewrite INV, (lval_drop_zero xs r) by (first [clear - Hr; lia | rewrite LXr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
        * intros _; reflexivity.
        * intros KF. exfalso. apply KF. rewrite bv_unsigned_sx32. apply (proj2 (sxz_zero_iff _ Bx)). exact K1.
    all: match goal with |- ?g => idtac "ILOOP1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00a0?L14946119086.76L23100341967.77L25080995374.2 L33087595724.2 L38555126942.76L38557611169.76L39172636981.0 L41872764395.74L44822653989.3 L45130434338.1 L46160487540.74L46164721063.71L5262012942.76 L55166432096.2 L57261330391.3 L59314873579.4 L59579459854.76L61929812114.74L61931718958.76L65271643703.0 L68512857134.2 L935128771.3   Q1219017780.75 Q12370813529.79Q17205383785.78Q21798041355.75Q23150033886.75Q26207421841.75Q26207721832.76Q26220321612.73Q31394594844.75Q31654082872.75Q37623048587.78Q39212284437.76Q41126203749.75Q4143427880.75 Q43925228937.76Q44034257392.75Q53519952433.75Q5483112342.78 Q5485174314.79 Q59531472556.75Q60511567613.76Q60697995187.76Q6143569392.79 Q63037100374.75Q66715549212.75Q8884992016.73 Q9534297315.73 00000100900?00E00F00G00H00Q00Z00^00g01001;01@01H01Q01Y01d02102202802@02M02\02b02c03003603<03B03F03L03R03X03Y03Z03`03l04904?04E04F04J04S04Y04e05105705;FS1X1P2xsS1z2HzS1n2HnFFSS2AL1X2xsS1n2Hn2K0S2sgS1X2xs2XBS1X2xs2XBS1X1P2xs2XBS1P1nS1z2Hz1HS1z2Hz2K1S1X1P2xsS1X1n2xs2HnS1X1P1n2xs2HnSS1z2HzS1z2Hz1HS2AL2xs5ALWF'S1X1P2xs2XB3ALXS1X2xsFS2AL2xs5ALWF'S1X2xsS1X2xsS1X2xsS2xsS1X2xsS1X2xsS1X2xsFFS1X2xsS2AL2xs4IMG'S2AL2xs5ALWF'S1X2xsS1X2xsFS2xsS1X2xs2XBS1X2xsS2AL2xs4IMG'S2AL2xs4IMG'S1X2xsS2xs". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK junk P pad CX HX LX Hn SG XB PB Hz MI ALX OX OP FR ST MU WM LO0 SLO SCS SPR PBB"] Lemma i_main : ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_int ()) "Pxt0,(1.&40.)Pxt1,(1.&40.)Pxt2,(1.&40.)Pxa2,(1.&40.)Pxa3,(1.&40.)Pxa4,(1.&40.)Pxa5,(1.&40.)Pxa6,(1.&40.)Pxa7,(1.&40.)Pxt3,(1.&40.)Pxt4,(1.&40.)Pxt5,(1.&40.)Pxt6,(1.&40.)P,(15.$2:.VAL,Vmm,)(22.$2:.VAL,VCS,VPOST,(26.(27.Vra,(21.&40.(20.(1;.&40.Vsp,)-10.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(21.&40.VX,)(21.&40.Vz,)R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(21.&40.+9=8<4.)Vfc,(28.(1.&40.))Vmm,(29.$2:.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros AB. al_facts.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - Hn; lia). zstep. rewrite ?signed_lit_small by (clear - Hz; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn; lia).
    - (* [comment removed for export] *)
      assert (V0 : lval xs n = 0) by (rewrite K0; apply lval_0).
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *) apply i_negsign; [| exact V0]. intros Ez. apply K1. rewrite Ez. reflexivity.
      + (* [comment removed for export] *)
        assert (Ez : z = 0).
        { destruct (Z.lt_ge_cases z 0).
          - replace (z mod 18446744073709551616) with (z + 2^64) in K1 by (symmetry; rewrite <- (Z.mod_add z 1 18446744073709551616) by (clear; lia); apply Z.mod_small; clear - H Hz; lia). exfalso; clear - K1 H Hz; lia.
          - rewrite Z.mod_small in K1 by (clear - H Hz; lia). exact K1. }
        zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - z))); [apply i_ret| f_equal]. rewrite V0, Ez. clear; lia.
    - destruct PB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite sint_abs32 by (clear - Hz; lia).
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (i_loop1 (Z.to_nat n) n); [reflexivity| clear - K0 Hn; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "IMAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?K8159284910.76 L1685717371.0  L19945316590.2 L20433961190.72L23515373696.2 L32049487064.70L43059266230.70L46748113268.70L57394221385.8 L8164022338.2  L9164419877.5  P23511823980.76Q15643324129.72Q25513505925.75Q45914037331.73Q49698585326.74Q58146298210.75Q67528989526.76Q9843367298.72 00000W00X00_00j00k01601H01S01T01U01`02J02X03803F03^04B04f058S2ra2sp2dX2lo3SLO2XS3PBB2HB5Ha_st5Hl_stSS2sp2loS2sp2dX3PBBFS2sp2dX3PBBS2sp2dX2lo3SLO3PBBS2sp2dX3PBBFFS2dX2LX3PBBS2ra2sp2dX2lo3SLO2PS2LX3PBB2HB5Ha_st5Hl_stS2sp2dX2lo3PBBS2ra2sp2dX2lo3PBB2HB5Ha_st5Hl_stS2sp2dX3PBB2HBS2sp2dX3SPR3PBB2HB5Ha_stS2ra2sp2dX2lo3SLO3PBB2HB5Ha_st5Hl_stS2ra2sp2dX2lo3SLO3PBB2HB5Ha_st5Hl_stS2sp2dX2lo3SLO3PBB". (* [comment removed for export] *)
Theorem A_mpi_cmp_int_spec : forall AL, asan_img_ok AL -> mpi_cmp_int_stmtA asegs AL A_MPI_CMP_INT_E.
Proof.
  intros AL IMG. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E. intros until lo. intros HX PX Hz MI ALWF CSOK AB OX OP ST LO0 SLO SPA SCS XS PS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  pose proof (proj1 (proj2 (proj1 HX))) as ALX.
  pose proof (bytes_at_bound _ _ _ _ BX) as PBB. rewrite u32s_length in PBB.
  unfold mpd_val. fold (mpd_abs dX). rewrite !mpd_abs_lval by assumption.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply i_main; try eassumption; try reflexivity.
  all: try (clear - NX LX PBB PBX; lia).
  all: try (intros N1; destruct (PS N1); [left| right]; assumption).
  all: try (intros N1; eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m);
            [unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]
            | exact MU | exact (OP N1)]).
  all: match goal with |- ?g => idtac "CMPINT-TOP-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
