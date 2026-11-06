(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA.
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
Ltac2 gd_tbl_A_mpi_mod_mpi_C () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.iff"; "Stdlib.ZArith.BinInt.Z.sgn"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"].


Section CmpWalkM.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (xra sp' gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells asegs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at asegs m P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 < X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis ALX : X mod 8 = 0.
  Hypothesis OX : aobj asegs AL CS m X 16.
  Hypothesis OP : 1 <= n -> aobj asegs AL CS m P (4 * n).
  Hypothesis PBB : 0 <= P /\ P + 4 * n <= 2^64.
  Hypothesis CY : rw_cells asegs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at asegs m Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis SG' : sg' = 1 \/ sg' = -1.
  Hypothesis YB : 0 < Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis ALY : Y mod 8 = 0.
  Hypothesis OY : aobj asegs AL CS m Y 16.
  Hypothesis OQ : 1 <= n' -> aobj asegs AL CS m Q (4 * n').
  Hypothesis QBB : 0 <= Q /\ Q + 4 * n' <= 2^64.
  Hypothesis MI : mem_inv asegs m.

  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX8 := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL + 1)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3 + al_sb AL)).
  Notation SHY8 := (Z_to_bv 64 (Z.shiftr Y 3 + al_sb AL + 1)).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ciR_post (s0 s1 s5 s7 s10 xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.$3.Lpc,$3.(4.(5.$0.R7.(6.(7.Vxra,Vsp',Vgp,Vtp,O:.O9.O8.O?.O>.R6.R5.R4.R3.R2.O7.O6.O5.(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))O=.(8.&40.(:.VAL,))O<.(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))O;.(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))O4.O3.O2.O1.)VF,(8.&40.R1.)Vfc,(<.(2.&40.))Vm,(=.$>.)))(?.(4.(5.$3.R1.+:0320.)(?.(5.$3.(10.Vxs,Vn,)=)(5.$3.Vsg,+1.)))(4.(5.$3.R1.+:02><.)(4.(5.$3.Vsg,-1.)(11.=(10.Vxs,Vn,))))))))))))")
(* [comment removed for export] *).

  Section CIR.
  Variables (s0 s1 s5 s7 s10 xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word).
  Let POST := ciR_post s0 s1 s5 s7 s10 xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6.
  Local Ltac done_at := apply evtA_done; subst POST; unfold ciR_post; deexists 6; split; [reflexivity|].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L66184348993.2 Q22289810348.72Q24418818504.73Q24423392593.72Q29198954429.72Q36081244985.73Q54241215429.72Q56512145356.73Q59435680517.7300000700@00I00R00[00d00m01B01CS2sg2SGS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs1Y2ys2XB3ALX2YBF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Y ys CX SG XB ALX OX YB"] Lemma ciR_sign : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)P,(11.=(10.Vxs,Vn,))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,Vs0,Vs1,R6.R5.R4.R3.R2.Vxa5,Vxa6,Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))Vs5,(8.&40.(:.VAL,))Vs7,(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vs10,(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:02=<.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros xa0 xa1 xa2 xa3 xa4 NZ. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite sx16_small by (clear - SG; lia).
    (* [comment removed for export] *)
    destruct SG as [Es|Es]; rewrite Es in *; zstep.
    - done_at. left. split; [reflexivity| right; exact Es].
    - done_at. right. split; [reflexivity|]. split; [exact Es| exact NZ].
    all: match goal with |- ?g => idtac "CIRSIGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L11014210082.3 L16475646230.76L16475699316.79L23917405863.3 L23970764156.82L29971580958.3 L31326834835.4 L33397803794.4 L36571201320.0 L45380526330.2 L54425655405.3 L55166369148.2 L56393850587.4 L59308546259.3 L59308551419.6 L59308587409.4 L892450547.4   Q24418024571.83Q26295627581.83Q39944472214.83Q42426514348.83Q50458135125.83Q57547169194.83Q57549166911.83Q57549198250.80Q63571026702.80Q8943673138.80 00000800[01>01F01o02702B02C02D02I02Q02V02a02j03;03F03S03h04604K04d05405I05^06306H06VS1n1r2HrS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2HrS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2HrS1k1r2HkS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2Hr2PP2wxS1n1r2HrS1n1r2Hr2K2FSS1P1rS1n1r2HrS1P1rS1n1r2Hr2K2S1n2N12N0S1n2xs2LX1r2Hr2NXS1n1r2Hk2HrS2xs1r2TN3PP'S1P1n2xs2ys1k1r2Hk2HrS2xs2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys3PBB1k1r2Hk2HrS1P2xs2ys1k1r2HkS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS1P1n2xs2ys1k1r2Hk2HrS2xs2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pad Y ys CX HX LX SG XB PB ALX OX OP PBB YB"] Lemma ciR_loop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pk,$13.Pr,$3.Pw,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)P,(5.$13.(14.R4.)R5.)P,(4.(15.+1.R5.)(15.R5.Vn,))P,(5.$3.(10.Vxs,Vn,)(10.Vxs,R6.))P,(5.(2.&40.)R6.(8.&40.(9.VP,(16.(17.+4.R7.)+4.))))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,Vs0,Vs1,R7.(8.&40.R8.)R7.R6.R5.Vxa5,Vxa6,Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))Vs5,(8.&40.(:.VAL,))Vs7,(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vs10,(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:02:0.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w xa3 xa4 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= n) by (clear - Hr; lia). pose proof (OP N1) as OPn.
    destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hr LX; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m P xs (r - 1) wx _ HX NX ltac:(clear - Hr; lia) eq_refl) as RDX.
    replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply ciR_sign. rewrite INV. pose proof (lval_top_nonzero xs r ltac:(clear - Hr; lia) NZ) as TN.
      pose proof (pow32_pos (r - 1) ltac:(clear - Hr; lia)) as PP'. clear - TN PP'. lia.
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LXr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. done_at. left. split; [reflexivity|]. left.
        rewrite INV, (lval_drop_zero xs r) by (first [clear - Hr; lia | rewrite LXr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). apply lval_0.
    all: match goal with |- ?g => idtac "CIRLOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L23100341967.71L33087595724.2 L39172636981.0 L44822653989.3 L55166432096.2 L61929812114.68L61931718958.70Q12370813529.75Q17205383785.74Q24418818504.72Q24423392593.71Q26220321612.71Q29198954429.71Q31649507301.71Q36081244985.72Q37623048587.74Q45132659991.75Q5483112342.74 Q5485174314.75 Q56512145356.72Q59435680517.72Q6143569392.75 00000=00C00D00M00R00b01401K01T01]01f01o02802A02J02S02T02]02f03;03<03ES1X1P2xs1Y2ysS1n2HnSS1n2Hn2K0S1P1nS1X1n2xs1Y2ys2HnS1X1P1n2xs1Y2ys2HnS1X1P2xs1Y2ys2XB3ALX2YBS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysFS1X2xs2ysS1X2xs2ysS1X2xs1Y2ys2XB3ALX2YBFS1X2xs2ys". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Y ys CX HX LX Hn SG XB PB ALX OX OP PBB YB"] Lemma ci_R : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,Vs0,Vs1,R5.R4.R3.R2.R1.Vxa5,Vxa6,Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))Vs5,(8.&40.(:.VAL,))Vs7,(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vs10,(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0274.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xa4. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite zx16_small by (clear - Hn; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn; lia).
    - done_at. left. split; [reflexivity|]. left. rewrite K0. apply lval_0.
    - destruct PB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (ciR_loop (Z.to_nat n) n); [reflexivity| clear - K0 Hn; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "CIR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End CIR.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L39188636933.0 L44841576906.1600000100ISS1a2r02Ha1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="Type"] Lemma shr3_10 : forall a, a mod 8 = 0 -> Z.shiftr (a + 10) 3 = Z.shiftr a 3 + 1.
  Proof. intros a Ha. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. clear - Ha. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L39188636933.0 L44841576906.1600000100ISS1a2r02Ha1q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="Type"] Lemma shr3_8 : forall a, a mod 8 = 0 -> Z.shiftr (a + 8) 3 = Z.shiftr a 3 + 1.
  Proof. intros a Ha. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. clear - Ha. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition ciB_post (wr xt0 xt1 xt2 xa2 xa6 xa7 s3 s4 s5 s8 s9 s11 xt3 xt4 xt5 xt6 : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.$3.Lpc,$3.(4.(5.$0.R7.(6.(7.Vxra,Vsp',Vgp,Vtp,O10.O?.O>.(8.&40.VY,)(8.&40.(9.VY,+:.))R6.R5.O=.R4.R3.R2.O<.O;.O11.O:.O9.O8.(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))O7.O6.(8.&40.(;.VY,+3.))O5.O4.O3.O2.O1.)VF,(8.&40.R1.)Vfc,(<.(2.&40.))Vm,(=.$>.)))(?.(4.(5.$3.R1.+:01?0.)(?.(5.$3.(10.Vys,Vn',)=)(5.$3.Vsg',+1.)))(4.(5.$3.R1.+:0594.)(5.$3.Vsg',-1.))))))))))")
(* [comment removed for export] *).

  Section CIB.
  Variables (wr xt0 xt1 xt2 xa2 xa6 xa7 s3 s4 s5 s8 s9 s11 xt3 xt4 xt5 xt6 : word).
  Let POST := ciB_post wr xt0 xt1 xt2 xa2 xa6 xa7 s3 s4 s5 s8 s9 s11 xt3 xt4 xt5 xt6.
  Local Ltac done_at := apply evtA_done; subst POST; unfold ciB_post; deexists 6; split; [reflexivity|].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L37314936640.72L37327480467.69L39973646689.2 Q12059154310.73Q39212284437.76Q39424119965.76Q49046334496.76Q4958620598.75 Q60511567613.76Q61405460898.73Q61417400191.75Q61418027910.76Q9534297315.73 00000>00L00U00^00g01001<01E01L01U01^01g01nS1X2xs1Y2ys2YBS1X2xs1Y2ys2YBS3sg'3SG'S2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ys2YBS2xs1Y2ysS2xs2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs2ys". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK X xs Q pad' CY SG' YB OY"] Lemma ciB_sign : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R5.R4.Vxa2,R3.R2.R1.Vxa6,Vxa7,Vwr,Vs3,Vs4,Vs5,(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))Vs8,Vs9,(8.&40.(;.VY,+3.))Vs11,Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:01=4.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xa5. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OY (Y + 8) 2.
    (* [comment removed for export] *)
    zstep. rewrite sx16_small by (clear - SG'; lia).
    (* [comment removed for export] *)
    destruct SG' as [Es|Es]; rewrite Es in *; zstep.
    - done_at. left. split; [reflexivity| right; exact Es].
    - done_at. right. split; [reflexivity| exact Es].
    all: match goal with |- ?g => idtac "CIBSIGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L11014210082.3 L1137720866.4  L1962756882.4  L23917405863.3 L23970764156.84L28574840970.2 L31326834835.4 L36257472189.3 L36571201320.0 L47910126524.2 L54425655405.3 L58198864894.81L58198942495.78L59308546259.3 L59308551544.6 L59308587409.4 Q10125995177.85Q26295627581.85Q40946738878.82Q50458135125.85Q612084707.85  Q67028169811.85Q6761749719.85 Q6764271681.85 Q6764303191.82 Q8943673009.82 00000900E00F00N01801=01I01R01S01X01a02E02i03303E03Q03k04904O04_05505K05a06706M06[S2n'1r2HrS2n'1r2Hr2K2FS1k1r2HkS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2Hr2PP2wyS1Q1rS2n'1r2Hr2K2S2n'1r2HrSS1Q1rS2n'1r2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS2n'2N12N0S2n'2ys2LY1r2Hr2NYS2n'1r2Hk2HrS2xs1Q2n'2ys3QBB1k1r2Hk2HrS2xs2ys1k1r2HkS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2ys1k1r2HkS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs1Q2n'2ys1k1r2Hk2HrS2xs2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK X xs pad' XB CY HY LY SG' YB QB OY OQ QBB"] Lemma ciB_loop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pk,$13.Pr,$3.Pw,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)P,(5.$13.(14.R4.)R5.)P,(4.(15.+1.R5.)(15.R5.Vn',))P,(5.$3.(10.Vys,Vn',)(10.Vys,R6.))P,(5.(2.&40.)R6.(8.&40.(9.VQ,(16.(17.+4.R7.)+4.))))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R7.(8.&40.R8.)Vxa2,R7.R6.R5.Vxa6,Vxa7,Vwr,Vs3,Vs4,Vs5,(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))Vs8,Vs9,(8.&40.(;.VY,+3.))Vs11,Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0198.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w xa4 xa5 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= n') by (clear - Hr; lia). pose proof (OQ N1) as OQn.
    destruct QB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Hr LY; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OQn (Q + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m Q ys (r - 1) wy _ HY NY ltac:(clear - Hr; lia) eq_refl) as RDY.
    replace (Q + 4 * (r - 1)) with (Q + (4 * r - 4)) in RDY by (clear; lia).
    zstep. clear RDY. pose proof (limb32_of_read ys r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - apply ciB_sign.
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ By)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn'; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LYr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. done_at. left. split; [reflexivity|]. left.
        rewrite INV, (lval_drop_zero ys r) by (first [clear - Hr; lia | rewrite LYr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). apply lval_0.
    all: match goal with |- ?g => idtac "CIBLOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L1120085281.78 L14972936856.3 L35868517827.2 L39172636981.0 L47548442835.72L47560995072.75L47912431207.2 L50704676279.2 L54258658734.75L54261158930.77L9327403994.74 Q14485421028.82Q20233606338.76Q20246173414.79Q20246661663.78Q24361940092.81Q24363994560.82Q35030107133.79Q39212284437.79Q42349454934.78Q48520856102.76Q50107086626.82Q54200448131.81Q60511567613.79Q67373181291.81Q7748271680.79 Q9534297315.76 00000=00H00N00O00]00k01101901K01_01m02A02J02S02\02e02n03703@03I03R03[03d03k04404@04GS1X2xs1Y1Q2ysS2n'3Hn'2K0S2AL1YSS1X2xs1Y2ys2YBS1X2xs1Y2ys2YBS1Q2n'S2n'3Hn'S1X2xs1Y2n'2ys3Hn'S1X2xs1Y1Q2n'2ys3Hn'S1X2xs1Y2ys2YBS1X2xs1Y1Q2ys2YB3ALYS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS2xs2ysS2xs1Y2ysS2xs1Y2ys2YBS2xs2ys". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK X xs Q pad' XB CY HY LY Hn' SG' YB QB ALY OY OQ QBB"] Lemma ci_B : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxs1,(2.&40.)Pxs2,(2.&40.)Pxs7,(2.&40.)Pxs10,(2.&40.)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)R4.Vwr,R8.Vxa2,R7.R6.R5.Vxa6,Vxa7,R3.Vs3,Vs4,Vs5,(8.&40.(:.VAL,))R2.Vs8,Vs9,R1.Vs11,Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0154.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs10. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OY (Y + 10) 2.
    replace (Z.shiftr (Y + 10) 3 + al_sb AL) with (Z.shiftr Y 3 + al_sb AL + 1) by (rewrite (shr3_10 Y ALY); clear; lia).
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - Hn'; lia). zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn'; lia).
    - done_at. left. split; [reflexivity|]. left. rewrite K0. apply lval_0.
    - destruct QB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (ciB_loop (Z.to_nat n') n'); [reflexivity| clear - K0 Hn'; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "CIB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End CIB.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SL32 : rw_cells asegs m (bv_unsigned sp' + 32) [C8 SHY8].
  Hypothesis SLC : crange CS (bv_unsigned sp' + 32) 8.
  Hypothesis SPB : 0 <= bv_unsigned sp' /\ bv_unsigned sp' + 40 <= 2^64.

  Definition cmRB_post (xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.$3.Lpc,$3.(4.(5.$0.R9.(6.(7.Vxra,Vsp',Vgp,Vtp,O8.O7.O6.(8.&40.VY,)(8.&40.(9.VY,+:.))R8.R7.R6.R5.R4.R3.R2.O5.(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))O4.O3.O2.O1.)VF,(8.&40.R1.)Vfc,(<.(2.&40.))Vm,(=.$>.)))(?.(4.(5.$3.R1.+:035<.)(15.=(16.(17.Vsg,(10.Vxs,Vn,))(17.Vsg',(10.Vys,Vn',)))))(4.(5.$3.R1.+:058<.)(11.(16.(17.Vsg,(10.Vxs,Vn,))(17.Vsg',(10.Vys,Vn',)))=))))))))))))")
(* [comment removed for export] *).

  Section CMRB.
  Variables (xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 : word).
  Let POST := cmRB_post xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6.
  Let V := sg * lval xs n - sg' * lval ys n'.
  Local Ltac done_at := apply evtA_done; subst POST; unfold cmRB_post; deexists 8; split; [reflexivity|].
  Local Notation ST a0 a1 a2 a3 a4 a5 a6 pc :=
    (MS (mkR xra sp' gp tp xt0 xt1 xt2 (Z_to_bv 64 Y) (Z_to_bv 64 (Y + 10)) a0 a1 a2 a3 a4 a5 a6 xa7
             (Z_to_bv 64 X) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 (X + 10)) (Z_to_bv 64 (Y + 8)) SB SHY8 SHX SHX8 SHY SHX8
             xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L52188639198.8L63944976030.800000H00`S1n2sg2xs2n'3sg'2ys1V2HVS1n2sg2xs2n'3sg'2ys1V2HV". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma cm_dec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "PT,$3.Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(?.(5.$3.R7.+1.)(5.$3.R7.-1.))P,(18.(11.R8.=)(11.VV,=))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R8.R7.(8.&40.R9.)R6.R5.R4.R3.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0358.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros T xa0 xa1 xa3 xa4 xa5 xa6 HT HV. al_facts.
    destruct HT as [E|E]; rewrite E in *; zstep.
    - done_at. left. split; [reflexivity|]. fold V. clear - HV. lia.
    - done_at. right. split; [reflexivity|]. fold V. clear - HV. lia.
    all: match goal with |- ?g => idtac "CMDEC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2088038862.8 L58826455508.800000H00`S1n2sg2xs2n'3sg'2ys1V2HVS1n2sg2xs2n'3sg'2ys1V2HV". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma cm_neg : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "PT,$3.Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(?.(5.$3.R7.+1.)(5.$3.R7.-1.))P,(18.(11.=R8.)(11.VV,=))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R8.R7.(8.&40.R9.)R6.R5.R4.R3.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0354.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros T xa0 xa1 xa3 xa4 xa5 xa6 HT HV. al_facts.
    destruct HT as [E|E]; rewrite E in *; zstep.
    - apply (cm_dec (-1)); [right; reflexivity| clear - HV; lia].
    - replace (Z_to_bv 64 (-18446744073709551615)) with (Z_to_bv 64 1) by (apply Z_to_bv_eqm; reflexivity).
      apply (cm_dec 1); [left; reflexivity| clear - HV; lia].
    all: match goal with |- ?g => idtac "CMNEG-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170?L11014201954.11L11014201954.12L11014202083.11L1120085281.87 L16475699316.87L16477430914.84L21743477688.1 L22553357965.11L23100341967.85L23917405863.3 L28574840970.2 L29010565666.73L29971744258.5 L32502960807.9 L3508006412.11 L36259467494.5 L36571201320.0 L40332400465.9 L41773732473.3 L44654450861.3 L45380526330.2 L46720886775.1 L47013807010.12L52188638940.8 L54425655282.3 L54425655405.4 L56840611386.1 L58196651164.87L58198864894.90L59308546259.3 L59308551419.8 L59308551544.8 L59308628179.4 L66151418440.3 Q10125995177.94Q12370813529.89Q14485421028.91Q17205367401.88Q24363994560.91Q24364461956.90Q24415828206.93Q26295627581.91Q26295627581.94Q29651637810.89Q36157561789.91Q37623064971.88Q39944472214.91Q40948640061.91Q41750243048.91Q42426514348.91Q45132659991.89Q50107086626.91Q50458135125.91Q50458135125.94Q54201986939.90Q5483128726.88 Q5485174314.89 Q57547218494.88Q57549166911.91Q57549166911.93Q612084707.93  Q6143569392.89 Q62561324959.89Q63569342106.88Q67028169811.94Q67375772307.90Q6761749716.91 Q6761749719.93 Q6764271681.94 Q8945554086.88 Q8945570098.91 00000>00L00Z01>02502l02o03N04204:04?04g05405O05n06=06>06Y06c06k07007407V07n08608>08A0990:10:A0:W0:o0;:0;C0;k0<Y0=D0=b0>@0>^0?B0?^0@:0@;0@<0@Z0AA0Af0Ag0BO0BP0Bn0CL0Cj0DH0Df0ED0Ee0FF0Fg0GL0Gj0Gk0HO0I80IV0J70JX0K90KU0L1S1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS1k1r2Hk2wx2wyS1X1P1n2sg2xs1Y1Q2n'3sg'2ys1V1k1r2HkS1X1P1n2sg2xs1Y1Q2n'2ys2XB3PBB2YB3QBB1V1k1r2Hk2Rn2HT2PPS1X1P1n2sg2xs1Y1Q2n'2ys2XB3PBB2YB3QBB1V1k1r2Hk2Rn2HT2PPS1rS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K1S1X1P1n2sg2xs1Y1Q2n'3sg'2ys1V1k1r2HkS1k1r2HkS1Q1rS1X1P1n2xs1Y2ys2XB3PBB2YB1V1k1r2Hk2Hr2RnS1n1k1r2Hk2RnS1n2sg2xs2n'3sg'2ys2SG1V2HTS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K2S2n'1k1r2Hk3Rn'SS1n2sg2xs2n'3sg'2ys2SG1V2HTS2n'1r3Rn'S1n1r2RnS1P1rS2sgS2xs2ys1k1r2Hk2wx2wy3LXr3LYr2K12K2S1n2sg2xs2n'3sg'2ys1V2HTS1k1r2HkS1k1r2HkS1rS1X1P1n2sg2xs1Y1Q2n'2ys2XB3PBB2YB3QBB1V1k1r2Hk3Rn'2HT2QPS1X1P1n2sg2xs1Y1Q2n'2ys2XB3PBB2YB3QBB1V1k1r2Hk3Rn'2HT2QPS1n2N12N02n'3N1'S1n2xs2LX1k1r2Hk2Rn2NXS2n'2ys2LY1k1r2Hk3Rn'2NYS1k1r2Hk2K0S1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys3QBB1V1k1r2Hk2HT2QPS1X1P1n2sg2xs1Y1Q2n'3sg'2ys2XB3ALX2YB1V1k1r2HkS1X1P1n2sg2xs1Y1Q2n'3sg'2ys2YB3ALY1V1k1r2HkS1X1n2sg2xs2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Y2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Y2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2Rn2HTS1n2sg2xs2n'3sg'2ys1V1k1r2HkS1n2sg2xs2n'3sg'2ys1V1k1r2HkFFS1X1n2sg2xs2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2Rn2HT2N1S1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk3Rn'2HTFS1P1n2sg2xs2n'3sg'2ys3PBB1V1k1r2Hk2HT2PPFS1n2sg2xs1Y2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Q2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Y2n'3sg'2ys1V1k1r2HkS1X1n2sg2xs2n'3sg'2ys1V1k1r2HkS1X1n2sg2xs2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HTS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HTS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HTS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk3Rn'2HTS1X1n2sg2xs2n'3sg'2ys1V1k1r2HkFS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2Rn2HTS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk3Rn'2HT3N1'S1n2sg2xs1Y2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HTS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HTS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HTS1n2sg2xs2n'3sg'2ys1V1k1r2HkS1n2sg2xs2n'3sg'2ys1V1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Q pad' CX HX LX SG XB PB ALX OX OP PBB CY HY LY YB QB ALY OY OQ QBB"] Lemma cm_loop3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pk,$13.Pr,$3.Pw13,(2.&40.)Pw14,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(5.$13.(14.R7.)R8.)P,(15.=R8.)P,(15.R9.Vn,)P,(15.R:.Vn',)P,(5.$3.Vsg',Vsg,)P,(5.$3.(19.VV,)(17.Vsg,(19.(16.(10.Vxs,R<.)(10.Vys,R<.)))))P,(5.(2.&40.)R<.(8.&40.(16.(17.+4.R=.)+4.)))P,(5.(2.&40.)R<.(8.&40.(9.R>.+1.)))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R<.R;.(8.&40.Vsg,)R>.R=.R:.R9.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:04<0.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w13 w14 xa0 xa1 xa5 xa6 Hk Hr Rn Rn' ES HT -> ->; al_facts.
    - assert (r = 0) as -> by (clear - Hk Hr; lia).
      (* [comment removed for export] *)
      zstep. zstep.
      done_at. left. split; [reflexivity|]. fold V. rewrite !lval_0 in HT. cbn in HT. replace (sg * 0) with 0 in HT by (clear; lia). clear - HT. lia.
    - zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - Hk Hr Rn Hn; lia); clear - K0 Hk; lia|]. clear K0.
      destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Rn LX Hk; lia].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Rn' LY Hk; lia].
      assert (N1 : 1 <= n) by (clear - Hk Rn; lia). assert (N1' : 1 <= n') by (clear - Hk Rn'; lia).
      pose proof (OP N1) as OPn. pose proof (OQ N1') as OQn.
      destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|]. destruct QB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs m P xs (r - 1) wx _ HX NX ltac:(clear - Hk Hr; lia) eq_refl) as RDX.
      replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
      zstep. zstep. shadow_chk OQn (Q + (4 * r - 4)) 4.
      clear RDX.
      (* [comment removed for export] *)
      pose proof (u32ro_read asegs m Q ys (r - 1) wy _ HY NY ltac:(clear - Hk Hr; lia) eq_refl) as RDY.
      replace (Q + 4 * (r - 1)) with (Q + (4 * r - 4)) in RDY by (clear; lia).
      zstep. clear RDY.
      pose proof (limb32_of_read xs r wx NX) as LXr. pose proof (limb32_of_read ys r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      + apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
        apply (cm_dec sg); [exact SG|]. rewrite (cmp_step_gt xs ys r) in HT by (clear - K1 LXr LYr Hk Hr; lia).
        clear - HT SG. lia.
      + apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
        (* [comment removed for export] *)
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
        * apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
          eapply (IH (r - 1)); [clear - Hk; lia| clear - Hk; lia| clear - Rn; lia| clear - Rn'; lia| exact ES
                               | rewrite HT, (cmp_step_eq xs ys r) by (clear - K1 K2 LXr LYr Hk Hr; lia); reflexivity| f_equal; clear; lia| f_equal; clear; lia].
        * apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
          (* [comment removed for export] *)
          zstep. apply (cm_neg sg); [exact SG|]. rewrite (cmp_step_lt xs ys r) in HT by (clear - K2 LXr LYr Hk Hr; lia).
          clear - HT SG. lia.
    all: match goal with |- ?g => idtac "CMLOOP3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L10351590514.3 L10907032063.4 L2424960062.2  L27601760771.4 L32954672704.80L32954672833.79L36412255982.81L36412255982.82L39172636981.0 L39973646689.2 L39973646689.4 L41247890161.4 L42989026026.2 L44872450572.3 L45272779239.3 L51196083649.1 L53768759474.3 L55488359596.80L57415930929.3 L66182251873.4 L66184348993.2 L66253547196.86L66253710909.79L66253711036.80Q16797449996.86Q16797486638.85Q22285569813.85Q22285598390.85Q24418818504.86Q24419117544.85Q24419227723.85Q29203108519.85Q29203227396.85Q30617915122.85Q30618009552.86Q30618418898.86Q30618418898.87Q36081244985.86Q4957673938.85 Q4957792496.86 Q54174821103.86Q54174821103.87Q54253719420.85Q54253846239.85Q54914329697.86Q54914329697.87Q56512145356.86Q59435680517.86Q61417997369.86Q61418091803.8500000800@00F00Q01201S02402S02T02]02f03203:03B03K03N03V03W03`03g03n04L04l05L05g06@06Y07407O07h08C08^09709P09k0:D0:_0;:0;S0;n0<S0=@0=Y0>40>M0>h0?U0?V0@10@JS1n1i2I1S1i1j2K2S1n2HnS1i1j2K12K2S1X2xs1Y1Q2n'2ys2XB2YB3QBB1i1j2J1S1X2xs1Y1Q2n'2ys2XB2YB3QBB1i1j2J1S3sp'1X1n2sg2xs1Y2n'3sg'2ys1V1i1jS3sp'1X1n2sg2xs1Y2n'3sg'2ys1V1iSS3sg'3SG'S3sg'3SG'S1n1i2I13NeiS2n'3Hn'S1i1j2K1S2n'1j2J1S1iS1n1i2I1FS2n'1i2J1S2sg2SGS2sg2SGS1X1P1n2xs1Y2ys2XB3PBB2YB1i2I1S1X1P1n2xs1Y2ys2XB3PBB2YB1i1j2I1S1X1P1n2xs1Y2ys2XB3PBB2YB1i1j2I1S1n2sg2xs1Y2n'3sg'2ys1V1i1jS1n2sg2xs1Y2n'3sg'2ys1V1iS1X1n2sg2xs2n'3sg'2ys1V1iS1X1n2sg2xs2n'3sg'2ys1V1i1jS1X1n2sg2xs2n'3sg'2ys1V1i1jS1X1n2sg2xs2n'3sg'2ys1V1iS1X1n2sg2xs2n'3sg'2ys1V1i1jS1X1n2sg2xs2n'3sg'2ys1V1i1jS1X1n2sg2xs2n'3sg'2ys1V1iS1n2sg2xs1Y2n'3sg'2ys1V1iS1n2sg2xs1Y2n'3sg'2ys1V1i1jS1n2sg2xs1Y2n'3sg'2ys1V1iS1n2sg2xs1Y2n'3sg'2ys1V1i1jS1X1n2sg2xs2n'3sg'2ys1V1i1jS1n2sg2xs1Y2n'3sg'2ys1V1iS1n2sg2xs1Y2n'3sg'2ys1V1i1jS1X1n2sg2xs1Y2n'3sg'2ys2XB2YB3ALY1V1iS1X1n2sg2xs1Y2n'3sg'2ys2XB2YB3ALY1V1i1j2I12K2S1X1n2sg2xs2n'3sg'2ys1V1iS1X1n2sg2xs2n'3sg'2ys1V1i1jS1n2sg2xs1Y2n'3sg'2ys1V1iS1n2sg2xs1Y2n'3sg'2ys1V1i1jS1X1n2sg2xs1Y2n'3sg'2ys2XB3ALX2YB1V1i1j2J12K1FS1n2sg2xs1Y2n'3sg'2ys1V1i1jS1n2sg2xs1Y2n'3sg'2ys1V1i". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Q pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_decide : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pi,$3.Pj,$3.Pxa0,(2.&40.)Pxa2,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(1:.Vxs,Vn,R7.)P,(1:.Vys,Vn',R7.)P,(1;.(4.(5.$3.R9.=)(5.$3.R8.=)))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R8.(8.&40.R:.)R7.(8.&40.R9.)R6.R5.R4.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0454.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros i j xa0 xa2 xa4 xa5 xa6 SX SY NZ. al_facts.
    dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (lval_range xs i ltac:(clear - I1; lia)) as RX. pose proof (lval_range ys j ltac:(clear - J1; lia)) as RY.
    pose proof SL32 as SL32'. pose proof SLC as SLC'. pose proof SPB as SPB'.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - I1 J1 Hn Hn'; lia).
    2: { (* [comment removed for export] *)
      zstep. zstep. zstep. rewrite sx16_small by (clear - SG; lia). zstep.
      apply (cm_dec sg); [exact SG|].
      pose proof (lval_range ys n' ltac:(clear - Hn'; lia)) as RY'. pose proof (SIGF_lt xs n i ys n' j SX SY ltac:(clear - K1; lia)) as LT.
      subst V. clear - SG SG' RY' LT. nia. }
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - I1 J1 Hn Hn'; lia).
    2: { (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. rewrite sx16_small by (clear - SG'; lia). zstep. zstep.
      pose proof (lval_range xs n ltac:(clear - Hn; lia)) as RX'. pose proof (SIGF_lt ys n' j xs n i SY SX ltac:(clear - K1 K2; lia)) as LT.
      destruct SG' as [Es'|Es']; rewrite Es' in *.
      - apply (cm_dec (-1)); [right; reflexivity|]. subst V. rewrite ?Es'. clear - SG RX' LT. nia.
      - replace (Z_to_bv 64 (0 - -1 mod 18446744073709551616)) with (Z_to_bv 64 1) by (apply Z_to_bv_eqm; reflexivity).
        apply (cm_dec 1); [left; reflexivity|]. subst V. rewrite ?Es'. clear - SG RX' LT. nia. }
    (* [comment removed for export] *)
    assert (j = i) as -> by (clear - K1 K2; lia). assert (Nei : i <> 0) by (intros E; apply NZ; split; exact E). clear K1 K2 NZ.
    destruct I3 as [I3|I3]; [exfalso; exact (Nei I3)|]. destruct J3 as [J3|J3]; [exfalso; exact (Nei J3)|].
    pose proof (pow32_pos (i - 1) ltac:(clear - I1 Nei; lia)) as PP.
    assert (LP : forall s xa0' xa3' xa4', s = 1 \/ s = -1 -> sg = s -> sg' = s ->
      evtA asegs AL CS POST (ST xa0' (Z_to_bv 64 i) (Z_to_bv 64 s) xa3' xa4' xa5 xa6 0x0a04b4)).
    { intros s xa0' xa3' xa4' Hs E1 E2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      rewrite <- E1.
      eapply (cm_loop3 (Z.to_nat i) i); [reflexivity| clear - I1; lia| clear - I1; lia| clear - J1; lia| rewrite E1, E2; reflexivity| | f_equal; clear; lia| f_equal; clear; lia].
      subst V. rewrite I2, J2, E2, <- E1. apply sgn_same_sign. exact SG. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite !sx16_small by (clear - SG SG'; lia).
    destruct SG as [Es|Es]; rewrite Es in *; zstep; destruct SG' as [Es'|Es']; rewrite Es' in *; zstep.
    - (* [comment removed for export] *) apply LP; [left; reflexivity| reflexivity| reflexivity].
    - (* [comment removed for export] *)
      zstep. done_at. left. split; [reflexivity|]. rewrite I2, J2, ?Es, ?Es'. clear - RX RY. nia.
    - (* [comment removed for export] *)
      zstep. done_at. right. split; [reflexivity|]. rewrite I2, J2, ?Es, ?Es'. clear - RX RY I3 J3 PP. nia.
    - (* [comment removed for export] *) zstep. apply LP; [right; reflexivity| reflexivity| reflexivity].
    all: match goal with |- ?g => idtac "CMDECIDE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L64501562960.2000008S2sg3sg'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Q pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_zero_j : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pi,$3.Pxf,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(1:.Vxs,Vn,R7.)P,(1:.Vys,Vn',=)P,P,(5.$3.(1<.&40.R8.)=)(1;.(5.$3.R:.=))P,P,(1;.(5.$3.(1<.&40.R9.)=))(5.$3.R;.=)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R9.(8.&40.R;.)R:.R8.R7.R6.R5.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:044<.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros i xf xa0 xa3 xa4 xa5 xa6 SX SY XF0 XF1. al_facts.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      pose proof (XF1 K) as Ei. done_at. left. split; [reflexivity|].
      ddestruct SX as (I1 & I2 & I3). ddestruct SY as (J1 & J2 & J3). rewrite I2, J2, Ei, !lval_0. clear; lia.
    - (* [comment removed for export] *)
      zstep. apply cm_decide; [exact SX| exact SY|]. intros [Ei _]. exact (XF0 K Ei).
    all: match goal with |- ?g => idtac "CMZEROJ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L11014210082.3 L1137720866.4  L1962756882.4  L21411420601.2 L23917405863.3 L23970764156.85L28574840970.2 L31326834835.4 L36257472189.3 L36571201320.0 L43921905810.3 L47910126524.2 L54425655405.3 L58198864894.82L58198890295.79L59308546259.3 L59308551544.6 L59308587409.4 L59308668297.4 Q10125995177.86Q26295627581.86Q40946651798.83Q50458135125.86Q612084707.86  Q67028169811.86Q6761749719.86 Q6764271681.86 Q6764291967.83 Q8943594137.83 00000900E00F00N00V01@01E01Q01Z01[01d01i02202V03:03E03W03c03o04T05005Q05o06P07107R08308T090S2n'1r2HrS2n'1r2Hr2K2FS2n'3Hn'S1k1r2HkS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2Hr2QP2wyS1Q1rS2n'1r2Hr2K2S2n'1r2HrSS2n'1r2HrS1Q1rS2n'1r2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS1X2xs1Y1Q2n'2ys2XB2YB3QBB1k1r2Hk2HrS2n'3N1'2N0S2n'2ys2LY1r2Hr2NYS2n'1r2Hk2HrS2n'1r2Hr2EjS1n2sg2xs1Q2n'3sg'2ys3QBB1V1k1r2Hk2HrS1n2sg2xs2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys1V1k1r2HkS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs1Q2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs2n'3sg'2ys1V1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_loop2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pk,$13.Pi,$3.Pr,$3.Pxf,(2.&40.)Pw,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(5.$13.(14.R5.)R7.)P,(4.(15.+1.R6.)(15.R6.Vn',))P,(1:.Vxs,Vn,R8.)P,(5.$3.(10.Vys,Vn',)(10.Vys,R8.))P,P,(5.$3.(1<.&40.R8.)=)(1;.(5.$3.R;.=))P,P,(1;.(5.$3.(1<.&40.R9.)=))(5.$3.R<.=)P,(5.(2.&40.)R9.(8.&40.(9.VQ,(16.(17.+4.R;.)+4.))))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R:.(8.&40.R=.)R;.(8.&40.R<.)R:.R9.R8.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0410.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i r xf w xa5 xa6 Hk Hr SX INV XF0 XF1 ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1' : 1 <= n') by (clear - Hr; lia). pose proof (OQ N1') as OQn.
    destruct QB as [N0|[QP QAL]]; [exfalso; clear - N0 N1'; lia|].
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY Hr LY; lia].
    dpose SX as (I1 & _ & _).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OQn (Q + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m Q ys (r - 1) wy _ HY NY ltac:(clear - Hr; lia) eq_refl) as RDY.
    replace (Q + 4 * (r - 1)) with (Q + (4 * r - 4)) in RDY by (clear; lia).
    zstep. clear RDY. pose proof (limb32_of_read ys r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
      apply cm_decide; [exact SX| | intros [_ Ej]; clear - Ej Hr; lia].
      split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ By)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn'; lia).
      + eapply (IH i (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| exact SX| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LYr; exact K1]| exact XF0| exact XF1| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. apply cm_zero_j; [exact SX| | exact XF0| exact XF1]. split; [clear - Hn'; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero ys r) by (first [clear - Hr; lia | rewrite LYr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
    all: match goal with |- ?g => idtac "CMLOOP2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L1120085281.74 L14972936856.3 L21411420601.2 L39172636981.0 L47912431207.2 L50704676279.2 L54258658734.71L54261175314.73Q14485421028.78Q16797417357.74Q20246194648.74Q24361956476.77Q24363994560.78Q30617976657.74Q30618418898.75Q42349266321.74Q50107086626.78Q54174821103.75Q54200464515.77Q54914329697.75Q67373197675.7700000K00V00^00_00e00m01?01S02502L02c03:03Q03h04?04V04m05P05g06>06US1X1n2sg2xs1Y1Q2n'3sg'2ys1VS2n'3Hn'2K0S2n'3Hn'SS1Q2n'S2n'3Hn'S1X2xs1Y2n'2ys3Hn'S1X2xs1Y1Q2n'2ys3Hn'S1X1n2sg2xs1Y1Q2n'3sg'2ys2YB3ALY1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1X1n2sg2xs1Y2n'3sg'2ys2XB2YB3ALY1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1VS1n2sg2xs1Y2n'3sg'2ys1V". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Q pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_stage2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pi,$3.Pxf,(2.&40.)Pxa0,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(1:.Vxs,Vn,R7.)P,P,(5.$3.(1<.&40.R7.)=)(1;.(5.$3.R9.=))P,P,(1;.(5.$3.(1<.&40.R8.)=))(5.$3.R:.=)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R8.(8.&40.R:.)R9.R7.R6.R5.R4.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:03>4.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros i xf xa0 xa3 xa4 xa5 xa6 SX XF0 XF1. al_facts. dpose SX as (I1 & _ & _).
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite zx16_small by (clear - Hn'; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn'; lia).
    - (* [comment removed for export] *)
      apply cm_zero_j; [exact SX| | exact XF0| exact XF1]. split; [clear - Hn'; lia|]. split; [rewrite K0; reflexivity| left; reflexivity].
    - destruct QB as [N0|[QP QAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (cm_loop2 (Z.to_nat n') i n'); [reflexivity| clear - K0 Hn'; lia| exact SX| reflexivity| exact XF0| exact XF1| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "CMSTAGE2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L11014210082.3 L1546378976.3  L16475646230.75L16475699316.78L21007906567.2 L23917405863.3 L23970764156.81L29971580958.3 L31326834835.4 L33397803794.4 L36571201320.0 L42164753195.3 L45380526330.2 L54425655405.3 L55166369148.2 L56393850587.4 L58127621921.0 L59308546259.3 L59308551419.6 L59308586639.4 L59308587409.4 L59355849605.0 L64930767917.4 Q24418024571.82Q26295627581.82Q39944472214.82Q42426514348.82Q50458135125.82Q57547169194.82Q57549166911.82Q57549198250.79Q63571026702.79Q8943673138.79 00000800@00c01F01L01T02=02E02P02Q02R02Z02_02g02l03703803A03R03_03j03k04604W05305T06906W07807Y08:08[097S1n1r2HrS1n1r2HrS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2HrS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2HrS1n2HnS1k1r2HkS1X1P1n2xs1Y2ys2XB3PBB2YB1k1r2Hk2Hr2PP2wxS1n1r2HrS1n1r2Hr2K2FSS1n1r2HrS1P1rS1n1r2HrS1P1rS1n1r2Hr2K2SS1n2N12N0S1n2xs2LX1r2Hr2NXS2wx2Bx2K12HlS1n1r2Hk2HrSS1n1r2Hr2K2S1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1P1n2sg2xs2n'3sg'2ys3PBB1V1k1r2Hk2HrS1P1n2sg2xs2n'3sg'2ys1V1k1r2HkS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1P1n2sg2xs2n'3sg'2ys1V1k1r2Hk2HrS1n2sg2xs2n'3sg'2ys1V1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK pad Q pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_loop1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pk,$13.Pr,$3.Pw,(2.&40.)Pxa2,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)P,(5.$13.(14.R6.)R7.)P,(4.(15.+1.R7.)(15.R7.Vn,))P,(5.$3.(10.Vxs,Vn,)(10.Vxs,R8.))P,(5.(2.&40.)R8.(8.&40.(9.VP,(16.(17.+4.R9.)+4.))))(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R9.(8.&40.R:.)R8.R9.R7.R6.R5.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:03:0.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w xa2 xa4 xa5 xa6 Hk Hr INV ->; [exfalso; clear - Hk Hr; lia|]. al_facts.
    assert (N1 : 1 <= n) by (clear - Hr; lia). pose proof (OP N1) as OPn.
    destruct PB as [N0|[PP PAL]]; [exfalso; clear - N0 N1; lia|].
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hr LX; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPn (P + (4 * r - 4)) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs m P xs (r - 1) wx _ HX NX ltac:(clear - Hr; lia) eq_refl) as RDX.
    replace (P + 4 * (r - 1)) with (P + (4 * r - 4)) in RDX by (clear; lia).
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply cm_stage2.
      + split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZ].
      + intros _. clear - Hr; lia.
      + intros KF. exfalso. apply KF. cbn. rewrite bv_unsigned_sx32.
        destruct (Z.ltb_spec (sxz (bv_unsigned wx mod 2 ^ 32)) 1) as [Hl|Hl]; [exfalso; pose proof (proj2 (sxz_zero_iff _ Bx)); unfold sxz in *; destruct (bv_unsigned wx mod 2 ^ 32 <? 2 ^ 31); clear - K1 Hl Bx; lia| reflexivity].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - Hr Hn; lia).
      + eapply (IH (r - 1)); [clear - Hk; lia| clear - Hr K2; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LXr; exact K1]| f_equal; clear; lia].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        apply cm_stage2.
        * split; [clear - Hn; lia|]. split; [| left; reflexivity]. rewrite INV, (lval_drop_zero xs r) by (first [clear - Hr; lia | rewrite LXr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity.
        * intros KF. exfalso. revert KF. cbn. rewrite bv_unsigned_sx32. rewrite (proj2 (sxz_zero_iff _ Bx) K1). cbn. rewrite ?unsigned_lit by (clear; lia). clear. lia.
        * intros _; reflexivity.
    all: match goal with |- ?g => idtac "CMLOOP1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L23100341967.70L33087595724.2 L39172636981.0 L44822653989.3 L55166432096.2 L58127621921.0 L58796964359.2 L59308631013.1 L61929812114.67L61931718958.69Q12370813529.74Q17205383785.73Q24418818504.71Q24423392593.70Q26220321612.70Q29198954429.70Q31649507301.70Q36081244985.71Q37623048587.73Q45132659991.74Q5483112342.73 Q5485174314.74 Q56512145356.71Q59435680517.71Q6143569392.74 00000K00Q00R00[00`00a00g00k01;01M02202I02`03703N03e04<04S04j04k05B05Y06<06=06TS1X1P1n2sg2xs1Y2n'3sg'2ys1VS1n2HnSS1n2Hn2K0S1P1nSS1n2HnS2KFS1X1n2xs1Y2ys2HnS1X1P1n2xs1Y2ys2HnS1X1P1n2sg2xs1Y2n'3sg'2ys2XB3ALX2YB1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VFS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs2n'3sg'2ys1VS1X1n2sg2xs1Y2n'3sg'2ys2XB3ALX2YB1VFS1X1n2sg2xs2n'3sg'2ys1V". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK P pad Q pad' CX HX LX Hn SG XB PB ALX OX OP PBB CY HY LY Hn' SG' YB QB ALY OY OQ QBB SL32 SLC SPB V"] Lemma cm_RB : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mod_mpi_C ()) "Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)(12.$>.VAL,VCS,VPOST,(6.(7.Vxra,Vsp',Vgp,Vtp,Vxt0,Vxt1,Vxt2,(8.&40.VY,)(8.&40.(9.VY,+:.))R7.R6.R5.R4.R3.R2.R1.Vxa7,(8.&40.VX,)(8.&40.(9.VX,+8.))(8.&40.(9.VX,+:.))(8.&40.(9.VY,+8.))(8.&40.(:.VAL,))(8.&40.(9.(9.(;.VY,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VX,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))(8.&40.(9.(;.VY,+3.)(:.VAL,)))(8.&40.(9.(9.(;.VX,+3.)(:.VAL,))+1.))Vxt3,Vxt4,Vxt5,Vxt6,)VF,(8.&40.+:0374.)Vfc,(<.(2.&40.))Vm,(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until xa6. al_facts.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite zx16_small by (clear - Hn; lia).
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - Hn; lia).
    - (* [comment removed for export] *)
      zstep. apply (cm_stage2 n); [| intros KF; exfalso; rewrite unsigned_lit in KF by (clear; lia); clear - KF; lia| intros _; exact K0].
      split; [clear - Hn; lia|]. split; [reflexivity| left; exact K0].
    - destruct PB as [N0|[PP PAL]]; [exfalso; exact (K0 N0)|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (cm_loop1 (Z.to_nat n) n); [reflexivity| clear - K0 Hn; lia| reflexivity| f_equal; clear; lia].
    all: match goal with |- ?g => idtac "CMRB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End CMRB.
End CmpWalkM.
