(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_rsa_check_context.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_mpi_cmp_int A_mpi_bitlen.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Ltac2 gd_tbl_A_rsa_check_context () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.RepRsa.rsa_st"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.RepRsa.rsa_head_cells"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.RepRsa.r_N"; "OSSVerify.KrLib.Spec.RepRsa.r_E"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Spec.RepRsa.RSA_CTX_SIZE"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "rsa_ctxck_postA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"].


Definition A_RSA_CHECK_CONTEXT : Z := 0x0b14c8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_CTXCK_STACK_A := 96 (only parsing).

Definition rsa_ctxck_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_context ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.O15.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O2.(10.&40.O13.))(11.(=.$>.$>.)))O1.R1.)(4.(12.O15.O1.R1.)(4.(13.O15.R1.)(14.O15.R1.O2.(10.&40.O13.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_check_context_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_context ()) "PCS,P,$>.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(15.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(16.$17.)PC,$>.Pr,$18.Plo,$>.P,(19.O3.R5.R3.(1:.R2.))P,(4.(1;.=(1<.R3.))(1=.(1<.R3.)(1>.+2.+40.)))P,(1?.O3.R7.R6.(20.R4.))P,(1?.O3.R8.R7.(21.R5.))P,(5.$>.(22.(20.R6.))(23.R7.+10.))P,(5.$>.(22.(21.R7.))(23.R8.+20.))P,(24.(5.$25.(26.(20.R8.))$27.))P,(24.(5.$25.(26.(21.R9.))$27.))P,P,(5.$25.(26.(20.R:.))$28.)(1=.=(29.(20.R;.)))P,P,(5.$25.(26.(21.R;.))$28.)(1=.=(29.(21.R<.)))P,(5.$>.(2:.R=.+8.)=)P,(1=.=R>.)P,(1;.(23.R?.$2;.)(1>.+2.+40.))P,(13.O3.R12.)P,(5.$>.(2:.(10.&40.R34.)+2.)=)P,(2<.O2.)P,(2=.O2.R37.)P,(2>.O3.O2.R16.)P,(2?.O3.O2.R39.R17.R15.+30.)P,P,(1;.+1.(30.(20.R15.)))(2?.O3.O2.R3;.R19.(29.(20.R16.))(31.+4.(30.(20.R16.))))P,P,(1;.+1.(30.(21.R16.)))(2?.O3.O2.R3<.R1:.(29.(21.R17.))(31.+4.(30.(21.R17.))))P,(14.O3.R1:.R16.(10.&40.R3:.))P,(1;.=R17.)P,(1;.R18.(32.(10.&40.R3<.)+60.))P,(5.$>.(2:.(10.&40.R3=.)+10.)=)P,(33.R40.R1:.(32.(10.&40.R3>.)R1:.))P,(34.(1;.(23.R1=.+30.)R1;.)(1;.(10.&40.R3?.)R1=.))P,P,(5.$25.(26.(20.R1=.))$28.)(34.(1;.(23.(29.(20.R1>.))(31.+4.(30.(20.R1>.))))R1=.)(1;.(10.&40.R41.)(29.(20.R1>.))))P,P,(5.$25.(26.(21.R1>.))$28.)(34.(1;.(23.(29.(21.R1?.))(31.+4.(30.(21.R1?.))))R1>.)(1;.(10.&40.R42.)(29.(21.R1?.))))P,(5.(2.&40.)R3:.(35.&40.R20.))P,(5.(2.&40.)R3:.(35.&40.=))(36.O3.O2.R46.(37.O3.R45.R44.R43.R42.R3>.R3=.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R26.R25.R20.R24.)(6.(7.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R26.(35.&40.O1.)R25.(9.(2.&40.))R24.(:.O3.)))")
(* [comment removed for export] *).

Section CK.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CTXCK_STACK_A.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).

  Notation POST := (rsa_ctxck_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME xj := ([CB 8 xj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L12283411672.62L14106684376.62L36423572754.61L41288976216.62L44866992728.62L48429268312.62L49345641752.60L5145216728.62 L8722184664.62 Q15641571313.61Q18364008945.61Q21877860242.61Q27904922642.61Q32653583601.61Q33915847314.61Q3832213010.61 Q39941340946.61Q41154178801.61Q44650597233.61Q51233519217.61Q59840696433.61Q66523984274.61Q9840925842.61 00000400800C00G00K00O00S00W00[00b00i01401?01F01Q01\01g01n02502<02C02N02YS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2spS2spS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK LO0 SLO SCS"] Lemma epilogue : ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_context ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)Px4,(2.&40.)Px5,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pxj,(16.(2.&8.))P,(;.(<.(=.$>.$>.)(?.$>.$>.Vlo,(10.&40.Vsp,))(11.(=.$>.$>.)))Vm,R18.)P,(12.$38.Vm,R19.)P,(13.$38.R1:.)P,(14.$38.R1;.Vlo,(23.(10.&40.Vsp,)-40.))P,(19.$38.R1<.(23.(10.&40.Vsp,)-40.)(<.$39.(3:.#8.R5.)(<.$39.(3;.Vs5,)(<.$39.(3;.Vs4,)(<.$39.(3;.Vs3,)(<.$39.(3;.Vs2,)(<.$39.(3;.Vs1,)(<.$39.(3;.Vs0,)(<.$39.(3;.Vra,)(11.$39.))))))))))(36.$38.VAL,VCS,(37.$38.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R1<.(35.&40.(23.(10.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.R18.R17.R12.R11.R10.R?.R>.R=.R<.R;.R16.R15.R14.R13.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(35.&40.+;1684.)Vfc,(9.(2.&40.))R1=.(:.$38.)))")
(* [comment removed for export] *).
  Proof.
    intros until xj. intros MU WM MI ST FR. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evtA_done. unfold rsa_ctxck_postA. deexists 16.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK LO0 SLO SCS"] Lemma fail : ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_context ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)Px4,(2.&40.)Px5,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pxj,(16.(2.&8.))P,(;.(<.(=.$>.$>.)(?.$>.$>.Vlo,(10.&40.Vsp,))(11.(=.$>.$>.)))Vm,R18.)P,(12.$38.Vm,R19.)P,(13.$38.R1:.)P,(14.$38.R1;.Vlo,(23.(10.&40.Vsp,)-40.))P,(19.$38.R1<.(23.(10.&40.Vsp,)-40.)(<.$39.(3:.#8.R5.)(<.$39.(3;.Vs5,)(<.$39.(3;.Vs4,)(<.$39.(3;.Vs3,)(<.$39.(3;.Vs2,)(<.$39.(3;.Vs1,)(<.$39.(3;.Vs0,)(<.$39.(3;.Vra,)(11.$39.))))))))))(36.$38.VAL,VCS,(37.$38.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R1<.(35.&40.(23.(10.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.R18.R17.R12.R11.R10.R?.R>.R=.R<.R;.R16.R15.R14.R13.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(35.&40.+;167<.)Vfc,(9.(2.&40.))R1=.(:.$38.)))")
(* [comment removed for export] *).
  Proof.
    intros until xj. intros MU WM MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@C17025492443.114C17027589628.151C17027589631.132C17027589631.168K14560412036.132K14560412036.168K14560412039.151K14562509216.114K37211889074.95 K37211889074.96 L10041968289.0  L12174595177.81 L12283411672.90 L13301871092.90 L14106684376.89 L14549078981.3  L15447306016.89 L16075575155.161L16075583823.126L1685717371.0   L17646078182.91 L18293330070.2  L18714606648.90 L22271502648.89 L22598188190.91 L22598188190.92 L26368079009.0  L27804619052.80 L30985071382.113L30985071382.94 L30987168563.131L30987362533.149L31714561233.108L36294353073.93 L36294353073.94 L36715738693.2  L37222368707.2  L38235734261.1  L39025209581.14 L39025210477.14 L39835060509.81 L39845870340.14 L39845871492.14 L39887139444.90 L41288976216.90 L41872764395.92 L43059266230.89 L43882049225.3  L43884818473.2  L44866992728.90 L45061257730.146L45174768033.0  L45330285420.14 L45330286572.14 L45898055924.90 L48429268312.90 L5145216728.90  L51882119172.14 L51925114228.90 L53517126283.14 L54324727969.0  L55197438459.91 L56652673549.14 L56652674701.14 L57933933556.90 L58755387131.92 L59308586893.3  L61486510573.14 L61486511469.14 L63962036340.89 L65278129752.80 L7274816372.90  L8722184664.90  N21804656085.115N25673818932.152N34343554153.169N34999734301.169N37110879153.115N45601414740.133N47142626754.152N6396369602.133 O17025492443.114O17027589628.151O17027589631.132O17027589631.168O33932766420.151O33932766423.132O33932766423.168O33934863603.114Q1219017780.94  Q15457446739.92 Q15457446739.93 Q15643324129.91 Q16152254692.112Q16152254692.93 Q18365925601.92 Q21798041355.94 Q21879645826.92 Q23150033886.94 Q25513505925.94 Q25513505925.95 Q2577138615.94  Q27126674124.94 Q27907200258.92 Q30985071382.113Q30985071382.94 Q30987168563.131Q30987362533.149Q31394594844.94 Q32655500769.92 Q32799224464.92 Q32799392305.111Q33918256002.92 Q35595639279.112Q35595639279.93 Q36436139936.132Q36436139936.168Q36436139939.151Q36438237060.114Q3830427394.92  Q39939554818.92 Q41126203749.94 Q41152393185.92 Q44034257392.94 Q44648843873.92 Q49367596931.111Q49367666466.92 Q49698585326.93 Q49698585326.94 Q502448136.94   Q51235796833.92 Q52590069023.112Q52590069023.93 Q53519952433.94 Q57533912001.94 Q59843137889.92 Q63037100374.94 Q66522067074.92 Q66715549212.94 Q67528989526.95 Q67528989526.96 Q7377275490.94  Q7377275490.95  Q9742927161.92  Q9742988696.111 Q9743135771.112 Q9743135771.93  Q9843367298.91  00000100200300400B00P00^00l01P02C02D02O02Z02e03003103C03D03E03F03Q03X03i04:04K04\04]04h05I05f06G06h06i07:07K07L07M07Q07h08?08J08U08`08k09609D09V09]09d09o0:L0:M0:Z0:g0;20;=0;H0;S0;^0;b0;c0<40<I0<^0<i0=:0=C0=G0=K0=V0=a0=l0>70>G0>W0>g0?70?G0?W0?g0@70@B0@M0@X0@c0@d0@e0@f0@g0A30A<0AE0AN0AO0AP0AY0AZ0Ag0B30BN0C80C90C:0CG0C\0D10DF0D[0D^0Dg0Dl0E10E>0EC0EH0EU0Eb0Eo0F<0FI0FV0FW0F`0Fk0G40G90G>0GQ0Gd0Ge0Gn0HM0Hc0Ho0I00I90ID0IQ0I\0J;0Ji0KH0L60L;0L@0LE0LJ0LWFFFFS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2ra2sp1C1r2lo3SLO2DC2HB5Ha_st5Hl_stS2sp2s01C1r2lo3SLO2DC2HB5Ha_st5Hl_st2s12s22s32s42s5SS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rFS2ra2sp1C1r2C03CSZFFSS2ra2sp1C1rS2sp2loS2ra2sp1C1r2lo2DCS2ra2sp1C1r2lo2DCS2ra2sp1C1r2lo2H0S2ra2sp1C1r2lo2H0SS2ra2sp1C1rS2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPBS2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPB3x14FS2ra2sp1C1r2lo2H0S2ra2sp1C1r2lo2H0FFS2loS2sp2lo3LO03SLO3SPA3SPBS2sp2lo3LO03SLO3SPA3SPBS2ra2sp1C1rS2sp2lo3SLOS2sp2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS2AL2ra2sp1C1rS2ra2sp1C1r2lo3SLOS2sp2loS2sp2loS2ra2sp1C1rS2ra2sp1C1r3x143x453PC05POST1SS2sp1r2lo3DN'S2sp1r2lo3DE'S2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2sp2lo3SLOS2ra2sp1C1rS2spSS2ra2sp1C1r2lo2DCS2sp1C1r2lo2AN2DC3SPBS2sp1C1r2lo2AE2DC3SPBS2ra2sp1C1rS2ra2sp1C1r2lo2DCS1r2N02HnS2spS2spS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2sp1r2lo3x152C1S2sp1r2lo3x462C1S2sp1r2lo3x612C1S2sp1r2lo3x612C1S2sp1r2lo3x152C1S2sp1r2lo3x302C1S2sp1r2lo3x462C1S2sp1r2lo3x302C1S2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOFFFFS2AL1r5ALWF'S2sp1r2HBS2sp1r2HBS2sp1r2loFFS2sp1r2loFS2sp1r2lo3SLOS2AL1r5ALWF'S2ra2sp1r2lo2HB5Ha_st5Hl_stS2sp2s01r2lo2HB5Ha_st5Hl_st2s12s22s32s42s5FFS2sp1r2lo3SLOS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS1rS2sp1r2loS1C1rS1C1rS2sp1r2lo3SLOS1C1rS1C1rS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOFS2sp1r2loS2AL1r4IMG'S2sp1r2loS1C1rS1C1rS2sp1r3SPB2HB5Ha_stS2sp1r3SPB2HB5Ha_stFS2sp1r2loS2ra2sp1C1r3CAL2C03SPB3x144POSTS2ra2sp1C1r3CAL2C03SPBS2AL1r5ALWF'FS2sp1r2loS2AL1r4IMG'S2sp1r2lo3SLOS2AL1r4IMG'S2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S1C1rS1C1rS1C1rS1C1rS2sp1r2lo3SLO". (* [comment removed for export] *)
Theorem A_rsa_check_context_spec : forall AL, asan_img_ok AL -> rsa_check_context_stmtA asegs AL A_RSA_CHECK_CONTEXT.
Proof.
  intros AL IMG. unfold rsa_check_context_stmtA, A_RSA_CHECK_CONTEXT. intros until lo.
  intros HD LEN MN ME AN AE NSN NSE PN PE CAL C0 CSZ MI RA ALWF CSOK AB OC ON OE ST LO0 SLO SPA SCS DC DN DE -> ->.
  unfold RSA_CTX_SIZE in CSZ.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  dpose MN as [[_ (_ & _ & LENN & NRN & OWNN)] SGN]. dpose ME as [[_ (_ & _ & LENE & NRE & OWNE)] SGE]. unfold MPI_MAX_LIMBS in NRN, NRE.
  (* [comment removed for export] *)
  assert (ON16 : aobj asegs AL CS m (md_addr (r_N r)) 16) by (rewrite AN; eapply aobj_sub; [exact OC| lia| lia]).
  assert (OE16 : aobj asegs AL CS m (md_addr (r_E r)) 16) by (rewrite AE; eapply aobj_sub; [exact OC| lia| lia]).
  (* [comment removed for export] *)
  assert (DN' : 1 <= md_n (r_N r) -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DN eq_refl)| exfalso; exact (NSN eq_refl)]. }
  assert (DE' : 1 <= md_n (r_E r) -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DE eq_refl)| exfalso; exact (NSE eq_refl)]. }
  (* [comment removed for export] *)
  assert (TRN : forall ma mb, mpd_at asegs ma LB (r_N r) -> munch [(lo, bv_unsigned sp + -64)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DN EO); lia. }
  assert (TRE : forall ma mb, mpd_at asegs ma LB (r_E r) -> munch [(lo, bv_unsigned sp + -64)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DE EO); lia. }
  assert (TRN' : forall ma mb, mpd_at asegs ma LB (r_N r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DN EO); lia. }
  assert (TRE' : forall ma mb, mpd_at asegs ma LB (r_E r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DE EO); lia. }
  assert (SCS64 : crange CS lo (bv_unsigned sp + -64 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SLO; lia]).
  clear OWNN OWNE.
  unfold rsa_head_cells in HD.
  (* [comment removed for export] *)
  Ltac cur_aobj CSOK SCS MU ON ON1 :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ON with (?P -> aobj ?segs ?AL ?CS ?m0 ?A ?n) =>
        assert (ON1 : P -> aobj segs AL CS mx A n)
          by (let Hn := fresh in intros Hn; eapply (aobj_munch segs AL CS CSOK _ m0 mx); [| exact MU| exact (ON Hn)];
              unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear; lia] | apply Forall_nil])
      end end.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  (* [comment removed for export] *)
  do 8 zstep.
  (* [comment removed for export] *)
  pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
  zstep. zstep. zstep. clear GOT GSB.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PROLOGUE-LEFT:" g end.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONa.
  pose proof (A_mpi_size_spec AL IMG) as SP. unfold mpi_size_stmtA, mpi_query_stmtA in SP.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SP with (lo := lo) (LB := LB) (dX := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity; try exact I;
     first [ exact ONa | eapply TRN'; [exact MN| exact MU| exact WM]
           | rewrite AN; reflexivity
           | exact SCS64
           | clear - SLO SPA SPB LO0 CSZ C0 DC AN DN' NRN; first [lia | rewrite AN; lia | intros Hn; destruct (DN' Hn); lia]
           | match goal with |- ?g => idtac "SIZE-PRE-LEFT:" g end ]).
  clear SP.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-SIZE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases K1; zify_cond K1.
  { eapply fail; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep; if_cases K2; zify_cond K2.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PRE-CMPN-LEFT:" g end.
  (* [comment removed for export] *)
  clear ONa. cur_aobj CSOK SCS MU ON ONb.
  pose proof (A_mpi_cmp_int_spec AL IMG) as SP. unfold mpi_cmp_int_stmtA in SP.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SP with (lo := lo) (LB := LB) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact ONb | match goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- mpd_at _ ?mc _ _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end
           | rewrite AN; reflexivity
           | exact SCS64
           | clear - SLO SPA SPB LO0 CSZ C0 DC AN DN' NRN; first [lia | rewrite AN; lia | intros Hn; destruct (DN' Hn); lia]
           | match goal with |- ?g => idtac "CMPN-PRE-LEFT:" g end ]).
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPN-LEFT:" g end.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep; if_cases K3; zify_cond K3.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  clear ONb. cur_aobj CSOK SCS MU ON ONc.
  pose proof (A_mpi_get_bit_spec AL IMG) as SP3. unfold mpi_get_bit_stmtA, mpi_query_stmtA in SP3.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SP3 with (lo := lo) (LB := LB) (dX := r_N r) (v := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact ONc | match goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- mpd_at _ ?mc _ _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end
           | rewrite AN; reflexivity
           | exact SCS64
           | clear - SLO SPA SPB LO0 CSZ C0 DC AN DN' NRN; first [lia | rewrite AN; lia | intros Hn; destruct (DN' Hn); lia]
           | match goal with |- ?g => idtac "GETBIT-PRE-LEFT:" g end ]).
  clear SP3.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-GETBIT-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases KD; zify_cond KD.
  { eapply fail; eassumption. }
  (* [comment removed for export] *)
  zstep. try (if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity]).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  clear ONc. cur_aobj CSOK SCS MU OE OEa.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SP with (lo := lo) (LB := LB) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact OEa | match goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- mpd_at _ ?mc _ _ => eapply TRE'; [exact ME| exact MUx| exact WMx] end
           | rewrite AE; reflexivity
           | exact SCS64
           | clear - SLO SPA SPB LO0 CSZ C0 DC AE DE' NRE; first [lia | rewrite AE; lia | intros Hn; destruct (DE' Hn); lia]
           | match goal with |- ?g => idtac "CMPE-PRE-LEFT:" g end ]).
  clear SP.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases KG; zify_cond KG.
  - eapply fail; eassumption.
  - zstep. zstep. eapply epilogue; eassumption.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
