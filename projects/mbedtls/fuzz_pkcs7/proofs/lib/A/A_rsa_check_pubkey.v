(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_rsa_check_context.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg A_mpi_cmp_int A_mpi_cmp_mpi A_mpi_bitlen A_rsa_check_context.
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
Ltac2 gd_tbl_A_rsa_check_pubkey () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.RepRsa.rsa_st"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.RepRsa.rsa_head_cells"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.RepRsa.r_N"; "OSSVerify.KrLib.Spec.RepRsa.r_E"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Spec.RepRsa.RSA_CTX_SIZE"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "OSSVerify.KrLib.A.A_rsa_check_context.rsa_ctxck_postA"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"].


Definition A_RSA_CHECK_PUBKEY : Z := 0x0b0f98.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_CKPUB_STACK_A := 80 (only parsing).

Definition rsa_check_pubkey_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_pubkey ()) "PCS,P,$0.SpPra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))PLB,(4.$5.)PC,$0.Pr,$6.Plo,$0.P,(7.O3.R5.R3.(8.R2.))P,(9.(:.=(;.R3.))(<.(;.R3.)(=.+2.+40.)))P,(>.O3.R7.R6.(?.R4.))P,(>.O3.R8.R7.(10.R5.))P,(11.$0.(12.(?.R6.))(13.R7.+10.))P,(11.$0.(12.(10.R7.))(13.R8.+20.))P,(14.(11.$15.(16.(?.R8.))$17.))P,(14.(11.$15.(16.(10.R9.))$17.))P,P,(11.$15.(16.(?.R:.))$18.)(<.=(19.(?.R;.)))P,P,(11.$15.(16.(10.R;.))$18.)(<.=(19.(10.R<.)))P,(11.$0.(1:.R=.+8.)=)P,(<.=R>.)P,(:.(13.R?.$1;.)(=.+2.+40.))P,(1<.O3.R12.)P,(11.$0.(1:.(1=.&40.R34.)+2.)=)P,(1>.O2.)P,(1?.O2.R37.)P,(20.O3.O2.R16.)P,(21.O3.O2.R39.R17.R15.+30.)P,P,(:.+1.(22.(?.R15.)))(21.O3.O2.R3;.R19.(19.(?.R16.))(23.+4.(22.(?.R16.))))P,P,(:.+1.(22.(10.R16.)))(21.O3.O2.R3<.R1:.(19.(10.R17.))(23.+4.(22.(10.R17.))))P,(24.O3.R1:.R16.(1=.&40.R3:.))P,(:.=R17.)P,(:.R18.(25.(1=.&40.R3<.)+50.))P,(11.$0.(1:.(1=.&40.R3=.)+10.)=)P,(26.R40.R1:.(25.(1=.&40.R3>.)R1:.))P,(27.(:.(13.R1=.+30.)R1;.)(:.(1=.&40.R3?.)R1=.))P,P,(11.$15.(16.(?.R1=.))$18.)(27.(:.(13.(19.(?.R1>.))(23.+4.(22.(?.R1>.))))R1=.)(:.(1=.&40.R41.)(19.(?.R1>.))))P,P,(11.$15.(16.(10.R1>.))$18.)(27.(:.(13.(19.(10.R1?.))(23.+4.(22.(10.R1?.))))R1>.)(:.(1=.&40.R42.)(19.(10.R1?.))))P,(11.(1.&40.)R3:.(28.&40.R20.))(29.O3.O2.R45.(2:.O3.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R1?.R23.)(2;.(2<.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(28.&40.O1.)R24.(2=.(1.&40.))R23.(2>.O3.)))")
(* [comment removed for export] *).

Section CK.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CKPUB_STACK_A.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).

  Notation POST := (rsa_ctxck_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME := ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L11741095640.60L26924648792.60L27904922642.59L4202106291.60 L43654564952.60L51711223320.58L59499841752.60L7510805464.60 Q15641571313.59Q18364008945.59Q27904922642.59Q32653583601.59Q33915847314.59Q3832213010.59 Q39941340946.59Q44650597233.59Q51233519217.59Q59840696433.59Q66523984274.59Q9840925842.59 00000400800C00G00K00O00S00W00^00e01001701B01M01X01_01f01m02802CS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2spS2sp2loS2sp2loS2sp2lo3SLOS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK LO0 SLO SCS"] Lemma epilogue : ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_pubkey ()) "Pm1,P,(1.&40.)(3.(1.&8.))Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Px0,(1.&40.)Px1,(1.&40.)Px2,(1.&40.)Px3,(1.&40.)Px4,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(2?.(30.(31.$0.$0.)(32.$0.$0.Vlo,(1=.&40.Vsp,))(33.(31.$0.$0.)))Vm,R16.)P,(34.$35.Vm,R17.)P,(1<.$35.R18.)P,(24.$35.R19.Vlo,(13.(1=.&40.Vsp,)-30.))P,(7.$35.R1:.(13.(1=.&40.Vsp,)-30.)(30.$36.(37.Vs4,)(30.$36.(37.Vs3,)(30.$36.(37.Vs2,)(30.$36.(37.Vs1,)(30.$36.(37.Vs0,)(30.$36.(37.Vra,)(33.$36.))))))))(29.$35.VAL,VCS,(2:.$35.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(2;.(2<.R1:.(28.&40.(13.(1=.&40.Vsp,)-30.))Vgp,Vtp,R19.R18.R17.R16.R15.R11.R10.R?.R>.R=.R<.R;.R:.R14.R13.R12.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(28.&40.+;1090.)Vfc,(2=.(1.&40.))R1;.(2>.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evtA_done. unfold rsa_ctxck_postA. deexists 16.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK LO0 SLO SCS"] Lemma fail : ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_pubkey ()) "Pm1,P,(1.&40.)(3.(1.&8.))Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Px0,(1.&40.)Px1,(1.&40.)Px2,(1.&40.)Px3,(1.&40.)Px4,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(2?.(30.(31.$0.$0.)(32.$0.$0.Vlo,(1=.&40.Vsp,))(33.(31.$0.$0.)))Vm,R16.)P,(34.$35.Vm,R17.)P,(1<.$35.R18.)P,(24.$35.R19.Vlo,(13.(1=.&40.Vsp,)-30.))P,(7.$35.R1:.(13.(1=.&40.Vsp,)-30.)(30.$36.(37.Vs4,)(30.$36.(37.Vs3,)(30.$36.(37.Vs2,)(30.$36.(37.Vs1,)(30.$36.(37.Vs0,)(30.$36.(37.Vra,)(33.$36.))))))))(29.$35.VAL,VCS,(2:.$35.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(2;.(2<.R1:.(28.&40.(13.(1=.&40.Vsp,)-30.))Vgp,Vtp,R19.R18.R17.R16.R15.R11.R10.R?.R>.R=.R<.R;.R:.R14.R13.R12.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(28.&40.+;1088.)Vfc,(2=.(1.&40.))R1;.(2>.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK LO0 SLO SCS"] Lemma fail2 : ltac2:(CDefT.buildp (gd_tbl_A_rsa_check_pubkey ()) "Pm1,P,(1.&40.)(3.(1.&8.))Pxra,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Px0,(1.&40.)Px2,(1.&40.)Px3,(1.&40.)Px4,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(2?.(30.(31.$0.$0.)(32.$0.$0.Vlo,(1=.&40.Vsp,))(33.(31.$0.$0.)))Vm,R15.)P,(34.$35.Vm,R16.)P,(1<.$35.R17.)P,(24.$35.R18.Vlo,(13.(1=.&40.Vsp,)-30.))P,(7.$35.R19.(13.(1=.&40.Vsp,)-30.)(30.$36.(37.Vs4,)(30.$36.(37.Vs3,)(30.$36.(37.Vs2,)(30.$36.(37.Vs1,)(30.$36.(37.Vs0,)(30.$36.(37.Vra,)(33.$36.))))))))(29.$35.VAL,VCS,(2:.$35.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(2;.(2<.R19.(28.&40.(13.(1=.&40.Vsp,)-30.))Vgp,Vtp,R18.R17.R16.R15.(28.&40.-4000.)R11.R10.R?.R>.R=.R<.R;.R:.R14.R13.R12.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(28.&40.+;1080.)Vfc,(2=.(1.&40.))R1:.(2>.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "0300@C17025492443.117C17027589626.226C17027589627.244C17027589628.153C17027589629.189C17027589631.135C17027589631.171C17027589631.207K26090385536.244K26090385537.226K26090385540.135K26090385540.171K26090385540.207K26090385542.189K26090385543.153K26092482720.117K37211889074.94 K37211889074.95 L10897409697.0  L11246298883.89 L11741095640.88 L12174595177.82 L14791043170.169L14791043171.133L14791043172.116L14791043173.97 L14791044321.225L14791044323.206L14791044324.187L14791044325.152L15447306016.88 L16073480909.164L16075583823.128L16085877070.235L1685717371.0   L17272767236.14 L19354909044.89 L23778900769.0  L25382082548.89 L26104603333.3  L26924648792.89 L27804619052.81 L28717461921.0  L29325809668.14 L29325810820.14 L29325810820.17 L31378308326.90 L31392867444.89 L31714561233.111L32879090465.0  L36294353073.92 L36294353073.93 L37222368707.2  L37414286068.89 L38235734261.1  L38712304397.14 L38712305549.14 L38712305549.17 L39835060509.82 L40065549985.0  L41872764395.91 L4202106291.89  L43059266230.88 L43442376564.88 L43654564952.89 L43882049225.3  L43884818473.2  L45063350578.148L45330285420.14 L45330286572.14 L45330286572.17 L4630754987.202 L46599481914.220L52069193234.235L53056398486.2  L53517126283.14 L53517127179.14 L55197438459.90 L567271841.0    L56758455764.183L58755387131.91 L59308586893.3  L59499841752.89 L61486510573.14 L61486511469.14 L62935018273.0  L6514053445.2   L65278129752.81 L7510805464.89  L8060680993.0   L808096237.14   L808096237.17   L808097133.14   N15085513317.227N18357708512.245N18523877275.208N21804656085.118N25673818932.154N34343554153.172N34999734301.172N36726440211.208N37110879153.118N39991602143.190N44210174337.227N45601414740.136N47142626754.154N52318795519.190N52972835382.245N6396369602.136 O17025492443.117O17027589626.226O17027589627.244O17027589628.153O17027589629.189O17027589631.135O17027589631.171O17027589631.207O33932766418.226O33932766419.244O33932766420.153O33932766421.189O33932766423.135O33932766423.171O33932766423.207O33934863603.117Q1219017780.93  Q14791043170.169Q14791043171.133Q14791043172.116Q14791043173.97 Q14791044321.225Q14791044323.206Q14791044324.187Q14791044325.152Q15643324129.90 Q16152254692.115Q16152254692.92 Q18365925601.91 Q21798041355.93 Q23150033886.93 Q25513505925.93 Q25513505925.94 Q25604052563.91 Q25604052563.92 Q2577138615.93  Q27126674124.93 Q27907200258.91 Q27909133984.135Q27909133984.171Q27909133984.207Q27909133986.189Q27909133987.153Q27909133988.244Q27909133989.226Q27911231108.117Q31394594844.93 Q32655500769.91 Q32799224464.91 Q32799392305.114Q33721217258.92 Q33918256002.91 Q35595639279.115Q35595639279.92 Q37821600610.93 Q37821600610.94 Q3830427394.91  Q39939554818.91 Q41126203749.93 Q44034257392.93 Q44648843873.91 Q49367596931.114Q49367666466.91 Q49698585326.92 Q49698585326.93 Q502448136.93   Q51235796833.91 Q52590069023.115Q52590069023.92 Q53519952433.93 Q57198265401.94 Q57533912001.93 Q59843137889.91 Q63037100374.93 Q66522067074.91 Q66715549212.93 Q67528989526.94 Q67528989526.95 Q9742927161.91  Q9742988696.114 Q9743135771.115 Q9743135771.92  Q9843367298.90  00000100200300400500600700800O00a00o01=01O01]01k02902]03M03N03Y03d03o04P05105R05o06Y07>07c08D08V08W08X08Y08Z08e09009109<09=09H09S09T09_09j0:50:@0:K0:L0:M0:^0:o0;00;;0;?0;T0;i0<A0<L0<M0<[0<f0=80=C0=N0=U0=\0>90>F0>S0>d0?E0?F0?G0?N0?R0?V0?g0?h0?i0@:0@C0@N0@R0@V0@W0@X0@c0@n0@o0AF0A]0B40BI0Bc0C70CG0CW0Cg0D70DK0D[0Dk0E@0EP0E`0F00FJ0FZ0Fe0G00G;0GF0GQ0G\0Gg0H20H30H40H50H60H70H80H90H:0HF0H[0I00IE0IZ0J80JQ0Jj0K?0KH0KI0KJ0KS0KT0K`0L;0Lb0Lk0M40M50M60MC0MP0M]0Mn0N;0NH0N^0No0O<0O?0OH0OM0OR0O[0Oh0Om0P20PQ0Q90QF0QS0QT0Q_0Qh0Qm0R20RE0RX0RY0Rb0SA0SW0Sc0TB0TC0TL0TW0Td0To0UN0V90V>0VC0VH0VM0VZFFFFFFFFS2sp1C1r2lo2DC3x764x108S2sp1C1r2lo2DC3x76S2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DC3x76S2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2ra2sp1C1r2lo3SLO2DC2HB5Ha_st5Hl_stS2sp2s01C1r2lo3SLO2DC2HB5Ha_st5Hl_st2s12s22s32s4SS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPBS2ra2sp1C1r2lo2C03LO03SLO3SPB3x143x764x108S2ra2sp1C1r2lo2C03LO03SLO3SPB3x143x76S2ra2sp1C1r2lo2C03LO03SLO3SPB3x143x76S2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2C03CSZFFFSS2sp2lo3SLOS2ra2sp1C1rSS2ra2sp1C1rFS2ra2sp1C1rS2ra2sp1C1rSS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2ra2sp1C1rS2ra2sp1C1rFSS2ra2sp1C1r2lo2H0S2ra2sp1C1r2lo2H0FS2ra2sp1C1rS2loS2sp1C1r2lo2AN2DC3SPBS2sp1C1r2lo2AE2DC3SPBS2sp1C1r2lo2AE2DC3SPB2ANS2ra2sp1C1rSS2AL2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1r2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS2sp2loS2sp2loS2ra2sp1C1r3x143x453PC05POST1S2sp1r2lo3DN'S2sp1r2lo3DE'S2sp1r2lo3DE'3DN'S2ra2sp1C1r3x143x763x923PC15POST0FFS2sp2loS2spS2spS2ra2sp1C1r2lo2DCSFS2ra2sp1C1r2lo2DCS1r2N02HnS2ra2sp1C1rS2spS2spSFS2ra2sp1C1rS2ra2sp1C1rSS2sp2lo3LO03SLO3SPA3SPBS2sp2lo3LO03SLO3SPA3SPBS2sp2lo3LO03SLO3SPA3SPBS2sp1r2lo3x764x1092C1S2sp1r2lo3x764x1084x1242C1S2sp1r2lo3x763x932C1S2sp1r2lo3x152C1S2sp1r2lo3x462C1S2sp1r2lo3x612C1S2sp1r2lo3x612C1S2sp1r2lo3x763x932C1S2sp1r2lo3x152C1S2sp1r2lo3x772C1S2sp1r2lo3x764x1092C1S2sp1r2lo3x302C1S2sp1r2lo3x462C1S2sp1r2lo3x772C1S2sp1r2lo3x764x1084x1242C1S2sp1r2lo3x302C1S2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFS2AL1r5ALWF'S2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPB3x764x108S2sp1r2lo3LO03SLO3SPB3x76S2sp1r2lo3LO03SLO3SPB3x76S2sp1r2lo3LO03SLO3SPBS2sp1r2loFFS2sp1r2loFS2AL1r5ALWF'S2ra2sp1r2lo2HB5Ha_st5Hl_stS2sp2s01r2lo2HB5Ha_st5Hl_st2s12s22s32s4S2sp1r2HBS2sp1r2HBFFS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLO3x76S2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLO3x764x108S2sp1r2lo3SLO3x76S2sp1r2lo3SLOS1rS2sp1r2loS1C1rS1C1rS2sp1r2HBS2sp1r2lo3SLOS1C1rS1C1rS2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s3S2sp1r2lo3SLOS2sp1r2lo3SLOFS2AL1r4IMG'S2sp1r2loS1C1rS1C1rS2sp1r3SPB2HB5Ha_stS2sp1r3SPB2HB5Ha_stFS2sp1r2loS2ra2sp1C1r3CAL2C03SPB3x144POSTS2ra2sp1C1r3CAL2C03SPBS2AL1r5ALWF'S2sp2s41r2lo3SLO2HB5Ha_st5Hl_stFS2sp1r2loS2AL1r4IMG'S2sp1r2lo3SLOS2AL1r4IMG'S2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s4S1C1rS1C1rS1C1rS1C1rS2sp1r2lo3SLO". (* [comment removed for export] *)
Theorem A_rsa_check_pubkey_spec : forall AL, asan_img_ok AL -> rsa_check_pubkey_stmtA asegs AL A_RSA_CHECK_PUBKEY.
Proof.
  intros AL IMG. unfold rsa_check_pubkey_stmtA, A_RSA_CHECK_PUBKEY. intros until lo.
  intros HD LEN MN ME AN AE NSN NSE PN PE CAL C0 CSZ MI RA ALWF CSOK AB OC ON OE ST LO0 SLO SPA SCS DC DN DE ->.
  unfold RSA_CTX_SIZE in CSZ.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  dpose MN as [[_ (_ & _ & LENN & NRN & OWNN)] SGN]. dpose ME as [[_ (_ & _ & LENE & NRE & OWNE)] SGE]. unfold MPI_MAX_LIMBS in NRN, NRE.
  assert (ON16 : aobj asegs AL CS m (md_addr (r_N r)) 16) by (rewrite AN; eapply aobj_sub; [exact OC| lia| lia]).
  assert (OE16 : aobj asegs AL CS m (md_addr (r_E r)) 16) by (rewrite AE; eapply aobj_sub; [exact OC| lia| lia]).
  assert (DN' : 1 <= md_n (r_N r) -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DN eq_refl)| exfalso; exact (NSN eq_refl)]. }
  assert (DE' : 1 <= md_n (r_E r) -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DE eq_refl)| exfalso; exact (NSE eq_refl)]. }
  assert (TRN' : forall ma mb, mpd_at asegs ma LB (r_N r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DN EO); lia. }
  assert (TRE' : forall ma mb, mpd_at asegs ma LB (r_E r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DE EO); lia. }
  assert (SCS48 : crange CS lo (bv_unsigned sp + -48 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SLO; lia]).
  clear OWNN OWNE.
  unfold rsa_head_cells in HD.
  Ltac cur_aobj CSOK SCS MU ON ON1 :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ON with (?P -> aobj ?segs ?AL ?CS ?m0 ?A ?n) =>
        assert (ON1 : P -> aobj segs AL CS mx A n)
          by (let Hn := fresh in intros Hn; eapply (aobj_munch segs AL CS CSOK _ m0 mx); [| exact MU| exact (ON Hn)];
              unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear; lia] | apply Forall_nil])
      end end.
  (* [comment removed for export] *)
  Ltac qside SLO SPA SPB LO0 CSZ C0 DC OX TR MX AX DX NRX SCS48 :=
    first [ exact OX
          | match goal with MUx : munch _ ?m0 ?mc, WMx : wmono asegs ?m0 ?mc |- mpd_at _ ?mc _ _ => eapply TR; [exact MX| exact MUx| exact WMx] end
          | rewrite AX; reflexivity
          | exact SCS48
          | lazymatch goal with |- ?x = Z_to_bv 64 ?v => is_evar v; symmetry; exact (Z_to_bv_bv_unsigned x) end
          | clear - SLO SPA SPB LO0 CSZ C0 DC AX DX NRX; first [lia | rewrite AX; lia | intros Hn; destruct (DX Hn); lia]
          | match goal with |- ?g => idtac "QSIDE-LEFT:" g end ].
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  do 7 zstep.
  (* [comment removed for export] *)
  pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
  zstep. zstep. zstep. clear GOT GSB.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PROLOGUE-LEFT:" g end.
  pose proof (A_mpi_size_spec AL IMG) as SPs. unfold mpi_size_stmtA, mpi_query_stmtA in SPs.
  pose proof (A_mpi_cmp_int_spec AL IMG) as SPc. unfold mpi_cmp_int_stmtA in SPc.
  pose proof (A_mpi_get_bit_spec AL IMG) as SPg. unfold mpi_get_bit_stmtA, mpi_query_stmtA in SPg.
  pose proof (A_mpi_bitlen_spec AL IMG) as SPb. unfold mpi_bitlen_stmtA, mpi_query_stmtA in SPb.
  pose proof (A_mpi_cmp_mpi_spec AL IMG) as SPm. unfold mpi_cmp_mpi_stmtA in SPm.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONa.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPs with (lo := lo) (LB := LB) (dX := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; try exact I; qside SLO SPA SPB LO0 CSZ C0 DC ONa TRN' MN AN DN' NRN SCS48).
  clear ONa.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-SIZE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases K1; zify_cond K1.
  { eapply fail; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep; if_cases K2; zify_cond K2.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONb.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPc with (lo := lo) (LB := LB) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; qside SLO SPA SPB LO0 CSZ C0 DC ONb TRN' MN AN DN' NRN SCS48).
  clear ONb.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPN-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases K3; zify_cond K3.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONc.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPg with (lo := lo) (LB := LB) (dX := r_N r) (v := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; qside SLO SPA SPB LO0 CSZ C0 DC ONc TRN' MN AN DN' NRN SCS48).
  clear ONc.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-GETBITN-LEFT:" g end.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep; if_cases Kb4; zify_cond Kb4.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU OE OEa.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPc with (lo := lo) (LB := LB) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; qside SLO SPA SPB LO0 CSZ C0 DC OEa TRE' ME AE DE' NRE SCS48).
  clear OEa.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases Kb5; zify_cond Kb5.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONd.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPb with (lo := lo) (LB := LB) (dX := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; try exact I; qside SLO SPA SPB LO0 CSZ C0 DC ONd TRN' MN AN DN' NRN SCS48).
  clear ONd.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLENN-LEFT:" g end.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep; if_cases Kb6; zify_cond Kb6.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU OE OEb.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPg with (lo := lo) (LB := LB) (dX := r_E r) (v := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; qside SLO SPA SPB LO0 CSZ C0 DC OEb TRE' ME AE DE' NRE SCS48).
  clear OEb.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-GETBITE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep; if_cases Kb7; zify_cond Kb7.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU OE OEc.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPb with (lo := lo) (LB := LB) (dX := r_E r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity; try exact I; qside SLO SPA SPB LO0 CSZ C0 DC OEc TRE' ME AE DE' NRE SCS48).
  clear OEc.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLENE-LEFT:" g end.
  (* [comment removed for export] *)
  zstep. zstep.
  zstep; if_cases Kb8; zify_cond Kb8.
  2:{ (* [comment removed for export] *) eapply fail2; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONe. cur_aobj CSOK SCS MU OE OEe.
  callxA_sp (bv_unsigned sp + -48)
    (eapply SPm with (lo := lo) (LB := LB) (dX := r_E r) (dY := r_N r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity;
     first [ exact OEe | exact ONe
           | match goal with MUx : munch _ ?m0 ?mc, WMx : wmono asegs ?m0 ?mc |- mpd_at _ ?mc _ (r_E r) => eapply TRE'; [exact ME| exact MUx| exact WMx] end
           | match goal with MUx : munch _ ?m0 ?mc, WMx : wmono asegs ?m0 ?mc |- mpd_at _ ?mc _ (r_N r) => eapply TRN'; [exact MN| exact MUx| exact WMx] end
           | rewrite AE; reflexivity | rewrite AN; reflexivity
           | exact SCS48
           | clear - SLO SPA SPB LO0 CSZ C0 DC AE DE' NRE AN DN' NRN;
             first [lia | rewrite AE; lia | rewrite AN; lia | intros Hn; destruct (DE' Hn); lia | intros Hn; destruct (DN' Hn); lia]
           | match goal with |- ?g => idtac "CMPM-LEFT:" g end ]).
  clear ONe OEe.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPM-LEFT:" g end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  eapply epilogue; eassumption.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
