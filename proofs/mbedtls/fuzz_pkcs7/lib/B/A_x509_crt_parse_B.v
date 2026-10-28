(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_crt_parse_stmt24 A_crt_free_stmt2 A_pkcs7_free A_x509_crt_parse_area.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A A_x509_crt_parse_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_crt_parse_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_own"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.ext_junk"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_parse_area.chunks"; "RocqVerifyHarness.AgentSubmission.B.A_x509_crt_parse_area.owns"; "Stdlib.Sorting.Permutation.Permutation"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.crt_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_x509_crt_parse.f_of"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_crt_parse_stmt24.x509_crt_parse_der_postA24"].



Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM3 : arl_smalloc R 3 = 0x53398.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_crt_parse_A.STKx R STKc).
  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH0 : 0 <= arl_need_setsh R.
  Hypothesis STKc4 : arl_need_setsh R <= STKc.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (CRT Q blen BUF lo slo : Z) (bs : list byte) (WS : list ivl).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= Q. Hypothesis B2 : 0 <= blen. Hypothesis B3 : Q + blen <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CRT 744.
  Hypothesis CRTLO : CRT + 744 <= lo.
  Hypothesis DXB : CRT + 744 <= BUF \/ BUF + n <= CRT.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_x509_crt_parse_A.STKx in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := ((CRT, CRT + 744) :: WS).
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  Local Notation FSHP := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.


  Local Notation RSLX FB k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ja jb :=
    [CB 24 ja; C8 k24; C8 k32; C8 k40; C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88; C8 k96; C8 k104; C8 k112; C8 k120; CB 16 jb; C8 (Z_to_bv 64 FB)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m2x : mem) (WA WB : list ivl) (r : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(:.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(;.Vra,)Vfc,(<.(2.&40.))R10.(=.$5.)))(6.(>.$5.R10.)(6.(?.$5.R10.Vlo,(10.&40.Vsp,))(6.(11.$5.(12.VR,)R10.Vslo,(10.&40.Vsp,))(6.(13.$5.VR,VHIA,O6.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)O3.Vm,R10.)(6.(13.$5.VR,VHIA,O6.(14.$15.O5.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)O2.O4.R10.)(6.(7.P,$16.Sp(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O6.))(6.(7.$16.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O6.))(6.(7.$16.(19.$5.VR,VHIA,R?.)(19.$5.VR,VHIA,O6.))(6.(7.$16.(1:.$5.VR,VHIA,R?.)(1:.$5.VR,VHIA,O6.))(6.(7.$16.(1;.$5.VR,VHIA,R?.)(1;.$5.VR,VHIA,O6.))(6.(7.$16.(1<.$5.VR,VHIA,R?.)(1<.$5.VR,VHIA,O6.))(6.Pmo,$1=.(1>.(1?.$5.VR,VHIA,R10.R1.)(1?.$5.VR,VHIA,O6.R1.))(20.$5.VR,VHIA,R?.(14.$15.O5.VLB,)VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DXB; try lx_pin1 CRTLO; try lx_pin1 CWX; try lx_pin1 ALC; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 WS; try lx_pin1 BUF; try lx_pin1 blen; try lx_pin1 Q; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 NSH0; try lx_pin1 SM3; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0220@C17014793671.188C57276794631.189D2459793318.145 D32452690557.145D3374278032.144 D39760256259.145D43016287773.146D45715803169.144D62011770188.146D68405837779.144D6909504982.144 K39961251074.188L10084946068.131L10084946073.127L13176305223.2  L1540877545.3   L16575822004.6  L19546883927.130L19546883930.134L21218866939.2  L22788604467.2  L24902899785.3  L2676383091.149 L26772847875.9  L28321813694.136L30443668812.11 L3066763050.3   L32516831197.3  L34098687479.1  L34802572956.2  L35655538631.11 L37028630485.0  L37549236628.2  L38235734261.1  L38255709121.1  L39188636933.0  L39382487321.198L39844638933.0  L39959168648.2  L40379729337.204L41409160545.3  L48117620902.131L48117620903.132L48117620904.128L48117620907.127L48132467214.12 L50790731766.11 L51611265137.4  L52597941171.3  L54336156040.9  L54488093861.205L55085943702.3  L55227642482.130L55227642495.134L58790154276.10 L60098763854.6  L60754583113.0  L62018535662.1  L64681452487.7  L65776827307.1  L67028235242.13 L6899380056.1   L6912107235.131 L6912107246.127 L7021056161.0   L8518658028.2   L9080220944.4   L9108443469.4   L9356559676.16  O12506809262.188O1489189746.188 O17014793671.188O2064787831.188 O22994697610.188O42024878704.188O55103961204.188O59610505133.188P21218174016.188P24903256818.188P37559411472.203P41408280538.188P51611499210.188P52599990329.188P55086766381.188P9108603894.188 Q10084946068.155Q10084946073.151Q10084946973.157Q10099627429.149Q10099627453.153Q10592386204.150Q10592386207.154Q21218168933.151Q21218168936.155Q22358563588.153Q23925414036.159Q29719392697.150Q29719392698.154Q30147450662.151Q31314676345.149Q34796740410.154Q38248895679.158Q38697992091.201Q4125667684.200 Q42439443119.202Q42441479401.161Q4279611329.202 Q43880146019.158Q48117620905.154Q48117620906.150Q48132302223.153Q48132302231.149Q5935758158.202 Q59668625896.155Q60382659730.155Q60382659743.151Q62009673036.159Q64133651577.201Q64681502656.161Q64683667846.202Q67397950268.150Q68104228746.201Q6897428426.153 Q6897428434.149 Q6912107235.155 Q6912107246.151 Q6912108138.157 Q7917062807.155 Q7917062810.151 Q9350270635.166 00000100700800G00H00W00o01>01O01P01_02002;02F02N02Z03003E03Z03[03\03]04104U05505U05_05j05o06506N06O06P06T06X06Y06m06n06o07A07B08708l09a0:V0;D0;d0;e0;f0<J0=<0==0=W0>10>U0>_0>`0>c0?=0?A0?i0?m0@80@C0@D0@J0@Y0@Z0AN0AO0AP0AQ0AR0AS0AT0AU0AV0AW0B\0B]0C40D90E60EL0Em0F80FC0FN0FY0Fd0Fo0G:0G;0G<0G=0GM0GX0Gc0Gd0Ge0Gf0H10HA0HN0Hf0I90IF0IT0JI0K>0L30Lh0M50M60M70M80MB0MO0N00NV0NW0Ng0O20O=0OH0OS0O^0P20PF0PWFS1R2FBFS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R2LF3LFB2FB3APSS2LF3LFB2FBS2LF3LFB2FBS2lo3sp1S2sp3sp13SP1S1R3slo4SLOS2FB3ALO2F1S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0FFFS2LF3LFB2FB3sp11c2HcS1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1S1R2LF2sp3slo3LFB4SLOS2FB3ALO2F1S1R3NS14STKc5STKc02sp2lo3SLO3LOSS2FB2x02HxS2sp2lo3sp1S3sp1S1R2FBS1R3HIA1h2sp2lo3TOP5HTOP3SFS2loS2FBSS2LF3LFB2FB3sp11p2PBSFS2LF2sp3LFB2FB3sp1FS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02sp2lo3slo4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02sp2lo3SLO3LOSFFS1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1S1R3NS14STKc5STKc02LF2sp2lo3LFB3SLO2FB3sp14SP1R2F0FS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S1R3NS14STKc5STKc42sp2lo3SLO3sp13SP1S1R2lo3LOSSS1RS1R3HIA1h2sp3slo3TOP5HTOP3S2FBS1R3NS14STKc5STKc02sp2lo3SLO3LOS3sp13SP1S2FBS2LF3LFB2FBS2LF3LFB2FBSS1R2FBS2sp2lo3sp13SP1FS1R3NS14STKc5STKc02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO2FB3sp13SP13ALO4SBNDFS2LF2lo3LFB2FB3sp14FBLOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO2FB3sp13SP13ALO4SBNDS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO2FB3ALO4SBNDS2LF2sp2lo3LFB3sp13SP1S1R2LF2lo3LFB3LOS2FB3sp13ALO4SBNDS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFFFS1R3HIA1h2LF3LFBS2LF3LFB2FBS2LF3LFB2FBFFFS2LF2lo3LFBS2LF3LFB2FB1p2PBS2LF3LFB1p2PBS1R2LF3slo3LFB4SLOS1p2PBS1R2LF3slo3LFB4SLOSS2LF3LFB1p2PBS2LF2sp2lo3LFBS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS14STKc5STKc02LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS2LF3LFB1p2PBFFFS1R2LF3LFBS2LF3LFB1p2PBS1R3HIA1h2LF2sp3slo3LFB3TOP5HTOP3S1R3HIA1h2LF2sp3slo3LFB3TOP5HTOP31p2PBFS2LF3LFB2FB1p2PBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1S2LF3LFB3sp14SP1R". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS CRT0 LFB bs CRT STKc4 SF5 STKc0 STKc NS1 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_B ()) "Ph3,(4.$5.VR,VHIA,)PLBc,(21.$15.)Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(21.$22.)PWB,(21.$22.)PFB,$16.Psp1,$16.Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps7v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps11v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pr,$16.Pja,(21.(2.&8.))Pjb,(21.(2.&8.))Pk24,(2.&40.)Pk32,(2.&40.)Pk40,(2.&40.)Pk48,(2.&40.)Pk56,(2.&40.)Pk64,(2.&40.)Pk72,(2.&40.)Pk80,(2.&40.)Pk88,(2.&40.)Pk96,(2.&40.)Pk104,(2.&40.)Pk112,(2.&40.)Pk120,(2.&40.)P,(20.$5.VR,VHIA,R31.(14.$15.R30.VLB,)(23.(24.$16.$16.)(25.$16.$16.R2;.+200.)VLF,)R2>.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R34.R2.)P,(7.$16.(18.$5.VR,VHIA,R33.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R34.)(19.$5.VR,VHIA,Vh,))P,(6.(26.(27.(10.&40.Vsp,)+110.)R2>.)(26.R2>.(27.(10.&40.Vsp,)+100.)))P,(7.$16.(28.R2?.+20.)=)P,(7.$16.(28.R31.+40.)=)P,(29.VR,VLB,VLF,R32.+200.)P,(29.VR,(14.$15.R38.VLB,)VLF,R33.+200.)P,(2:.(17.$5.VR,VHIA,Vh,)R34.+200.)P,(2;.$5.R38.R35.(23.$2<.(2=.R1=.)(23.$2<.(2=.R1<.)(23.$2<.(2=.R1;.)(2>.$2<.)))))P,(2;.$5.R39.(2?.(30.R36.+3.)(31.(12.VR,)))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(2>.$2<.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))P,(2;.$5.R3:.(2?.(10.&40.Vsp,)-68.)(23.$2<.(2=.Vs11,)(23.$2<.(2=.Vs10,)(23.$2<.(2=.Vs9,)(23.$2<.(2=.Vs8,)(23.$2<.(2=.Vs7,)(23.$2<.(2=.Vs6,)(23.$2<.(2=.Vs5,)(23.$2<.(2=.Vs4,)(23.$2<.(2=.Vs3,)(23.$2<.(2=.Vs2,)(23.$2<.(2=.Vs1,)(23.$2<.(2=.Vs0,)(23.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))P,(2;.$5.R3;.R37.(23.$2<.(33.#18.R1<.)(23.$2<.(2=.R1:.)(23.$2<.(2=.R19.)(23.$2<.(2=.R18.)(23.$2<.(2=.R17.)(23.$2<.(2=.R16.)(23.$2<.(2=.R15.)(23.$2<.(2=.R14.)(23.$2<.(2=.R13.)(23.$2<.(2=.R12.)(23.$2<.(2=.R11.)(23.$2<.(2=.R10.)(23.$2<.(2=.R?.)(23.$2<.(2=.R>.)(23.$2<.(33.#10.R1;.)(23.$2<.(2=.(:.&40.R38.))(2>.$2<.))))))))))))))))))P,(?.$5.R3<.(2?.R38.+98.)(2?.(10.&40.Vsp,)-68.))P,(?.$5.R3=.Vlo,R39.)P,(>.$5.R3>.)P,(13.$5.VR,VHIA,R42.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)R3>.Vm,R3?.)P,(13.$5.VR,VHIA,R43.(14.$15.R42.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)R3>.R41.R40.)P,(11.$5.(12.VR,)R41.Vslo,(10.&40.Vsp,))(34.$5.(12.VR,)(17.$5.VR,VHIA,R45.)(35.R45.R44.R43.R41.R40.R24.)(8.(9.R3=.(:.&40.R3>.)Vgp,Vtp,R3<.R3;.R3:.Vsp,(:.&40.R3>.)R39.R38.R37.R36.R35.R34.R33.R32.(:.&40.(2?.(30.R3?.+3.)(31.(12.VR,))))(:.&40.R3?.)R31.R30.R2>.R2?.(:.&40.R3?.)R2=.(:.&40.R24.)R2<.R2;.R2:.R29.R28.)VF,(:.&40.+:95>0.)Vfc,(<.(2.&40.))R42.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
  intros until k120.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE RSL SThi STlo MI PRES PRES2 SS.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKc0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 512) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKc0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 512 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (512 / 8) with 64 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x6b330] [] 848%N). lx_tree.
  lxr_leaf. lx_carry.
  idtac "T-EPI-2".
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  assert (BLa : blocks_low R LB LF) by (destruct PRES as (_ & _ & _ & K); exact K).
  assert (BLb : blocks_low R (LBc ++ LB) LF) by (destruct PRES2 as (_ & _ & _ & K); exact K).
  assert (SFa : shadow_free R LB LF (bv_unsigned sp) (hstkhi asegs R HIA h3) FB (8 * 64)).
  { eapply shadow_free_fresh; [exact FRSH| exact BLa| clear; lia| clear; lia| first [ clear - ALO LOS SLO NS1 STKc0; lia | lx_side_lia ]| exact AP3]. }
  assert (SFb : shadow_free R (LBc ++ LB) LF (bv_unsigned sp) (hstkhi asegs R HIA h3) FB (8 * 64)).
  { eapply shadow_free_fresh; [exact FRSH3| exact BLb| clear; lia| clear; lia| first [ clear - ALO LOS SLO NS1 STKc0; lia | lx_side_lia ]| exact AP3]. }
  replace (Z_to_bv 64 439088) with (Z_to_bv 64 (if Z.eqb 0xf5 0 then arl_set00 R else if Z.eqb 0xf5 0xf5 then arl_setf5 R else arl_setf8 R))
  by (cbn [Z.eqb Pos.eqb]; rewrite SF5; reflexivity).
  change (presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m ma) with (hidden (presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m ma)) in PRES.
  change (presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x ma) with (hidden (presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x ma)) in PRES2.
  pose proof (artA_set_shadow asegs R HIA 0xf5) as SPEC.
  specialize SPEC with (h := h3).
  lazymatch goal with HHc : HM _ _ _ h3 _ _ ma, STc : stk _ ma lo sp1, MIc : mem_inv _ ma, FSALL : rw_cells _ ma (Z.shiftr FB 3 + al_sb AL) _ |- _ =>
  callrt sp1 (eapply SPEC with (LB := LBc ++ LB) (LF := (FB, 512) :: LF) (A := FB) (s := Z.shiftr FB 3 + al_sb AL) (n := 64) (lo := lo); clear SPEC;
  rewrite ?(unsigned_lit sp1) by exact SP1R;
  first [ exact HHc | exact LOS | exact F8 | exact FSALL | exact STc | exact MIc | reflexivity
  | lazymatch goal with
  | |- _ \/ _ \/ _ => right; left; reflexivity
  | |- 0 < 64 => clear; lia
  | |- _ = shadow_of _ _ => unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear; lia
  | |- crange _ FB _ => exact CFB3
  | |- forall x, _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; right; exists (FB, 512); split; [left; reflexivity| cbn; first [ clear - Hx; lia | lx_side_lia ]]
  | |- Z.of_nat _ = 64 => cbn; reflexivity
  | |- lo <= _ => first [ clear - SLO SP1 NS1 STKc0 STKc4; lia | lx_side_lia ]
  | |- crange _ lo _ => eapply crange_sub; [exact SCS3| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]
  end
  | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SETSH-PRE-LEFT:" g end ])
  end.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SETSH-LEFT:" g end.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  rename PC into MUs.
  rename PC0 into WMs.
  rename PC1 into MIs.
  rename PC2 into FSH5.
  rename PC3 into STs.
  rename POST into HHs.
  assert (ESH : shadow_of AL FB = Z.shiftr FB 3 + al_sb AL) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear; lia).
  pose proof MUs as MU'.
  rewrite <- ESH in MU'.
  unfold hidden in PRES, PRES2.
  apply (presW_munch_sh R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m ma mb FB 64 lo sp1) in PRES;
  [| exact MU'| exact WMs| exact CFB3| exact SFa| exact LOS| first [ clear - SP1; lia | lx_side_lia ]| first [ clear - ALO LOS SLO NS1 STKc0; lia | lx_side_lia ]| exact F8].
  apply (presW_munch_sh R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x ma mb FB 64 lo sp1) in PRES2;
  [| exact MU'| exact WMs| exact CFB3| exact SFb| exact LOS| first [ clear - SP1; lia | lx_side_lia ]| first [ clear - ALO LOS SLO NS1 STKc0; lia | lx_side_lia ]| exact F8].
  apply (sshad_munch_sh R HIA h3 ma mb FB 64 lo sp1) in SS;
  [| exact MU'| exact WMs| eapply crange_sub; [exact SCS03| exact SLOS| first [ clear - TOP HTOP3; lia | lx_side_lia ]]| exact F8| left; first [ clear - F1 ALO SLOS; lia | lx_side_lia ]| exact LOS].
  clear MU'.
  idtac "T-EPI-3".
  transport_after_call asegs ma mb MUs WMs.
  clear MI.
  clear HH3.
  clear MUs WMs.
  (* [comment removed for export] *)
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 512) :: LF) mb FB 512 HHs ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 512 - 8) with (FB + 504) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 512) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 512) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 STKc0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 152 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SP1 SLO LOS NS1 STKc0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ]]).
  clear HHs NCp NSp.
  repeat match goal with H : rw_cells _ mb FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ mb (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ mb (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  idtac "EPI-DONE".
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf (sp1 + 152) (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _, RS : rw_cells _ mf sp1 _ |- _ =>
          chunk_to_stk RS;
          lazymatch type of RS with stk _ _ _ ?hi => replace hi with (sp1 + 152) in RS by (clear; lia) end;
          pose proof (stk_merge asegs mf lo sp1 _ ST0 RS ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as ST2;
          pose proof (stk_merge asegs mf lo (sp1 + 152) _ ST2 STA ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as ST3;
          release_frame SV ST3 (bv_unsigned sp); exact ST3 end).
  }
  split; [assumption|].
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Variable PK : pk_class asegs.
  Variable SI : sinv L.
  Variable mo0 : Model.
  Variable d : Z.
  Variables (PHIc : Z -> Z) (FFRc : Z -> Z -> Z) (CNTc : Z -> Z) (C24c : Z).
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).   (* [comment removed for export] *)
  Hypothesis CWXs : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CRT 744.

  Local Notation POST := (x509_crt_parse_der_postA24 asegs R HIA PK SI PHIc FFRc CNTc h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            CRT blen lo slo d m mo0).
  Local Notation WSI := ((CRT, CRT + 744) :: si_fp SI).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L19391405798.10L26892418956.1 L50790731766.11L53969727459.2 L9873114841.11 00000Z00^01>01E022S1R3NS14STKc5STKc02sp3CRT2lo5CRTLO3SLO3SPRS2spS1R3NS14STKc5STKc02sp2lo3SLO3LOSS1R3ACVS1R3NS14STKc5STKc02sp2lo3slo4SLOL3SLO3sp13SP1". (* [comment removed for export] *)
  Lemma c_fin : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_B ()) "Phq,(4.$5.VR,VHIA,)PLc,(21.$15.)PFB,$16.Psp1,$16.Pmm,P,(2.&40.)(3.(2.&8.))Pr,$16.Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pja,(21.(2.&8.))Pjb,(21.(2.&8.))Pk24,(2.&40.)Pk32,(2.&40.)Pk40,(2.&40.)Pk48,(2.&40.)Pk56,(2.&40.)Pk64,(2.&40.)Pk72,(2.&40.)Pk80,(2.&40.)Pk88,(2.&40.)Pk96,(2.&40.)Pk104,(2.&40.)Pk112,(2.&40.)Pk120,(2.&40.)Pob,(2.&40.)Ph1,(2.&40.)Ph2,(2.&40.)Ph3,(2.&40.)Prawlen,$16.Prawp,$16.Ptbt,(2.&40.)Ptbd,(2.&40.)Ptbl,(2.&40.)Ptbp,(2.&40.)Pver,(2.&40.)Pverpad,(2.&40.)Pstg,(2.&40.)Pspd,(2.&40.)Pslen,$16.Psq,$16.Pso1,(2.&40.)Pso2,(2.&40.)Pso3,(2.&40.)Pso4,(2.&40.)Pir1,(2.&40.)Pir2,(2.&40.)Pir3,(2.&40.)Pir4,(2.&40.)Psr1,(2.&40.)Psr2,(2.&40.)Psr3,(2.&40.)Psr4,(2.&40.)Pij48,(21.(2.&8.))Pinext,$16.Pimg,(2.&8.)Pipad,(21.(2.&8.))Psj48,(21.(2.&8.))Psnext,$16.Psmg,(2.&8.)Pspad,(21.(2.&8.))Pdates,(21.(2.&8.))Ppr1,(2.&40.)Ppr2,(2.&40.)Ppr3,(2.&40.)Ppr4,(2.&40.)Ppkinfo,$16.Ppkctx,$16.Pu1,(2.&40.)Pu2,(2.&40.)Pu3,(2.&40.)Pu4,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)Pv3,(2.&40.)Pv4,(2.&40.)Peo,$36.Pej,$37.Pgtg,(2.&40.)Pgpd,(2.&40.)Pglen,$16.Pgq,$16.Psigmd,(2.&40.)Psigpk,(2.&40.)Psigopts,$16.Pinodes,(21.$16.)Psnodes,(21.$16.)Prawjunk,(21.(2.&8.))Ppkowned,(21.$15.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps7v,(2.&40.)Ps8v,(2.&40.)Ps9v,(2.&40.)Ps11v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)P,(20.$5.VR,VHIA,R6>.(14.$15.R6=.VLB,)(23.(24.$16.$16.)(25.$16.$16.R6<.+200.)VLF,)R6:.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R71.R2.)P,(7.$16.(18.$5.VR,VHIA,R70.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R71.)(19.$5.VR,VHIA,Vh,))P,(7.$16.(1:.$5.VR,VHIA,R72.)(1:.$5.VR,VHIA,Vh,))P,(26.(1;.$5.VR,VHIA,R73.)(2?.(1;.$5.VR,VHIA,Vh,)A1.VPHIc,Vblen,))P,(26.(1<.$5.VR,VHIA,R74.)(2?.(1<.$5.VR,VHIA,Vh,)A2.VFFRc,Vblen,Vd,))P,(26.(38.(39.$15.R74.))A1.VCNTc,Vblen,)P,(6.(26.(27.(10.&40.Vsp,)+110.)R73.)(26.R73.(27.(10.&40.Vsp,)+100.)))P,(7.$16.(28.R74.+20.)=)P,(7.$16.(28.R76.+40.)=)P,(29.VR,VLB,VLF,R77.+200.)P,(2:.(17.$5.VR,VHIA,Vh,)R78.+200.)P,(2;.$5.R77.R79.(23.$2<.(2=.R75.)(23.$2<.(2=.R74.)(23.$2<.(2=.R73.)(2>.$2<.)))))P,(2;.$5.R78.(2?.(30.R7:.+3.)(31.(12.VR,)))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?1.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?2.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?8.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.+?3.))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(23.$2<.(32.(:.&8.=))(2>.$2<.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))P,(2;.$5.R79.(2?.(10.&40.Vsp,)-68.)(23.$2<.(2=.Vs11,)(23.$2<.(2=.Vs10,)(23.$2<.(2=.Vs9,)(23.$2<.(2=.Vs8,)(23.$2<.(2=.Vs7,)(23.$2<.(2=.Vs6,)(23.$2<.(2=.Vs5,)(23.$2<.(2=.Vs4,)(23.$2<.(2=.Vs3,)(23.$2<.(2=.Vs2,)(23.$2<.(2=.Vs1,)(23.$2<.(2=.Vs0,)(23.$2<.(2=.Vra,)(2>.$2<.)))))))))))))))P,(2;.$5.R7:.R7;.(23.$2<.(33.#18.R75.)(23.$2<.(2=.R73.)(23.$2<.(2=.R72.)(23.$2<.(2=.R71.)(23.$2<.(2=.R70.)(23.$2<.(2=.R6?.)(23.$2<.(2=.R6>.)(23.$2<.(2=.R6=.)(23.$2<.(2=.R6<.)(23.$2<.(2=.R6;.)(23.$2<.(2=.R6:.)(23.$2<.(2=.R69.)(23.$2<.(2=.R68.)(23.$2<.(2=.R67.)(23.$2<.(33.#10.R74.)(23.$2<.(2=.(:.&40.R7<.))(2>.$2<.))))))))))))))))))P,(?.$5.R7;.(2?.R7<.+98.)(2?.(10.&40.Vsp,)-68.))P,(?.$5.R7<.Vlo,R7=.)P,(>.$5.R7=.)P,(13.$5.VR,VHIA,R82.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)(23.(24.$16.$16.)(25.$16.$16.VCRT,(2?.VCRT,+2>8.))(3:.(3;.VR,)VSI,))Vm,R7>.)P,(11.$5.(12.VR,)R7?.Vslo,R80.)P,(11.$5.(12.VR,)R80.R81.(10.&40.Vsp,))P,(3<.$5.R81.VCRT,R6=.R6<.R6;.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)P,(3=.$5.VPK,R82.(14.$15.R85.VLB,)VCRT,R6>.R6:.R69.R51.R32.R4=.R31.R45.R44.R2?.R3;.R33.R30.)P,(3>.$15.R86.(3?.(40.R6?.R6;.R6:.R52.R33.R4>.R32.R46.R45.R30.R3<.R34.)))P,(41.R6<.(42.+2.+28.))P,(43.(3;.VR,)VSI,R85.)P,(26.(44.(14.$15.R89.VLB,))(2?.(44.VLB,)(45.+2.(46.Vblen,+1701.))))P,(6.(41.(47.(42.+2.+1?.))R86.)(26.R86.=))(48.$5.(49.$5.VR,VHIA,R8<.Vmo0,)(4:.$5.VR,VHIA,VPK,VSI,VPHIc,VFFRc,VCNTc,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VCRT,Vblen,Vlo,Vslo,Vd,Vm,Vmo0,)(8.(9.R34.(:.&40.R89.)Vgp,Vtp,R33.R32.R31.Vsp,(:.&40.R89.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(:.&40.(2?.(30.R8:.+3.)(31.(12.VR,))))(:.&40.R8:.)R28.R27.R25.R26.(:.&40.R8:.)R24.(:.&40.R87.)R23.R22.R21.R20.R1?.)VF,(:.&40.+:95>0.)Vfc,(<.(2.&40.))R88.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE RSL SThi STlo MI PRESq SS1 SS2 CH OW PERM RAWS SIP C24 RR.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq Lc LB LF mm FB 512 FRSH HHq) as FRSHq.
    pose proof (presW_init_at R HIA hq _ _ (Lc ++ LB) LF mm (bv_unsigned sp) (bv_unsigned sp) [] hq HHq
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 STKc0; lia)) as PRES2.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 STKc0; lia)) as SSm.
    assert (CRB : CRT + 744 <= 2^64) by (clear - CRTLO SLO SPR NS1 STKc0; lia).
    destruct (crt_at_build asegs PK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CH OW ALC CRT0 CRB) as [jx CAx].
    destruct CAx as (CCELLS & _ & _ & _ & OWN).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := Lc) (WA := WSI) (WB := @nil ivl) (m2x := mm);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact SSm | exact RSL
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29) as HP29.
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' ((Lc ++ LB) ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((Lc ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    pose proof (blocks_below_hm R HIA h4 _ _ m9 (Lc ++ LB) HH4 ltac:(intros b Hb; exact Hb)) as BB4.
    unfold x509_crt_parse_der_postA24.
    do 15 eexists. exists m9, mo9, h4, r, (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts), jx, Lc.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES9) as HPF; rewrite ESq in HPF; unfold CRT_SIZE; exact HPF|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact ECNT|].
    split.
    { split; [eapply (presA_rw_cells asegs R); [exact HP29| exact CCELLS| replace (Z.of_nat (cells_size (crt_cells (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts) jx))) with 744 by reflexivity; apply CRo; [exact CRTLO| exact (client_range_of_w L _ _ _ _ _ CWXs)]| exact I]|].
      split; [exact ALC|]. split; [exact CRT0|]. split; [unfold CRT_SIZE; exact CRB|].
      eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := @nil ivl) (SP := bv_unsigned sp) (L2 := Lc ++ LB);
        [exact OWN| intros b Hb; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb] | | exact BB4 | clear - ACV; lia| exact MI9| intros b Hb Hk; exact I].
      eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    split; [exact PERM|]. split; [exact (HMND _ _ _ _ HH4)|]. split; [exact RAWS|]. split; [exact HH4|].
    split; [| exact C24].
    eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP29)| intros a Ha; exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
