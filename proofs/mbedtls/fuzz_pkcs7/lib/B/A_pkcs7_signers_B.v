(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_signers_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01853f236235f280 0 3 0 1 35 1 74 1P03ac05655da8d087 0 10 0 1 46 1 51 1 53 1 57 1 64 1 65 1 66 1 73 1 74 1P03f29c07a46e2097 0 6 0 1 57 1 62 1 75 1 76 1 77 1P047a1bf89efce4d3 0 4 0 1 21 1 84 1 85 1P05f623562c4bafe2 0 6 0 1 57 1 62 1 75 1 76 1 77 1P071af2483f82c6d6 0 3 0 1 35 1 74 1P0993f39895c74820 0 6 0 1 57 1 62 1 75 1 76 1 77 1P0cc3eb2d1ae4f998 0 6 0 1 57 1 62 1 75 1 76 1 77 1P0deeba86cfc13c89 0 3 0 1 35 1 74 1P10ca592afa893544 0 3 0 1 35 1 74 1P11472895d7563177 0 3 0 1 35 1 74 1P13dcf8ca6bc76f35 0 3 0 1 35 1 74 1P163d921704c0d6db 0 6 0 1 57 1 62 1 75 1 76 1 77 1P174038b423cea9c1 0 6 0 1 57 1 62 1 75 1 76 1 77 1P1b9af998460cafe7 1 1 64 2 53 1 73 1 3 0 1 72 1 74 64P1e95af064867ceb0 0 3 0 1 35 1 74 1P1eda7cf724f78f62 0 6 0 1 57 1 62 1 75 1 76 1 77 1P1ef9d58a1c9d18fe 0 3 0 1 35 1 74 1P20f998a52dfb512a 1 1 64 2 0 1 72 1 3 2 1 73 1 74 64P20fb1e1d0e4f2263 0 6 0 1 57 1 62 1 75 1 76 1 77 1P215095c601de55ba 0 3 0 1 35 1 74 1P2293e1bcac293707 0 3 0 1 35 1 74 1P25476ceb9a1aa5e5 0 6 0 1 57 1 62 1 75 1 76 1 77 1P255aa4a9b0cd7022 0 3 0 1 35 1 74 1P272941b1a8f01e87 0 6 0 1 57 1 62 1 75 1 76 1 77 1P29c0820ee3c3aca7 0 7 0 1 22 1 57 1 62 1 75 1 84 1 85 1P2ba81c03dfceccf6 1 1 64 2 1 1 72 1 3 0 1 73 1 74 64P2ca0fddc30e6bbbd 0 6 0 1 57 1 62 1 75 1 76 1 77 1P2f7e06fbcca22f61 0 6 0 1 57 1 62 1 75 1 76 1 77 1P32d6bd12187618df 0 4 0 1 21 1 84 1 85 1P393f299a9e1a9b72 0 3 0 1 35 1 74 1P398961348a87513b 0 3 0 1 35 1 62 1P3b34e6922356dcc3 0 6 0 1 57 1 62 1 75 1 76 1 77 1P3bd996eaeca62f4e 0 6 0 1 45 1 50 1 63 1 64 1 65 1P3e51a9396658f833 0 3 0 1 35 1 74 1N02061052e46324d1N08146cc553e3a7d2N1534a90663cea5d1N173ec37f0c98f572N1d56106454ad8770N1dcf4130adc6ed60N1df68c2f21712adaN1e7d90ce66fc5153N217afcf0c6cb95c6N220ac745f5f28327N26563f8ab0152762N309f4a268717a3cbN364ac45b5a7a6dfcN366fc637bfaad2deN368a1cb2e2ac7ce4N39b5d5a0a0158332N39f4c12e9f2f899eN3a92c09207eb08cdN3f0cab7c8b0ca874"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_signers_B () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.EPOST"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55853786883.20000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold A_pkcs7_signers_A.STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBn : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_B ()) "Lms,$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.$5.VR,VHIA,)Lh4,(4.$5.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(6.(7.$0.R11.(8.(9.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(:.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(;.Vra,)Vfc,(<.(2.&40.))R10.(=.$5.)))(6.(>.$5.R10.)(6.(?.$5.R10.Vlo,(10.&40.Vsp,))(6.(11.$5.(12.VR,)R10.Vslo,(10.&40.Vsp,))(6.(13.$5.VR,VHIA,O7.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)O3.O5.R10.)(6.(13.$5.VR,VHIA,O7.(14.$15.O6.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)O2.O4.R10.)(6.(7.P,$16.Sp(17.$5.VR,VHIA,R?.)(17.$5.VR,VHIA,O7.))(6.(7.$16.(18.$5.VR,VHIA,R?.)(18.$5.VR,VHIA,O7.))(6.(7.$16.(19.$5.VR,VHIA,R?.)(19.$5.VR,VHIA,O7.))(6.(7.$16.(1:.$5.VR,VHIA,R?.)(1:.$5.VR,VHIA,O7.))(6.(7.$16.(1;.$5.VR,VHIA,R?.)(1;.$5.VR,VHIA,O7.))(6.(7.$16.(1<.$5.VR,VHIA,R?.)(1<.$5.VR,VHIA,O7.))(6.Pmo,$1=.(1>.(1?.$5.VR,VHIA,R10.R1.)(1?.$5.VR,VHIA,O7.R1.))(20.$5.VR,VHIA,R?.(14.$15.O6.VLB,)VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 Q3; try lx_pin1 Q2; try lx_pin1 Q1; try lx_pin1 DALO; try lx_pin1 CRDA; try lx_pin1 ALD; try lx_pin1 HDA; try lx_pin1 SGLO; try lx_pin1 CWS; try lx_pin1 ALS; try lx_pin1 HSG; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 BIN; try lx_pin1 HBY; try lx_pin1 PPLO; try lx_pin1 CWP; try lx_pin1 ALP; try lx_pin1 HPP; try lx_pin1 sj; try lx_pin1 dq; try lx_pin1 dlen; try lx_pin1 dpad; try lx_pin1 dtg; try lx_pin1 d; try lx_pin1 END; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 NRT; try lx_pin1 STKsi0; try lx_pin1 CNTsi_mono; try lx_pin1 FFRsi_mono; try lx_pin1 PHIsi_mono; try lx_pin1 SIGNER; try lx_pin1 CNTsi; try lx_pin1 FFRsi; try lx_pin1 PHIsi; try lx_pin1 GETTAG; try lx_pin1 FREE; try lx_pin1 CALLOC; try lx_pin1 HMND; try lx_pin1 DIMG; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@D2459793318.138 D32452690557.138D3374278032.137 D43016287773.139D45715803169.137D62011770188.139D64997949699.138D68405837779.137D6909504982.137 L10775412926.125L16578761643.1  L17605293682.119L17605293695.123L19546883927.119L19546883930.123L21224591641.172L30443668812.10 L31168734356.120L31168734361.116L35655538631.10 L38077847203.1  L39844638933.0  L42411609006.0  L45363093875.142L48117620902.120L48117620903.121L48117620904.117L48117620907.116L50790731766.10 L55715474836.2  L60098763854.6  L61745680350.187L61954813928.186L62018535662.1  L67922604617.0  L6912107235.120 L6912107246.116 L9356559676.15  P55705235216.181Q10592386204.143Q10592386207.147Q14681873509.144Q14681873512.148Q22358563588.146Q23218748857.143Q23218748858.147Q23925414036.152Q30147450662.144Q31158247845.142Q31158247869.146Q31168733213.150Q31168734356.148Q31168734361.144Q31314676345.142Q33433749386.179Q34796740410.147Q38248895679.151Q4125667684.178 Q42439443119.180Q42441479401.154Q4279611329.180 Q43880146019.151Q4590099355.179 Q48117620905.147Q48117620906.143Q48132302223.146Q48132302231.142Q5935758158.180 Q59668625896.148Q60382659730.148Q60382659743.144Q62009673036.152Q64133651577.179Q64681502656.154Q64683667846.180Q67397950268.143Q6897428426.146 Q6897428434.142 Q6912107235.148 Q6912107246.144 Q6912108138.150 Q7917062807.148 Q7917062810.144 00000100H00I00g01>01U01l01m02D02j02n03P04204O04l05M05h06;06N06m07107207307R08>08j09V0:B0:]0:^0:h0<=0=S0=V0=W0=j0>=0>h0>i0?<0?O0?P0?Q0?R0?e0@80@N0@O0@b0A50AH0A[0An0Ao0BL0BM0B`0C:0C]0D60DP0Df0EC0Eo0F[0GG0H30HM0HN0HO0HP0H`0I:0Ia0JR0JS0Jf0K90KL0K_0L20LL0LfFS1R5STKsi2LF3LFB2FB3sp1FS1R3HIA5STKsi2LF3LFB2h32FB3sp1S1R5STKsi2LF3LFB2FB3sp1S1R5STKsi2LF3LFB2FB3sp1S1R5STKsi2LF3LFB2FB3sp1FS1R5STKsi2LF3LFB2FB3sp1S1R5STKsi2LF2sp3slo3LFB4SLOS2FB3ALO2F1S2FBS1R5STKsi2LF3LFB2FB3sp14SP1R2F82F0S1R5STKsi2LF3LFB2FB3sp14SP1R2F82F0S1R5STKsi2LF3LFB2FB3sp12F82F0S1R5STKsi2LF3LFB2FB3sp12F82F0S1R5STKsi2LF3LFB2FB3sp14lxHn1p2PBS1R3NS15STKsi2sp2lo3SLO3LOSS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R3HIA5STKsi1h2sp2lo3TOP5HTOP3S2spSSS1R5STKsi2LF2bs3LFB2FB3sp11c2HcS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R3NS15STKsi2sp2lo3SLO3LOSFS1R2lo3LOSS1R5STKsi2LF2sp2PP3BUF3SIG4DALG2lo2bs3LFB3DPB3DSB2D12D22D33SLO2FB3sp13SP12F04lxHn3H15S1R3NS15STKsi2LF2sp2PP3BUF3SIG4DALG2lo2bs3LFB3DPB3DSB2D12D22D33SLO2FB3sp14SP1R2F04lxHnS1RSS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBFFFS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R3HIA5STKsi1h2LF3LFBFS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBFS1R5STKsi2LF3LFB2FB4lxHn1p2PBFS1R5STKsi2LF2lo3LFBS1R5STKsi2LF3LFB4lxHn1p2PBS1R5STKsi2LF3slo3LFB4SLOS4lxHn1p2PBS1R5STKsi2LF3slo3LFB4SLOSS1R5STKsi2LF3LFB4lxHn1p2PBS1R5STKsi2LF2sp2lo3LFBS1R5STKsi2LF3LFB2FB4lxHn1p2PBS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF2sp2lo3slo3LFB4SLOS4SLOL3SLO3ALOS1R5STKsi2LF3LFB4lxHn1p2PBFFFS1R5STKsi2LF3LFBS1R5STKsi2LF3LFB4lxHn1p2PBS1R3HIA5STKsi1h2LF2sp3slo3LFB3TOP5HTOP3S1R3HIA5STKsi1h2LF2sp3slo3LFB3TOP5HTOP34lxHn1p2PBFS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FBS1R5STKsi2LF3LFB2FB3ALO2F1S1R5STKsi2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS D3 D2 D1 DA0 DSB SG0 DPB PP0 LFB bs DALG SIG BUF PP STKsi NS1 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_B ()) "Ph3,(4.$5.VR,VHIA,)PLBn,(21.$15.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(21.$22.)PWB,(21.$22.)PFB,$16.Psp1,$16.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps8v,(2.&40.)Ps11v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pb4,(2.&8.)Pr,$16.P,(20.$5.VR,VHIA,R24.(14.$15.R23.VLB,)(23.(24.$16.$16.)(25.$16.$16.R1=.+40.)VLF,)R20.)P,Px,$16.P,(17.$5.VR,VHIA,Vh,R1.)(17.$5.VR,VHIA,R27.R2.)P,(7.$16.(18.$5.VR,VHIA,R26.)(18.$5.VR,VHIA,Vh,))P,(7.$16.(19.$5.VR,VHIA,R27.)(19.$5.VR,VHIA,Vh,))P,(6.(26.(27.(10.&40.Vsp,)+;0.)R20.)(26.R20.(27.(10.&40.Vsp,)+:0.)))P,(7.$16.(28.R21.+20.)=)P,(7.$16.(28.R23.+40.)=)P,(29.VR,VLB,VLF,R24.+40.)P,(29.VR,(14.$15.R2;.VLB,)VLF,R25.+40.)P,(2:.(17.$5.VR,VHIA,Vh,)R26.+40.)P,PB,$16.Pj,$16.P,(2;.(24.$16.$16.)(25.$16.$16.R2.R1.)VLF,)(2<.(26.(2=.R2:.+40.)R3.)(26.(2=.R3.R2.)R2:.))P,(2>.$5.R2;.R28.(23.$2?.(30.R10.)(23.$2?.(30.R?.)(23.$2?.(30.R>.)(31.$2?.)))))P,(2>.$5.R2<.(2=.(32.R29.+3.)(33.(12.VR,)))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.(:.&8.+?1.))(23.$2?.(34.R>.)(23.$2?.(34.(:.&8.+?3.))(23.$2?.(34.(:.&8.+?3.))(23.$2?.(34.(:.&8.+?3.))(31.$2?.))))))))))P,(2>.$5.R2=.(2=.(10.&40.Vsp,)-68.)(23.$2?.(30.Vs11,)(23.$2?.(30.Vs10,)(23.$2?.(30.Vs9,)(23.$2?.(30.Vs8,)(23.$2?.(30.Vs7,)(23.$2?.(30.Vs6,)(23.$2?.(30.Vs5,)(23.$2?.(30.Vs4,)(23.$2?.(30.Vs3,)(23.$2?.(30.Vs2,)(23.$2?.(30.Vs1,)(23.$2?.(30.Vs0,)(23.$2?.(30.Vra,)(31.$2?.)))))))))))))))P,(?.$5.R2>.R2:.(2=.(10.&40.Vsp,)-68.))P,(?.$5.R2?.Vlo,R2;.)P,(>.$5.R30.)P,(13.$5.VR,VHIA,R35.VLB,VLF,(10.&40.Vsp,)(10.&40.Vsp,)R30.R33.R31.)P,(13.$5.VR,VHIA,R36.(14.$15.R35.VLB,)VLF,(10.&40.Vsp,)(10.&40.Vsp,)R30.R33.R32.)P,(11.$5.(12.VR,)R33.Vslo,(10.&40.Vsp,))P,(6.(35.(36.(37.+2.+1?.))R15.)(35.R15.(37.+2.+1?.)))(38.$5.(12.VR,)(17.$5.VR,VHIA,R39.)(39.R39.R38.R37.R36.R34.R33.R16.)(8.(9.R30.(:.&40.R31.)Vgp,Vtp,R2?.R2>.R2=.Vsp,(:.&40.R31.)R2<.R2;.R2:.R29.R28.R27.R26.R25.(:.&40.R32.)(:.&40.R16.)R20.R1?.R1>.R1=.R1<.(:.&40.R32.)(:.&40.(2=.(32.R32.+3.)(33.(12.VR,))))R1;.R24.R23.R22.R21.)VF,(:.&40.+98;40.)Vfc,(<.(2.&40.))R35.(=.$5.)))")
(* [comment removed for export] *).
  Proof.
  intros until r.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP FHD FSH SAVE ST1 STlo MI PRES PRES2 SS Hr.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBn ++ LB) LF mm FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x98b7c] [] 285%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBn ++ LB) ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 64) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBn ++ LB) ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBn ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
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
  End Call.
End Walk.
