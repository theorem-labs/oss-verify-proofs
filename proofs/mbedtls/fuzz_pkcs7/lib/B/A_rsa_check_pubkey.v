(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_rsa_check_context.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_cmp_int A_mpi_cmp_mpi A_mpi_bitlen A_rsa_check_context.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_rsa_check_pubkey () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_head_cells"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_check_context.rsa_ctxck_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Definition A_RSA_CHECK_PUBKEY : Z := 0x0b26e0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_CKPUB_STACK_A := 192 (only parsing).

Definition rsa_check_pubkey_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (C : Z) (r : rsa_st) (lo slo : Z),
    HM segs R HIA h LB LF m ->
    (length LF < 512)%nat ->
    rw_cells segs m C (rsa_head_cells r) ->
    0 <= r_len r < 2^64 ->
    mpd_at segs m LB (r_N r) -> mpd_at segs m LB (r_E r) ->
    md_addr (r_N r) = C + 16 -> md_addr (r_E r) = C + 32 ->
    md_own (r_N r) <> LStatic -> md_own (r_E r) <> LStatic ->
    (md_own (r_N r) = LHeap -> 0 < md_p (r_N r)) -> (md_own (r_E r) = LHeap -> 0 < md_p (r_E r)) ->
    C mod 8 = 0 -> 0 < C -> C + RSA_CTX_SIZE <= 2^64 ->
    mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
    aobj segs (arl_AL R) (hcs segs R HIA h) m C 48 ->
    (1 <= md_n (r_N r) -> aobj segs (arl_AL R) (hcs segs R HIA h) m (md_p (r_N r)) (4 * md_n (r_N r))) ->
    (1 <= md_n (r_E r) -> aobj segs (arl_AL R) (hcs segs R HIA h) m (md_p (r_E r)) (4 * md_n (r_E r))) ->
    client_range (arl_L R) (LB ++ fdata LF) lo C 48 ->
    stk segs m lo (bv_unsigned sp) ->
    arl_stklo R <= lo ->
    lo <= bv_unsigned sp - RSA_CKPUB_STACK_A ->
    lo <= bv_unsigned sp - 160 - arl_need_smalloc R ->
    bv_unsigned sp <= htop segs R HIA h ->
    bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) ->
    sshad segs (arl_AL R) m slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= bv_unsigned sp - 144 ->
    (C + 48 <= lo \/ bv_unsigned sp <= C) ->
    (md_own (r_N r) = LHeap -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)) ->
    (md_own (r_E r) = LHeap -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)) ->
    a0 = Z_to_bv 64 C ->
    evtA segs (arl_AL R) (hcs segs R HIA h)
      (rsa_ctxck_postA segs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs))
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b2828]).
Local Ltac zchk_new ::= constr:([0x0b26fc; 0x0b2700; 0x0b2704; 0x0b2708]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section CK.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Hypothesis IMG : asan_img_ok (arl_AL R).
  Variable h : HST asegs R HIA.
  Variables (LB LF : list blk).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CKPUB_STACK_A.
  Hypothesis SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo).

  Notation POST := (rsa_ctxck_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME := ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Ltac al_facts :=
    pose proof (art_alwf asegs R HIA) as ALWF; pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L11741095640.65L26924648792.65L27904922642.64L4202106291.65 L43654564952.65L51711223320.63L59499841752.65L7510805464.65 Q15641571313.64Q18364008945.64Q27904922642.64Q32653583601.64Q33915847314.64Q3832213010.64 Q39941340946.64Q44650597233.64Q51233519217.64Q59840696433.64Q66523984274.64Q9840925842.64 00000400800C00G00K00O00S00W00^00e01001701B01M01X01_01f01m02802CS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2spS2sp2loS2sp2loS2sp2lo3SLOS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG LO0 SLO SCS"] Lemma epilogue : forall (m1 : mem) (hc : HST asegs R HIA)
      (xra t0 t1 t2 x0 x1 x2 x3 x4 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    HM asegs R HIA hc LB LF m1 -> ck_hsame asegs R HIA hc h ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells asegs m1 (bv_unsigned sp + -48) FRAME ->
    evtA asegs (arl_AL R) (hcs asegs R HIA h) POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb27e4) fc None m1 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PW HHc HS MI ST FR. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evtA_done. unfold rsa_ctxck_postA. destruct HS as (E1 & E2 & E3 & E4 & E5 & E6 & E7). deexists 17.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [eapply presW_presA; exact PW|].
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    split; [exact E5|]. split; [exact E6|]. split; [exact E7| exact HHc].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG LO0 SLO SCS"] Lemma fail : forall (m1 : mem) (hc : HST asegs R HIA)
      (xra t0 t1 t2 x0 x1 x2 x3 x4 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    HM asegs R HIA hc LB LF m1 -> ck_hsame asegs R HIA hc h ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells asegs m1 (bv_unsigned sp + -48) FRAME ->
    evtA asegs (arl_AL R) (hcs asegs R HIA h) POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb27dc) fc None m1 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PW HHc HS MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG LO0 SLO SCS"] Lemma fail2 : forall (m1 : mem) (hc : HST asegs R HIA)
      (xra t0 t1 t2 x0 x1 x3 x4 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    HM asegs R HIA hc LB LF m1 -> ck_hsame asegs R HIA hc h ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells asegs m1 (bv_unsigned sp + -48) FRAME ->
    evtA asegs (arl_AL R) (hcs asegs R HIA h) POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16384)) x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb27d4) fc None m1 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PW HHc HS MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "0590@C17025492443.146C17027589626.276C17027589627.294C17027589628.239C17027589629.257C17027589631.192D11189028015.123D11189028015.124D2778354014.226 D2778354015.179 D30171831570.180D33586717206.124D35881667587.123D35881667587.124D38384834950.180D38384834950.181D41350365441.192D51449298002.227D51449298002.228D60109446735.146D60111543912.239D60111543913.257D60111543915.192D60111543918.276D60111543919.294D63478228670.227D64311484648.146D936947610.294  D936947611.276  D936947612.257  D936947613.239  K26090385536.294K26090385537.276K26090385540.192K26090385542.257K26090385543.239K26092482720.146K37211889074.123K37211889074.124L10904683277.22 L11246298883.118L11672873254.146L11741095640.117L12174595177.105L13563454509.220L14186142497.0  L14790845925.147L14790846307.193L14791043170.219L14791043171.172L14791043173.126L14791044321.275L14791044323.256L14791044324.237L15442391391.70 L15447306016.117L15899734327.178L15899734327.179L15899734327.225L15899734327.226L16073480909.214L16075583823.167L16085877070.285L1685717371.0   L17090287777.0  L17105561926.110L17105561926.111L17272767236.14 L18101405995.98 L18730093456.70 L19354909044.118L19652550953.97 L20383212091.252L218633476.22   L23280295779.70 L233576990.22   L24400208695.24 L24926391073.0  L25382082548.118L26104603333.3  L26365223677.112L26365223677.113L26365223677.114L26365223677.115L26903911514.270L26924648792.118L27804619052.104L28006855460.117L28011507035.70 L28119365102.22 L29325809668.14 L29325810820.14 L29325810820.17 L29432667347.90 L31378308326.119L31392867444.118L31714561233.140L319065984.22   L34023826209.0  L34506786468.233L35668187074.90 L36294353073.121L36294353073.122L37222368707.2  L37390987758.226L37414286068.118L38235734261.1  L38712304397.14 L38712304397.22 L38712305549.14 L38712305549.17 L38714141719.22 L39835060509.105L40834179097.120L40870879649.0  L4202106291.118 L42435059287.94 L43059266230.117L43442376564.117L43654564952.118L43882049225.3  L43884818473.2  L44801149202.22 L44807702024.22 L45315345526.22 L45330285420.14 L45330285420.22 L45330286572.14 L45330286572.17 L4855685921.0   L51246598228.22 L52069193234.285L53056398486.2  L53517126283.14 L53517127179.14 L54437155233.0  L55197438459.119L55387529092.22 L55394078878.22 L55517648206.22 L58123966592.110L58123966592.111L58755387131.120L59308586893.3  L59499841752.118L60098763883.90 L61391482632.24 L61472094839.22 L61486511469.22 L62022716265.91 L63545986128.146L64688188798.94 L6514053445.2   L65278129752.104L65475478426.22 L66459372650.174L66590572961.0  L7073377794.187 L7510805464.118 L808096237.14   L808096237.17   L808097133.14   L808097133.22   L818846327.22   N10900300768.193N16450080357.258N19439633793.258N21804656085.147N24114234387.240N29348222513.277N29564526036.295N37110879153.147N58601491766.193N60683658069.277N65766519963.240N67346764098.295O17025492443.146O17027589626.276O17027589627.294O17027589628.239O17027589629.257O17027589631.192O33932766418.276O33932766419.294O33932766420.239O33932766421.257O33932766423.192O33934863603.146P13845530960.225P13845530961.178P17097212520.226P17097212521.179P9878841286.225 P9878841287.178 Q10890414220.225Q11905122913.120Q12662757089.119Q14342765596.122Q14696181936.294Q14696181937.276Q14696181940.192Q14696181942.257Q14696181943.239Q14790845925.147Q14790846307.193Q14791043170.219Q14791043171.172Q14791043173.126Q14791044321.275Q14791044323.256Q14791044324.237Q15465823187.122Q15643324129.119Q15766564435.146Q15768661618.276Q15768661619.294Q15768661620.239Q15768661621.257Q15768661623.192Q15897683434.178Q15897683435.225Q16152254692.121Q16152254692.144Q17554297864.122Q18365925601.120Q18694146040.122Q22712450012.123Q22712450012.124Q22956719842.122Q22956719842.123Q23622925864.122Q24198187873.120Q254569562.124  Q25513505925.122Q25513505925.123Q25604052563.120Q25604052563.121Q25662358575.122Q27907200258.120Q27909133984.192Q27909133986.257Q27909133987.239Q27909133988.294Q27909133989.276Q27911231108.146Q27955433697.120Q28119249268.178Q29063872258.119Q31036487312.178Q31228709292.122Q32655500769.120Q32799224464.120Q32799392305.143Q33721217258.121Q33918256002.120Q34820943771.123Q34820943771.124Q35014437530.122Q35074665858.120Q35595639279.121Q35595639279.144Q369648097.120  Q37821600610.122Q37821600610.123Q3830427394.120 Q39939554818.120Q40277632081.179Q41100122114.120Q42437286888.178Q42437286889.225Q44648843873.120Q47111190146.120Q4746191627.122 Q49367596931.143Q49367666466.120Q49628194954.226Q49628194955.179Q49698585326.121Q49698585326.122Q50840533351.146Q50842630464.239Q50842630465.257Q50842630467.192Q50842630470.276Q50842630471.294Q51235796833.120Q52590069023.121Q52590069023.144Q53140858114.120Q53969758199.122Q54124893692.122Q54242951095.122Q55364873099.122Q57198265401.123Q57574552929.120Q58552136721.226Q59151700866.120Q59321350679.123Q59321350679.124Q59321559671.146Q59323656784.239Q59323656785.257Q59323656787.192Q59323656790.276Q59323656791.294Q59843137889.120Q59981801349.122Q59981801349.123Q62022257230.226Q62022257231.179Q62639976808.192Q62639976810.257Q62639976811.239Q62639976812.294Q62639976813.276Q64708948186.226Q64708948187.179Q65075826572.122Q66461567952.225Q66522067074.120Q67528989526.123Q67528989526.124Q7167641263.122 Q7757632185.123 Q9742927161.120 Q9742988696.143 Q9743135771.121 Q9743135771.144 Q9843367298.119 00000100200300400500600l01n02D02Z03704004]05Y06606S07:07W08408P09009T0:40:X0;A0;^0<?0<o0=Z0>E0>l0?J0?c0@80@Q0@f0A;0Af0B]0Bo0CA0Cm0D?0DQ0ED0EE0Em0FU0G=0Ge0HI0I:0If0JR0Jh0KA0Kl0LW0MB0Mm0Mn0Mo0N00N10N20ND0NV0Na0OJ0OX0Oj0PI0Q10Q<0QR0Q]0Q^0Q_0R10R20RI0R`0S70SN0SO0Sa0T30TL0T^0Tn0U90UD0UO0V60VH0VZ0V[0V\0V]0V^0WI0Wa0X90X:0Xj0Y<0Y@0YU0Yj0Z?0ZW0Zl0[>0[R0[S0[e0\@0\Y0\k0]=0]D0]K0]Y0]g0^40^A0^N0^[0^l0^m0^n0^o0_60_:0_>0_?0_W0_d0`10`20`D0`V0`n0a70aI0ac0ad0ah0al0b>0b]0cI0cJ0c\0c]0dL0dM0e10eC0eZ0f10fH0f_0g60gM0gh0hC0hZ0i10iM0in0jE0j\0k80kO0l00l;0lF0lQ0l\0lg0m20m30m40m50m60m70m80m]0n60n[0o40o_10>11011A11R11\12312E12S12e13313O13k14G14c15?15d16D16d16e16f17>17Z18;18S18o19G19b1:=1:>1:?1:@1:A1:R1;11;\1<D1=51=F1=W1>H1>I1>J1>Z1>j1>k1??1?S1?k1@?1@\1A41AH1AY1B?1BU1C;1CM1CN1CZ1Cf1D61DJ1E;1F51FG1F]1Fi1G51GF1Gl1H[1Ho1IC1IU1Ik1J@1JU1JV1Jl1Jm1K91KE1KR1K_1L91LS1Lc1M31MG1MW1Mk1ND1NE1Nb1OH1O^1P01PA1PB1PC1Pi1Q:1QS1Qi1Qj1Qk1Ql1Qm1Qn1Qo1R01R11R21RU1SD1SP1S\1Sm1TB1TS1Tm1UB1UC1UD1UE1V71VK1W11Wc1Wd1XL1XX1Xd1Y01Y<1YPFFFFFFS1R2LF2ra2sp1C1r2lo3LFB2C04SLOS3SLO3SPB2HB5Ha_st5Hl_stS1R2LF2ra2sp2s01C1r2lo3LFB2C04SLOS3SLO3SPB2HB5Ha_st5Hl_st2s12s22s3S2LF2ra2sp1C1r3LFB3x14S2LF2ra2sp1C1r3LFB3x14S2LF2ra2sp1C1r3LFB3x143x132HxS1R2LF2ra2sp2s41C1r2lo3LFB2C04SLOS3SLO3SPB2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1C1r3LFB3TOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2s01C1r3LFB3TOP2HB5Ha_st5Hl_st2s12s22s32s4S2LF2ra2sp1C1r3LFB3x143x132HxS2LF2ra2sp1C1r3LFB3x143x132HxS1R3HIA2LF2ra2sp1C1r2lo3LFB3x142h14TOP1S2LF2ra2sp1C1r3LFB3x143x422HxS2LF2ra2sp1C1r3LFB3x143x422HxS1R2LF2ra2sp1C1r2lo3LFB4SLOSS1R2LF2ra2sp1C1r2lo3LFB4SLOS3x14S1R2LF2ra2sp1C1r2lo3LFB4SLOS3x143x72S1R2LF2ra2sp1C1r2lo3LFB4SLOS3x14S1R2LF2ra2sp1C1r2lo3LFB4SLOS3x143x72S1R2LF2ra2sp1C1r2lo3LFB4SLOS3x143x724x104S2LF2ra2sp1C1r3LFB3x143x422HxS1R3HIA1h2LF2ra2sp1C1r2lo3LFB3TOPS1R3HIA2LF2ra2sp1C1r2lo3LFB3x142h24TOP23x724x104S1R3HIA2LF2ra2sp1C1r2lo3LFB3x142h24TOP23x72S1R3HIA2LF2ra2sp1C1r2lo3LFB3x142h24TOP23x72S1R3HIA2LF2ra2sp1C1r2lo3LFB3x142h24TOP2S2LF2sp1C1r2lo3LFB2DC3x724x104S2LF2sp1C1r2lo3LFB2DC3x72S2LF2sp1C1r2lo3LFB2DCS2LF2sp1C1r2lo3LFB2DC3x72S2LF2sp1C1r2lo3LFB2DCS2LF2sp1C1r2lo3LFB2DCS2LF2ra2sp1C1r2lo3LFB3SLO2DC2HB5Ha_st5Hl_stS2LF2sp2s01C1r2lo3LFB3SLO2DC2HB5Ha_st5Hl_st2s12s22s32s4S1R3HIA2sp2h14TOP1S2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r2lo3LFB2C03SLO3SPA3SPB3LO03x14S2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBS1R3HIA2LF2ra2sp1C1r3LFB2C03SPB3x142h14TOP12h24PC12SS2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x14S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x14S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x14S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x14S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO0S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x143x724x104S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x143x72S2LF2ra2sp1C1r2lo3LFB2C03SLO3SPB3LO03x143x72S2ra2sp1C1r3CAL2C03SPBS2LF2ra2sp1C1r3LFB2C03CSZS1R2LF2ra2sp1C1r2lo3LFB2C04SLOS3SLO3SPB3x14S1R2LF2ra2sp1C1r2lo3LFB2C04SLOS3SLO3SPB3x14S1R2LF2ra2sp1C1r2lo3LFB2C04SLOS3SLO3SPB3x14S1R2LF2ra2sp1C1r2lo3LFB2C04SLOS3SLO3SPB3x14FFFSSS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBS2sp2lo3SLOS1R2LB2LF2ra2sp1C2lo3LFB2C02DC3SPB1a2Ha1XS2ra2sp1C1r2C0S2LF2ra2sp1C1r3LFBS2LF2ra2sp1C3LFB2C02DC3SPB1a2HaS2LF2ra2sp1C1r3LFB3x143x723x883PC15POST2S2sp2lo3SLOS2ra2sp1C1r3CAL2C03SPBS2sp2lo3SLOFSS2LF2ra2sp1C1r3LFBFS2LF2ra2sp1C1r3LFB1a2HaS2LF2ra2sp1C1r3LFB1a2HaS2LF2ra2sp1C1r3LFB1a2HaS2LF2ra2sp1C1r3LFB1a2HaFS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFB2C03CSZS2ra2sp1C1r2C03CSZS1R3HIA1h2sp3TOPS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS1R2LF2ra2sp1C2lo3LFB2C04SLOS3SPB3ALO1HS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBFFSFS1R3HIA1h2LF2ra2sp1C2lo3LFB2C03TOP3SPB4HTOPS2LF2ra2sp1C1r2lo3LFB2H0S2LF2ra2sp1C1r2lo3LFB2H0FS1R3HIA1h2LF2ra2sp1C1r3LFB2C03SPB3x142h12EK2xc1HS2LF2ra2sp1C1r3LFBS2loS2sp1C1r2lo2AN2DC3SPBS2sp1C1r2lo2AN2DC3SPBS2sp1C1r2lo2AE2DC3SPBS2sp1C1r2lo2AE2DC3SPB2ANS2sp1C1r2lo2AE2DC3SPBS2LF2ra2sp1C1r3LFBS1R2LF2ra2sp1C1r3LFBSS2LF2ra2sp1C1r3LFBS1R2LF2ra2sp1C3slo3LFB4SSL1S2LF2ra2sp1C1r2lo3LFB3SLOS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBS2sp2loS2sp2loS1R2sp2lo4SLO2S1R2sp2lo4SLO2S2sp1r2lo3DE'S2sp1r2lo3DN'S2sp1r2lo3DN'S2sp1r2lo3DE'S2sp1r2lo3DE'3DN'SFFS2sp2loS2spS2spSS2LF2ra2sp1C1r2lo3LFB2DCS2sp3slo4SSL2S2sp3slo4SSL2FS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r3LFBS2LF2ra2sp1C1r2lo3LFB2DCS1r2N02HnS2LF2ra2sp1C1r3LFBS1R2LF2ra2sp1C2lo3LFB4SLOSFS2spS2spS1R2LF2ra2sp1C3LFBS2LF2ra2sp1C1r3slo3LFB4SSL23x14S1R3HIA1h2LF2ra2sp1C3slo3LFB2C03TOP3SPB4HTOPFS2LF2ra2sp1C1r3LFBFS1R3HIA1h2LF2ra2sp1C1r3LFB2C03TOP3SPB3x142h12EHSS2LF2ra2sp1C1r3LFB3x143x433PC05POST0S2LF2ra2sp1C1r3LFBS2sp2lo3SLO3SPA3SPB3LO0S2sp2lo3SLO3SPA3SPB3LO0S2sp2lo3SLO3SPA3SPB3LO0S2sp2lo3SLO3SPA3SPB3LO0S2sp2lo3SLO3SPA3SPB3LO0S2LF2sp1r2lo3LFB3x442C1S2LF2sp1r2lo3LFB3x723x892C1S2LF2sp1r2lo3LFB3x723x892C1S2LF2sp1r2lo3LFB3x152C1S2LF2sp1r2lo3LFB3x732C1S2LF2sp1r2lo3LFB3x724x1052C1S2LF2sp1r2lo3LFB3x724x1044x1202C1S2LF2sp1r2lo3LFB3x152C1S2LF2sp1r2lo3LFB3x442C1S2LF2sp1r2lo3LFB3x724x1052C1S2LF2sp1r2lo3LFB3x732C1S2LF2sp1r2lo3LFB3x724x1044x1202C1S2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOFFFFFFS2LF2sp1C1r2lo3LFB3SLO2DC3x433PC03Kb4S2LF2sp1C1r2lo3LFB3SLO2DCS2LF2sp1C1r2lo3LFB3SLO2DC3x433PC03Kb4S2LF2sp1C1r2lo3LFB3SLO2DCS2LF2sp1C1r2lo3LFB2AE3SLO2DC3x433PC03Kb42ANS2LF2sp1C1r2lo3LFB2AE3SLO2DC2ANS1R3HIA1h2LF2sp1r3LFB4HTOP2h13PC43PC52h24PC124TOP2S2LF2sp1r3slo3LFBS2LF2sp1r3slo3LFBS2LF1r3LFBS2LF1r3slo3LFB3x724x104S2LF1r3slo3LFB3x72S2LF1r3slo3LFBS2LF1r3slo3LFB3x72S2LF1r3slo3LFBS2LF2sp1r2lo3LFB3SLO3SPB3LO0S2LF2sp1r2lo3LFB3SLO3SPB3LO0S2LF2sp1r2lo3LFB3SLO3SPB3LO0S2LF2sp1r2lo3LFB3SLO3SPB3LO0S2LF2sp1r2lo3LFB3SLO3SPB3LO0S2LF2sp1r2lo3LFB3SLO3SPB3LO03x724x104S2LF2sp1r2lo3LFB3SLO3SPB3LO03x72S2LF2sp1r2lo3LFB3SLO3SPB3LO03x72FFS1R2LF1r2lo3LFB4SLOS3ALOS1R2LF1r2lo3LFB4SLOS3ALO3x72S1R2LF1r2lo3LFB4SLOS3ALO3x724x104S1R2LF1r2lo3LFB4SLOS3ALOS1R2LF1r2lo3LFB4SLOS3ALO3x72S1R2LF1r2lo3LFB4SLOS3ALOS1R2LF2sp1r2lo3LFB4SLOS3SLOS1R2LF2sp1r2lo3LFB4SLOS3SLOFFFFS1R2LF1r3LFB4IMG'S2LF2ra2sp1r3LFB2HB5Ha_st5Hl_stS2LF2sp2s01r3LFB2HB5Ha_st5Hl_st2s12s22s32s4S2LF2ra2sp1r3slo3LFB4SSL22HB5Ha_st5Hl_stS2LF2sp2s01r3slo3LFB4SSL22HB5Ha_st5Hl_st2s12s22s3S1R2LF1r3LFB4IMG'S2LF2sp1r3slo3LFBS1R2LF2sp2s41r2lo3LFB4SLOS3SLO3ALO2HB5Ha_st5Hl_stFFS2LF2sp1r3LFB2HBS2LF2sp1r3LFB2HBFS2LF2sp1r2lo3LFB3SLOS2LF2sp1r2lo3LFB3SLOS2LF2sp1r2lo3LFB3SLO3x72S2LF2sp1r2lo3LFB3SLOS2LF2sp1r2lo3LFB3SLO3x724x104S2LF2sp1r2lo3LFB3SLO3x72S2LF2sp1r2lo3LFB3SLOS2LF2sp1r3slo3LFBS1R3HIA1h2LF2sp1r3LFB4HTOP2h13PC44TOP1S2LF2sp1r3slo3LFB4SSL2S1R3HIA1h2LF2sp1r3LFB4HTOP2h13PC44TOP1S1R2LF1r3LFB5ALWF'FS2LF1C1r3LFBS2LF1C1r3LFBS2LF2sp1r3LFB2HBS2LF2sp1r2lo3LFB3SLOS1R2LF2ra2sp1r2lo3LFB4SLOS3SLO3ALO2HB5Ha_st5Hl_stS1R2LF2sp2s01r2lo3LFB4SLOS3SLO3ALO2HB5Ha_st5Hl_st2s12s22s3S1R2LF1r3LFB5ALWF'S2LF2sp1r3slo3LFB4SSL2S2LF1C1r3LFBS2LF1C1r3LFBS2LF2sp1r3slo3LFBS2LF2ra2sp1r2lo3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp2s01r2lo3LFB3SLO2HB5Ha_st5Hl_st2s12s22s3S2LF2sp1r2lo3LFB3SLOS2LF2sp1r2lo3LFB3SLOS1R3HIA1h2LF1r3LFBS2LF2sp1r3slo3LFB4SSL2S1R2LF1r3slo3LFB4SSL1S1R2LF1r3slo3LFB4SSL1FS2LF2sp1r3slo3LFB4SSL2FS2LF1C1r3LFBS2LF1C1r3LFBS2LF2sp1r3LFBS2LF2sp1r3LFBS2LF2sp1r3LFB3SPB2HB5Ha_stS2LF2sp1r3LFB3SPB2HB5Ha_stS2LF2sp1r2lo3LFBS2LF2sp1r2lo3LFBS2LF2sp1r2lo3LFB3x72S2LF2sp1r2lo3LFBS2LF2sp1r2lo3LFB3x72S2LF2sp1r2lo3LFB3x724x104FS2LF2ra2sp1C1r3LFB3CAL2C03SPBS2LF2ra2sp1C1r3LFB3CAL2C03SPB3x144POSTS2LF2sp1r3slo3LFB4SSL2S1R2LF1r3LFB5ALWF'S1R2LF1r3LFB4IMG'FFS2LF2sp2s41r2lo3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp1r3slo3LFBS1R3HIA1h2LF1r3LFB2h13PC5S2LF2sp1r3slo3LFB4SSL2FFFFFFFFFS2LF2ra2sp1r3slo3LFB2HB5Ha_st5Hl_stS2LF2sp2s01r3slo3LFB2HB5Ha_st5Hl_st2s12s22s32s4S1R2LF1r3LFBS1R2LF1r3LFBS2LF2sp1r3slo3LFBS2LF2sp1r3slo3LFB3x72S2LF2sp1r3slo3LFBS2LF2sp1r3slo3LFB3x724x104S2LF2sp1r3slo3LFB3x72FFFS1R3HIA1h2LF2sp1r3LFB4HTOP2h13PC43PC52h24PC124TOP2S2LF2sp1r2lo3LFB3SLOS2LF2ra2sp1r2lo3LFB3SLO2HB5Ha_st5Hl_stS2LF2sp2s01r2lo3LFB3SLO2HB5Ha_st5Hl_st2s12s22s32s4FS2LF2sp2s41r3slo3LFB4SSL22HB5Ha_st5Hl_stS2LF1C1r3LFBS2LF1C1r3LFBS2LF1C1r3LFBS2LF1C1r3LFBS2LF2sp1r2lo3LFB3SLO". (* [comment removed for export] *)
Theorem A_rsa_check_pubkey_spec : forall (R : art_layout) (HIA : artA asegs R),
    asan_img_ok (arl_AL R) -> arl_uar_got R = A_UAR_GOT_CI -> arl_smalloc R 0 = A_SMALLOC_0_CI ->
    0 <= arl_need_smalloc R ->
    rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY.
Proof.
  intros R HIA IMG UG SM0 NS0. unfold rsa_check_pubkey_stmtA, A_RSA_CHECK_PUBKEY. intros until slo.
  intros HH LFB HD LEN MN ME AN AE NSN NSE PN PE CAL C0 CSZ MI RA OC ON OE CRC ST SLOS SLO SLO2 TOP SPA TPV SSH SSL1 SSL2 DC DN DE ->.
  unfold RSA_CTX_SIZE in CSZ.
  pose proof (art_alwf asegs R HIA) as ALWF. pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP. pose proof (art_lo asegs R HIA) as ALO.
  assert (LO0 : 0 <= lo) by (pose proof (@alloc_ceiling_pos (arl_L R)); lia).
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| lia| lia]).
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(lia)) as PW.
  pose proof (ck_hsame_refl asegs R HIA h) as HS0.
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  assert (SCSS : crange (hcs asegs R HIA h) slo (bv_unsigned sp - slo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| lia| lia]).
  assert (CRC48 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -48) C 48).
  { unfold client_range, client_addr in CRC |- *. intros a Ha. destruct DC as [DC|DC]; [| left; lia].
    destruct (CRC a Ha) as [X|X]; [lia| right; exact X]. }
  dpose MN as [[_ (_ & _ & LENN & NRN & OWNN)] SGN]. dpose ME as [[_ (_ & _ & LENE & NRE & OWNE)] SGE]. unfold MPI_MAX_LIMBS in NRN, NRE.
  assert (ON16 : aobj asegs (arl_AL R) (hcs asegs R HIA h) m (md_addr (r_N r)) 16) by (rewrite AN; eapply aobj_sub; [exact OC| lia| lia]).
  assert (OE16 : aobj asegs (arl_AL R) (hcs asegs R HIA h) m (md_addr (r_E r)) 16) by (rewrite AE; eapply aobj_sub; [exact OC| lia| lia]).
  assert (DN' : 1 <= md_n (r_N r) -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DN eq_refl)| exfalso; exact (NSN eq_refl)]. }
  assert (DE' : 1 <= md_n (r_E r) -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DE eq_refl)| exfalso; exact (NSE eq_refl)]. }
  assert (CLN : 1 <= md_n (r_N r) -> client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -48) (md_p (r_N r)) (4 * md_n (r_N r))).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| | exfalso; exact (NSN eq_refl)].
    destruct OWNN as (_ & HIN & _). eapply client_range_block; [apply in_or_app; left; exact HIN| lia| lia]. }
  assert (CLE : 1 <= md_n (r_E r) -> client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -48) (md_p (r_E r)) (4 * md_n (r_E r))).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| | exfalso; exact (NSE eq_refl)].
    destruct OWNE as (_ & HIN & _). eapply client_range_block; [apply in_or_app; left; exact HIN| lia| lia]. }
  assert (CRN : client_range (arl_L R) (LB ++ fdata LF) lo (md_addr (r_N r)) 16)
    by (rewrite AN; unfold client_range in CRC |- *; intros a Ha; apply CRC; lia).
  assert (CRE : client_range (arl_L R) (LB ++ fdata LF) lo (md_addr (r_E r)) 16)
    by (rewrite AE; unfold client_range in CRC |- *; intros a Ha; apply CRC; lia).
  assert (CRN48 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -48) (md_addr (r_N r)) 16)
    by (rewrite AN; unfold client_range in CRC48 |- *; intros a Ha; apply CRC48; lia).
  assert (CRE48 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -48) (md_addr (r_E r)) 16)
    by (rewrite AE; unfold client_range in CRC48 |- *; intros a Ha; apply CRC48; lia).
  assert (TRN' : forall ma mb, mpd_at asegs ma LB (r_N r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DN EO); lia. }
  assert (TRE' : forall ma mb, mpd_at asegs ma LB (r_E r) -> munch [(lo, bv_unsigned sp)] ma mb -> wmono asegs ma mb -> mpd_at asegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (DE EO); lia. }
  assert (SCS48 : crange (hcs asegs R HIA h) lo (bv_unsigned sp + -48 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SLO; lia]).
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
  zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PROLOGUE-LEFT:" g end.
  pose proof (A_mpi_size_spec (arl_AL R) IMG) as SPs. unfold mpi_size_stmtA, mpi_query_stmtA in SPs.
  pose proof (A_mpi_cmp_int_spec R HIA IMG UG SM0 NS0) as SPc. unfold mpi_cmp_int_stmtA, mpi_cmp_int_postA in SPc.
  pose proof (A_mpi_get_bit_spec (arl_AL R) IMG) as SPg. unfold mpi_get_bit_stmtA, mpi_query_stmtA in SPg.
  pose proof (A_mpi_bitlen_spec (arl_AL R) IMG) as SPb. unfold mpi_bitlen_stmtA, mpi_query_stmtA in SPb.
  pose proof (A_mpi_cmp_mpi_spec (arl_AL R) IMG) as SPm. unfold mpi_cmp_mpi_stmtA in SPm.
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
  cur_aobj CSOK SCS MU ON ONb. cur_aobj CSOK SCS MU OE OEb.
  lazymatch goal with SSx : sshad _ _ ?mc slo (bv_unsigned sp) |- _ =>
    destruct (sshad_split asegs (arl_AL R) mc slo (bv_unsigned sp + -48) (bv_unsigned sp) SSx ltac:(lia) ltac:(lia)) as [SSa SSb]; clear SSb end.
  callrt (bv_unsigned sp + -48)
    (eapply SPc with (h := h) (LB := LB) (LF := LF) (lo := lo) (slo := slo) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity;
     first [ exact CRN | (intros NSx; exfalso; exact (NSN NSx))
           | clear - SLO SLO2 SPA SPB LO0 CSZ C0 DC AN DN' NRN SSL1 SSL2 TOP; first [lia | rewrite AN; lia | intros Hn; destruct (DN' Hn); lia]
           | qside SLO SPA SPB LO0 CSZ C0 DC ONb TRN' MN AN DN' NRN SCS48 ]).
  clear SPc.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPN-LEFT:" g end.
  lazymatch goal with H : presA _ _ _ _ _ _ _ _ ?ma ?mb |- _ => rename H into HP1; rename ma into mc1; rename mb into mn1 end.
  lazymatch goal with H : HM _ _ _ ?hh LB LF mn1 |- _ => rename hh into h1; rename H into HH1 end.
  assert (HS1 : ck_hsame asegs R HIA h1 h) by (unfold ck_hsame; do 6 (split; [assumption|]); assumption).
  assert (TOP1 : bv_unsigned sp <= htop asegs R HIA h1) by (destruct HS1 as (_ & EH & _); lia).
  assert (MN1 : mpd_at asegs mn1 LB (r_N r)).
  { eapply mpd_at_presA_ck; [exact HP1| | exact NSN| exact CRN48].
    match goal with MUx : munch _ m mc1, WMx : wmono asegs m mc1 |- _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end. }
  assert (ME1 : mpd_at asegs mn1 LB (r_E r)).
  { eapply mpd_at_presA_ck; [exact HP1| | exact NSE| exact CRE48].
    match goal with MUx : munch _ m mc1, WMx : wmono asegs m mc1 |- _ => eapply TRE'; [exact ME| exact MUx| exact WMx] end. }
  assert (ON1 : 1 <= md_n (r_N r) -> aobj asegs (arl_AL R) (hcs asegs R HIA h) mn1 (md_p (r_N r)) (4 * md_n (r_N r))).
  { intros Hn. eapply (presA_aobj0 asegs R); [exact CSOK| exact HP1| exact (ONb Hn)| solve_cs_top| right; split; [exact (CLN Hn)| lia]]. }
  assert (OE1 : 1 <= md_n (r_E r) -> aobj asegs (arl_AL R) (hcs asegs R HIA h) mn1 (md_p (r_E r)) (4 * md_n (r_E r))).
  { intros Hn. eapply (presA_aobj0 asegs R); [exact CSOK| exact HP1| exact (OEb Hn)| solve_cs_top| right; split; [exact (CLE Hn)| lia]]. }
  presA_transport HP1. clear HP1 ONb OEb.
  lazymatch goal with H : HM _ _ _ h LB LF mc1 |- _ => clear H end.
  repeat lazymatch goal with H : stk _ mc1 _ _ |- _ => clear H end.
  clear MU WM MN ME ON OE. rename MN1 into MN. rename ME1 into ME. rename ON1 into ON. rename OE1 into OE.
  pose proof (munch_refl [(lo, bv_unsigned sp)] mn1) as MU. pose proof (wmono_refl asegs mn1) as WM.
  pose proof (hm_abase asegs R HIA h1 LB LF mn1 HH1) as AB1.
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
  cur_aobj CSOK SCS MU OE OEa. cur_aobj CSOK SCS MU ON ONa.
  pose proof (A_mpi_cmp_int_spec R HIA IMG UG SM0 NS0) as SPc. unfold mpi_cmp_int_stmtA in SPc.
  specialize (SPc h1). rewrite (proj1 HS1) in SPc. unfold mpi_cmp_int_postA in SPc.
  callrt (bv_unsigned sp + -48)
    (eapply SPc with (LB := LB) (LF := LF) (lo := lo) (slo := slo) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
     try eassumption; try reflexivity;
     first [ exact CRE | (intros NSx; exfalso; exact (NSE NSx))
           | clear - SLO SLO2 SPA SPB LO0 CSZ C0 DC AE DE' NRE SSL1 SSL2 TOP1; first [lia | rewrite AE; lia | intros Hn; destruct (DE' Hn); lia]
           | qside SLO SPA SPB LO0 CSZ C0 DC OEa TRE' ME AE DE' NRE SCS48 ]).
  clear SPc.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPE-LEFT:" g end.
  lazymatch goal with H : presA _ _ _ _ _ _ _ _ ?ma ?mb |- _ => rename H into HP2; rename ma into mc2; rename mb into mn2 end.
  lazymatch goal with H : HM _ _ _ ?hh LB LF mn2 |- _ => rename hh into h2; rename H into HH2 end.
  pose proof (ck_hsame_trans asegs R HIA h2 h1 h ltac:(unfold ck_hsame; do 6 (split; [assumption|]); assumption) HS1) as HS2.
  assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (destruct HS2 as (_ & EH & _); lia).
  assert (MN2 : mpd_at asegs mn2 LB (r_N r)).
  { eapply mpd_at_presA_ck; [exact HP2| | exact NSN| exact CRN48].
    match goal with MUx : munch _ mn1 mc2, WMx : wmono asegs mn1 mc2 |- _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end. }
  assert (ME2 : mpd_at asegs mn2 LB (r_E r)).
  { eapply mpd_at_presA_ck; [exact HP2| | exact NSE| exact CRE48].
    match goal with MUx : munch _ mn1 mc2, WMx : wmono asegs mn1 mc2 |- _ => eapply TRE'; [exact ME| exact MUx| exact WMx] end. }
  assert (CTOP1 : forall xc, hcs asegs R HIA h xc -> xc < hstkhi asegs R HIA h1).
  { intros xc Hxc. pose proof (hcs_below_top asegs R HIA h xc Hxc). destruct HS1 as (_ & _ & EK & _). lia. }
  assert (ON2 : 1 <= md_n (r_N r) -> aobj asegs (arl_AL R) (hcs asegs R HIA h) mn2 (md_p (r_N r)) (4 * md_n (r_N r))).
  { intros Hn. eapply (presA_aobj0 asegs R); [exact CSOK| exact HP2| exact (ONa Hn)| exact CTOP1| right; split; [exact (CLN Hn)| lia]]. }
  assert (OE2 : 1 <= md_n (r_E r) -> aobj asegs (arl_AL R) (hcs asegs R HIA h) mn2 (md_p (r_E r)) (4 * md_n (r_E r))).
  { intros Hn. eapply (presA_aobj0 asegs R); [exact CSOK| exact HP2| exact (OEa Hn)| exact CTOP1| right; split; [exact (CLE Hn)| lia]]. }
  presA_transport HP2. clear HP2 ONa OEa.
  lazymatch goal with H : HM _ _ _ h1 LB LF mc2 |- _ => clear H end.
  repeat lazymatch goal with H : stk _ mc2 _ _ |- _ => clear H end.
  clear MU WM MN ME ON OE. rename MN2 into MN. rename ME2 into ME. rename ON2 into ON. rename OE2 into OE.
  pose proof (munch_refl [(lo, bv_unsigned sp)] mn2) as MU. pose proof (wmono_refl asegs mn2) as WM.
  pose proof (hm_abase asegs R HIA h2 LB LF mn2 HH2) as AB2.
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
