(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_rsa_check_context.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_cmp_int A_mpi_bitlen.
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
Ltac2 gd_tbl_A_rsa_check_context () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_head_cells"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "rsa_ctxck_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Definition A_RSA_CHECK_CONTEXT : Z := 0x0b2cb0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_CTXCK_STACK_A := 208 (only parsing).

Definition rsa_ctxck_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (h : HST segs R HIA)
    (LB LF : list blk) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := fun ms' =>
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (h' : HST segs R HIA),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
    /\ presA segs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m'
    /\ hcs segs R HIA h' = hcs segs R HIA h /\ htop segs R HIA h' = htop segs R HIA h
    /\ hstkhi segs R HIA h' = hstkhi segs R HIA h /\ hflag segs R HIA h' = hflag segs R HIA h
    /\ havol segs R HIA h' = havol segs R HIA h /\ hfr segs R HIA h' = hfr segs R HIA h
    /\ (forall mo, HK segs R HIA h' mo <-> HK segs R HIA h mo)
    /\ HM segs R HIA h' LB LF m'
(* [comment removed for export] *).

Definition rsa_check_context_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
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
    lo <= bv_unsigned sp - RSA_CTXCK_STACK_A ->
    lo <= bv_unsigned sp - 176 - arl_need_smalloc R ->
    bv_unsigned sp <= htop segs R HIA h ->
    bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) ->
    sshad segs (arl_AL R) m slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= bv_unsigned sp - 160 ->
    (C + 48 <= lo \/ bv_unsigned sp <= C) ->
    (md_own (r_N r) = LHeap -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)) ->
    (md_own (r_E r) = LHeap -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)) ->
    a0 = Z_to_bv 64 C ->
    a1 = Z_to_bv 64 0 ->
    evtA segs (arl_AL R) (hcs segs R HIA h)
      (rsa_ctxck_postA segs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs))
(* [comment removed for export] *).

Definition ck_hsame (segs : list Segment) (R : art_layout) (HIA : artA segs R) (h' h : HST segs R HIA) : Prop :=
  hcs segs R HIA h' = hcs segs R HIA h /\ htop segs R HIA h' = htop segs R HIA h
  /\ hstkhi segs R HIA h' = hstkhi segs R HIA h /\ hflag segs R HIA h' = hflag segs R HIA h
  /\ havol segs R HIA h' = havol segs R HIA h /\ hfr segs R HIA h' = hfr segs R HIA h
  /\ (forall mo, HK segs R HIA h' mo <-> HK segs R HIA h mo).

Lemma ck_hsame_refl : forall segs R HIA h, ck_hsame segs R HIA h h.
Proof. intros. unfold ck_hsame. repeat split; try reflexivity; intros; tauto. Qed.

Lemma ck_hsame_trans : forall segs R HIA h2 h1 h,
  ck_hsame segs R HIA h2 h1 -> ck_hsame segs R HIA h1 h -> ck_hsame segs R HIA h2 h.
Proof.
  intros segs R HIA h2 h1 h (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold ck_hsame. do 6 (split; [congruence|]).
  intros mo; split; intros X; [apply B7, A7, X| apply A7, B7, X].
Qed.

Lemma mpd_at_presA_ck : forall (R : art_layout) (LB LF : list blk) (SP SSP TOP : Z) (m m' : mem) (d : mpd),
  presA asegs R LB LF SP SSP TOP [] m m' -> mpd_at asegs m LB d -> md_own d <> LStatic ->
  client_range (arl_L R) (LB ++ fdata LF) SP (md_addr d) 16 -> mpd_at asegs m' LB d.
Proof.
  intros R LB LF SP SSP TOP m m' d HP [(HC & HA & HP0 & HL & HN & HO) HS] NS CR.
  split; [| exact HS]. split; [| split; [exact HA| split; [exact HP0| split; [exact HL| split; [exact HN|]]]]].
  - eapply presA_rw_cells; [exact HP| exact HC| exact CR| exact I].
  - destruct (md_own d) eqn:EO; [exact HO| | exfalso; exact (NS eq_refl)].
    cbv beta iota in HO |- *.
    destruct HO as (H1 & HIN & HAL & HU). split; [exact H1|]. split; [exact HIN|]. split; [exact HAL|].
    eapply u32arr_of_cells; [| reflexivity].
    eapply presA_rw_cells; [exact HP| apply u32arr_cells; exact HU| | exact I].
    cbn [cells_size csize]. eapply client_range_block; [apply in_or_app; left; exact HIN| lia| lia].
Qed.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b2e9c]).
Local Ltac zchk_new ::= constr:([0x0b2cd0; 0x0b2cd8; 0x0b2cdc; 0x0b2ce0; 0x0b2ce4; 0x0b2ce8]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section CK.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Hypothesis IMG : asan_img_ok (arl_AL R).
  Variable h : HST asegs R HIA.
  Variables (LB LF : list blk).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_CTXCK_STACK_A.
  Hypothesis SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo).

  Notation POST := (rsa_ctxck_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation FRAME xj := ([CB 8 xj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Ltac al_facts :=
    pose proof (art_alwf asegs R HIA) as ALWF; pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L12283411672.62L14106684376.62L36423572754.61L41288976216.62L44866992728.62L48429268312.62L49345641752.60L5145216728.62 L8722184664.62 Q15641571313.61Q18364008945.61Q21877860242.61Q27904922642.61Q32653583601.61Q33915847314.61Q3832213010.61 Q39941340946.61Q41154178801.61Q44650597233.61Q51233519217.61Q59840696433.61Q66523984274.61Q9840925842.61 00000400800C00G00K00O00S00W00[00b00i01401?01F01Q01\01g01n02502<02C02N02YS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2spS2spS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS2sp2lo3SLOS2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG LO0 SLO SCS"] Lemma epilogue : forall (m1 : mem) (hc : HST asegs R HIA)
      (xra t0 t1 t2 x0 x1 x2 x3 x4 x5 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (xj : list (bv 8)),
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    HM asegs R HIA hc LB LF m1 -> ck_hsame asegs R HIA hc h ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64) (FRAME xj) ->
    evtA asegs (arl_AL R) (hcs asegs R HIA h) POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb2e78) fc None m1 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xj. intros PW HHc HS MI ST FR. al_facts.
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
      (xra t0 t1 t2 x0 x1 x2 x3 x4 x5 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (xj : list (bv 8)),
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    HM asegs R HIA hc LB LF m1 -> ck_hsame asegs R HIA hc h ->
    mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64) (FRAME xj) ->
    evtA asegs (arl_AL R) (hcs asegs R HIA h) POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb2e70) fc None m1 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xj. intros PW HHc HS MI ST FR. al_facts.
    zstep. zstep. eapply epilogue; eassumption.
  Qed.
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@C17025492443.114C17027589628.151C17027589631.132C17027589631.168K14560412036.132K14560412036.168K14560412039.151K14562509216.114K37211889074.95 K37211889074.96 L10041968289.0  L12174595177.81 L12283411672.90 L13301871092.90 L14106684376.89 L14549078981.3  L15447306016.89 L16075575155.161L16075583823.126L1685717371.0   L17646078182.91 L18293330070.2  L18714606648.90 L22271502648.89 L22598188190.91 L22598188190.92 L26368079009.0  L27804619052.80 L30985071382.113L30985071382.94 L30987168563.131L30987362533.149L31714561233.108L36294353073.93 L36294353073.94 L36715738693.2  L37222368707.2  L38235734261.1  L39025209581.14 L39025210477.14 L39835060509.81 L39845870340.14 L39845871492.14 L39887139444.90 L41288976216.90 L41872764395.92 L43059266230.89 L43882049225.3  L43884818473.2  L44866992728.90 L45061257730.146L45174768033.0  L45330285420.14 L45330286572.14 L45898055924.90 L48429268312.90 L5145216728.90  L51882119172.14 L51925114228.90 L53517126283.14 L54324727969.0  L55197438459.91 L56652673549.14 L56652674701.14 L57933933556.90 L58755387131.92 L59308586893.3  L61486510573.14 L61486511469.14 L63962036340.89 L65278129752.80 L7274816372.90  L8722184664.90  N21804656085.115N25673818932.152N34343554153.169N34999734301.169N37110879153.115N45601414740.133N47142626754.152N6396369602.133 O17025492443.114O17027589628.151O17027589631.132O17027589631.168O33932766420.151O33932766423.132O33932766423.168O33934863603.114Q1219017780.94  Q15457446739.92 Q15457446739.93 Q15643324129.91 Q16152254692.112Q16152254692.93 Q18365925601.92 Q21798041355.94 Q21879645826.92 Q23150033886.94 Q25513505925.94 Q25513505925.95 Q2577138615.94  Q27126674124.94 Q27907200258.92 Q30985071382.113Q30985071382.94 Q30987168563.131Q30987362533.149Q31394594844.94 Q32655500769.92 Q32799224464.92 Q32799392305.111Q33918256002.92 Q35595639279.112Q35595639279.93 Q36436139936.132Q36436139936.168Q36436139939.151Q36438237060.114Q3830427394.92  Q39939554818.92 Q41126203749.94 Q41152393185.92 Q44034257392.94 Q44648843873.92 Q49367596931.111Q49367666466.92 Q49698585326.93 Q49698585326.94 Q502448136.94   Q51235796833.92 Q52590069023.112Q52590069023.93 Q53519952433.94 Q57533912001.94 Q59843137889.92 Q63037100374.94 Q66522067074.92 Q66715549212.94 Q67528989526.95 Q67528989526.96 Q7377275490.94  Q7377275490.95  Q9742927161.92  Q9742988696.111 Q9743135771.112 Q9743135771.93  Q9843367298.91  00000100200300400B00P00^00l01P02C02D02O02Z02e03003103C03D03E03F03Q03X03i04:04K04\04]04h05I05f06G06h06i07:07K07L07M07Q07h08?08J08U08`08k09609D09V09]09d09o0:L0:M0:Z0:g0;20;=0;H0;S0;^0;b0;c0<40<I0<^0<i0=:0=C0=G0=K0=V0=a0=l0>70>G0>W0>g0?70?G0?W0?g0@70@B0@M0@X0@c0@d0@e0@f0@g0A30A<0AE0AN0AO0AP0AY0AZ0Ag0B30BN0C80C90C:0CG0C\0D10DF0D[0D^0Dg0Dl0E10E>0EC0EH0EU0Eb0Eo0F<0FI0FV0FW0F`0Fk0G40G90G>0GQ0Gd0Ge0Gn0HM0Hc0Ho0I00I90ID0IQ0I\0J;0Ji0KH0L60L;0L@0LE0LJ0LWFFFFS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2sp1C1r2lo2DCS2ra2sp1C1r2lo3SLO2DC2HB5Ha_st5Hl_stS2sp2s01C1r2lo3SLO2DC2HB5Ha_st5Hl_st2s12s22s32s42s5SS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rFS2ra2sp1C1r2C03CSZFFSS2ra2sp1C1rS2sp2loS2ra2sp1C1r2lo2DCS2ra2sp1C1r2lo2DCS2ra2sp1C1r2lo2H0S2ra2sp1C1r2lo2H0SS2ra2sp1C1rS2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPBS2ra2sp1C1r2lo2C03LO03SLO3SPB3x14S2ra2sp1C1r2lo2C03LO03SLO3SPB3x14FS2ra2sp1C1r2lo2H0S2ra2sp1C1r2lo2H0FFS2loS2sp2lo3LO03SLO3SPA3SPBS2sp2lo3LO03SLO3SPA3SPBS2ra2sp1C1rS2sp2lo3SLOS2sp2lo3SLOS2ra2sp1C1rS2ra2sp1C1rS2AL2ra2sp1C1rS2ra2sp1C1r2lo3SLOS2sp2loS2sp2loS2ra2sp1C1rS2ra2sp1C1r3x143x453PC05POST1SS2sp1r2lo3DN'S2sp1r2lo3DE'S2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2sp2lo3SLOS2ra2sp1C1rS2spSS2ra2sp1C1r2lo2DCS2sp1C1r2lo2AN2DC3SPBS2sp1C1r2lo2AE2DC3SPBS2ra2sp1C1rS2ra2sp1C1r2lo2DCS1r2N02HnS2spS2spS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2ra2sp1C1rS2sp1r2lo3x152C1S2sp1r2lo3x462C1S2sp1r2lo3x612C1S2sp1r2lo3x612C1S2sp1r2lo3x152C1S2sp1r2lo3x302C1S2sp1r2lo3x462C1S2sp1r2lo3x302C1S2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOS2sp2lo3SLOFFFFS2AL1r5ALWF'S2sp1r2HBS2sp1r2HBS2sp1r2loFFS2sp1r2loFS2sp1r2lo3SLOS2AL1r5ALWF'S2ra2sp1r2lo2HB5Ha_st5Hl_stS2sp2s01r2lo2HB5Ha_st5Hl_st2s12s22s32s42s5FFS2sp1r2lo3SLOS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS2sp1r2lo3LO03SLO3SPBS1rS2sp1r2loS1C1rS1C1rS2sp1r2lo3SLOS1C1rS1C1rS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOS2sp1r2lo3SLOFS2sp1r2loS2AL1r4IMG'S2sp1r2loS1C1rS1C1rS2sp1r3SPB2HB5Ha_stS2sp1r3SPB2HB5Ha_stFS2sp1r2loS2ra2sp1C1r3CAL2C03SPB3x144POSTS2ra2sp1C1r3CAL2C03SPBS2AL1r5ALWF'FS2sp1r2loS2AL1r4IMG'S2sp1r2lo3SLOS2AL1r4IMG'S2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S2ra2sp1r2lo3SLO2HB5Ha_st5Hl_stS2sp2s01r2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S1C1rS1C1rS1C1rS1C1rS2sp1r2lo3SLO". (* [comment removed for export] *)
Theorem A_rsa_check_context_spec : forall (R : art_layout) (HIA : artA asegs R),
    asan_img_ok (arl_AL R) -> arl_uar_got R = A_UAR_GOT_CI -> arl_smalloc R 0 = A_SMALLOC_0_CI ->
    0 <= arl_need_smalloc R ->
    rsa_check_context_stmtA asegs R HIA A_RSA_CHECK_CONTEXT.
Proof.
  intros R HIA IMG UG SM0 NS0. unfold rsa_check_context_stmtA, A_RSA_CHECK_CONTEXT. intros until slo.
  intros HH LFB HD LEN MN ME AN AE NSN NSE PN PE CAL C0 CSZ MI RA OC ON OE CRC ST SLOS SLO SLO2 TOP SPA TPV SSH SSL1 SSL2 DC DN DE -> ->.
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
  assert (CRC64 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -64) C 48).
  { unfold client_range, client_addr in CRC |- *. intros a Ha. destruct DC as [DC|DC]; [| left; lia].
    destruct (CRC a Ha) as [X|X]; [lia| right; exact X]. }
  dpose MN as [[_ (_ & _ & LENN & NRN & OWNN)] SGN]. dpose ME as [[_ (_ & _ & LENE & NRE & OWNE)] SGE]. unfold MPI_MAX_LIMBS in NRN, NRE.
  (* [comment removed for export] *)
  assert (ON16 : aobj asegs (arl_AL R) (hcs asegs R HIA h) m (md_addr (r_N r)) 16) by (rewrite AN; eapply aobj_sub; [exact OC| lia| lia]).
  assert (OE16 : aobj asegs (arl_AL R) (hcs asegs R HIA h) m (md_addr (r_E r)) 16) by (rewrite AE; eapply aobj_sub; [exact OC| lia| lia]).
  (* [comment removed for export] *)
  assert (DN' : 1 <= md_n (r_N r) -> md_p (r_N r) + 4 * md_n (r_N r) <= lo \/ bv_unsigned sp <= md_p (r_N r)).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DN eq_refl)| exfalso; exact (NSN eq_refl)]. }
  assert (DE' : 1 <= md_n (r_E r) -> md_p (r_E r) + 4 * md_n (r_E r) <= lo \/ bv_unsigned sp <= md_p (r_E r)).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| exact (DE eq_refl)| exfalso; exact (NSE eq_refl)]. }
  assert (CLN : 1 <= md_n (r_N r) -> client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -64) (md_p (r_N r)) (4 * md_n (r_N r))).
  { intros Hn. destruct (md_own (r_N r)) eqn:EO; [destruct OWNN as [P0 N0]; exfalso; clear - N0 Hn; lia| | exfalso; exact (NSN eq_refl)].
    destruct OWNN as (_ & HIN & _). eapply client_range_block; [apply in_or_app; left; exact HIN| lia| lia]. }
  assert (CLE : 1 <= md_n (r_E r) -> client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -64) (md_p (r_E r)) (4 * md_n (r_E r))).
  { intros Hn. destruct (md_own (r_E r)) eqn:EO; [destruct OWNE as [P0 N0]; exfalso; clear - N0 Hn; lia| | exfalso; exact (NSE eq_refl)].
    destruct OWNE as (_ & HIN & _). eapply client_range_block; [apply in_or_app; left; exact HIN| lia| lia]. }
  assert (CRN : client_range (arl_L R) (LB ++ fdata LF) lo (md_addr (r_N r)) 16)
    by (rewrite AN; unfold client_range in CRC |- *; intros a Ha; apply CRC; lia).
  assert (CRE : client_range (arl_L R) (LB ++ fdata LF) lo (md_addr (r_E r)) 16)
    by (rewrite AE; unfold client_range in CRC |- *; intros a Ha; apply CRC; lia).
  assert (CRN64 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -64) (md_addr (r_N r)) 16)
    by (rewrite AN; unfold client_range in CRC64 |- *; intros a Ha; apply CRC64; lia).
  assert (CRE64 : client_range (arl_L R) (LB ++ fdata LF) (bv_unsigned sp + -64) (md_addr (r_E r)) 16)
    by (rewrite AE; unfold client_range in CRC64 |- *; intros a Ha; apply CRC64; lia).
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
  assert (SCS64 : crange (hcs asegs R HIA h) lo (bv_unsigned sp + -64 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SLO; lia]).
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
  zstep. clear GOT GSB.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "PROLOGUE-LEFT:" g end.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONa.
  pose proof (A_mpi_size_spec (arl_AL R) IMG) as SP. unfold mpi_size_stmtA, mpi_query_stmtA in SP.
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
  clear ONa. cur_aobj CSOK SCS MU ON ONb. cur_aobj CSOK SCS MU OE OEb.
  lazymatch goal with SSx : sshad _ _ ?mc slo (bv_unsigned sp) |- _ =>
    destruct (sshad_split asegs (arl_AL R) mc slo (bv_unsigned sp + -64) (bv_unsigned sp) SSx ltac:(lia) ltac:(lia)) as [SSa SSb]; clear SSb end.
  pose proof (A_mpi_cmp_int_spec R HIA IMG UG SM0 NS0) as SP. unfold mpi_cmp_int_stmtA, mpi_cmp_int_postA in SP.
  callrt (bv_unsigned sp + -64)
    (eapply SP with (h := h) (LB := LB) (LF := LF) (lo := lo) (slo := slo) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact ONb | match goal with MUx : munch _ m ?mc, WMx : wmono asegs m ?mc |- mpd_at _ ?mc _ _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end
           | rewrite AN; reflexivity
           | exact CRN
           | (intros NSx; exfalso; exact (NSN NSx))
           | clear - SLO SLO2 SPA SPB LO0 CSZ C0 DC AN DN' NRN SSL1 SSL2 TOP; first [lia | rewrite AN; lia | intros Hn; destruct (DN' Hn); lia]
           | match goal with |- ?g => idtac "CMPN-PRE-LEFT:" g end ]).
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPN-LEFT:" g end.
  clear SP.
  lazymatch goal with H : presA _ _ _ _ _ _ _ _ ?ma ?mb |- _ => rename H into HP1; rename ma into mc1; rename mb into mn1 end.
  lazymatch goal with H : HM _ _ _ ?hh LB LF mn1 |- _ => rename hh into h1; rename H into HH1 end.
  assert (HS1 : ck_hsame asegs R HIA h1 h) by (unfold ck_hsame; do 6 (split; [assumption|]); assumption).
  assert (TOP1 : bv_unsigned sp <= htop asegs R HIA h1) by (destruct HS1 as (_ & EH & _); lia).
  assert (MN1 : mpd_at asegs mn1 LB (r_N r)).
  { eapply mpd_at_presA_ck; [exact HP1| | exact NSN| exact CRN64].
    match goal with MUx : munch _ m mc1, WMx : wmono asegs m mc1 |- _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end. }
  assert (ME1 : mpd_at asegs mn1 LB (r_E r)).
  { eapply mpd_at_presA_ck; [exact HP1| | exact NSE| exact CRE64].
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
  zstep. zstep.
  zstep; if_cases K3; zify_cond K3.
  { eapply epilogue; eassumption. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  cur_aobj CSOK SCS MU ON ONc.
  pose proof (A_mpi_get_bit_spec (arl_AL R) IMG) as SP3. unfold mpi_get_bit_stmtA, mpi_query_stmtA in SP3.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SP3 with (lo := lo) (LB := LB) (dX := r_N r) (v := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact ONc | match goal with MUx : munch _ mn1 ?mc, WMx : wmono asegs mn1 ?mc |- mpd_at _ ?mc _ _ => eapply TRN'; [exact MN| exact MUx| exact WMx] end
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
  pose proof (A_mpi_cmp_int_spec R HIA IMG UG SM0 NS0) as SP. unfold mpi_cmp_int_stmtA in SP.
  specialize (SP h1). rewrite (proj1 HS1) in SP. unfold mpi_cmp_int_postA in SP.
  callrt (bv_unsigned sp + -64)
    (eapply SP with (LB := LB) (LF := LF) (lo := lo) (slo := slo) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
     try eassumption; try reflexivity;
     first [ exact OEa | match goal with MUx : munch _ mn1 ?mc, WMx : wmono asegs mn1 ?mc |- mpd_at _ ?mc _ _ => eapply TRE'; [exact ME| exact MUx| exact WMx] end
           | rewrite AE; reflexivity
           | exact CRE
           | (intros NSx; exfalso; exact (NSE NSx))
           | clear - SLO SLO2 SPA SPB LO0 CSZ C0 DC AE DE' NRE SSL1 SSL2 TOP1; first [lia | rewrite AE; lia | intros Hn; destruct (DE' Hn); lia]
           | match goal with |- ?g => idtac "CMPE-PRE-LEFT:" g end ]).
  clear SP.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPE-LEFT:" g end.
  lazymatch goal with H : presA _ _ _ _ _ _ _ _ ?ma ?mb |- _ => rename H into HP2; rename ma into mc2; rename mb into mn2 end.
  lazymatch goal with H : HM _ _ _ ?hh LB LF mn2 |- _ => rename hh into h2; rename H into HH2 end.
  pose proof (ck_hsame_trans asegs R HIA h2 h1 h ltac:(unfold ck_hsame; do 6 (split; [assumption|]); assumption) HS1) as HS2.
  presA_transport HP2. clear HP2.
  lazymatch goal with H : HM _ _ _ h1 LB LF mc2 |- _ => clear H end.
  repeat lazymatch goal with H : stk _ mc2 _ _ |- _ => clear H end.
  (* [comment removed for export] *)
  zstep; if_cases KG; zify_cond KG.
  - eapply fail; eassumption.
  - zstep. zstep. eapply epilogue; eassumption.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
