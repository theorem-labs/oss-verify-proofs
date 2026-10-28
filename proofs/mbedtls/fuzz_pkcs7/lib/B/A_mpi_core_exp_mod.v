(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_montmul P_mpi_core_exp_mod_working_limbs P_mpi_core_exp_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts A_mpi_core_mla A_mpi_core_montmul A_mpi_core_exp_mod_stmtA.
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
Ltac2 gd_tbl_A_mpi_core_exp_mod () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_stmtA.mpi_core_exp_mod_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "A_ASAN_MEMCPY_CE"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.A_ASAN_MEMSET_MM"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.mul"; "Walk.Loop.MINV"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.A_MPI_CORE_MONTMUL"; "Walk.Loop.NUMS"; "Walk.Loop.KBODY"; "Stdlib.ZArith.BinInt.Z.lor"; "Corelib.Lists.ListDef.skipn"; "Walk.Loop.PINV"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_stmtA.mpi_core_exp_mod_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_stmtA.A_MPI_CORE_EXP_MOD"].


Definition A_ASAN_MEMCPY_CE : Z := 0x67dbc.        (* [comment removed for export] *) (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([681124]).
Local Ltac zchk_new ::= constr:([679600; 679604; 679608; 679636; 679640; 679644; 679648; 679652; 679656; 679660; 679928; 679932; 679936; 679940; 679944; 679948; 679968; 679972; 679984; 679988; 679992; 680012; 680016; 680020; 680024; 680028; 680032; 680080; 680084; 680088; 680212; 680216; 680220; 680224; 680228; 680232; 680300; 680304; 680368; 680372; 680376; 680380; 680564; 680568; 680572; 680576; 680588; 680592; 680596; 680600; 680604; 680608; 680612; 680616; 680696; 680700; 680704; 680708; 680712; 680716; 680720; 680724; 680728; 680816; 680820; 680824; 680828; 680832; 680836; 680840; 680844; 680848; 681004; 681008; 681012; 681016; 681020; 681024]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac zstep_to L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).
Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Hypothesis MM : mpi_core_montmul_stmtA asegs R HIA A_MPI_CORE_MONTMUL.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A N an E en RR T lx la ln le_ lr lt lo : Z) (xs0 ys ns es rs ts0 : list word).
  Hypothesis Han : 1 <= an <= 4999.
  Hypothesis Hen : 1 <= en <= 10000.
  Hypothesis Ln : an <= lx /\ an <= la /\ an <= ln /\ en <= le_ /\ an <= lr /\ exp_mod_working_limbs an en <= lt.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LT0 : Z.of_nat (length ts0) = lt.
  Hypothesis DXT : X + 4 * lx <= T \/ T + 4 * lt <= X.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis TB : 0 < T /\ T + 4 * lt < 2^64.
  Hypothesis ALX : X mod 4 = 0. Hypothesis ALT : T mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - MPI_CORE_EXP_MOD_STACK_A - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis STT : T + 4 * lt <= lo \/ bv_unsigned sp <= T.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * an).
  Hypothesis CWT : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) T (4 * lt).
  (* [comment removed for export] *)
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LN : Z.of_nat (length ns) = ln.
  Hypothesis LE : Z.of_nat (length es) = le_.
  Hypothesis LR : Z.of_nat (length rs) = lr.
  Hypothesis DAT : locked (A + 4 * la <= T \/ T + 4 * lt <= A).
  Hypothesis DNT : locked (N + 4 * ln <= T \/ T + 4 * lt <= N).
  Hypothesis DET : locked (E + 4 * le_ <= T \/ T + 4 * lt <= E).
  Hypothesis DRT : locked (RR + 4 * lr <= T \/ T + 4 * lt <= RR).
  Hypothesis DNX : locked (N + 4 * ln <= X \/ X + 4 * lx <= N).
  Hypothesis DEX : locked (E + 4 * le_ <= X \/ X + 4 * lx <= E).
  Hypothesis ALA : A mod 4 = 0. Hypothesis ALN : N mod 4 = 0. Hypothesis ALE : E mod 4 = 0. Hypothesis ALR : RR mod 4 = 0.
  Hypothesis AB : 0 < A /\ A + 4 * la < 2^64.
  Hypothesis NB : 0 < N /\ N + 4 * ln < 2^64.
  Hypothesis EB : 0 < E /\ E + 4 * le_ < 2^64.
  Hypothesis RB : 0 < RR /\ RR + 4 * lr < 2^64.
  Hypothesis SA : locked (A + 4 * la <= lo \/ bv_unsigned sp <= A).
  Hypothesis SN : locked (N + 4 * ln <= lo \/ bv_unsigned sp <= N).
  Hypothesis SE : locked (E + 4 * le_ <= lo \/ bv_unsigned sp <= E).
  Hypothesis SRR : locked (RR + 4 * lr <= lo \/ bv_unsigned sp <= RR).
  Hypothesis HN0 : bytes_at asegs m N (u32s ns).
  Hypothesis HE0 : bytes_at asegs m E (u32s es).
  Hypothesis HR0 : bytes_at asegs m RR (u32s rs).
  Hypothesis HA0 : bytes_at asegs m A (u32s ys).
  Hypothesis OX0 : aobj asegs AL CS m X (4 * an).
  Hypothesis OA0 : aobj asegs AL CS m A (4 * an).
  Hypothesis ON0 : aobj asegs AL CS m N (4 * an).
  Hypothesis OE0 : aobj asegs AL CS m E (4 * en).
  Hypothesis OR0 : aobj asegs AL CS m RR (4 * an).
  (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_CE.
  Hypothesis T47A : A + 4 * an + 8 <= 2^47.

  Notation POST := (mpi_core_exp_mod_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X an T xs0 ts0 lo m).
  Notation W := [(X, X + 4 * an); (T, T + 4 * lt); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -208)).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12912023583.16L19591444130.16L2541019192.16 L27441934262.7 L29428324939.5 L30678931555.16L35653441506.7 L60098763854.3 L67686456439.16L7029671751.18500000<00L00\01601H01N01f02002@036S1R2sp2lo2LOS2sp2lo3SRC1n2SSS2sp2lo3DST1n2SDS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOS3ALO3ACPS1n2HnS1R3HIA1h2sp2lo3TOP4HTOPS1R2lo3LOSS1R3HIA1h2sp3TOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ds2ss3RET3RRg". (* [comment removed for export] *)
    #[using="IMG NEED0 A N E RR ys ns es rs SPR LOS LO TOP AMC"] Lemma amemcpy_call : forall (DST SRC n : Z) (ds ss : list (bv 8)) (mm : mem) (RET : Z)
        (xra xt0 xt1 xt2 ys0 ys1 xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 : word),
      HM asegs R HIA h LB LF mm -> u8arr asegs mm DST ds -> bytes_at asegs mm SRC ss ->
      Z.of_nat (length ds) = n -> Z.of_nat (length ss) = n ->
      aobj asegs AL CS mm DST n -> aobj asegs AL CS mm SRC n -> DST + n <= SRC \/ SRC + n <= DST ->
      stk asegs mm lo (bv_unsigned sp + -208) -> mem_inv asegs mm ->
      DST + n <= lo \/ bv_unsigned sp <= DST -> SRC + n <= lo \/ bv_unsigned sp <= SRC ->
      DST + n + 8 <= 2^47 -> SRC + n + 8 <= 2^47 -> 0 < n < 2^40 ->
      client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) DST n ->
      xra = Z_to_bv 64 RET -> RET mod 2 = 0 -> 0 <= RET < 2^64 ->
      (forall (mm' : mem) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
          munch [(DST, DST + n); (lo, bv_unsigned sp + -208)] mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
          u8arr asegs mm' DST ss -> stk asegs mm' lo (bv_unsigned sp + -208) -> HM asegs R HIA h LB LF mm' ->
          evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6)
                                   F (Z_to_bv 64 RET) fc None mm' (seg_rom asegs))) ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 ys1 (Z_to_bv 64 DST) (Z_to_bv 64 SRC) (Z_to_bv 64 n) xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 A_ASAN_MEMCPY_CE) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH HD HS LD LS OD OS DJ ST MI SD SS TD TS Hn CWD -> RE RRg K. rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CE) as SPC.
      eapply evtA_cut.
      { eapply SPC with (h := h) (LB := LB) (LF := LF) (DST := DST) (SRC := SRC) (n := n) (lo := lo) (ds := ds) (ss := ss);
          rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia);
          first [ exact HH | exact HD | exact HS | exact LD | exact LS | exact OD | exact OS | exact ST | exact MI | exact LOS | exact CWD | reflexivity
                | left; symmetry; exact AMC
                | right; exact DJ | right; exact TD | right; exact TS
                | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
                | clear - SD SS LO NEED0 SPR LO0 TOP Hn; lia
                | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]. }
      unfold call_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia).
      intros ms' PO.
      ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & -> & MUc & WMc & MIc & _ & HDc & STc & HHc).
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      eapply (K m2); assumption.
      all: match goal with |- ?g => idtac "MEMCPY-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12912023583.14L2541019192.14 L27441934262.7 L29428324939.5 L30678931555.14L35653441506.7 L57017963659.14L60098763854.3 L67686456439.14L7029671751.17700000<00L00f01801>01V01W01a02102dS1R2sp2lo2LOS2sp2lo3DST1n2SDS1R5NEED02sp2lo3SPR2LO3LO0S1R2lo3LOS3ALO3ACPS1n2HnS1R3HIA1h2sp2lo3TOP4HTOPSS1R2lo3LOSS1R3HIA1h2sp3TOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ds3RET3RRg". (* [comment removed for export] *)
  #[using="IMG NEED0 A N E RR ys ns es rs SPR LOS LO TOP AMS"] Lemma amemset_call : forall (DST n : Z) (ds : list (bv 8)) (mm : mem) (RET : Z)
      (xra xt0 xt1 xt2 ys0 ys1 xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 : word),
    HM asegs R HIA h LB LF mm -> u8arr asegs mm DST ds -> Z.of_nat (length ds) = n -> aobj asegs AL CS mm DST n ->
    stk asegs mm lo (bv_unsigned sp + -208) -> mem_inv asegs mm ->
    DST + n <= lo \/ bv_unsigned sp <= DST -> DST + n + 8 <= 2^47 -> 0 < n < 2^40 ->
    client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) DST n ->
    xra = Z_to_bv 64 RET -> RET mod 2 = 0 -> 0 <= RET < 2^64 ->
    (forall (mm' : mem) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        munch [(DST, DST + n); (lo, bv_unsigned sp + -208)] mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
        u8arr asegs mm' DST (repeat (Z_to_bv 8 0) (Z.to_nat n)) -> stk asegs mm' lo (bv_unsigned sp + -208) -> HM asegs R HIA h LB LF mm' ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6)
                                 F (Z_to_bv 64 RET) fc None mm' (seg_rom asegs))) ->
    evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 ys1 (Z_to_bv 64 DST) (Z_to_bv 64 0) (Z_to_bv 64 n) xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6)
                             F (Z_to_bv 64 A_ASAN_MEMSET_MM) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HD LD OD ST MI SD TD Hn CWD -> RE RRg K. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_MM) as SPC.
    eapply evtA_cut.
    { eapply SPC with (h := h) (LB := LB) (LF := LF) (DST := DST) (v := 0) (n := n) (lo := lo) (ds := ds);
        rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia);
        first [ exact HH | exact HD | exact LD | exact OD | exact ST | exact MI | exact LOS | exact CWD | reflexivity
              | left; symmetry; exact AMS
              | right; exact TD
              | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
              | clear - SD LO NEED0 SPR LO0 TOP Hn; lia
              | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]. }
    unfold call_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia).
    intros ms' PO.
    ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & -> & MUc & WMc & MIc & _ & HDc & STc & HHc).
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
    eapply (K m2); assumption.
    all: match goal with |- ?g => idtac "MEMSET-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Loop.
    Variables (ws welem : Z) (wmm : word) (tl : list word).
    Hypothesis HWS : (ws = 1 /\ welem = 2) \/ (ws = 3 /\ welem = 8).
    Hypothesis HWL : welem * an + an + (2 * an + 1) <= lt.
    Hypothesis LTL : Z.of_nat (length tl) = lt - (welem * an + an + (2 * an + 1)).

    Notation SEL := (T + 4 * (welem * an)).
    Notation TMP := (T + 4 * (welem * an + an)).
    Notation TLA := (T + 4 * (welem * an + an + (2 * an + 1))).
    Notation WLN := (welem * an + an + (2 * an + 1)).
    Hypothesis OTL : aobj asegs AL CS m T (4 * WLN).
    (* [comment removed for export] *)
    Notation WT := [(X, X + 4 * an); (T, T + 4 * WLN); (lo, bv_unsigned sp)].
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L28573892092.1000000PS2sp1X2an1T2lt2lo5welem3HWL1x2Hx". (* [comment removed for export] *)
    Lemma sub_WT_W : sub_fp WT W.
    Proof using HWL. intros x Hx. cbn [outside] in *. clear - Hx HWL. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation FRAMEL mm j := (rw_cells asegs mm (bv_unsigned sp + -208)
       [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 (18446744073709551615 - T)); C8 (Z_to_bv 64 0x2a2a2a2a); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1);
        C8 (Z_to_bv 64 ws); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 0x2000000000000000); C8 (Z_to_bv 64 X); C8 (Z_to_bv 64 j);
        C8 wmm; C8 (Z_to_bv 64 TMP); C8 (Z_to_bv 64 N);
        C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    (* [comment removed for export] *)
    Definition MINV (mm : mem) (xs tab sel tmp : list word) : Prop :=
      u32arr asegs mm X xs /\ Z.of_nat (length xs) = lx /\ same_from (Z.to_nat an) xs xs0 /\
      u32arr asegs mm T tab /\ Z.of_nat (length tab) = welem * an /\
      u32arr asegs mm SEL sel /\ Z.of_nat (length sel) = an /\
      u32arr asegs mm TMP tmp /\ Z.of_nat (length tmp) = 2 * an + 1 /\
      u32arr asegs mm TLA tl /\
      munch [(X, X + 4 * an); (T, T + 4 * WLN); (lo, bv_unsigned sp)] m mm /\
      wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -208) /\ HM asegs R HIA h LB LF mm
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L35735384464.5 L39077525840.13L53429205430.9 L57540516048.7 00000D01601X023S2an1T5welem3tab3LTBS2an2lt3ts03LT05welem2tl3LTL3tab3sel3tmp3LTB2LS2LMS2an1T5welem3tab3sel3tmp3LTB2LS2LMS2an1T5welem3tab3sel3LTB2LS". (* [comment removed for export] *)
    #[using="lt LT0 LTL"] Lemma join_T : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))P,(33.R5.R4.R3.R2.R1.)(15.(30.$5.R6.VT,(19.(2.&40.)R4.(19.(2.&40.)R3.(19.(2.&40.)R2.Vtl,))))(8.$34.(:.(2.&40.)(19.(2.&40.)R4.(19.(2.&40.)R3.(19.(2.&40.)R2.Vtl,))))(:.(2.&40.)Vts0,)))")
(* [comment removed for export] *).
    Proof.
      (intros mm xs tab sel tmp dd_H; ddestruct dd_H as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & _)).
      split.
      - apply u32arr_app. split; [exact HT|]. apply u32arr_app. split.
        { replace (T + 4 * Z.of_nat (length tab)) with SEL by (clear - LTB; lia). exact HS. }
        apply u32arr_app. split.
        { replace (T + 4 * Z.of_nat (length tab) + 4 * Z.of_nat (length sel)) with TMP by (clear - LTB LS; lia). exact HMm. }
        replace (T + 4 * Z.of_nat (length tab) + 4 * Z.of_nat (length sel) + 4 * Z.of_nat (length tmp)) with TLA by (clear - LTB LS LM; lia). exact HL.
      - rewrite !length_app. clear - LTB LS LM LTL LT0. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L22053004888.162L22193487704.162L2779640280.162 L29321180504.162L29428324939.5  L3310647320.164 L35653441506.7  L37878424280.162L38923399768.162L46063675480.162L5303231320.162 L54619284952.162L54768680664.162L57166284943.5  L60098763854.3  L60140069080.162L61904762072.162L65531224197.165L9917822936.162 Q15641568614.165Q18364007270.165Q18376347397.165Q21877861637.165Q24387680389.165Q27583156582.165Q27904925317.165Q29503565670.165Q30413285893.165Q31269115878.165Q32653586022.165Q33915848709.165Q36423571333.165Q3832210565.165 Q39941338501.165Q41154176102.165Q44650594790.165Q4531767910.165 Q51233520870.165Q52099386854.165Q54488095749.165Q59254978790.165Q59840699110.165Q60513700229.165Q66523986693.165Q9840924165.165 00000m01j02g03d04605305K06H07E08B09?0:<0;90;J0;T0<Q0=N0?B0@?0@o0A_0BZ0CU0DP0E@0F;0Fk0Gf0HV0IF0JA0K<0L70M20Mb0NR0OB0P20Pb0Q]0RM0S=0T80U30UnS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2lx3xs02L02xs2LXS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2LO2AB2NB2EB2RB2tl2xs3tab3sel3tmp2LTS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LTS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp2LT". (* [comment removed for export] *)
    #[using="IMG NEED0 A RR la ln le_ lr lt ys ns es rs L0 LT0 XB TB SPR LOS LO TOP AB NB EB RB HWL LTL"] Lemma exit_walk : forall (mm : mem) (xs tab sel tmp : list word) (j : Z)
      (xra xt0 xt1 xt2 ys0 ys1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 : word),
      MINV mm xs tab sel tmp -> FRAMEL mm j ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 ys1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 681064) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros MV FR. pose proof (join_T _ _ _ _ _ MV) as [HT LT].
      ddestruct MV as (HX & LX & FX & _ & _ & _ & _ & _ & _ & _ & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      zstep_to [681120]. release_frame FR ST (bv_unsigned sp). zstep.
      apply evtA_done. unfold mpi_core_exp_mod_postA. deexists 15. dexists mm, xs, (tab ++ sel ++ tmp ++ tl).
      split; [reflexivity|]. split; [rewrite LT0; exact (munch_weaken _ _ _ _ sub_WT_W MU)|]. split; [exact WM|]. split; [exact MI|]. split; [exact HX|].
      split; [clear - LX L0; lia|]. split; [apply same_from_skipn; [exact FX| clear - LX L0; lia]|]. split; [exact HT|]. split; [exact LT|]. split; [exact ST| exact HH].
      all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L29428324939.5L35653441506.7L37824102549.2L48155834837.3L60098763854.300000B00Z00`00l016S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1X2anS2an1T5welemS1R2lo3LOS". (* [comment removed for export] *)
    #[using="IMG LOS TOP OX0 ON0 OE0 OTL"] Lemma objs_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxs,(1.(2.&40.))Ptab,(1.(2.&40.))Psel,(1.(2.&40.))Ptmp,(1.(2.&40.))P,(33.R5.R4.R3.R2.R1.)(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VX,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VN,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VE,(32.+4.Ven,))(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R6.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))))")
(* [comment removed for export] *).
    Proof.
      intros mm xs tab sel tmp MV.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (WC : w_client CS WT).
      { unfold w_client. repeat apply Forall_cons; cbn [fst snd]; [| | | apply Forall_nil].
        - replace (X + 4 * an - X) with (4 * an) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OX0).
        - replace (T + 4 * WLN - T) with (4 * WLN) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OTL).
        - exact SCS. }
      repeat split; eapply (aobj_munch asegs AL _ CSOK WT m mm); first [exact WC | exact MU | eassumption].
      all: match goal with |- ?g => idtac "OBJS-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Notation SB := (Z_to_bv 64 (al_sb AL)).
    Notation WL := (welem * an + an + (2 * an + 1)).
    (* [comment removed for export] *)
    Notation OBJT mm := (aobj asegs AL CS mm T (4 * WL)).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01M0@C33844532175.195C68255727078.194D36604751191.194D39932794823.194K4002977679.195 K40484668124.194K42587433812.194K60443225391.195L10354034516.168L10689860916.123L13043732721.168L17020861261.193L17307733061.193L17646261672.123L21921278833.193L21990112464.141L23499095854.193L25611388853.123L25611388853.170L26903556165.123L29428324939.5  L29519831493.168L29778232784.123L31340985616.123L32958882881.170L35653441506.7  L39459316037.189L3996309521.5   L40500120010.5  L42591480661.6  L44833485463.178L45272713316.181L45542517052.123L48836048277.181L51858086845.123L51989836049.189L53506586257.170L53813766467.123L59308546259.177L59308546259.180L60098763854.3  L60433113777.5  L60437718071.5  L60437798955.5  L65067422056.189L65069863792.190L67134409590.123L67221579272.191L68640898245.123L7058484880.173 L8929111654.172 L8929159528.173 L8929159528.177 L8929159528.179 L8941784865.123 L8941784865.170 L9964611196.173 P60443225391.195Q26295627581.177Q26295627581.181Q26295627581.183Q2958501345.192 Q2964842857.177 Q2964842857.181 Q2964842857.183 Q30206126178.194Q3286077752.177 Q3286077752.181 Q3286077752.183 Q36262265265.174Q36264016123.178Q36266672818.180Q36592349486.177Q36592349486.180Q36592349486.181Q36592349486.183Q36592448935.182Q36593012627.180Q36594532142.190Q36594546138.178Q36604923024.174Q36607027031.194Q46928622045.194Q46939105188.180Q46939464493.182Q46941546916.190Q49698585326.193Q50458135125.177Q50458135125.181Q50458135125.183Q8944085786.180 Q8945570131.178 Q8956160025.174 00000100202504605_06b08B09E0:T0<L0=[0>_0AF0C00D?0Go0I90KB0MU0OE0OW0P_0RL0T?0V40VL0XA0XB0XC0XD0[00\70\80]>0_A0`I0aM0c@0f00hZ0hd0he0hf0hg0k:0mM0oF11]13G16;18K1:^1<n1?>1AH1C[1D_1D`1EQ1FB1G31H=1I=1JG1KQ1Lf1Ml1Nl1Ol1Q21R21S21Sn1Tj1V01W61X<1YB1ZH1[N1\J1]S1^V1_\1`\1a\1bg1c\1dU1eN1f?1g01gaFFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v43AW13AW2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1j2xs3tab3sel3tmp2Hk2Hj2v4S1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2v43AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v43LTBS1X2an1T2lx2lt3xs02ys2ns2es2rs3ts03Han3DXT5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2v42LX3AW13AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1i1j2xs3tab3sel3tmp2Hj2LS3AW13TB1S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3tmp2Hk3ws0S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1j2xs3tab3tmp2Hk2Hj3LTB3ws02LSS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1j2xs3tab3sel3tmp4HJ61S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3tmp2Hk2Hi3ws0S1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl1i1j2mm3xra3xt03xt13xt23xa03xa13xa73ys33ys53ys84ys104ys113xt33xt43xt53xt62Hk2HjS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3tmp2Hk2Hj3ws02K1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1i2xs3tab3sel3tmp2LS3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2LS3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB4T47A2tl1j2xs3tab3sel3tmp2HjS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl1k1j2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1i1j2xs3tab3sel3tmp2HjS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1i2xs3tab3sel3tmp2LS3AW13TB1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB4T47A2tl1k1j2xs3tab3sel3tmp2Hk2HjS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB4T47A2tl1k1j2xs3tab3tmp2Hk2Hj3ws0FFFS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i1j2xs3tab3sel3tmp2Hk2Hj2Hi3LTB2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2Hk2HjFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL2xs3tab3sel3tmp3LTB2LS3TB13TB2S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl1k1j2xs3tab3tmp2Hk3ws0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1i2xs3tab3sel3tmp2LS3AW13TB1S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i1j2xs3tab3sel3tmp2Hk2Hj3LTB2LS3AW22N0S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1j2xs3tab3sel3tmp2Hk2Hj3LTB2LS2N0S1R2lo3LOSFFFS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1j2xs3tab3sel3tmp2Hj3TB2S1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2tl1k1j2xs3tab3sel3tmp2Hk2Hj2LX2LSS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1j2xs3tab3sel3tmp4HJ61S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB4T47A2ws5welem2tl3HWS3LTL1k1j2xs3tab3sel3tmp2Hk2Hj3LTB2LS3TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2LS3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1i1j2xs3tab3sel3tmp2Hj2LS3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i1j2xs3tab3sel3tmp2Hk2Hj2LS3AW13AW23TB13TB2S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkFS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB1S2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13TB1S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB1S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW23TB1S2sp1X2an1T2lo3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v43AW13AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW1S2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW1S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW13AW2S2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW1S2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj2v43AW13AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2Hj2v4S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i1j2xs3tab3sel3tmp2Hk2Hj3AW2S2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1j2xs3tab3sel3tmp2Hk2HjS2an1T2lt3xs02ys2ns2es2rs3ts03Han5welem2tl3LTL1k1j2xs3tab3sel3tmp2Hk2Hj3TB2S2an1T3xs02ys2ns2es2rs3ts02tl1k1i1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2HkS2an1T3xs02ys2ns2es2rs3ts05welem2tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2HkS2an3xs02ys2ns2es2rs3ts02tl1k1j2xs3tab3sel3tmp2Hk". (* [comment removed for export] *)
    #[using="IMG NEED0 A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB SPR LOS LO TOP SX STT CWT AB NB EB RB T47A HWS LTL"] Lemma ct_inner_walk : forall (k : nat) (i j jl : Z) (mm : mem) (xs tab sel tmp : list word)
      (xra xt0 xt1 xt2 xa0 xa1 xa7 ys3 ys5 ys8 ys10 ys11 xt3 xt4 xt5 xt6 wpa wa5 wa6 : word),
      Z.to_nat (an - j) = k -> 0 <= j < an -> 0 <= i < welem ->
      wpa = Z_to_bv 64 (T + 4 * (an * i)) -> wa5 = Z_to_bv 64 (4 * j) -> wa6 = Z_to_bv 64 j ->
      MINV mm xs tab sel tmp -> OBJT mm -> FRAMEL mm jl ->
      (forall (mm' : mem) (sel' : list word) (ya0 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word),
         MINV mm' xs tab sel' tmp -> OBJT mm' -> FRAMEL mm' jl ->
         evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL))
             ya0 xa1 (Z_to_bv 64 i) wpa wpa ya5 ya6 ya7 SB ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) ys10 ys11 yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 681004) fc None mm' (seg_rom asegs))) ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL))
          xa0 xa1 (Z_to_bv 64 i) wpa wpa wa5 wa6 xa7 SB ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) ys10 ys11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 680816) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i j jl mm xs tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa7 ys3 ys5 ys8 ys10 ys11 xt3 xt4 xt5 xt6 wpa wa5 wa6 Hk Hj Hi -> -> -> MV OT FR KO; [lia|].
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AW : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      pose proof AW as [AW1 AW2]. pose proof TB as [TB1 TB2].
      assert (HJ61 : Z.shiftr j 61 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
      (* [comment removed for export] *)
      zstep_to [680860]. shadow_chk OT (T + 4 * (an * i) + 4 * j) 4.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      prd HT (an * i + j) RDw.
      shadow_chk OT (SEL + 4 * j) 4.
      try clear RDw.
      (* [comment removed for export] *)
      rd HS j. vstep 29%positive.
      shadow_chk OT (SEL + 4 * j) 4.
      (* [comment removed for export] *)
      vstep 28%positive. vstep 29%positive. zstep. vstep 28%positive. vstep 7%positive. vstep 6%positive. vstep 6%positive.
      assert (FS : same_from (length sel) sel sel) by (apply same_from_refl).
      (* [comment removed for export] *)
      wr HS LS FS j.
      zstep.
      lazymatch goal with H6 : mem_inv asegs ?m2, H7 : stk asegs ?m2 lo _, H8 : HM _ _ _ h LB LF ?m2 |- _ =>
        lazymatch type of HS with u32arr _ _ _ ?sel2 =>
        assert (MV2 : MINV m2 xs tab sel2 tmp)
          by (refine (conj HX (conj LX (conj FX (conj HT (conj LTB (conj HS (conj LS (conj HMm (conj LM (conj HL (conj MU (conj WM (conj H6 (conj H7 H8))))))))))))))) end end.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - eapply (IH i (j + 1)); [lia | lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact MV2 | assumption | exact FR | exact KO].
      - (* [comment removed for export] *)
        step; zsimp. eapply KO; [exact MV2 | assumption | exact FR].
      all: match goal with |- ?g => idtac "INNER-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L10354034516.168L12276447763.205L13043732721.168L16321291844.178L21920704885.178L22458920676.201L25607144757.168L28084690364.205L29428324939.5  L29519831493.168L35518900524.178L35653441506.7  L35732324389.178L3727711704.178 L48773092840.201L51989835922.167L54429812235.205L59308628179.171L59308628304.7  L60098763854.3  L62530280414.17800001:03k05506?07I09V0;Z0=60=H0>V0AA0AY0Bc0Cm0F30GA0HP0Ia0J90JC0KQS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB4sel'3LS'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW4sel'3LS'2K2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW2LSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2Hi2K04sel'2K2S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB2LSS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi2AW4sel'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk4sel'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2K0S2an1T3Han5welem1i2AW2K1S1R2lo3LOSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk". (* [comment removed for export] *)
    Local Ltac ct_norm v :=
      repeat match goal with
      | |- context [Z_to_bv 64 ?e] =>
          lazymatch e with context [T] => idtac end;
          tryif constr_eq e v then fail else replace e with v by zlia
      end.
    Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L10354034516.168L10613735978.145L12276447763.210L13043732721.168L16076328398.146L17450994275.141L21583288927.146L21920704885.182L22458920676.206L23414546339.146L2344963174.145 L25607144757.172L25609304239.205L25609369135.145L28084690364.210L29292452755.146L29329766776.146L29428324939.5  L29519831493.168L35518900524.182L35653441506.7  L35733324448.146L48773092840.206L51989835922.171L53517060491.205L53811730649.145L59308628179.175L59308628304.7  L60098763854.3  L60372547970.145L62530280414.182L8927113275.205 L8927182523.145 00001:02k05\06f06g0:]0;a0<k0?E0@I0BB0DS0Fj0I90JU0JV0JW0Ji0L70Nb0O:0O;0QJ0RX0Sd0U]0Vn0WF0WP0WQ0X_0[60]AS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2tl1i2xs3tab3sel3tmp4sel'S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB4sel'3LS'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiFS1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl1i2mm3xra3xt03xt13xt23xa03xa13xa53xa63xa73ys33ys53ys84ys104ys113xt33xt43xt53xt62Hk2HiS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1i2xs3tab3sel3tmp4sel'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi3TB13TB24sel'3AW13AW23LS'2K2S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1i2xs3tab3sel3tmp4sel'S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2tl1i2xs3tab3sel3tmp3AW13TB14sel'S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi3AW13AW23TB13TB22LSS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi3AW13AW23TB13TB24sel'3LS'S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1i2xs3tab3sel3tmp3AW13AW23TB13TB24sel'3LS'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2Hi2K04sel'2K2FFS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS1k1i2xs3tab3sel3tmp2Hk2Hi3LTB2LSS1R3HIA1h2sp2lo3TOP4HTOPFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi3AW23TB13TB24sel'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i2xs3tab3sel3tmp2Hk4sel'S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl1i2xs3tab3sel3tmp3AW13TB14sel'3LS'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2Hk2K0S2an1T3Han5welem1i2AW2K1S1R2lo3LOSFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i2xs3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i2xs3tab3sel3tmp2Hk2Hi3AW13AW23TB13TB24sel'3LS'S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1i2xs3tab3sel3tmp3AW13AW23TB13TB24sel'".
    #[using="IMG NEED0 A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB SPR LOS LO TOP SX STT CWT AB NB EB RB T47A HWS LTL"] Lemma ct_outer_walk : forall (k : nat) (i j : Z) (mm : mem) (xs tab sel tmp : list word)
      (xra xt0 xt1 xt2 xa0 xa1 xa5 xa6 xa7 ys3 ys5 ys8 ys10 ys11 xt3 xt4 xt5 xt6 wi wpa : word),
      Z.to_nat (welem - i) = k -> 0 <= i < welem -> wi = Z_to_bv 64 i -> wpa = Z_to_bv 64 (T + 4 * (an * i)) ->
      MINV mm xs tab sel tmp -> OBJT mm -> FRAMEL mm j ->
      (forall (mm' : mem) (sel' : list word) (ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word),
         MINV mm' xs tab sel' tmp -> OBJT mm' -> FRAMEL mm' j ->
         evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL))
             ya0 xa1 ya2 ya3 ya4 ya5 ya6 ya7 SB ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) ys10 ys11 yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 680440) fc None mm' (seg_rom asegs))) ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL))
          xa0 xa1 wi wpa wpa xa5 xa6 xa7 SB ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) ys10 ys11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 680764) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i j mm xs tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa5 xa6 xa7 ys3 ys5 ys8 ys10 ys11 xt3 xt4 xt5 xt6 wi wpa Hk Hi -> -> MV OT FR KM; [lia|].
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AW : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      pose proof AW as [AW1 AW2]. pose proof TB as [TB1 TB2].
      (* [comment removed for export] *)
      zstep. zstep. vstep 10%positive.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [exfalso; lia|].
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; clear - K1 AW Han; lia|].
      (* [comment removed for export] *)
      zstep. zstep. vstep 17%positive. vstep 10%positive. vstep 10%positive. vstep 17%positive. vstep 10%positive. vstep 5%positive.
      eapply (ct_inner_walk (Z.to_nat an) i 0); [lia | lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact MV | exact OT | exact FR |].
      intros mm' sel' ya0 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 MV' OT' FR'.
      dpose MV' as (HX' & _ & _ & HT' & _ & HS' & LS' & HM' & _ & HL' & MU' & WM' & MI' & ST' & HH').
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      - ct_norm (T + 4 * (an * (i + 1))).
        eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | exact MV' | exact OT' | exact FR' | exact KM].
      - zstep. eapply KM; [exact MV' | exact OT' | exact FR'].
      all: match goal with |- ?g => idtac "OUTER-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "02>0@C13335976522.210C17025492443.209C40241445883.210C40241445883.211C45137625611.210C45137625611.213C45137625611.215D17582764468.213D51233741152.213D5472627854.213 D54966761497.213D60109446735.213D64311484648.213K15588900467.209K15938578720.209K19288291295.210K24619625091.210K24619625091.211K30679969784.210K40247853644.209K42475897931.211K49644543183.210K49644543183.213K49644543183.215K50513409450.210K50513409450.211K55676933043.212K55676933043.214K59567225318.211K60232333163.211K61705120587.210K65354691088.210K68505827192.211K68636050656.211L14220071842.6  L15601019926.4  L15951756101.2  L17597577141.6  L17737826157.39 L17738133748.28 L19281407145.4  L21428770966.2  L23461856521.10 L24621705022.39 L24622049447.25 L24622232571.6  L24624281211.6  L26188388139.39 L268088281.39   L27441934262.7  L27954094300.28 L27954409285.39 L28166690994.25 L29428324939.5  L30673089678.4  L34196968712.39 L3467313635.39  L35653441506.7  L36415273132.6  L37030167487.39 L3873698411.20  L40246206135.5  L42464007210.4  L42465364470.39 L43651006716.25 L49654562871.3  L49656466606.3  L50501282130.5  L50503379150.5  L50503462098.5  L50663673252.28 L50663883325.39 L52005607282.39 L53811483993.39 L53811731136.25 L54039657959.39 L54039704190.28 L54909219693.39 L55670312779.4  L55672046546.4  L59288134590.39 L59571168284.3  L60098763854.3  L60230839184.4  L60642549393.39 L60642562312.25 L61689853487.4  L61689934387.4  L61690767727.25 L61691951027.4  L65357244774.4  L65833526006.39 L65833545071.28 L67686274030.39 L68508330883.5  L68512070341.39 L68648735873.4  L68650781021.39 L7030096054.1   L7030098507.2   L7044745654.212 L7048038937.28  L9085623103.212 N44259866089.210N56949504728.210N63244352774.210N64040766665.210O10395993057.210O11831570240.210O11831570240.211O12090631900.209O13335976522.210O17025492443.209O17223163713.209O28775363370.210O28775363370.211O33362358519.211O33591221596.211O40241445883.210O40241445883.211O45137625611.210O45137625611.213O45137625611.215O4669439211.210 O49867185343.211O67018931761.211O67099258375.212O67099258375.214O6777839498.211 P15938578720.209P49644543183.210P49644543183.213P49644543183.215P55676933043.212P55676933043.214Q17582764468.213Q27441946799.191Q38248387216.213Q43879899724.213Q51233741152.213Q5472627854.213 Q8144514863.213 00000100200300400500600702<03B04E06F07R08d0:50:60;V0<g0>50?C0@Q0BP0BQ0BR0BS0D20EU0EV0EW0G30HL0ID0JA0L90Ma0N10N20N30NJ0Nl0OK0OL0OS0P60QO0R:0R;0R<0R^0Rl0SF0SU0Sf0Sl0T>0T?0TM0Ub0V:0VF0VO0WP0WQ0WR0Wg0XV0XW0XX0XY0XZ0X[0YE0ZK0ZY0[e0\W0\e0\n0^O0^P0^Q0^^0^_0^i0^j0`K0aA0aB0aC0aO0a^0a_0am0b60bH0bI0d20d30dE0dF0dO0ef0f30gI0h?0i:0j=0k30k40k50k60k70k80k90k:0k;0k<0k=0k>0k?0kg0kh0ki0kj0kk0kl0km0kn0ko0l00l10l20l30l40l50l60m30n>0nk0o[10J11611kFFFFFFFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl1B2zs2xs3tab3sel3tmp3RET3RRg3LTB3BF2S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RETS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RETS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1B2zs2xs3tab3sel3tmp3RET3RRg3BF2S1R2ra2sp1X1A1N1E2RR1T2lo3xs02ys2ns2es2rs3ts03LOS2tl1B2zs2xs3tab3sel3tmp3RETS1R3HIA1h2ra2sp1X1A1N1E2RR1T2lo3xs02ys2ns2es2rs3ts03TOP2tl1B2zs2xs3tab3sel3tmp3RETS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2SX2tl2zs2xs3tab3sel3tmpFS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LSS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS1R3HIA1h2LB2LF2sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2LN5welem2tl2zs2xs3tab3sel3tmp3x144DNX'3x153x164POSTFFFS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LSS1X2an2en1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln3DXT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB2LMFFS1R5NEED02sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln2LO2SX2tl2zs2xs3tab3sel3tmpS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL2zs2xs3tab3sel3tmp3LTBS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp2LSS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTBS1R3HIA1h2LB2LF2sp1X1N2an1T2ln2lt2lo3xs02ys2ns2es2rs3ts03Han2LN5welem2tl3LTL2zs2xs3tab3sel3tmp3LTB3x144DNT'3x153x164POSTS1R3HIA1h2LB2LF2sp1X1N2an1T2ln2lo3xs02ys2ns2es2rs3ts02LN5welem2tl2zs2xs3tab3sel3tmp3x143SN'3x153x164POSTS2an1T3Han5welemFFS2an1T3Han2ws5welem3HWSS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS1X2an2en2lx2la2ln3le_2lr2lt2LnFS2sp2loS2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han2TB3STT2ws5welem3HWS3HWLFFS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS2sp1N1T2ln2NBS1R5NEED02sp2lo3SPR2LO3LO0S2sp1X2lx2lo2SXS2sp1X1T2lx2lo2SXS2an1TS1R2lo3LOS3ALO3ACPFS1R2sp1T2lo2LOS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln2XB2TB3SPR2LO3STT2ws5welem3HWS3HWLS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welemS2sp2an1TS2sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo2Ln5welem3HWL4DNX'4DNT'3SN'FFS2sp1X1N1T2lx2ln4DNX'S1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO5welem3HWLFFFFFS1X2an1T2lx2lt3Han3DXT2XB2ws5welem3HWS3HWLS1R5NEED02sp1X2an1T2lx2lt2lo3Han3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWLS2sp1N1T2ln2NBS1R5NEED02sp2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln2TB3SPR2LO2ws5welem3HWS3LO0S1R5NEED02sp2an1T2lt2lo3Han2TB2LO2ws5welem3HWS3LO0S2sp1X1T2lx2XBS1X2lx2XBS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR3SPA2LO2SX3STT2ws5welem3HWS3HWL3LO0FFS2sp2an1T3HanFS1R2lo3LOSFS1R5NEED02sp1X2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3ALT3SPR2LO2SX3STT2ws5welem3HWS3HWL3LO0S1R5NEED02sp2an1T2lt2lo3Han2TB3ALT2LO2ws5welem3HWS3LO0FFS2an1T5welemS2an1T5welem2tlFS2sp1X1T2lx2XBS1X2lx2XBS1R3HIA1h2sp1T3TOPFS1R5NEED02sp1X1N2an2en1T2lx2la2ln3le_2lr2lt2lo3Han2Ln3DXT2TB3SPR2LO2SX3STT2ws5welem3HWS3HWL4DNX'4DNT'3SN'FS2sp1N1T2ln2lo3SN'FS3RET3RRgS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RET3RRg3x153x163PC03PC3S1X2lx2XB3ALXS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs2xs3tab3sel3tmp3RET3x153x163PC03PC3S2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmp3x171CS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp3x171CS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTB3x171CS2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmp3x171CFFFFFFFFFFFFS2an1T3Han5welem2tl2zs3tab3sel3tmp2LS2LMFFFFFFFFFFFFFFFS2an1T3xs02ys2ns2es2rs3ts03Han5welem2tl2zs2xs3tab3sel3tmp3LTBS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts03SPR3LOS2LO2tl2zs2xs3tab3sel3tmp3ALO3ACPS2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS1X2an3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS1X3xs02ys2ns2es2rs3ts02tl2zs2xs3tab3sel3tmpS2an1T3xs02ys2ns2es2rs3ts05welem2tl2zs2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A en RR la ln le_ lr lt ys ns es rs Han Ln LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 HWS HWL LTL OTL"] Lemma mm_call : forall (B : Z) (zs : list word) (mm : mem) (xs tab sel tmp : list word) (RET j : Z)
        (xra xt0 xt1 xt2 ys0 ys1 xa6 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 : word),
      (B = X /\ zs = xs) \/ (B = SEL /\ zs = sel) ->
      xra = Z_to_bv 64 RET -> RET mod 2 = 0 -> 0 <= RET < 2 ^ 64 ->
      MINV mm xs tab sel tmp -> FRAMEL mm j ->
      (forall (mm' : mem) (xs' tmp' : list word) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
        MINV mm' xs' tab sel tmp' -> FRAMEL mm' j ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6) F (Z_to_bv 64 RET) fc None mm' (seg_rom asegs))) ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 ys1 (Z_to_bv 64 X) (Z_to_bv 64 X) (Z_to_bv 64 B) (Z_to_bv 64 an) (Z_to_bv 64 N) (Z_to_bv 64 an) xa6 (Z_to_bv 64 TMP) ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 A_MPI_CORE_MONTMUL) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HB -> RE RRg MV FR K.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      pose proof (unlock _ DNX) as DNX'. pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'.
      pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNX' DNT' SN' Ln HWL Han; lia)) as HN.
      assert (HBro : bytes_at asegs mm B (u32s zs)) by (destruct HB as [[-> ->]|[-> ->]]; apply u32arr_ro; assumption).
      assert (LZ : Z.of_nat (length zs) = lx \/ (B = SEL /\ Z.of_nat (length zs) = an)) by (destruct HB as [[-> ->]|[-> ->]]; [left; exact LX| right; split; [reflexivity| exact LS]]).
      assert (OB : aobj asegs AL CS mm B (4 * an)) by (destruct HB as [[-> _]|[-> _]]; [exact OX| eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]]).
      assert (OTM : aobj asegs AL CS mm TMP (4 * (2 * an + 1))) by (eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]).
      assert (CWM : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) TMP (4 * (2 * an + 1))) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia).
      assert (BF : B mod 4 = 0 /\ 0 < B /\ B + 4 * Z.of_nat (length zs) < 2^64 /\ an <= Z.of_nat (length zs)
                   /\ (B + 4 * Z.of_nat (length zs) <= TMP \/ TMP + 4 * Z.of_nat (length tmp) <= B)
                   /\ (B + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp + -208 <= B)).
      { rewrite LM. destruct HB as [[-> ->]|[-> ->]].
        - rewrite LX. clear - Han Ln HWL HWS DXT XB TB SPR LO NEED0 LO0 SX ALX. repeat split; try lia.
        - rewrite LS. clear - Han Ln HWL HWS TB SPR LO NEED0 LO0 STT ALT. repeat split; try lia. all: Z.div_mod_to_equations; lia. }
      ddestruct BF as (BF1 & BF2 & BF3 & BF4 & BF5 & BF6).
      pose proof (u32arr_ro _ _ _ _ HX) as HXro.
      pose proof MM as MM'. unfold mpi_core_montmul_stmtA, MPI_CORE_MONTMUL_STACK_A in MM'.
      callxA_sp (bv_unsigned sp + -208)
        (eapply MM' with (h := h) (LB := LB) (LF := LF) (X := X) (A := X) (B := B) (bn := an) (N := N) (an := an) (T := TMP) (lo := lo)
                         (xs := xs) (ys := xs) (zs := zs) (ns := ns) (ts := tmp);
         rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia);
         first [ exact HH | exact HX | exact HXro | exact HBro | exact HN | exact HMm | exact ST | exact LOS | exact MI | exact OX | exact OB | exact ON | exact OTM
               | exact CWX | exact CWM | exact Han | exact ALX | exact ALN | exact BF1 | exact BF2 | exact BF3 | exact BF4 | exact BF5 | exact BF6 | reflexivity
               | rewrite unsigned_lit by (clear - RRg; lia); exact RE
               | rewrite ?LX, ?LN, ?LM; destruct LZ as [LZ|[EB' LZ]]; rewrite ?LZ; try subst B;
                 clear - Han Ln HWL HWS DXT XB NB TB SPR SPA LO NEED0 LO0 SX STT DNX' DNT' SN' TOP ALT HTOP; first [ lia | Z.div_mod_to_equations; lia ]
               | match goal with |- ?g => idtac "MM-PRE-LEFT:" g end ]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MM-LEFT:" g end.
      try replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      lazymatch goal with H1 : u32arr asegs ?m2 X ?xs2, H2 : length ?xs2 = length xs, H3 : skipn _ ?xs2 = skipn _ xs,
                       H4 : u32arr asegs ?m2 (TMP) ?tmp2, H5 : length ?tmp2 = length tmp,
                       H6 : mem_inv asegs ?m2, H7 : stk asegs ?m2 lo _, H8 : HM _ _ _ h LB LF ?m2 |- _ =>
        eapply (K m2 xs2 tmp2); [| exact FR];
        refine (conj H1 (conj _ (conj _ (conj HT (conj LTB (conj HS (conj LS (conj H4 (conj _ (conj HL (conj MU (conj WM (conj H6 (conj H7 H8))))))))))))));
        [ rewrite H2; exact LX | eapply (same_from_of_window (Z.to_nat an)); [exact H3 | lia | exact FX] | rewrite H5; exact LM ]
      end.
      all: match goal with |- ?g => idtac "MMCALL-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Definition NUMS (limb bit wbits window : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "(15.(15.(?.=O3.)(?.O3.+1?.))(15.(15.(?.=O4.)(?.O4.Ven,))(15.(>.(16.O4.Ven,)(8.$0.O3.=))(15.(?.+1.(10.(32.+20.O4.)O3.))(15.(15.(?.=O2.)(16.O2.Vws,))(15.(?.=O1.)(16.O1.(14.+2.O2.))))))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Definition KBODY (RBd : Z) : Prop :=
      forall (limb bit wbits window : Z) (mm : mem) (xs tab sel tmp : list word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys8 ys11 xt3 xt4 xt5 xt6 : word),
        NUMS limb bit wbits window -> 32 * limb + bit <= RBd -> MINV mm xs tab sel tmp -> FRAMEL mm limb ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 wbits) (Z_to_bv 64 an) (Z_to_bv 64 window) (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) (Z_to_bv 64 bit) ys11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa622c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L29428324939.5  L35653441506.7  L36158162381.173L56713546224.145L56713771218.168L60098763854.3  L66058234656.145L66058443266.16800000B00Z03W04Q05Z05d07Y09]S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS1R5NEED02ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws2tl4limb3bit5wbits6window2xs3tab3sel3tmp4Hbit5Hlimb3Hwb4Hwin3LOR2LX2K02NZS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit5wbits4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit5wbits2xs3tab3sel3tmp4HbitS1R2lo3LOSS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl4limb5wbits5Hlimb3HwbS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl4limb5wbits2xs3tab3sel3tmp5Hlimb3Hwb". (* [comment removed for export] *)
    #[using="IMG NEED0 A RR la ln le_ lr lt ys ns es rs Ln L0 LT0 DXT XB TB SPR LOS LO TOP SX STT AB NB EB RB HWL LTL"] Lemma cont_walk : forall (RBB limb bit wbits window : Z) (mm : mem) (xs tab sel tmp : list word)
        (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys10 xt3 xt4 xt5 xt6 : word),
      0 <= bit <= 31 -> 0 <= limb < en -> 0 <= wbits < ws -> 0 <= window < 2 ^ wbits -> 32 * limb + bit <= RBB -> KBODY RBB ->
      MINV mm xs tab sel tmp -> FRAMEL mm limb ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 wbits) (Z_to_bv 64 an) (Z_to_bv 64 window) (Z_to_bv 64 welem) (Z_to_bv 64 SEL) (Z_to_bv 64 (Z.lor limb bit)) (Z_to_bv 64 T) ys10 (Z_to_bv 64 bit) xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa6224) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb Hwb Hwin HRB KB MV FR.
      pose proof (lor_lt_pow2 limb bit 64 ltac:(lia) ltac:(lia)) as LOR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      zstep. zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      - apply Z.lor_eq_0_iff in K0. destruct K0 as [-> ->]. eapply exit_walk; [exact MV | exact FR].
      - assert (NZ : limb <> 0 \/ bit <> 0) by (destruct (Z.eq_dec limb 0) as [E0|]; [right; intros E1; apply K0; rewrite E0, E1; reflexivity | left; assumption]).
        eapply KB; [| exact HRB | exact MV | exact FR]. unfold NUMS. lia.
      all: match goal with |- ?g => idtac "CONT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L24063822168.166L29189102680.166L29428324939.5  L3005110713.186 L35422804568.166L35653441506.7  L51303916321.0  L55430846429.0  L56711266935.168L60098763854.3  L61763771352.166L62238965067.186L66056478887.168L9595732537.3   Q42451520258.169Q44959008386.169Q48477206658.169Q50851826913.169Q53365627489.169Q5678005985.169 Q56995815810.169Q63330912737.16900000j01d02603904304K04L04M05P05Z06T07\09S09a0:Y0;Q0<I0=60=c0>P0?H0@5S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit2xs3tab3sel3tmp4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R3HIA1h2sp2lo3TOP4HTOPSSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3bit2xs3tab3sel3tmp4HbitS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl4limb2xs3tab3sel3tmp5HlimbS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2tl4limb2xs3tab3sel3tmp5HlimbS2ws5welem3HWSS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 HWS HWL LTL OTL"] Lemma mult_walk : forall (RBB limb bit : Z) (mm : mem) (xs tab sel tmp : list word)
        (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys3 ys5 ys10 xt3 xt4 xt5 xt6 : word),
      0 <= bit <= 31 -> 0 <= limb < en -> 32 * limb + bit <= RBB -> KBODY RBB ->
      MINV mm xs tab sel tmp -> FRAMEL mm limb ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (al_sb AL)) ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) (Z_to_bv 64 (Z.lor limb bit)) (Z_to_bv 64 T) ys10 (Z_to_bv 64 bit) xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa61f8) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb HRB KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      pose proof (lor_lt_pow2 limb bit 64 ltac:(lia) ltac:(lia)) as LOR.
      (* [comment removed for export] *)
      zstep_to [0xa6218]. zstep.
      eapply (mm_call SEL sel mm xs tab sel tmp 0xa621c); [right; split; reflexivity | reflexivity | reflexivity | clear; lia | exact MV | exact FR |].
      clear dependent mm. intros mm xs' tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MV FR.
      dpose MV as (HX2 & _ & _ & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep. zstep.
      eapply (cont_walk RBB limb bit 0 0); [lia | lia | clear - HWS; lia | clear; lia | exact HRB | exact KB | exact MV | exact FR].
      all: match goal with |- ?g => idtac "MULT-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L14023587864.172L25820126552.169L2589518799.172 L29428324939.5  L34354857587.3  L34825681674.168L35205373606.168L35653441506.7  L58493925670.2  L60098763854.3  L6416703448.169 L64734430706.3  Q31451817831.172Q32833664231.172Q63021096324.172Q8846014212.172 00001Z02T03N03`03n03o04004H04N04X05R05`06M07:08208jS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2tl6window2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R2lo3LOS3ALO3ACPS2ws5welem3HWSFFS1R3HIA1h2sp2lo3TOP4HTOPS2an1TS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2ws5welem3HWSS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl2xs3tab3sel3tmp". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN DNT DNX ALN AB NB EB RB SN HN0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma lookup_walk : forall (window RBB limb bit : Z) (mm : mem) (xs tab sel tmp : list word)
        (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys3 ys10 xt3 xt4 xt5 xt6 : word),
      0 <= bit <= 31 -> 0 <= limb < en -> 32 * limb + bit <= RBB -> KBODY RBB ->
      MINV mm xs tab sel tmp -> FRAMEL mm limb ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (al_sb AL)) ys3 (Z_to_bv 64 an) (Z_to_bv 64 window) (Z_to_bv 64 welem) (Z_to_bv 64 SEL) (Z_to_bv 64 (Z.lor limb bit)) (Z_to_bv 64 T) ys10 (Z_to_bv 64 bit) xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa62e8) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hbit Hlimb HRB KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      (* [comment removed for export] *)
      zstep_to [0xa6330].
      (* [comment removed for export] *)
      zstep_to [0xa633c].
      eapply (ct_outer_walk (Z.to_nat welem) 0 limb); [clear - HWS; lia | clear - HWS; lia | reflexivity | f_equal; clear; lia | exact MV | exact OT | exact FR |].
      clear dependent mm. intros mm sel' ya0 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 MV OT FR.
      eapply (mult_walk RBB limb bit); [exact Hbit | exact Hlimb | exact HRB | exact KB | exact MV | exact FR].
      all: match goal with |- ?g => idtac "LOOKUP-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L16966794342.198L16966794471.199L17468845586.192L18947339828.191L19886797616.183L20402632581.189L27625049176.186L29428324939.5  L32880766689.189L34823974375.179L35653441506.7  L37032795739.199L37032795866.198L39833942540.185L39835945900.190L39836414876.193L41415872618.178L41418083415.186L41953455944.183L42599461041.178L45710833846.180L45712880613.177L54418629900.185L54418701239.177L54420804780.190L54420876444.193L56713773925.174L59308546259.189L60098763854.3  L60200242136.178L64189350643.190L66058396085.174L67524055061.199L67524055188.198L6757073015.188 L8255261546.20  Q20999335462.189Q26295627581.189Q27348161633.191Q27348259048.189Q27350351948.186Q2870651775.191 Q38931724217.186Q44300927607.186Q44959008386.194Q48729518810.186Q50458135125.189Q54107469312.189Q5678005985.194 Q8945665283.186 00001C02S03\04f05o06007307E07F09H09`0<g0?n0AO0B[0D<0E?0FB0HD0Jn0ME0O\0R30TJ0VP0Xg0Z30]B0]L0^O0`00b70cC0dR0eU0fV0h40hd0j;0kR0li0n@0oH10_11g12]13U14l15b16RS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp2eb2B1FS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1R2lo3LOS3ALO3ACPFS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS1R3HIA1h2sp2lo3TOP4HTOPS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem3LTB2LS5limb'3Hl2S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem3LTB2LS5limb'3Hl2S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk5wbits2xs3tab3sel3tmp3Hwb3LTB2LSS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3Hl1S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk3bit5wbits2xs3tab3sel3tmp4HbitS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Hen2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2LE2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3LTB2LS2db5limb'3Hl'2N0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02Ln2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb5wbits2xs3tab3sel3tmp5Hlimb3HwbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp1X2an1E2en1T2lx2la2ln3le_2lr2lt2lo2Ln5welem3HWL4DEX'4DET'3SE'S1E2en3le_3xs02ys2ns2es2rs3ts02EB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1E3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb2db5limb'3Hl'S2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp". (* [comment removed for export] *)
    Local Ltac bx_hib :=
      repeat match goal with
      | |- context [Z.shiftr ?x 62] => replace (Z.shiftr x 62) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; zlia)
      end.
    Local Ltac2 Set LiaOrc.tbl := fun () => "01O0@D35881667587.203D59583840943.203K40484668124.203K42587433812.203K60443225391.203L16100474218.132L16966794342.205L16966794471.206L17468845586.197L18616305768.132L18679834456.178L18947339828.196L19886797616.188L20402632581.196L25296805206.132L27350351975.132L2927423588.132 L29428324939.5  L32880766689.196L34823974375.184L35653441506.7  L35909746608.132L37032795739.206L37032795866.205L37549186420.191L39833871516.132L39833942540.190L39835945900.197L39836414876.198L40500120010.3  L41415872618.178L41418083452.191L41953455944.188L42560983128.183L42591480661.3  L42599461041.178L42788682862.206L43475962169.132L44612169788.191L45710833846.185L45712880590.132L45712880590.182L46193205768.182L51246114520.191L53569704442.187L54418629900.190L54418701212.182L54420804780.197L54420876444.198L56116379715.132L56639015128.178L56639015128.191L56711616485.177L59075394073.132L59308546259.194L60098763854.3  L60437718071.5  L60437798955.5  L60439896503.5  L61600386751.132L64189350643.195L66056238389.177L66409954928.132L67524055061.206L67524055188.205L6757073015.193 L67997997528.183L8255261546.20  Q12351080471.186Q17823031379.200Q20999335462.194Q25513505925.202Q26295627581.194Q26983296116.186Q27348161633.196Q27348259048.194Q27350351975.191Q2870651775.196 Q30034265442.202Q30206126178.203Q312660498.191  Q34817331553.199Q38931724178.191Q44300927580.191Q48729518833.191Q49662502513.191Q49698585326.201Q50458135125.194Q5059447028.186 Q5059450721.199 Q50970143639.186Q50970145794.199Q54107469312.194Q6339983874.199 Q8945665320.191 00001T03n05i07Q09R0;V0<i0>90?B0AF0BI0CS0D\0D]0D^0F^0H`0I20I30K50KM0MF0PM0ST0TW0Uc0WD0XP0Z10Z20[50\80^:0_=0_>0ah0ec0gk0hn0k:0mF0oR12313616l19M1;n1>>1@_1Ak1Bn1D11E=1FG1II1IS1IT1IU1IV1IW1K81ME1MF1NR1Oa1Pd1Qg1Rh1T01Tf1V01W;1Wk1Xa1Yg1Zm1\31]91^V1`@1aH1b>1cF1dL1eB1f81g81h01hf1i\1jd1kl1m21n:1njS1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP2tl2kk5wbits2xs3tab3sel3tmp5limb'2HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem2tl3LTL2kk5wbits2xs3tab3sel3tmp3Hwb3LTB5limb'2HB5Ha_st5Hl_stS1R5NEED02sp1X2lx2lo3xs02ys2ns2es2rs3ts02LO2SX2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb2LX5limb'2HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem2tl3LTL2kk5wbits2xs3tab3sel3tmp3Hwb3LTB5limb'2HB5Ha_st5Hl_st2LM2LSS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB15limb'3HlAS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'3Hl1S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp2eb2B1FFS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB23LnES1R2lo3LOS3ALO3ACPFS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem5limb'3LTB2LS3Hl2S1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb4Hrem5limb'3LTB2LS3Hl2S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3HlBS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'FS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits6window2xs3tab3sel3tmp3Hwb4Hwin2PWS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpFS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB2ws5welem2tl3HWS2kk5wbits2xs3tab3sel3tmp3Hwb3LTB2LSS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2LE2AB2NB2EB2RB2ws5welem2tl3HWS3LTL2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp5Hlimb3Hle5Hrem13Hwb2Hb5limb'2LX3LTB2LS4DEX'4DET'3SE'3LnE3LOR2K12K2S2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR3ALE2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB15limb'3HlAS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE5limb'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE5limb'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE5limb'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE2db5limb'3Hl'3HlAS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Hen2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2LE2AB2NB2EB2RB2ws5welem2tl3HWS3LTL2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp5Hlimb3Hle5Hrem13Hwb2Hb2LX3LTB2LS4DEX'4DET'3SE'3LnE1H3Han4HbitS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE2db5limb'3Hl'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE2db5limb'3Hl'3HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3EB13EB23LnE3Hl13HlAS2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp3Hwb3EB13EB23LnE2db5limb'3Hl'3HlAS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3HlBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk3bit5wbits2xs3tab3sel3tmp4HbitS2ra2sp1X1A1N1E2RR1T3le_3xs02ys2ns2es2rs3ts02EB2tl2kk5wbits2xs3tab3sel3tmpS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Hen2Ln3LT03DXT2XB2TB3SPR2LO2SX3STT2LE2AB2NB2EB2RB2ws5welem2tl3HWS2kk5wbits2xs3tab3sel3tmp3Hwb3LTB2LS3LnE5limb'3HlA2N0S1R2lo3LOSFFFFS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit4bit'5wbits2xs3tab3sel3tmp2db5limb'3Hl'S2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws2tl2kk4limb5wbits2xs3tab3sel3tmp5Hlimb3Hwb3EB13EB23LnEFS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02ws2tl2kk4bit'5wbits2xs3tab3sel3tmp3Hl3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp1X2an1E2en1T2lx2la2ln3le_2lr2lt2lo2Ln5welem3HWL4DEX'4DET'3SE'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2sp3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp2HBS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb3EB15limb'3HlAS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'2HB5Ha_st5Hl_stS3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'2HB5Ha_st5Hl_stS1R5NEED02sp1X2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'2HB5Ha_st5Hl_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp3xs02ys2ns2es2rs3ts03SPR2tl2kk5wbits2xs3tab3sel3tmp2HB5Ha_stS1E3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp5limb'S2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS1E2en3xs02ys2ns2es2rs3ts02ws2tl2kk5wbits2xs3tab3sel3tmp3Hwb5limb'3HlAS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk5wbits2xs3tab3sel3tmp3HwbS3xs02ys2ns2es2rs3ts02tl2kk5wbits2xs3tab3sel3tmp".
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN ALE AB NB EB RB SN SE HN0 HE0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma body2_walk : forall (kk : nat) (limb bit bit' wbits window : Z) (mm : mem) (xs tab sel tmp : list word)
        (xra xt0 xt1 xt2 ys8 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      NUMS limb bit wbits window -> 32 * limb + bit <= Z.of_nat kk + 1 -> (bit = 0 /\ bit' = 31) \/ (1 <= bit /\ bit' = bit - 1) -> KBODY (Z.of_nat kk) ->
      MINV mm xs tab sel tmp -> FRAMEL mm limb ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (18446744073709551615 - SEL)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 wbits) (Z_to_bv 64 an) (Z_to_bv 64 window) (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 (Z_to_bv 64 T) (Z_to_bv 64 bit) (Z_to_bv 64 bit') xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xa6260) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros NU Hrem Hb KB MV FR.
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_at _ _ _ _ _ MV) as (OX & ON & OE & OT).
      ddestruct NU as (Hbit & Hlimb & Hle & Hrem1 & Hwb & Hwin).
      assert (PW : 2^wbits <= 4) by (change 4 with (2^2); apply Z.pow_le_mono_r; lia).
      pose proof (unlock _ DEX) as DEX'. pose proof (unlock _ DET) as DET'. pose proof (unlock _ SE) as SE'.
      pose proof (u32ro_transport _ _ _ _ _ _ HE0 MU ltac:(cbn [disjoint_from]; rewrite LE; clear - DEX' DET' SE' Ln HWL Han; lia)) as HE.
      pose proof EB as [EB1 EB2]. pose proof Ln as (_ & _ & _ & LnE & _).
      (* [comment removed for export] *)
      zstep_to [0xa6270].
      set (db := Z.b2z (bit <? 1)) in *.
      assert (Hl' : 0 <= limb - db < en /\ 32 * (limb - db) + bit' = 32 * limb + bit - 1 /\ 0 <= bit' <= 31 /\ 0 <= db <= 1).
      { subst db. destruct (Z.ltb_spec bit 1); cbn [Z.b2z]; lia. }
      clearbody db.
      set (limb' := limb - db) in *. clearbody limb'.
      pose proof Hl' as (HlA & _ & HlB & _).
      (* [comment removed for export] *)
      zpre; step; zsimp. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. zpre. zstep. zstep. bx_hib. zpre.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OE (E + limb' * 4) 4.
      (* [comment removed for export] *)
      rd HE limb'. clear HE.
      (* [comment removed for export] *)
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2. try rewrite (Z.mod_small (window * 2)) by lia.
      (* [comment removed for export] *)
      vstep 10%positive.
      lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 10%positive in
        lazymatch v with Z_to_bv 64 ?z => pose proof (land_1_range z) as B1 | _ => pose proof (land_1_range (bv_unsigned v)) as B1 end end.
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS ?R _ _ _ _ _ _) => let v := getx R 10%positive in
        lazymatch v with Z_to_bv 64 ?z => set (eb := z) in *; clearbody eb end end.
      pose proof (lor_bit_bound eb window wbits B1 ltac:(lia) Hwin) as WB.
      (* [comment removed for export] *)
      zstep. set (window' := Z.lor eb (window * 2)) in *. clearbody window'.
      pose proof (lor_lt_pow2 limb' bit' 64 ltac:(lia) ltac:(lia)) as LOR.
      (* [comment removed for export] *)
      zstep_to [0xa62e0].
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
        assert (MV2 : MINV m2 xs tab sel tmp) by (unfold MINV; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))); assumption) end.
      ddestruct Hl' as (Hl1 & Hl2 & Hl3 & Hl4).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - (* [comment removed for export] *)
        eapply (lookup_walk window' (Z.of_nat kk) limb' bit'); [lia | lia | lia | exact KB | exact MV2 | eassumption].
      - (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
        + (* [comment removed for export] *)
          eapply (cont_walk (Z.of_nat kk) limb' bit' (wbits + 1) window'); [lia | lia | lia | exact WB | lia | exact KB | exact MV2 | eassumption].
        + (* [comment removed for export] *)
          eapply (lookup_walk window' (Z.of_nat kk) limb' bit'); [lia | lia | lia | exact KB | exact MV2 | eassumption].
      all: match goal with |- ?g => idtac "BODY2-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L19037020683.189L24063822168.170L24471669126.189L26661471905.0  L29189102680.170L29428324939.5  L35422804568.170L35653441506.7  L50988289423.189L56713771218.184L59308681713.141L60098763854.3  L61763771352.170Q42457880190.174Q44948593662.174Q48479233534.174Q50866442653.174Q53355202333.174Q5680030621.174 Q57006243070.174Q63320364189.17400001F02W03e03f05705I06Z07208H09[0:W0:a0<20=H0>^0@40A80B<0C@0DV0EZS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4Hbit2K0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4HremSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4Hbit2K0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits3tab3sel3tmp4Hrem4HbitS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl4limb3bit2H14HremS1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4HremS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws2tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem3HwbS2sp2lo3xs02ys2ns2es2rs3ts02tl2kk4limb3bit5wbits2xs3tab3sel3tmp4Hrem". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN ALE AB NB EB RB SN SE HN0 HE0 OX0 ON0 OE0 T47A HWS HWL LTL OTL"] Lemma body_walk : forall kk : nat, KBODY (Z.of_nat kk).
    Proof.
      induction kk as [|kk IH]; unfold KBODY; intros limb bit wbits window mm xs tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys8 ys11 xt3 xt4 xt5 xt6 NU Hrem MV FR.
      { exfalso. ddestruct NU as (_ & _ & _ & H1 & _). lia. }
      dpose MV as (HX & LX & FX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      dpose NU as (Hbit & Hlimb & Hle & Hrem1 & Hwb & Hwin).
      (* [comment removed for export] *)
      zstep_to [0xa624c]. zstep.
      eapply (mm_call X xs mm xs tab sel tmp 0xa6250); [left; split; reflexivity | reflexivity | reflexivity | clear; lia | exact MV | exact FR |].
      clear dependent mm. clear dependent xs. intros mm xs tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MV FR.
      dpose MV as (HX2 & _ & _ & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      - (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (bit + -1)) with (Z_to_bv 64 (bit - 1)) by (f_equal; lia).
        eapply (body2_walk kk limb bit (bit - 1) wbits window); [exact NU | lia | right; lia | exact IH | exact MV | exact FR].
      - (* [comment removed for export] *)
        zstep. zstep.
        eapply (body2_walk kk limb bit 31 wbits window); [exact NU | lia | left; lia | exact IH | exact MV | exact FR].
      all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation W0T := [(T, T + 4 * WLN); (lo, bv_unsigned sp)].
    Definition PINV (mm : mem) (tab sel tmp : list word) : Prop :=
      u32arr asegs mm X xs0 /\ u32arr asegs mm T tab /\ Z.of_nat (length tab) = welem * an /\
      u32arr asegs mm SEL sel /\ Z.of_nat (length sel) = an /\
      u32arr asegs mm TMP tmp /\ Z.of_nat (length tmp) = 2 * an + 1 /\
      u32arr asegs mm TLA tl /\ munch W0T m mm /\
      wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -208) /\ HM asegs R HIA h LB LF mm
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L29428324939.5L35653441506.7L48155834837.3L60098763854.300000B00Z00f010S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welemS1R2lo3LOS". (* [comment removed for export] *)
    #[using="IMG LOS TOP OX0 OA0 ON0 OR0 OTL"] Lemma objs_pre : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pmm,P,(2.&40.)(3.(2.&8.))P,(4.$5.VR,VHIA,Vh,VLB,VLF,R1.)P,(20.(21.(22.$0.$0.)(23.$0.$0.VT,(10.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.)))))(21.(22.$0.$0.)(23.$0.$0.Vlo,(12.&40.Vsp,))(24.(22.$0.$0.))))Vm,R2.)(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VX,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VA,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VN,(32.+4.Van,))(15.(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VRR,(32.+4.Van,))(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)R3.VT,(32.+4.(10.(10.(32.Vwelem,Van,)Van,)(10.(32.+2.Van,)+1.))))))))")
(* [comment removed for export] *).
    Proof.
      intros mm HH MU. rt_facts.
      assert (WC : w_client CS W0T).
      { unfold w_client. repeat apply Forall_cons; cbn [fst snd]; [| | apply Forall_nil].
        - replace (T + 4 * WLN - T) with (4 * WLN) by (clear; lia). exact (aobj_crange _ _ _ _ _ _ OTL).
        - exact SCS. }
      repeat split; eapply (aobj_munch asegs AL _ CSOK W0T m mm); first [exact WC | exact MU | eassumption].
      all: match goal with |- ?g => idtac "OBJSPRE-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0150@L10351611861.177L10969596589.7  L13041178736.177L14220219354.6  L14220219356.6  L14222026245.7  L16347013912.3  L17597577141.6  L17597724619.5  L17597724621.5  L2054480397.28  L23461856521.10 L23461856521.12 L24352576421.28 L24621705022.38 L24622001404.23 L24622049447.28 L25502270292.38 L25814703959.178L26188388139.38 L268088281.38   L27163225748.3  L27441934262.7  L27954177159.25 L28573892092.15 L29127537594.28 L29428324939.5  L29519540155.178L29521865028.177L30673955207.23 L3090143128.7   L34196968712.38 L3467313635.38  L3467431546.28  L35653441506.7  L35735336831.5  L36415273132.6  L37030167487.38 L38732808811.7  L44160616706.178L49572570277.3  L50663590399.25 L51067033701.28 L51433150352.18 L51644778604.38 L52005607282.38 L53167460058.28 L53811483993.38 L54906982271.28 L54909219693.38 L5705634570.11  L59288134590.38 L60098763854.3  L60102575509.7  L60249634074.28 L60642549393.38 L60642562312.28 L60882515847.28 L60958122188.18 L61690455798.38 L61690686772.23 L61690767727.28 L65357034607.23 L67686274030.38 L68512070341.38 L68650781021.38 L7029671751.235 L7030098507.2   L7554033252.7   00001601S02Y03003F03`03j04A04S04f05805[06=06G07C08108g09<0:D0:f0;40;>0;X0;g0<O0=L0=^0>`0?b0@I0@f0A40B00C10CI0C\0Ch0D10DN0EV0Eb0FO0G;0Gb0H80HF0HT0IW0J70J]0K>0KK0KU0L10L;0MB0NC0Nk0OT0PE0Pe0QM0Qc0R50SC0SU0U40U=0UYS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1i3tab3sel3tmp3RET2HiS2an3Han5welem2ka3tab3LTB3AWkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1i3tab3sel3tmp3RET2HiS2an1T3Han5welem2ka3AWkS2an1T3Han5welem1i3AWiS2an1T3Han2ws5welem3HWS2W2S2an1T3HanS2an1T3Han2ws5welem3HWSS2an1T5welem1i3AWiS2an1T5welem2ka3AWkS2sp2RR2lr2lo4SRR'S2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS2an1T2lt3Han5welem3HWL1i3AWi1a2HaS2RR2lr2RBS2sp2an1T2lt2lo3Han2TB3SPR3STT5welem3HWL1i3AWi2ka3AWk2ws3HWSS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWL1i3AWiS2sp2an1T2lt2lo3Han2TB3STT2ws5welem3HWS3HWL3tab2W23LTBS2sp2an1T5welem1i3AWiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl2ka3tab3sel3tmp3RET3HkaS2sp2an2en1T2lx2la2ln3le_2lr2lt2LnS2sp1N1T2ln2NBS2an1T3HanS1R5NEED02sp2lo3SPR2LO3LO0S2sp1X2lx2lo2SXS2sp2an1T2lo3Han2ws5welem3HWS1i3AWi1x2HxS1R5NEED02sp2an1T2lt2lo3Han2TB2LO2ws5welem3HWS3tab2W23LTB3LO0S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl3tab3sel3tmp3RETS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2tl3tab3sel3tmp3RETS2sp2an1T2lt2lo3Han3STT5welem3HWL1i3AWiS2an3Han2ws5welem3HWS3tab3LTBS1R2sp1T2lo2LOS1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO5welem3HWL1i2ka3AWi3AWkS1R5NEED02sp2an1T2lt2lo3Han2TB3SPR2LO2ws5welem3HWS3HWL3tab2W23LTBS1R3HIA1h2sp2lo3TOP4HTOPS2an1T5welem2ka3AWkS2an1T5welemS2sp2an1TS2an3Han5welem2ka3tab3LTB3AWkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl2ka3tab3sel3tmp3RET3HkaS2an5welem1iS1X2an1T2lx2lt3Han3DXT5welem3HWL1i3AWi2ws3HWSS2an2RR1T2lr2lt3Han2RB2ws5welem3HWS3HWL4DRT'S2sp1N2an1T2ln2lt2lo5welem3HWL4DNT'3SN'S2sp2an1T5welem2ka3AWkS2sp1N1T2ln2NBS2RR2lr3ALR2RBS1R5NEED02sp2an1T2lt2lo2TB3SPR2LO5welem1i3LO03AWi2ka3AWk3Han2ws3HWSS2an2en2RR2lx2la2ln3le_2lr2lt2LnS1R5NEED02sp1T2lt2lo2TB3SPR3SPA2LO3LO0S2sp2an1T2lo5welem1i1a1n2D12D22D3S2sp2an1T3HanS1R2lo3LOSS2an3Han5welem1i3tab3LTB3AWiS2RR2lr2RBS1R5NEED02sp2an1T2lt2lo2TB3ALT3SPR2LO5welem1i3LO03AWi2ka3AWk3Han2ws3HWSS1R5NEED02sp2an1T2lt2lo3Han2TB3ALT2LO2ws5welem3HWS3tab2W23LTB3LO0S2an1T2lt3Han2TB2ws5welem3HWS3tab2W23LTBS2sp2an2RR1T2lr2lt2lo5welem3HWL4DRT'4SRR'S2sp2an1T2lt3Han2TB3SPR2ws5welem3HWS1i3AWi2ka3AWkS2an1T5welem1i3AWi2lt3Han2ws3HWSS2an1T2lt3Han2TB2ws5welem3HWS3tab2W23LTBS2an1T1i3Han5welem3AWiS1R3HIA1h2sp1T3TOPS1R5NEED02sp1N2an1T2ln2lt2lo3Han2TB3SPR2LO3STT2ws5welem3HWS3HWL1i3AWi4DNT'3SN'S2sp1N1T2ln2lo3SN'S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl1B2zs3tab3sel3tmp3RET3RRg3pre2xw2aw3xw'4tmp'3LXc3LTcS3RET3RRgS2an3Han5welem1i3tab3LTB3AWi". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A E en lx la ln le_ lr lt ys ns es Han Ln L0 DXT TB ALT SPR SPA LOS LO TOP SX STT CWT LN LR DNT DRT ALN ALR NB RB SN SRR HN0 HR0 OX0 OA0 ON0 OR0 ws HWS HWL LTL OTL"] Lemma mm_call_tab :
      forall (i ka B : Z) (zs : list word) (mm : mem) (tab sel tmp : list word) (RET : Z) (FRP : mem -> Prop)
             (xra xt0 xt1 xt2 ys0 ys1 xa6 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6 : word),
        0 <= i < welem -> 0 <= ka < welem ->
        (B = RR /\ zs = rs) \/ (B = T + 4 * an /\ zs = skipn (Z.to_nat an) tab /\ 2 <= welem) ->
        xra = Z_to_bv 64 RET -> RET mod 2 = 0 -> 0 <= RET < 2^64 ->
        (forall m1 m2 : mem, munch [(T + 4 * (an * i), T + 4 * (an * i) + 4 * an); (TMP, TMP + 4 * (2 * an + 1)); (lo, bv_unsigned sp + -208)] m1 m2 ->
                             wmono asegs m1 m2 -> FRP m1 -> FRP m2) ->
        PINV mm tab sel tmp -> FRP mm ->
        (forall (mm' : mem) (tab' tmp' : list word) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
            PINV mm' tab' sel tmp' -> FRP mm' ->
            evtA asegs AL CS POST (MS (mkR xra SP' gp tp yt0 yt1 yt2 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6)
                                     F (Z_to_bv 64 RET) fc None mm' (seg_rom asegs))) ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 ys1 (Z_to_bv 64 (T + 4 * (an * i))) (Z_to_bv 64 (T + 4 * (an * ka))) (Z_to_bv 64 B)
                                       (Z_to_bv 64 an) (Z_to_bv 64 N) (Z_to_bv 64 an) xa6 (Z_to_bv 64 TMP) ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 xt3 xt4 xt5 xt6)
                                 F (Z_to_bv 64 A_MPI_CORE_MONTMUL) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hi Hka HB -> RE RRg FRT PV FR K.
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      destruct (objs_pre _ HH MU) as (OX & OA & ON & OR & OT).
      assert (AWi : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (AWk : 0 <= an * ka /\ an * ka + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'. pose proof (unlock _ DRT) as DRT'. pose proof (unlock _ SRR) as SRR'.
      pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNT' SN' Ln HWL Han; lia)) as HN.
      pose proof (u32ro_transport _ _ _ _ _ _ HR0 MU ltac:(cbn [disjoint_from]; rewrite LR; clear - DRT' SRR' Ln HWL Han; lia)) as HR.
      (* [comment removed for export] *)
      set (pre := firstn (Z.to_nat (an * i)) tab). set (xw := skipn (Z.to_nat (an * i)) tab).
      assert (LPRE : Z.of_nat (length pre) = an * i) by (subst pre; rewrite firstn_length; clear - LTB AWi Han; lia).
      assert (LXW : Z.of_nat (length xw) = welem * an - an * i) by (subst xw; rewrite skipn_length; clear - LTB AWi Han; lia).
      pose proof HT as HT2. rewrite <- (firstn_skipn (Z.to_nat (an * i)) tab) in HT2. fold pre xw in HT2.
      apply u32arr_app in HT2. destruct HT2 as [HPRE HXW]. rewrite LPRE in HXW.
      pose proof (u32ro_window _ _ _ _ (Z.to_nat (an * ka)) (u32arr_ro _ _ _ _ HT) ltac:(clear - LTB AWk Han; lia)) as HAW.
      replace (T + 4 * Z.of_nat (Z.to_nat (an * ka))) with (T + 4 * (an * ka)) in HAW by (clear - AWk; lia).
      set (aw := skipn (Z.to_nat (an * ka)) tab) in *.
      assert (LAW : Z.of_nat (length aw) = welem * an - an * ka) by (subst aw; rewrite skipn_length; clear - LTB AWk Han; lia).
      assert (HBro : bytes_at asegs mm B (u32s zs)).
      { destruct HB as [[-> ->]|(-> & -> & _)]; [exact HR|].
        pose proof (u32ro_window _ _ _ _ (Z.to_nat an) (u32arr_ro _ _ _ _ HT) ltac:(clear - LTB Han HWS; lia)) as HW1.
        replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in HW1 by (clear - Han; lia). exact HW1. }
      assert (BF : B mod 4 = 0 /\ 0 < B /\ B + 4 * Z.of_nat (length zs) < 2^64 /\ an <= Z.of_nat (length zs)
                   /\ (B + 4 * Z.of_nat (length zs) <= TMP \/ TMP + 4 * Z.of_nat (length tmp) <= B)
                   /\ (B + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp + -208 <= B)).
      { rewrite LM. destruct HB as [[-> ->]|(-> & -> & W2)].
        - rewrite LR. clear - Han Ln HWL HWS DRT' RB TB SPR LO NEED0 LO0 SRR' ALR. repeat split; try lia.
        - rewrite skipn_length. clear - Han Ln HWL HWS TB SPR LO NEED0 LO0 STT ALT LTB W2. repeat split; try lia. all: Z.div_mod_to_equations; lia. }
      ddestruct BF as (BF1 & BF2 & BF3 & BF4 & BF5 & BF6).
      assert (OB : aobj asegs AL CS mm B (4 * an)).
      { destruct HB as [[-> _]|(-> & _ & W2)]; [exact OR| eapply aobj_sub; [exact OT| clear - Han; lia| clear - Han HWS W2; lia]]. }
      assert (OXW : aobj asegs AL CS mm (T + 4 * (an * i)) (4 * an)) by (eapply aobj_sub; [exact OT| clear - AWi; lia| clear - AWi Han; lia]).
      assert (OAW : aobj asegs AL CS mm (T + 4 * (an * ka)) (4 * an)) by (eapply aobj_sub; [exact OT| clear - AWk; lia| clear - AWk Han; lia]).
      assert (OTM : aobj asegs AL CS mm TMP (4 * (2 * an + 1))) by (eapply aobj_sub; [exact OT| clear - Han HWS; lia| clear - Han HWS; lia]).
      assert (CWW : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) (T + 4 * (an * i)) (4 * an)) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL AWi; lia).
      assert (CWM : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) TMP (4 * (2 * an + 1))) by (intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia).
      pose proof MM as MM'. unfold mpi_core_montmul_stmtA, MPI_CORE_MONTMUL_STACK_A in MM'.
      eapply evtA_cut.
      { eapply MM' with (h := h) (LB := LB) (LF := LF) (X := T + 4 * (an * i)) (A := T + 4 * (an * ka)) (B := B) (bn := an) (N := N) (an := an) (T := TMP) (lo := lo)
                         (xs := xw) (ys := aw) (zs := zs) (ns := ns) (ts := tmp);
         rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia);
         first [ exact HH | exact HXW | exact HAW | exact HBro | exact HN | exact HMm | exact ST | exact LOS | exact MI | exact OXW | exact OAW | exact OB | exact ON | exact OTM
               | exact CWW | exact CWM | exact Han | exact ALN | exact BF1 | exact BF2 | exact BF3 | exact BF4 | exact BF5 | exact BF6 | reflexivity
               | rewrite unsigned_lit by (clear - RRg; lia); exact RE
               | rewrite ?LXW, ?LAW, ?LN, ?LM;
                 clear - Han Ln HWL HWS NB TB SPR SPA LO NEED0 LO0 STT DNT' SN' TOP ALT HTOP AWi AWk; first [ lia | Z.div_mod_to_equations; lia ]
               | match goal with |- ?g => idtac "MMT-PRE-LEFT:" g end ]. }
      unfold mpi_core_montmul_postA. rewrite ?(unsigned_lit (bv_unsigned sp + -208)) by (clear - SPR LO NEED0 LO0; lia).
      intros ms' PO.
      ddestruct PO as (zt0 & zt1 & zt2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & m2 & xw' & tmp' & -> & MUc & WMc & MIc & HXc & LXc & _ & HTc & LTc & _ & STc & HHc).
      replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia | exact RE]).
      eapply (K m2 (pre ++ xw') tmp'); [| eapply FRT; [exact MUc| exact WMc| exact FR]].
      assert (DJ : forall a n, (a + n <= T + 4 * (an * i) \/ T + 4 * (an * i) + 4 * an <= a) -> (a + n <= TMP \/ TMP + 4 * (2 * an + 1) <= a) -> (a + n <= lo \/ bv_unsigned sp + -208 <= a) ->
                disjoint_from [(T + 4 * (an * i), T + 4 * (an * i) + 4 * an); (TMP, TMP + 4 * (2 * an + 1)); (lo, bv_unsigned sp + -208)] a n).
      { intros a n D1 D2 D3. cbn [disjoint_from]. clear - D1 D2 D3. lia. }
      unfold PINV.
      split; [eapply u32arr_transport; [exact HX| exact MUc| exact WMc| apply DJ; rewrite L0; clear - DXT SX Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [apply u32arr_app; split; [eapply u32arr_transport; [exact HPRE| exact MUc| exact WMc| apply DJ; rewrite LPRE; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]| rewrite LPRE; exact HXc]|].
      split; [rewrite length_app, Nat2Z.inj_add, LXc, LPRE, LXW; clear; lia|].
      split; [eapply u32arr_transport; [exact HS| exact MUc| exact WMc| apply DJ; rewrite LS; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [exact LS|]. split; [exact HTc|]. split; [rewrite LTc; exact LM|].
      split; [eapply u32arr_transport; [exact HL| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - STT Han Ln HWL HWS AWi LO NEED0; lia]|].
      split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; clear - Hx AWi Han HWS LO NEED0; lia|].
      split; [eapply wmono_trans; [exact WM| exact WMc]|].
      split; [exact MIc|]. split; [exact STc| exact HHc].
      all: match goal with |- ?g => idtac "MMTAB-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Notation FRAMEB mm j1 j2 := (rw_cells asegs mm (bv_unsigned sp + -208)
       [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 (18446744073709551615 - T)); CB 8 j1; C8 (Z_to_bv 64 0); CB 8 j2;
        C8 (Z_to_bv 64 ws); C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 0x2000000000000000); C8 (Z_to_bv 64 X); C8 (Z_to_bv 64 en);
        C8 wmm; C8 (Z_to_bv 64 TMP); C8 (Z_to_bv 64 N);
        C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@D35881667587.199D35881667587.200D59583840943.199D59583840943.200K40484668124.199K40484668124.200K42587433812.199K42587433812.200K60443225391.199K60443225391.200L10828273447.12 L14594643364.8  L16635876761.7  L17719497315.19 L18679834456.192L18866009566.9  L19282129351.23 L20886524867.18 L21231429831.7  L21431388375.19 L23063600908.2  L23898603878.1  L24622115995.23 L24953833255.17 L25607207054.191L25609302026.9  L25820126552.193L26126682082.19 L27950918981.2  L2925322862.191 L29428324939.5  L30673807840.23 L320454087.14   L35422804568.160L35653441506.7  L36754970035.160L40500120010.3  L42560983128.192L42589383443.3  L49904321809.12 L50502792114.23 L5261963543.159 L53519157674.191L55504905889.0  L55615837940.192L57628700040.11 L59569388482.19 L60098763854.3  L60437718071.5  L60437798955.5  L60439896503.5  L61453626589.6  L63157168055.2  L63781799294.117L64134455284.193L67025746339.3  L7048038937.117 L9278517154.5   L9685877192.2   Q12349053720.195Q17823031379.196Q17823031379.197Q25513505925.198Q25513505925.199Q26985463675.195Q30034265442.198Q30034265442.199Q30206126178.199Q30206126178.200Q310558744.195  Q31449867329.196Q34533085414.163Q44958993541.163Q49664603259.195Q49698585326.197Q49698585326.198Q5677561062.163 Q65531224197.163Q8847963170.196 00001P03005C07V09E0;20<V0>80?m0A`0BH0B^0C:0Cm0E20ER0FL0G40GQ0GX0G`0Gc0HK0IE0KE0Kf0Lk0M90MA0O=0OO0P00PX0QO0Qg0R^0R_0Sd0Se0TM0UG0W40X90X:0Y?0YX0ZK0ZU0ZV0ZW0ZX0Zo0[70\B0]G0]P0^[0_00_80`?0a70ao0c80d?0e70fO0ge0iG0jg0kn0lf0mP0nE0o=10?11A11k12`13gS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR3LOS2LO2AB2NB2EB2RB2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR3LOS2LO2AB2NB2EB2RB2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an1E1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp1X2an1E2lx2lo3xs02ys2ns2es2rs3ts03Han2LO2SX2tl3tab3sel3tmp2LP3LF13xs13LX12HB5Ha_st5Hl_stS1R5NEED02sp1X2an2lx2lo3xs02ys2ns2es2rs3ts03Han2LO2SX2tl3tab3sel3tmp2LP3LF13xs13LX12HB5Ha_st5Hl_stS1R5NEED02sp2an1E1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_st2LM2LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs12HB5Ha_st5Hl_st2LM2LSS2an2en2lx2la2ln3le_2lr2lt3xs03Han2Ln2L0S2sp1X2an2lo1a1n2D12D2S2an2lt3Han2ws5welem3HWS3HWLS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo3xs03Han2Ln2L02SXS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2an1T2lt3Han2ws5welem3HWS3HWL1QS1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2an3Han2ws5welem3HWS3tab3LTBS2sp2loS2en3HenS1TS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL3tab3sel3tmp3LTB2LP3LF13xs1S2an1T2lt3Han2TB2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S1X2an3xs03HanS2an3HanS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han3Hen2Ln2XB2TB3SPR2AB2NB2EB2RB2tl3tab3sel3tmp2LP3LF13xs1S1R2lo3LOS3ALO3ACPS2sp2an1T2lt2lo3Han3STT5welem3HWLS2sp1X2an2en2lx2la2ln3le_2lr2lt2lo2Ln2SXS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1FS2an2en2lx2la2ln3le_2lr2lt3xs03Han2Ln2L0S1X2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln3DXT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln2XB2TB3SPR2AB2NB2EB2RB2tl3tab3sel3tmpS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1SS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2sp1X2an1T2lo5welem1x2HxS1R5NEED02sp1X2an2en2lx2la2ln3le_2lr2lt2lo2Ln2LO2SXS1R2lo3LOSFFFS2an1T3Han2ws5welem3HWSS2an3HanS2ra2sp1X1A1N1E2RR1T2lx2la3xs02ys2ns2es2rs3ts02XB3ALX3SPR2AB2tl3tab3sel3tmpS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2an1q2HqS2ra2sp1X1A1N1E2RR1T2lx2la3xs02ys2ns2es2rs3ts02XB3ALX3SPR2AB2tl3tab3sel3tmpS2en3Hen2ws5welem3HWSS2an3HanS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs1S2sp2an3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HBS2sp2an3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HBS2sp2an1E2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S1R5NEED02sp2an1E2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp1X2an1E1T2lo3xs02ys2ns2es2rs3ts03Han2LO5welem2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp1X2an1T2lo3xs02ys2ns2es2rs3ts03Han2LO5welem2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_st5Hl_stS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs1S2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2sp2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl3tab3sel3tmpS2sp2an2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmp2LP3LF13xs1S2sp2an3xs02ys2ns2es2rs3ts03SPR2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_stS2sp2an3xs02ys2ns2es2rs3ts03SPR2tl3tab3sel3tmp2LP3LF13xs12HB5Ha_stS2sp2lo3xs02ys2ns2es2rs3ts02tl3tab3sel3tmpS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2tl3tab3sel3tmpS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts03Han2LO2tl3tab3sel3tmp2LP3LF13xs1". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE DNT DET DNX DEX ALN AB NB EB RB SN SE HN0 HE0 OX0 OA0 ON0 OE0 OR0 AMC T47A HWS HWL LTL OTL ALE"] Lemma pre_tail_walk :
      forall (j1 j2 : list (bv 8)) (mm : mem) (tab sel tmp : list word)
             (xra xt0 xt1 xt2 ys1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ys3 ys5 ys8 ys9 ys11 xt3 xt4 xt5 xt6 : word),
        PINV mm tab sel tmp -> FRAMEB mm j1 j2 ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) ys1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                       (Z_to_bv 64 (al_sb AL)) ys3 (Z_to_bv 64 an) ys5 (Z_to_bv 64 welem) (Z_to_bv 64 SEL) ys8 ys9 (Z_to_bv 64 0) ys11 xt3 xt4 xt5 xt6)
                                 F (Z_to_bv 64 0xa61b0) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros PV FR.
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      (* [comment removed for export] *)
      zstep_to [425404].
      lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo _, H3 : HM _ _ _ h LB LF ?m2 |- _ =>
        rename H1 into MI1; rename H2 into ST1; rename H3 into HH1; rename m2 into m1 end.
      destruct (objs_pre _ HH1 MU) as (OX & OA & ON & OR & OT).
      pose proof (firstn_skipn (Z.to_nat an) xs0) as EY. symmetry in EY.
      assert (LP : length (firstn (Z.to_nat an) xs0) = Z.to_nat an) by (rewrite firstn_length; clear - L0 Ln Han; lia).
      pose proof HX as HX2. rewrite EY in HX2. apply u32arr_app in HX2. destruct HX2 as [HXB HXC]. rewrite LP in HXC.
      apply u8arr_of_u32arr in HXB.
      pose proof (u32arr_ro _ _ _ _ HT) as HTro. rewrite <- (firstn_skipn (Z.to_nat an) tab), u32s_app in HTro.
      apply bytes_at_app in HTro. destruct HTro as [HTro _].
      assert (LF1 : length (firstn (Z.to_nat an) tab) = Z.to_nat an) by (rewrite firstn_length; clear - LTB Han HWS; lia).
      eapply (amemcpy_call X T (4 * an) _ _ m1 0xa61d0);
        [ exact HH1 | exact HXB | exact HTro | rewrite u32s_length, LP; clear - Han; lia | rewrite u32s_length, LF1; clear - Han; lia
        | exact OX | eapply aobj_sub; [exact OT| clear; lia| clear - Han HWS; lia]
        | clear - DXT Ln Han HWS HWL; lia | exact ST1 | exact MI1
        | clear - SX Ln Han; lia | clear - STT Ln Han HWS HWL; lia
        | pose proof (cw_top47 asegs R HIA h LB LF m1 _ X (4 * an) HH1 CWX ltac:(clear - Han; lia)) as Q; exact Q
        | pose proof (cw_top47 asegs R HIA h LB LF m1 _ T (4 * lt) HH1 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
        | clear - Han; lia | exact CWX | reflexivity | reflexivity | clear; lia | ].
      intros m2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MUc WMc MIc HDc STc HHc.
      apply u32arr_of_u8arr_u32s in HDc.
      assert (DJ : forall a n, (a + n <= X \/ X + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -208 <= a) ->
                disjoint_from [(X, X + 4 * an); (lo, bv_unsigned sp + -208)] a n).
      { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
      match goal with FRm : rw_cells asegs m1 (bv_unsigned sp + -208) _ |- _ =>
        apply (rw_cells_transport asegs _ m1 m2 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR2| apply DJ; simpl_sizes; clear - SX Ln Han SPR LO NEED0 LO0; lia] end.
      assert (MV : MINV m2 (firstn (Z.to_nat an) tab ++ skipn (Z.to_nat an) xs0) tab sel tmp).
      { unfold MINV.
        split; [apply u32arr_app; split; [exact HDc|]; rewrite LF1; eapply u32arr_transport; [exact HXC| exact MUc| exact WMc| apply DJ; rewrite skipn_length; clear - SX Ln Han L0 LO NEED0; lia]|].
        split; [rewrite length_app, Nat2Z.inj_add, LF1, skipn_length; clear - L0 Ln Han; lia|].
        split; [intros q Hq; rewrite nth_error_app2 by (rewrite LF1; exact Hq); rewrite LF1, nth_error_skipn; f_equal; clear - Hq; lia|].
        split; [eapply u32arr_transport; [exact HT| exact MUc| exact WMc| apply DJ; rewrite LTB; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LTB|].
        split; [eapply u32arr_transport; [exact HS| exact MUc| exact WMc| apply DJ; rewrite LS; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LS|].
        split; [eapply u32arr_transport; [exact HMm| exact MUc| exact WMc| apply DJ; rewrite LM; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|]. split; [exact LM|].
        split; [eapply u32arr_transport; [exact HL| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - DXT STT Ln Han HWS HWL LO NEED0; lia]|].
        split; [eapply munch_trans; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; clear - Hx; tauto|];
                eapply munch_weaken; [| exact MUc]; intros x Hx; cbn [outside] in *; clear - Hx LO NEED0; lia|].
        split; [eapply wmono_trans; [exact WM| exact WMc]|].
        split; [exact MIc|]. split; [exact STc| exact HHc]. }
      clear HX HT HS HMm HL MI1 ST1 HH1 HXB HXC HTro MU WM HDc MUc WMc.
      set (xs1 := firstn (Z.to_nat an) tab ++ skipn (Z.to_nat an) xs0) in *. clearbody xs1.
      (* [comment removed for export] *)
      dpose MV as (HX & LX1 & FX1 & HT & _ & HS & _ & HMm & _ & HL & MU & WM & MI & ST & HH).
      zstep_to [680492].
      rewrite (zb_lxor_ones (T + 4 * (welem * an))) by (clear - TB HWL Han HWS; lia).
      match goal with FRq : rw_cells asegs _ (bv_unsigned sp + -208) _ |- _ =>
        rewrite (proj2 (Z.ltb_lt 0 E) (proj1 EB)) in FRq; cbn [Z.b2z] in FRq end.
      lazymatch goal with H1 : mem_inv asegs ?m3, H2 : stk asegs ?m3 lo _, H3 : HM _ _ _ h LB LF ?m3, H4 : u32arr asegs ?m3 X ?xs3, H5 : u32arr asegs ?m3 T _,
                          H6 : u32arr asegs ?m3 SEL _, H7 : u32arr asegs ?m3 TMP _, H8 : u32arr asegs ?m3 TLA _, MU3 : munch _ m ?m3, WM3 : wmono _ m ?m3,
                          FR3 : rw_cells asegs ?m3 (bv_unsigned sp + -208) _ |- _ =>
        eapply (body_walk (Z.to_nat (32 * en)) en 0 0 0 m3 xs3 tab sel tmp);
        [ unfold NUMS; clear - Hen HWS; lia | clear - Hen; lia
        | exact (conj H4 (conj LX1 (conj FX1 (conj H5 (conj LTB (conj H6 (conj LS (conj H7 (conj LM (conj H8 (conj MU3 (conj WM3 (conj H1 (conj H2 H3))))))))))))))
        | exact FR3 ] end.
      all: match goal with |- ?g => idtac "PRETAIL-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L10354034516.162L12276447890.184L13043732721.162L18865000865.0  L19754568514.3  L21921318697.3  L24058921470.137L24063822168.165L25611249971.120L26492581323.25 L28084711781.3  L29189102680.165L29428324939.5  L29519831493.162L31341089686.120L35653441506.7  L38990313813.120L52067443989.180L54429812362.184L55670780969.184L60098763854.3  L61763771352.165L8675610171.184 Q42457732645.168Q48479085989.168Q50866557382.168Q53355054918.168Q57006128293.168Q63320511686.16800001703W04^04_04k05708c09g0<20<k0=70>;0>M0?X0AQ0Ai0C[0Eb0Fe0Gk0H50I90J90K>0LC0M:0N10O60OmS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk2HiS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2L03LT03DXT2XB2TB3SPR2LO2SX3STT2AB2NB2EB2RB5welem2tl1k1i3sel3tmp2Hk2Hi2LS4AWi24AWi3S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk2HiSS5welem1i2HiS5welem1i2HiS1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB5welem2tl1i2mm3xra3xt03xt13xt23xa03xa13xa23xa33xa43xa53xa63xa73xt33xt43xt53xt62Hk2HiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1i3tab3sel3tmp2Hi2LS3TB13TB24AWi24AWi3S1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWL1i3AWiS5welem1i2HiS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han5welem2tl1k1i3tab3sel3tmp2HkS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl1i3tab3sel3tmp2Hi2LS3TB1S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl1i3tab3sel3tmp2HiS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB5welem2tl3LTL1k1i3sel3tmp2Hk2Hi2LS3TB13TB24AWi3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2Hk2Hi2K1S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts05welem2tl1k1i3sel3tmp2HkS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO5welem2tl1k1i3tab3sel3tmp2Hk2HiS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO5welem2tl1k1i3tab3sel3tmp2Hk2HiS2sp2lo3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS2sp2lo3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2HkS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO5welem2tl1k1i3tab3sel3tmp2Hk2HiS2sp2lo3xs02ys2ns2es2rs3ts05welem2tl1k1i3tab3sel3tmp2Hk". (* [comment removed for export] *)
    #[using="IMG NEED0 MM A RR lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LN LE LR DNT DET DRT DNX DEX ALN ALR AB NB EB RB SN SE SRR HN0 HE0 HR0 OX0 OA0 ON0 OE0 OR0 AMC T47A HWS HWL LTL OTL ALE"] Lemma pre_loop_walk :
      forall (k : nat) (i : Z) (j1 j2 : list (bv 8)) (mm : mem) (tab sel tmp : list word)
             (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wcur wprev wcnt : word),
        Z.to_nat (welem - i) = k -> 2 <= i < welem ->
        wcur = Z_to_bv 64 (T + 4 * (an * i)) -> wprev = Z_to_bv 64 (T + 4 * (an * (i - 1))) -> wcnt = Z_to_bv 64 (welem - i) ->
        PINV mm tab sel tmp -> FRAMEB mm j1 j2 ->
        evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 (4 * an)) (Z_to_bv 64 (T + 4 * an)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                       (Z_to_bv 64 (al_sb AL)) wcur (Z_to_bv 64 an) wprev (Z_to_bv 64 welem) (Z_to_bv 64 SEL) wcur wcnt (Z_to_bv 64 0) wprev xt3 xt4 xt5 xt6)
                                 F (Z_to_bv 64 0xa616c) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i j1 j2 mm tab sel tmp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wcur wprev wcnt Hk Hi -> -> -> PV FR; [lia|].
      dpose PV as (HX & HT & LTB & HS & LS & HMm & LM & HL & MU & WM & MI & ST & HH). rt_facts.
      unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
      assert (AWi : 0 <= an * i /\ an * i + an <= welem * an).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite (Z.mul_comm welem an), <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
      (* [comment removed for export] *)
      pose proof TB as [TB1 TB2]. pose proof AWi as [AWi1 AWi2].
      assert (AWi3 : 2 * an <= an * i) by (clear - Hi Han; nia).
      zstep_to [677024].
      eapply (mm_call_tab i (i - 1) (T + 4 * an) (skipn (Z.to_nat an) tab) mm tab sel tmp 0xa6198 (fun mq => FRAMEB mq j1 j2));
        [ clear - Hi; lia | clear - Hi; lia | right; split; [reflexivity| split; [reflexivity| clear - Hi; lia]] | reflexivity | reflexivity | clear; lia
        | | exact PV | exact FR | ].
      { intros m1 m2 MUq WMq FRq. eapply rw_cells_transport; [exact FRq| exact MUq| exact WMq|].
        cbn [disjoint_from]. simpl_sizes. clear - STT Ln Han HWS HWL SPR LO NEED0 LO0 AWi. lia. }
      clear dependent mm. clear dependent tab. intros mm tab tmp' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 PV FR.
      dpose PV as (HX2 & HT2 & _ & HS2 & _ & HMm2 & _ & HL2 & MU2 & WM2 & MI2 & ST2 & HH2).
      (* [comment removed for export] *)
      zstep_to [680356]. zstep_to [680360]. zstep_to [680364].
      (zstep_to [680364]; zstep). if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact PV | exact FR].
      - eapply pre_tail_walk; [exact PV | exact FR].
      all: match goal with |- ?g => idtac "PRELOOP-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Loop.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L25833997221.107L35497640934.104L5744833530.104 L5744835054.107 L9271037271.107 00000]01E02202_03OS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts01n2HlS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts01x2HxS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts01x2HxS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts01n2Hn2Hl".
  Lemma ea_lxor_ones x : 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
  Proof.
    intros Hx. change 18446744073709551615 with (Z.ones 64).
    transitivity (Z.ldiff (Z.ones 64) x).
    - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
      destruct (Z.lt_ge_cases n 64) as [Hl|Hl].
      + rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
      + rewrite Z.ones_spec_high by lia. rewrite Bool.xorb_false_r. simpl andb.
        rewrite <- (Z.mod_small x (2^64)) by lia. apply Z.mod_pow2_bits_high; lia.
    - symmetry. apply Z.sub_nocarry_ldiff.
      rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.
  Ltac ea_lx := repeat match goal with |- context [Z.lxor ?x 18446744073709551615] => rewrite (ea_lxor_ones x) by (zchk_clear; lia) end.
  Ltac ea_pow := repeat match goal with |- context [2 ^ ?k] =>
    let v := eval vm_compute in (2 ^ k) in lazymatch v with Zpos _ => change (2 ^ k) with v end end.
  Ltac ea_rw := repeat match goal with
    | H : @eq Z (?x mod _) ?x |- _ => progress rewrite !H
    | H : @eq Z (Z.shiftl _ _) _ |- _ => progress rewrite !H
    | H : @eq Z (_ * 2 ^ _) _ |- _ => progress rewrite !H
    end.
  Ltac ea_fixG e := try match goal with |- context [Z_to_bv 64 ?x] =>
    assert_fails (constr_eq x e); replace x with e by (zchk_clear; lia) end.
  Ltac ea_raw_to L := repeat (lazymatch goal with |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => step; zsimp end end).
  Ltac ea_solve := ea_rw; ea_lx; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; ea_pow; zchk_solve.
  Ltac ea_if :=
    match goal with
    | |- _ (MS _ _ (if ?c then Z_to_bv 64 681124 else _) _ _ _ _) => replace c with false; [cbv_concl_iota | symmetry; ea_solve]
    | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 681124) _ _ _ _) => replace c with true; [cbv_concl_iota | symmetry; ea_solve]
    end.
  Ltac ea_go L := zstep_to L; repeat (ea_if; zpre; zstep_to L).
  Ltac ea_rwH := match goal with F : rw_cells _ _ (bv_unsigned sp + -208) _ |- _ =>
    repeat match goal with
    | H : @eq Z (?x mod _) ?x |- _ => progress rewrite !H in F
    | H : @eq Z (Z.shiftl _ _) _ |- _ => progress rewrite !H in F
    | H : @eq Z (_ * 2 ^ _) _ |- _ => progress rewrite !H in F
    end;
    repeat match type of F with context [Z.lxor ?x 18446744073709551615] => rewrite (ea_lxor_ones x) in F by (zchk_clear; lia) end
    end.
  Ltac ea_fixH e := ea_rwH;
    match goal with F : rw_cells _ _ (bv_unsigned sp + -208) ?cs |- _ =>
      match cs with context [Z_to_bv 64 ?x] => assert_fails (constr_eq x e); replace x with e in F by (zchk_clear; lia) end end.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04[0@C11386283792.221C17133037579.222D23904522630.221D35881667587.184D35881667587.220D35881667587.236D35881667587.237D54000479254.236D59583840943.184D59583840943.220D59583840943.237D8798035320.221 K1462938774.222 K24960274783.221K40484668124.184K40484668124.220K40484668124.236K40484668124.237K42587433812.184K42587433812.220K42587433812.236K42587433812.237K60443225391.184K60443225391.220K60443225391.236K60443225391.237K62730101946.221K67182834703.222K8081990310.184 L10377253507.126L10647043102.7  L11369673397.126L11784845588.173L11927462101.9  L11927529035.5  L12750296506.7  L14220071842.6  L14623972172.8  L1469545590.2   L1473280750.23  L15045215746.184L15258688857.126L16073508675.126L16078782184.2  L16342890722.2  L16347013912.3  L16467615677.2  L16635876761.7  L17597659033.126L17778595198.147L18679834456.174L18866009566.9  L19961711648.4  L20402407204.173L20404504323.226L20681122052.248L20886524867.18 L21343528382.126L21431323883.23 L22489030875.126L22760763246.186L23415946401.149L23420628101.2  L23461856521.10 L23898603878.1  L24063822168.210L24210147817.3  L24622115995.21 L2466525955.226 L24739615255.17 L24953049371.3  L24953833255.23 L25511211636.174L25607107988.173L25609220159.126L25954189758.3  L2645215455.179 L26492728748.23 L26726870002.7  L27109749153.0  L27163225748.3  L27954029792.23 L2875907256.9   L28811729723.226L29189102680.174L29189102680.197L29428324939.5  L29763808219.126L29765679640.176L29765889648.173L29784415212.255L29786557184.2  L29790375041.1  L30027602165.126L30500770141.9  L30673807840.21 L30796635144.149L30826989516.5  L3210077857.0   L32471086843.179L32582289310.3  L32904787608.7  L32908981806.12 L32911014689.9  L33158243239.126L33735064744.9  L34354857587.3  L35084787414.7  L35653441506.7  L35735451399.6  L36391968203.147L36754970035.226L36754970035.227L36754970035.248L37549186420.174L38062709726.2  L38434723225.182L38591815859.179L39317047323.126L403768116.9    L40378272383.126L40485439768.3  L40485439770.3  L40485439773.3  L40554715395.149L41216632490.7  L41418135240.179L41418135241.178L41422554759.182L42565272692.174L42589383440.3  L43574717428.210L43952631987.18 L44614037292.180L465456788.9    L47148908368.126L47290078684.149L47594481836.179L47803377056.173L47805456395.126L48038483326.18 L50663737752.23 L50681152649.179L51246114520.174L51246114520.227L51433150352.18 L51632866479.147L51692471101.126L51887855563.9  L51989825952.247L51989873072.173L52479917400.149L53519189168.173L55673726848.203L56149103713.178L56187388617.3  L56639015128.174L57443347889.126L57533285418.4  L57538479019.3  L57628700040.13 L58049519948.173L58121027956.227L58247750441.126L58386406616.227L58493925670.2  L59308546259.183L59308630497.3  L59490344052.2  L59726287611.179L60098763854.3  L60243210611.23 L6036657012.2   L60439896503.5  L60444008939.5  L60444094443.5  L60444094446.5  L60549448800.7  L60673442934.149L61453626589.6  L61600175108.126L61626753908.174L61690834259.21 L61763771352.174L61763771352.210L62730839678.4  L62730889342.4  L62743423010.4  L62744933058.21 L63157107674.3  L63157107803.7  L63157108714.3  L63192237729.0  L63471511624.8  L63982240019.179L64027888747.179L64391376334.126L65088918924.2  L65357181960.21 L65372077406.14 L66409735371.126L67182624712.2  L6748687073.1   L6753815904.2   L67653808628.174L67997997528.174L6882356298.1   L7450831556.1   L8077320871.3   L8171587126.194 L8171655512.197 L8171734320.173 L8173669271.179 L8173781147.126 L8173831447.226 L8184155409.147 L8184155414.203 L8691603343.126 L8927295659.126 L8929377536.173 L9106855645.147 L926524850.0    L9509555001.149 L9685877192.2   P62730101946.221P67182834703.222Q11303243435.183Q12348823042.180Q13187515078.233Q14263382981.221Q17823031379.181Q17823031379.217Q17823031379.234Q18037037355.201Q23099095643.204Q23891856895.204Q23891870054.201Q23894295551.217Q23906540422.221Q25188298217.180Q25513505925.183Q25513505925.219Q25513505925.235Q25513505925.236Q26295627581.183Q26295627581.204Q266119562.183  Q26985558625.180Q2822478245.233 Q2964607797.220 Q30034265442.183Q30034265442.219Q30034265442.236Q3008054787.204 Q32774307718.185Q32774632592.180Q32774732559.183Q34532776774.233Q34533004870.232Q34535052145.255Q34817185098.180Q34817233094.233Q38933719170.180Q39314856408.204Q39321195856.219Q41188933354.233Q42451356322.216Q42453453442.180Q45941463673.184Q45941463673.220Q45941463673.236Q45941463673.237Q48475011330.180Q48475043485.203Q48731712993.180Q49698585326.182Q49698585326.218Q49698585326.234Q49698585326.235Q5061711585.180 Q50853855998.203Q50854088033.180Q50972079490.180Q53365464001.216Q53367561185.180Q54506349450.185Q57006303266.216Q57728971805.183Q63320424513.216Q6340099625.180 Q6340148133.233 Q64676825657.235Q65528734482.255Q65530881573.232Q65530915621.233Q66976989964.221Q66989661045.217Q8943687998.201 Q8943802936.180 00000100201G02o04]06G0810:J0<a0?>0AW0Cl0E90FN0H;0Im0K[0MI0Nh0PF0Qb0S>0U=0W@0Y@0[@0\M0\N0]n0_j0`I0b`0cn0dR0di0eG0e^0f40f50fh0h20h30h40h:0h@0hJ0hT0i00jk0lT0m^0n>0nN10K12M14_15G17117817918C19R19X1:;1:>1;M1;Q1<91=H1>C1>D1>k1@51@61BL1BT1D11Dd1EC1ED1EN1E]1FA1HJ1IT1Jc1K51M91OD1QO1R^1R_1R`1Ra1SE1Sm1Sn1TD1TE1VQ1VY1W81W_1XC1ZH1Ze1[31[R1[j1\A1]V1^e1`41aC1bM1bS1dF1fY1gi1hI1j31j41j51j61j71jU1k_1li1n31o=1o>20M21422>22b22c22d23n23o26:26b27I28f2:02;?2;f2=02=12=U2>h2@62@72AA2BY2Cc2Ck2E52E62EF2EP2F22F32GB2I]2Jl2K22M_2Mj2Mn2Mo2N92Nl2O02O12O22O32O42OS2OT2Ok2Ol2Q62QP2RZ2Si2Sj2Sk2Sl2TF2TQ2To2U:2U;2UQ2W\2W]2Y^2Yf2Yl2ZU2ZV2ZW2ZX2ZY2[c2\m2]02]42]52_A2aM2cT2e`2gg2j32l?2nX2oh32732833a33b33c33k35>35?35k36f37[38j39Z3:O3;D3<M3=>3=o3>`3?Q3@B3A53B>3CF3DL3ER3F<3Fk3G]3HM3IM3Jb3L63MI3NZ3Oc3PO3Q;3Qg3R\3SQ3TO3U?3V43Vo3Wf3X]3YR3ZR3[M3\g3^E3__3a93b43c43cd3d^3e]3f\3g[3hK3i@3j03jk3k`3lP3mC3nC3o63ok40f41f43744@45@46@47I48R49A49kFFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab15Ha_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2ws5welem4tab04sel04tmp02tl3WA02HB5Ha_st5Hl_st2enS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2ws5welem4tab04sel04tmp02tl3WA03v114tab22HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2ws5welem4tab04sel02tl3WA04tab34tmp32HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03TOP2ws5welem4tab04sel02tl3WA04tab34tmp32HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws5welem4tab04sel02tl3WA04tab34tmp32HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA02HB5Ha_st5Hl_st2enS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA03v114tab22HB5Ha_st5Hl_stS1R5NEED02ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2ws5welem4tab04sel02tl3WA04tab34tmp32HB5Ha_st5Hl_stS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3WA03WA14WSM24WSM33EW44tab15Ha_stS1R5NEED02sp1T2lt2lo3xs02ys2ns2es2rs3ts03LT02LO3STT2ws4tab04sel04tmp02tl4tab1S1X2an1T2lx2lt3xs02ys2ns2es2rs3ts03Han2L03DXT2ws5welem4tab04sel04tmp02tl3LTL3EW44tab1S1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts02LO3STT2ws5welem4tab04sel04tmp02tl3LTB3LTL3WA12HB5Ha_st5Hl_st2en1ES1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts02LO3STT2ws5welem4tab04sel04tmp02tl3LTL3WA13v114tab24LTB22HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts02LO3STT2ws5welem4tab04sel02tl3LTL3WA14tab34tmp34LTB32HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts02LO3STT2ws5welem4tab04sel02tl3LTL3WA14tab34tmp34LTB32HB5Ha_st5Hl_stS1R5NEED02sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_st2an1T2en1ES1R5NEED02sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2ws4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp1X1T2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp1X1T2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel04tmp02tl3LTL3WA03WA13EW42HB5Ha_st5Hl_st2LM3LT02LS2en1ES1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel04tmp02tl3LTL3WA03WA13EW43v114tab22HB5Ha_st5Hl_st2LM3LT02LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel02tl3LTL3WA03WA13EW44tab34tmp32HB5Ha_st5Hl_st3LM33LT02LSS1R5NEED02sp2an1T2lt2lo3xs02ys2ns2es2rs3ts03Han2LO3STT2ws5welem4tab04sel02tl3LTL3WA03WA13EW44tab34tmp32HB5Ha_st5Hl_st3LM33LT02LSS2an1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA04tab13WA13EW4FS1R5NEED02sp1N2ln2lo3xs02ys2ns2es2rs3ts02LO2LN2ws4tab04sel04tmp02tl3SN'2HB5Ha_st5Hl_st2an1T2en1ES2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA04WSM3S2an3Han2ws5welem3HWS4tab14LTB1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3ALT3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl2LS3LTL3TB13TB23WA04WSM33EW13EW4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl3WA0S2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2an3Han5welem4tabr3LTRS2an3Han2ws5welem3HWS4tab03LTBS2an1T3Han2ws5welem3HWSS2sp2an1T2lo1a1n2D12D2FS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0FFS2an1TS2an1TS2an1T3HanS2an5welemS2an2lt3Han2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA03EW4S2ra2sp1X1A1N2an1E2RR1T2lx2la2lt3xs02ys2ns2es2rs3ts02XB2TB3ALT3SPR2AB2ws5welem4tab04sel04tmp02tl3WA04tab1S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2an1T2lt3Han2ws5welem3HWS3HWL1QS2en2ws5welem2HWS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA04WSM24WSM3S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3WA04WSM24WSM34tab34tmp3S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3WA04WSM24WSM34tmp32q02q12q24tab4S2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR3ALN2AB2NB2ws5welem4tab04sel04tmp02tl3WA0S2sp2loFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab1S2an1TS2an1T2lt3Han2ws5welem3HWS3HWL1a2HaS1TS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab2S2anS2sp2an1T2lt2lo3Han3STT5welem3HWL2ws3HWSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S1A2an2en1T2lx2la2ln3le_2lr2lt3Han2Ln2ws5welem3HWS3HWL4DAT'FS1X2an1T2lx2lt3Han3DXT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0FS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han3LT02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl2LS3LTL3TB13TB23WA03WA13EW13EW4S2an3HanS2ra2sp1X1A1N2an1E2RR1T2la3xs02ys2ns2es2rs3ts03SPR3ALA2AB2ws5welem4tab04sel02tl3WA04tab34tmp3S1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2an3Han2ws5welem3HWS4tab34LTB3SS2an1T3HanS2sp1X2lx2lo2SXS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB4T47A2ws5welem4tab04sel02tl3WA03WA13EW44tab34tmp3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab1S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2LN2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3NB23WA04WSM24WSM3S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3NB23WA04WSM24WSM3S2ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2Ln2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3NB23WA04WSM24WSM3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel02tl3WA04tmp32q02q12q24tab4SSFS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLFS2an3Han5welem3WA03WA1SS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3LTL3TB23WA03WA13EW44tab34tmp3S2an3HanS2an3Han2ws5welem3HWS4tab34LTB3S2an2en2lx2la2ln3le_2lr2lt2ys3Han2Ln2LAS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR3ALA2AB2NB2EB2RB4T47A2ws5welem4tab04sel04tmp02tl3WA03WA14WSM3S2an2lt3ts03Han3LT05welem3HWLS2ws5welem3HWSS2an3Han2ws5welem3HWS4tab34LTB3S1R3HIA1h2sp2lo3TOP4HTOPS2an1T3Han2ws5welem3HWSS2ra2sp1X1A1N2an1E2RR1T2lt3xs02ys2ns2es2rs3ts02TB2ws5welem4tab04sel04tmp02tl3WA04tab1S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts04tab04sel02tl3WA04tmp32q02q12q24tab4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2an1TS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl2LS3LTL3TB23WA03WA13EW13EW44tab34tmp3S2ra2sp1X1A1N2an1E2RR1T2lt3xs02ys2ns2es2rs3ts02TB2ws5welem4tab04sel04tmp02tl3WA0S2an1T2lt3Han2ws5welem3HWS3HWL1QS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR3ALN2AB2NB2ws5welem4tab04sel04tmp02tl3WA0FFFFS2an3Han2ws5welem3HWS4tab03LTBS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0FS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab2S2sp1A2an1T2la2lt2lo5welem3HWL4DAT'3SA'S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2an2lt3ts03Han3LT02ws5welem3HWS3HWLFFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0FS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA03Han3ALT3LTL3TB13TB23EW1S2sp2an1T2lt2lo3Han3STT2ws5welem3HWS3HWLS1X2an1T2lx2lt3Han3DXT2ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T2la3xs02ys2ns2es2rs3ts03SPR3ALA2AB2ws5welem4tab04sel02tl3WA04tab34tmp3S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S2sp1N2an1T2ln2lt2lo5welem3HWL4DNT'3SN'S2ra2sp1X1A1N2an1E2en2RR1T2lt3xs02ys2ns2es2rs3ts02H01H2lx2la2ln3le_2lr3Ln'FS2an2lt3ts03Han3LT02ws5welem3HWS3HWLS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han4tab04sel02tl3WA04tmp32q02q12q24tab4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl3WA0FS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tmp32q02q12q24tab4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2an3HanS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0FS2an1T3Han5welemS2an1T3HanS2sp2an1T2lo2ws5welem3HWS1x2Hx3HanFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3ALT3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl2LS3LTL3TB13TB23WA03WA14WSM33EW13EW4S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel02tl3WA04tab34tmp3S2an1TS1R5NEED02ra2sp1X1A1N2an1E2en2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts03Han2Ln2L03LT03DXT2XB2TB3SPR2LO2SX3STT2LN2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA04WSM24WSM32N0S2en3H792KBS2anFS1R2lo3LOSS1R5NEED02sp2an1T2lt2lo3Han2LO3STT2ws5welem3HWS3HWLS2anFFFFS2an3Han2ws5welem3HWS4tab34LTB3FS2an1T3Han2ws5welem3HWSFS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2an1T5welem2ws3HWS3Han2ltS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA04tab2FFFS2an1T5welem3Han2ws3HWS2ltS2an2ys3LYAS2an3Han2ws5welem3HWS4tab03LTBS2an2q13LQ1SS2sp2an1T2lo1a1n2D12D2S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB4T47A2ws5welem4tab04sel02tl3WA04WSM24WSM34tab34tmp3FS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3WA04WSM24WSM3S2an3HanS2an1TS2sp1A2an2en2lx2la2ln3le_2lr2lt2lo2Ln3SA'FFSSS2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T3xs02ys2ns2es2rs3ts02ws5welem4tab04sel04tmp02tl3WA0S1TS2anFS2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW44tab1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW44tab1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW4S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3LTL3TB23WA03WA13EW44tab34tmp3S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW4S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3LTL3TB23WA03WA13EW44tab34tmp3S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW44tab1S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han2XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel02tl3LTL3TB23WA03WA13EW44tmp32q02q12q23LQ24tab4S2ra2sp1X1A1N2an1E2RR1T2ln3xs02ys2ns2es2rs3ts02NB2ws5welem4tab04sel04tmp02tl3WA0S2ra2sp1X1A1N2an1E2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Han3LT02XB2TB3SPR2AB2NB2EB2RB2ws5welem4tab04sel04tmp02tl3LTL3TB13TB23WA03WA13EW4FS2ra2sp1X1A1N2an1E2RR1T2lx2la2lt3xs02ys2ns2es2rs3ts02XB2TB3ALT3SPR2AB2ws5welem4tab04sel04tmp02tl3WA04tab1SFS2an3HanS2an2en1T3xs02ys2ns2es2rs3ts03Han2ws5welem2HW3HWS4tab04sel04tmp02tl2LS3EW13EW44tab1FS1N3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp3S2sp2an1T2lo3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA03EW44tab1S2sp3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl2HBS2sp3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab22HBS2sp3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp32HBS2an1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA03EW44tab1S1T3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1T3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1N2an3xs02ys2ns2es2rs3ts03Han2ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl2HB5Ha_st5Hl_st2an1T2en1ES2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS2sp1T2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS2sp1T2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S1N2ln3xs02ys2ns2es2rs3ts02NB2ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp3S2an1T2lt3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl3LTL3TB23WA03WA13EW44tab1S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl2HB5Ha_st5Hl_st2an1T2en1ES1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp1T2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS2an1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA03EW44tab1S1N3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1N3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1N3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp3S2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp3S2sp2an2lo3xs02ys2ns2es2rs3ts04tab04sel02tl4tmp32q02q12q24tab4S2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp3S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS1T2lt3xs02ys2ns2es2rs3ts02TB2ws4tab04sel04tmp02tl4tab1S1T2lt3xs02ys2ns2es2rs3ts02TB2ws4tab04sel04tmp02tl4tab1S2sp3xs02ys2ns2es2rs3ts02ws4tab04sel02tl4tab34tmp32HBS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl4tab2S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem4tab04sel04tmp02tl2HB5Ha_st5Hl_st2en1ES1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem4tab04sel04tmp02tl3v114tab22HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2an1T2lo3xs02ys2ns2es2rs3ts02LO2ws5welem4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl4tab1S2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS2sp3xs02ys2ns2es2rs3ts03SPR2ws4tab04sel04tmp02tl2HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR2ws4tab04sel04tmp02tl4tab22HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR2ws4tab04sel02tl4tab34tmp32HB5Ha_stS2sp3xs02ys2ns2es2rs3ts03SPR2ws4tab04sel02tl4tab34tmp32HB5Ha_stS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab2S2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tlS1N2an3xs02ys2ns2es2rs3ts03Han2ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tl4tab2S1N2an3xs02ys2ns2es2rs3ts03Han2ws4tab04sel04tmp02tlS2sp2lo3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab2S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel04tmp02tlS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp3S1R5NEED02sp1T2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp32HB5Ha_st5Hl_stS1R5NEED02sp2an2lo3xs02ys2ns2es2rs3ts02LO4tab04sel02tl4tmp32q02q12q24tab4S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp3S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO2ws4tab04sel02tl4tab34tmp3S2an1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA03EW44tab1S2an1T3xs02ys2ns2es2rs3ts03Han2ws5welem4tab04sel04tmp02tl2LS3WA03EW44tab1S3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl4tab1S3xs02ys2ns2es2rs3ts02ws4tab04sel04tmp02tl". (* [comment removed for export] *)
  #[using="IMG NEED0 MM lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LA LN LE LR DAT DNT DET DRT DNX DEX ALA ALN ALE ALR AB NB EB RB SA SN SE SRR HN0 HE0 HR0 HA0 OX0 OA0 ON0 OE0 OR0 AMS AMC T47A"] Lemma setup_walk :
    forall (ws welem : Z) (mm : mem) (j0 j32 j72 : list (bv 8))
           (xra xt0 xt1 xt2 ys0 xa1 xa2 xa3 xa6 xa7 ys3 ys7 ys11 xt3 xt4 xt5 xt6 : word),
      (ws = 1 /\ welem = 2 /\ en * 32 <= 79) \/ (ws = 3 /\ welem = 8 /\ 80 <= en * 32) ->
      u32arr asegs mm X xs0 -> u32arr asegs mm T ts0 ->
      munch [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m mm ->
      wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (bv_unsigned sp + -208) -> HM asegs R HIA h LB LF mm ->
      aobj asegs AL CS m T (4 * (welem * an + an + (2 * an + 1))) ->
      rw_cells asegs mm (bv_unsigned sp + -208)
        [CB 24 j0; C8 (Z_to_bv 64 0); CB 32 j32; C8 (Z_to_bv 64 X); CB 24 j72; C8 (Z_to_bv 64 N);
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evtA asegs AL CS POST (MS (mkR xra SP' gp tp xt0 xt1 xt2 ys0 (Z_to_bv 64 1) (Z_to_bv 64 ws) xa1 xa2 xa3 (Z_to_bv 64 E) (Z_to_bv 64 en) xa6 xa7
                                     (Z_to_bv 64 (al_sb AL)) ys3 (Z_to_bv 64 an) (Z_to_bv 64 T) (Z_to_bv 64 RR) ys7 (Z_to_bv 64 (en * 32)) (Z_to_bv 64 A) (Z_to_bv 64 0) ys11
                                     xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0xa5ff4) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HW HX HT MU WM MI ST HH OTL FR. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    assert (HWS : (ws = 1 /\ welem = 2) \/ (ws = 3 /\ welem = 8)) by (clear - HW; lia).
    assert (HWL : welem * an + an + (2 * an + 1) <= lt).
    { pose proof Ln as Ln'. unfold exp_mod_working_limbs, exp_mod_welem in Ln'. destruct (Z.ltb_spec 79 (32 * en)); destruct HW as [(_ & -> & ?)|(_ & -> & ?)]; lia. }
    (* [comment removed for export] *)
    destruct (u32arr_take _ _ _ _ (Z.to_nat (welem * an)) HT ltac:(clear - LT0 HWL HWS Han; lia)) as [HTAB HR1].
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HR1 ltac:(clear - LT0 HWL HWS Han; rewrite skipn_length; lia)) as [HS HR2]. clear HR1.
    destruct (u32arr_take _ _ _ _ (Z.to_nat (2 * an + 1)) HR2 ltac:(clear - LT0 HWL HWS Han; rewrite !skipn_length; lia)) as [HMm HL]. clear HR2.
    rewrite !skipn_skipn in HL. rewrite skipn_skipn in HMm.
    replace (T + 4 * Z.of_nat (Z.to_nat (welem * an))) with (T + 4 * (welem * an)) in HS, HMm, HL by (clear - HWS Han; lia).
    replace (T + 4 * (welem * an) + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * (welem * an + an)) in HMm, HL by (clear - Han; lia).
    replace (T + 4 * (welem * an + an) + 4 * Z.of_nat (Z.to_nat (2 * an + 1))) with (T + 4 * (welem * an + an + (2 * an + 1))) in HL by (clear - Han; lia).
    lazymatch type of HTAB with u32arr _ _ _ ?l => set (tab0 := l) in HTAB end.
    lazymatch type of HS with u32arr _ _ _ ?l => set (sel0 := l) in HS end.
    lazymatch type of HMm with u32arr _ _ _ ?l => set (tmp0 := l) in HMm end.
    lazymatch type of HL with u32arr _ _ _ ?l => set (tl := l) in HL end.
    assert (LTB : Z.of_nat (length tab0) = welem * an) by (subst tab0; clear - LT0 HWL HWS Han; rewrite firstn_length; lia).
    assert (LS : Z.of_nat (length sel0) = an) by (subst sel0; clear - LT0 HWL HWS Han; rewrite firstn_length, skipn_length; lia).
    assert (LM : Z.of_nat (length tmp0) = 2 * an + 1) by (subst tmp0; clear - LT0 HWL HWS Han; rewrite firstn_length, skipn_length; lia).
    assert (LTL : Z.of_nat (length tl) = lt - (welem * an + an + (2 * an + 1))) by (subst tl; clear - LT0 HWL HWS Han; rewrite skipn_length; lia).
    clearbody tab0 sel0 tmp0 tl. clear HT.
    destruct (objs_pre welem OTL _ HH MU) as (OX & OA & ON & OR & OT).
    pose proof (unlock _ DNT) as DNT'. pose proof (unlock _ SN) as SN'.
    pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear - DNT' SN' Ln HWL Han; lia)) as HN.
    (* [comment removed for export] *)
    pose proof TB as [TB1 TB2]. pose proof NB as [NB1 NB2].
    assert (WA0 : 0 <= welem * an) by (clear - HWS Han; destruct HWS as [[_ ->]|[_ ->]]; lia).
    assert (WA1 : welem * an <= 8 * an) by (clear - HWS Han; destruct HWS as [[_ ->]|[_ ->]]; lia).
    assert (WSM2 : ws mod 64 = ws) by (clear - HWS; destruct HWS as [[-> _]|[-> _]]; reflexivity).
    assert (WSM3 : ws mod 18446744073709551616 = ws) by (clear - HWS; destruct HWS as [[-> _]|[-> _]]; reflexivity).
    assert (EW1 : Z.shiftl 1 ws = welem) by (clear - HWS; destruct HWS as [[-> ->]|[-> ->]]; reflexivity).
    assert (EW2 : Z.shiftl an ws = welem * an).
    { clear - HWS Han. destruct HWS as [[-> ->]|[-> ->]]; rewrite Z.shiftl_mul_pow2 by lia; [change (2^1) with 2| change (2^3) with 8]; lia. }
    assert (EW4 : an * 2 ^ ws = welem * an) by (rewrite <- EW2, Z.shiftl_mul_pow2 by (clear - HWS; destruct HWS as [[-> _]|[-> _]]; lia); reflexivity).
    assert (EW5 : (welem * an) mod 18446744073709551616 = welem * an) by (apply Z.mod_small; clear - WA0 WA1 Han; lia).
    assert (EW6 : Z.shiftl (welem * an) 2 = 4 * (welem * an)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia).
    assert (EW7 : Z.shiftl an 2 = 4 * an) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia).
    zstep.
    ea_go [680052]. shadow_chk ON N 4.
    (* [comment removed for export] *)
    ea_go [680060]. rd HN 0. clear HN.
    (* [comment removed for export] *)
    ea_go [680064]. try (rewrite !Z.shiftl_mul_pow2 by lia; change (2^2) with 4; replace (an * 4) with (4 * an) by (clear; lia)).
    ea_go [426584].
    (* [comment removed for export] *)
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HTAB ltac:(clear - LTB HWS Han; lia)) as [HT0 HT1].
    apply u8arr_of_u32arr in HT0.
    lazymatch type of HT1 with u32arr _ _ _ ?l => set (tabr := l) in HT1 end.
    assert (LTR : Z.of_nat (length tabr) = welem * an - an) by (subst tabr; rewrite skipn_length; clear - LTB HWS Han; lia). clearbody tabr.
    replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in HT1 by (clear - Han; lia). clear HTAB.
    lazymatch goal with H1 : mem_inv asegs ?m2, H2 : stk asegs ?m2 lo _, H3 : HM _ _ _ h LB LF ?m2 |- _ =>
      rename H1 into MI1; rename H2 into ST1; rename H3 into HH1; rename m2 into m1 end.
    eapply (amemset_call T (4 * an) _ m1 0xa6090);
      [ exact HH1 | exact HT0 | rewrite u32s_length, firstn_length; clear - LTB HWS Han; lia
      | eapply aobj_sub; [exact OT| clear; lia| clear - Han HWS; lia] | exact ST1 | exact MI1
      | clear - STT Ln Han HWS HWL; lia
      | pose proof (cw_top47 asegs R HIA h LB LF m1 _ T (4 * lt) HH1 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
      | clear - Han; lia | intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia | reflexivity | reflexivity | clear; lia | ].
    intros m2 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 MUc WMc MIc HDc STc HHc.
    apply (rw_cells_of_u8arr asegs) in HDc. rewrite repeat_length in HDc.
    apply (u32arr_of_cells asegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat an))) in HDc; [| rewrite u32s_repeat0; f_equal; clear - Han; lia].
    assert (DJ : forall a n, (a + n <= T \/ T + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -208 <= a) ->
              disjoint_from [(T, T + 4 * an); (lo, bv_unsigned sp + -208)] a n).
    { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
    eapply u32arr_transport in HX; [| exact MUc| exact WMc| apply DJ; rewrite L0; clear - DXT SX Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HT1; [| exact MUc| exact WMc| apply DJ; rewrite LTR; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HS; [| exact MUc| exact WMc| apply DJ; rewrite LS; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HMm; [| exact MUc| exact WMc| apply DJ; rewrite LM; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HL; [| exact MUc| exact WMc| apply DJ; rewrite LTL; clear - STT Ln Han HWS HWL LO NEED0; lia].
    match goal with FRm : rw_cells asegs m1 (bv_unsigned sp + -208) _ |- _ =>
      apply (rw_cells_transport asegs _ m1 m2 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR2| apply DJ; simpl_sizes; clear - STT Ln Han HWS HWL SPR LO NEED0 LO0; lia] end.
    assert (MU2 : munch [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x Hx; cbn [outside] in *; clear - Hx Han HWS LO NEED0; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM2. clear MU WM. rename MU2 into MU. rename WM2 into WM.
    assert (HTAB : u32arr asegs m2 T (repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr)).
    { apply u32arr_app. split; [exact HDc|]. rewrite repeat_length. replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) by (clear - Han; lia). exact HT1. }
    assert (LTB1 : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr)) = welem * an) by (rewrite length_app, repeat_length; clear - LTR Han; lia).
    set (tab1 := repeat (Z_to_bv 64 0) (Z.to_nat an) ++ tabr) in *. clearbody tab1. clear HDc HT1 LTR HT0 MUc WMc MI1 ST1 HH1 OX OA ON OR OT. clear tabr.
    destruct (objs_pre welem OTL _ HHc MU) as (OX & OA & ON & OR & OT).
    (* [comment removed for export] *)
    ea_go [680100]. shadow_chk OT T 4.
    (* [comment removed for export] *)
    ea_fixH (T + 4 * (welem * an + an)).
    vstep 10%positive. zstep. vstep 10%positive. vstep 10%positive. vstep 10%positive.
    (* [comment removed for export] *)
    vstep 12%positive. vstep 12%positive. vstep 10%positive. vstep 12%positive. vstep 11%positive. zstep.
    (* [comment removed for export] *)
    vstep 10%positive. vstep 11%positive. vstep 11%positive. vstep 16%positive.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok asegs _ T tab1 0 _ HTAB ltac:(clear - LTB1 Han HWS; lia) ltac:(f_equal; clear; lia)) as SOK.
    replace (T + 4 * 0) with T in SOK by (clear; lia).
    zstep_to [680176].
    lazymatch goal with |- context [write_to_mem ?mq _ (le4 ?v)] =>
      pose proof (u32arr_write asegs mq T tab1 0 v HTAB ltac:(clear - LTB1 Han HWS; lia)) as HX';
      replace (T + 4 * 0) with T in HX' by (clear; lia);
      store_done; try clear HTAB; rename HX' into HTAB;
      assert (LTB2 : Z.of_nat (length (upd tab1 (Z.to_nat 0) v)) = welem * an) by (rewrite upd_length; exact LTB1);
      set (tab2 := upd tab1 (Z.to_nat 0) v) in *; clearbody tab2; clear LTB1; try clear tab1
    end.
    (* [comment removed for export] *)
    zstep_to [677024].
    replace (Z_to_bv 64 T) with (Z_to_bv 64 (T + 4 * (an * 0))) by (f_equal; clear; lia).
    lazymatch goal with FRq : rw_cells asegs ?mq (bv_unsigned sp + -208) ?cells, H1 : mem_inv asegs ?mq, H2 : stk asegs ?mq lo _, H3 : HM _ _ _ h LB LF ?mq |- _ =>
      eapply (mm_call_tab ws welem tl HWS HWL LTL OTL 0 0 RR rs mq tab2 sel0 tmp0 0xa6110 (fun mz => rw_cells asegs mz (bv_unsigned sp + -208) cells));
        [ clear - HWS; lia | clear - HWS; lia | left; split; reflexivity | reflexivity | reflexivity | clear; lia
        | | exact (conj HX (conj HTAB (conj LTB2 (conj HS (conj LS (conj HMm (conj LM (conj HL (conj MU (conj WM (conj H1 (conj H2 H3)))))))))))) | exact FRq | ] end.
    { intros mz1 mz2 MUq WMq FRq. eapply rw_cells_transport; [exact FRq| exact MUq| exact WMq|].
      cbn [disjoint_from]. simpl_sizes. clear - STT Ln Han HWS HWL SPR LO NEED0 LO0. lia. }
    clear HX HTAB LTB2 HS HMm HL MU WM OX OA ON OR OT. clear dependent tab2. clear dependent tmp0.
    lazymatch goal with |- forall _, _ => idtac end.
    intros m3 tab3 tmp3 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 PV FR3.
    replace (T + 4 * (an * 0)) with T by (clear; lia).
    dpose PV as (HX & HTAB & LTB3 & HS & _ & HMm & LM3 & HL & MU & WM & MI3 & ST3 & HH3).
    (* [comment removed for export] *)
    ea_go [425404].
    clear PV. try clear FR2.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    lazymatch goal with H1 : mem_inv asegs m4, H2 : stk asegs m4 lo _, H3 : HM _ _ _ h LB LF m4 |- _ => rename H1 into MI4; rename H2 into ST4; rename H3 into HH4 end.
    destruct (objs_pre welem OTL _ HH4 MU) as (OX & OA & ON & OR & OT).
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) HTAB ltac:(clear - LTB3 HWS Han; lia)) as [Q0 QR].
    destruct (u32arr_take _ _ _ _ (Z.to_nat an) QR ltac:(rewrite skipn_length; clear - LTB3 HWS Han; lia)) as [Q1 Q2]. clear QR.
    apply u8arr_of_u32arr in Q1.
    replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in Q1, Q2 by (clear - Han; lia).
    replace (T + 4 * an + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * (an + an)) in Q2 by (clear - Han; lia).
    lazymatch type of Q0 with u32arr _ _ _ ?l => set (q0 := l) in Q0; assert (LQ0 : Z.of_nat (length q0) = an) by (subst q0; rewrite firstn_length; clear - LTB3 HWS Han; lia); clearbody q0 end.
    lazymatch type of Q2 with u32arr _ _ _ ?l => set (q2 := l) in Q2; assert (LQ2 : Z.of_nat (length q2) = welem * an - an - an) by (subst q2; rewrite !skipn_length; clear - LTB3 HWS Han; lia); clearbody q2 end.
    lazymatch type of Q1 with u8arr _ _ _ (u32s ?l) => set (q1 := l) in Q1; assert (LQ1 : Z.of_nat (length q1) = an) by (subst q1; rewrite firstn_length, skipn_length; clear - LTB3 HWS Han; lia); clearbody q1 end.
    clear HTAB LTB3.
    pose proof (unlock _ DAT) as DAT'. pose proof (unlock _ SA) as SA'.
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; clear - DAT' SA' Ln HWL Han; lia)) as HA.
    rewrite <- (firstn_skipn (Z.to_nat an) ys), u32s_app in HA. apply bytes_at_app in HA. destruct HA as [HA _].
    assert (LYA : Z.of_nat (length (firstn (Z.to_nat an) ys)) = an) by (rewrite firstn_length; clear - LA Ln Han; lia).
    eapply (amemcpy_call (T + 4 * an) A (4 * an) _ _ m4 0xa6148);
      [ exact HH4 | exact Q1 | exact HA | rewrite u32s_length; clear - LQ1; lia | rewrite u32s_length; clear - LYA; lia
      | eapply aobj_sub; [exact OT| clear - Han; lia| clear - Han HWS; lia] | exact OA
      | clear - DAT' Ln Han HWS HWL; lia | exact ST4 | exact MI4
      | clear - STT Ln Han HWS HWL; lia | clear - SA' Ln Han; lia
      | pose proof (cw_top47 asegs R HIA h LB LF m4 _ T (4 * lt) HH4 CWT ltac:(clear - Han HWS HWL; lia)) as Q; clear - Q Han HWS HWL; lia
      | exact T47A
      | clear - Han; lia | intros a Ha; apply CWT; clear - Ha Han HWS HWL; lia | reflexivity | reflexivity | clear; lia | ].
    try clear MIc STc HHc.
    intros m5 yt0' yt1' yt2' ya0' ya1' ya2' ya3' ya4' ya5' ya6' ya7' yt3' yt4' yt5' yt6' MUc WMc MIc HDc STc HHc.
    apply u32arr_of_u8arr_u32s in HDc.
    assert (DJ2 : forall a n, (a + n <= T + 4 * an \/ T + 4 * an + 4 * an <= a) -> (a + n <= lo \/ bv_unsigned sp + -208 <= a) ->
              disjoint_from [(T + 4 * an, T + 4 * an + 4 * an); (lo, bv_unsigned sp + -208)] a n).
    { intros a n D1 D2. cbn [disjoint_from]. clear - D1 D2. lia. }
    eapply u32arr_transport in HX; [| exact MUc| exact WMc| apply DJ2; rewrite L0; clear - DXT SX Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in Q0; [| exact MUc| exact WMc| apply DJ2; rewrite LQ0; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in Q2; [| exact MUc| exact WMc| apply DJ2; rewrite LQ2; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HS; [| exact MUc| exact WMc| apply DJ2; rewrite LS; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HMm; [| exact MUc| exact WMc| apply DJ2; rewrite LM3; clear - STT Ln Han HWS HWL LO NEED0; lia].
    eapply u32arr_transport in HL; [| exact MUc| exact WMc| apply DJ2; rewrite LTL; clear - STT Ln Han HWS HWL LO NEED0; lia].
    match goal with FRm : rw_cells asegs m4 (bv_unsigned sp + -208) _ |- _ =>
      apply (rw_cells_transport asegs _ m4 m5 _ _) with (2 := MUc) (3 := WMc) in FRm; [rename FRm into FR5| apply DJ2; simpl_sizes; clear - STT Ln Han HWS HWL SPR LO NEED0 LO0; lia] end.
    assert (MU5 : munch [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m m5).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x Hx; cbn [outside] in *; clear - Hx Han HWS LO NEED0; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WMc) as WM5. clear MU WM.
    assert (HTAB : u32arr asegs m5 T (q0 ++ firstn (Z.to_nat an) ys ++ q2)).
    { apply u32arr_app. split; [exact Q0|]. apply u32arr_app. split.
      - rewrite LQ0. exact HDc.
      - rewrite LQ0, LYA. replace (T + 4 * an + 4 * an) with (T + 4 * (an + an)) by (clear; lia). exact Q2. }
    assert (LTB4 : Z.of_nat (length (q0 ++ firstn (Z.to_nat an) ys ++ q2)) = welem * an) by (rewrite !length_app, !Nat2Z.inj_add, LQ0, LYA, LQ2; clear; lia).
    set (tab4 := q0 ++ firstn (Z.to_nat an) ys ++ q2) in *. clearbody tab4.
    assert (PV5 : PINV welem tl m5 tab4 sel0 tmp3) by (exact (conj HX (conj HTAB (conj LTB4 (conj HS (conj LS (conj HMm (conj LM3 (conj HL (conj MU5 (conj WM5 (conj MIc (conj STc HHc))))))))))))).
    clear HDc Q0 Q1 Q2 HA MUc WMc MI4 ST4 HH4 OX OA ON OR OT.
    (* [comment removed for export] *)
    zstep_to [680268]. ea_rwH. ea_rw. ea_fixG (T + 4 * (welem * an)).
    (zstep_to [680268]; zstep). if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear - Hen; lia).
    - (* [comment removed for export] *)
      destruct HW as [(-> & -> & H79)|(-> & -> & H79)]; [| exfalso; clear - KB H79; lia].
      eapply (pre_tail_walk 1 2 _ tl ltac:(left; split; reflexivity) HWL LTL OTL); [exact PV5 | exact FR5].
    - (* [comment removed for export] *)
      destruct HW as [(-> & -> & H79)|(-> & -> & H79)]; [exfalso; clear - KB H79; lia|].
      ea_raw_to [680300]. rewrite ?Z.shiftl_mul_pow2 by lia. ea_pow.
      eapply (pre_loop_walk 3 8 _ tl ltac:(right; split; reflexivity) HWL LTL OTL 6 2); [reflexivity | clear; lia | f_equal; clear; lia | f_equal; clear; lia | f_equal; clear; lia | exact PV5 | exact FR5].
    all: match goal with |- ?g => idtac "SETUP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0@D35881667587.137D59583840943.137K40484668124.137K42587433812.137L1685717371.0   L17777983920.129L18496683636.130L20681125023.130L21997097076.130L22053004888.130L22193487704.130L24506944756.130L2779640280.130 L28025253620.130L28081971108.4  L29189102680.130L29321180504.130L29428324939.5  L30532557172.130L31538905332.130L3174820682.4   L33163522278.133L34046671732.130L35422804568.130L35653441506.7  L36543870964.130L37878424280.130L38923399768.130L39284637285.0  L3950434548.130 L40057457140.130L40500118168.3  L40834179097.132L42589383440.3  L43061724204.131L46063675480.130L47816909591.126L48592851700.130L49585649780.130L5303231320.130 L54603181940.130L54619284952.130L54768680664.130L60098763854.3  L60140069080.130L60628794868.130L61904762072.130L6416703448.130 L6660460841.126 L66640104052.130L9917822936.130 L9961223540.130 Q14342765596.135Q15643324129.133Q17823031379.134Q18135760482.135Q18235909853.135Q18365925601.133Q18378753154.133Q18694146040.135Q21879645826.133Q21962771306.135Q23622925864.135Q24389563138.133Q25513505925.136Q25662358575.135Q27584944865.133Q27907200258.133Q29505479905.133Q30034265442.136Q30415036802.133Q30728837833.135Q31228709292.135Q31271525473.133Q32655500769.133Q32833779681.133Q33918256002.133Q34800357606.135Q35014437530.135Q36425882626.133Q37005758509.135Q3830427394.133 Q38452998860.135Q39939554818.133Q41152393185.133Q44648843873.133Q44961269506.133Q45217673672.135Q4533518817.133 Q45941463673.137Q4746191627.135 Q48475011330.133Q49208793878.135Q49698585326.135Q50854088033.133Q51235796833.133Q51371168465.135Q52101170785.133Q52938651676.135Q53969758199.135Q54124893692.135Q54485784450.133Q55639661864.135Q5675810657.133 Q59256763233.133Q59843137889.133Q60511257090.133Q61802139820.135Q63021244034.133Q64255486968.135Q66522067074.133Q9843367298.133 00001Y04105`07K07L08;08c0:;0:c0;K0<30<[0=C0=k0><0>d0?L0?^0@F0@n0A?0Ag0BO0C70CO0D70D_0EG0EH0F00FX0FY0GC0GD0Hc0IK0J80J`0KH0L00LX0M@0Mh0N20NZ0OB0Oj0PR0Q?0Qg0RO0S70SL0Sg0TB0TC0TD0T_0UE0Ua0VG0VH0Vd0WJ0Xa0Xb0Y=0Yc0Z>0[`0\F0\G0\d0]?0]Z0^50^[0^\0_90__0_`0`F0`G0`m0aH0ac0bI0bJ0be0dR0dS0e90e:0e_0f:0fU0fV0g10g20gO0gk0hQ0hR0hm0iH0ic0jI0jJ0k00k10kW0l=S1R3HIA1h2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts03TOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR3LOS2LO2AB2NB2EB2RB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R5NEED02ra2sp1T2lt2lo3xs02ys2ns2es2rs3ts03LT02LO3STT2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1NS1R5NEED02ra2sp1X2lx2lo3xs02ys2ns2es2rs3ts02L02LO2SX2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111NSS2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts03HenS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T2lx2la2ln3le_2lr2lt3xs02ys2ns2es2rs3ts03Hen2XB2TB3SPR2AB2NB2EB2RBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2en5welem3HWE2KWS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R2lo3LOS3ALO3ACPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2en5welem3HWE2KWS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0SS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0FS1R2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0FS1R5NEED02ra2sp1X1A1N1E2RR1T2lx2la2ln3le_2lr2lt2lo3xs02ys2ns2es2rs3ts02XB2TB3SPR2LO2AB2NB2EB2RBS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts01HS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S1R2lo3LOSS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2en2RR1T3xs02ys2ns2es2rs3ts01HS2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S2ra2sp1X1A1N1E2RR1T3xs02ys2ns2es2rs3ts0S3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S2sp3xs02ys2ns2es2rs3ts02HBFFS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R3xs02ys2ns2es2rs3ts04IMG'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R3xs02ys2ns2es2rs3ts04IMG'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2ra2sp2lo3xs02ys2ns2es2rs3ts02HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1NFS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02ra2sp2lo3xs02ys2ns2es2rs3ts02LO2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1NS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R3xs02ys2ns2es2rs3ts05ALWF'S2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R3xs02ys2ns2es2rs3ts05ALWF'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02ra2sp2an1T2lo3xs02ys2ns2es2rs3ts02LO5welem2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s111X1NFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS2sp3xs02ys2ns2es2rs3ts03SPR2HB5Ha_stS2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0FS2sp2lo3xs02ys2ns2es2rs3ts0FS1R3xs02ys2ns2es2rs3ts05ALWF'S1R3xs02ys2ns2es2rs3ts04IMG'S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S2sp2lo3xs02ys2ns2es2rs3ts0S1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOFS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LOS1R5NEED02sp2lo3xs02ys2ns2es2rs3ts02LO". (* [comment removed for export] *)
  #[using="IMG NEED0 MM lx la ln le_ lr lt ys ns es rs Han Hen Ln L0 LT0 DXT XB TB ALX ALT SPR SPA LOS LO TOP SX STT CWX CWT LA LN LE LR DAT DNT DET DRT DNX DEX ALA ALN ALE ALR AB NB EB RB SA SN SE SRR HN0 HE0 HR0 HA0 OX0 OA0 ON0 OE0 OR0 AMS AMC T47A"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(30.$5.Vm,VX,Vxs0,)P,(30.$5.Vm,VT,Vts0,)P,(13.$5.Vm,)P,(11.$5.Vm,Vlo,(12.&40.Vsp,))P,(4.$5.VR,VHIA,Vh,VLB,VLF,Vm,)P,(;.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)Vm,VT,(32.+4.(41.Van,Ven,)))(26.$5.(<.VR,)(=.$5.VR,VHIA,Vh,)(27.$5.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,)(28.(29.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(1>.&40.VX,)(1>.&40.VA,)(1>.&40.VN,)(1>.&40.Van,)(1>.&40.VE,)(1>.&40.Ven,)(1>.&40.VRR,)(1>.&40.VT,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(1>.&40.+:5>38.)Vfc,(2:.(2.&40.))Vm,(2;.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX HT MI ST HH OT0. rt_facts.
    unfold MPI_CORE_EXP_MOD_STACK_A, MPI_CORE_MONTMUL_STACK_A in LO.
    set (welem := exp_mod_welem en).
    assert (HWE : (welem = 2 /\ en * 32 <= 79) \/ (welem = 8 /\ 80 <= en * 32)).
    { subst welem. unfold exp_mod_welem. destruct (Z.ltb_spec 79 (32 * en)); [right| left]; split; try reflexivity; lia. }
    assert (OTL : aobj asegs AL CS m T (4 * (welem * an + an + (2 * an + 1)))) by exact OT0.
    clearbody welem. clear OT0.
    pose proof (munch_refl [(T, T + 4 * (welem * an + an + (2 * an + 1))); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lazymatch goal with |- evtA ?sg ?al ?cs ?P (MS ?Rg ?FF ?pc ?fcc ?rv m ?ro) =>
      enough (G : forall mm, mm = m -> evtA sg al cs P (MS Rg FF pc fcc rv mm ro)) by exact (G m eq_refl) end.
    intros mm Emm. rewrite <- Emm in HX, HT, MI, ST, HH. rewrite <- Emm in MU at 2. rewrite <- Emm in WM at 2. clear Emm.
    pose proof (hm_abase asegs R HIA h LB LF mm HH) as ABS.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep_to [679496].
    carve_frame 208%nat ST.
    (* [comment removed for export] *)
    zstep_to [679568].
    pose proof (abase_got _ _ _ ABS) as GOT. pose proof (abase_gsb _ _ _ ABS) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep_to [679572]. zstep_to [679576]. zstep_to [679580]. clear GOT GSB.
    (* [comment removed for export] *)
    zstep_to [679712].
    (* [comment removed for export] *)
    zstep_to [679892].
    (* [comment removed for export] *)
    zstep_to [679900]. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2^5) with 32.
    zstep_to [679904]. zstep_to [679908].
    (zstep_to [679908]; zstep). if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by (clear - Hen; lia);
      [ (* [comment removed for export] *) zstep_to [679924] | (* [comment removed for export] *) zstep_to [679916]; zstep_to [679924] ].
    - lazymatch goal with FR' : rw_cells asegs ?m2 (bv_unsigned sp + -208) _ |- _ =>
        eapply (setup_walk 3 welem m2); [right; clear - HWE KW; lia | | | exact MU | exact WM | | | | exact OTL | exact FR'] end;
        assumption.
    - lazymatch goal with FR' : rw_cells asegs ?m2 (bv_unsigned sp + -208) _ |- _ =>
        eapply (setup_walk 1 welem m2); [left; clear - HWE KW; lia | | | exact MU | exact WM | | | | exact OTL | exact FR'] end;
        assumption.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L11401030561.115L1316427937.115 L27951960317.115L3229129457.115 L56527267681.115L63432074286.115L64599781253.11500000a01R02C03403e04g05XS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZE2ET3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZT2TT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZN2NT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZA2AT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZX2XT3SPRS2ra2sp1X1A1N2an1E2en2RR1T2xs2ys2ns2es2rs2ts2LX2LA2LN2LE2LR2LT3SPRS2ra2sp1X1A1N1E2RR1T2xs2ys2ns2es2rs2ts3NZR2RT3SPR". (* [comment removed for export] *)
Theorem A_mpi_core_exp_mod_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_exp_mod ()) "PR,$42.PHIA,(43.$5.R1.)P,(44.(<.R2.))P,(8.$0.(45.R3.)$2?.)P,(8.$0.(46.R4.)$2<.)P,(?.=(47.R5.))(48.$5.R6.R5.$49.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS AMC NEED0. pose proof (A_mpi_core_montmul_spec R HIA IMG AMS NEED0) as MM.
  unfold mpi_core_exp_mod_stmtA, A_MPI_CORE_EXP_MOD.
  intros until ts. intros HH PRE LOS SLO TOP CWX CWT OX OA ON OE OR OT T47 -> -> -> -> -> -> -> ->.
  unfold mpi_core_exp_mod_pre, MPI_CORE_EXP_MOD_STACK in PRE. expmod_pre PRE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  eapply main_walk with (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (ln := Z.of_nat (length ns)) (le_ := Z.of_nat (length es))
                         (lr := Z.of_nat (length rs)) (lt := Z.of_nat (length ts)) (ys := ys) (ns := ns) (es := es) (rs := rs);
    try eassumption; try reflexivity; try (apply lock; assumption); try lia.
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
