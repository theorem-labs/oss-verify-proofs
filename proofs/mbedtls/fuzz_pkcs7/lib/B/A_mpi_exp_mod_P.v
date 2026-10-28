(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_frame_lib A_frame_kit A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_stmtA_sz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_exp_mod_lib.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_cmp_mpi.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_exp_mod_P () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "WEM.EM_POISON"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_exp_mod_lib.snapA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "WEM.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_EXP_MOD"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"].


From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([658888]).
Local Ltac zchk_new ::= constr:([657484; 657488; 657512; 657516; 657520; 657608; 657612; 657616; 657844; 657848; 658272; 658276; 658280; 658676; 658680; 658684; 658740; 658744; 658748]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac zstep_to L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).
Section WEM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dX : mpd) (A E N lo slo : Z).
  Local Notation X := (md_addr dX).
  Local Notation KEEP := (mpd_keep LB dX).
  Local Notation WX := [(X, X + 16)].
  (* [comment removed for export] *)
  Hypothesis SSMAP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_P ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pg,$6.P,(7.$1.VR,VHIA,R5.R4.R3.R2.)P,(8.(9.(:.VR,)R2.)(;.R2.(<.$1.VR,VHIA,R6.)))(=.(>.(5.(4.&8.))A1.R4.(?.(10.(11.VR,)R3.))(12.(4.&8.))))")
(* [comment removed for export] *).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 1088 - arl_need_ecp R.
  Hypothesis NEEDE : 0 <= arl_need_ecp R.
  Hypothesis SSL : arl_stklo R <= slo.
  Hypothesis SLL : slo <= lo.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation SBw := (Z_to_bv 64 (al_sb AL)).
  (* [comment removed for export] *)
  Definition EM_POISON : list cell := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_P ()) "(13.$14.(15.(16.&8.+?1.))(13.$14.(15.(16.&8.+?1.))(13.$14.(15.(16.&8.+?1.))(13.$14.(15.(16.&8.+?1.))(13.$14.(15.(16.&8.+?8.))(13.$14.(15.(16.&8.+?2.))(13.$14.(15.(16.&8.+?8.))(13.$14.(15.(16.&8.+?2.))(13.$14.(15.(16.&8.+?8.))(13.$14.(15.(16.&8.+?8.))(13.$14.(15.(16.&8.+?3.))(13.$14.(15.(16.&8.+?3.))(17.$14.)))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition S1P : Z -> machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_P ()) "Lc,$6.Lms,$18.(19.$6.Lsp1,$6.(19.P,(4.&40.)(5.(4.&8.))Lm1,P,(4.&40.)(5.(4.&8.))(19.(4.&40.)Lt0,(4.&40.)(19.(4.&40.)Lt1,(4.&40.)(19.(4.&40.)Lt2,(4.&40.)(19.(4.&40.)La1,(4.&40.)(19.(4.&40.)La2,(4.&40.)(19.(4.&40.)La3,(4.&40.)(19.(4.&40.)La4,(4.&40.)(19.(4.&40.)La5,(4.&40.)(19.(4.&40.)La6,(4.&40.)(19.(4.&40.)La7,(4.&40.)(19.(4.&40.)Lt3,(4.&40.)(19.(4.&40.)Lt4,(4.&40.)(19.(4.&40.)Lt5,(4.&40.)(19.(4.&40.)Lt6,(4.&40.)(19.(2.(4.&40.))Lsl,(2.(4.&40.))(8.(>.$18.R12.(1:.(1;.(16.&40.+:083<.)(16.&40.R11.)Vgp,Vtp,R?.R>.R=.Vsp,(16.&40.=)(16.&40.R13.)R<.R;.R:.R9.R8.R7.R6.(16.&40.VN,)(16.&40.(1=.VdX,))(16.&40.VE,)(16.&40.VA,)(16.&40.-4.)(16.&40.=)(16.&40.(1<.(1?.(1<.R11.+60.)+3.)(1>.(11.VR,))))(16.&40.(1>.(11.VR,)))Vs10,Vs11,R5.R4.R3.R2.)VF,(16.&40.+:0844.)Vfc,(12.(4.&40.))R10.(20.$1.)))(8.(8.(9.(21.(22.&40.Vsp,)+150.)R11.)(9.R11.(21.(22.&40.Vsp,)+140.)))(8.(>.$6.(23.R11.+20.)=)(8.(7.$1.VR,VHIA,Vh,VLB,VLF,R10.)(8.(24.$1.R10.(1<.(22.&40.Vsp,)-68.)(13.$14.(25.Vs11,)(13.$14.(25.Vs10,)(13.$14.(25.Vs9,)(13.$14.(25.Vs8,)(13.$14.(25.Vs7,)(13.$14.(25.Vs6,)(13.$14.(25.Vs5,)(13.$14.(25.Vs4,)(13.$14.(25.Vs3,)(13.$14.(25.Vs2,)(13.$14.(25.Vs1,)(13.$14.(25.Vs0,)(13.$14.(25.Vra,)(17.$14.)))))))))))))))(8.(24.$1.R10.R11.(26.(4.&40.)$14.$25.R1.))(8.(>.$27.(28.(4.&40.)R1.)#1;.)(8.(29.$1.R10.(1<.R11.+=8.)(1<.(22.&40.Vsp,)-68.))(8.(29.$1.R10.Vlo,R11.)(8.(2:.$1.R10.)(8.(24.$1.R10.(1<.(1?.(1<.R11.+60.)+3.)(1>.(11.VR,)))$2;.)(8.(2<.$1.(11.VR,)R10.Vslo,(1<.R11.+60.))(8.(2<.$1.(11.VR,)R10.(1<.R11.+<0.)(22.&40.Vsp,))(8.(2=.$1.(11.VR,)Vm,R10.(:.VR,)(1<.R11.+60.))(8.(2=.$1.(11.VR,)Vm,R10.(1<.R11.+<0.)(22.&40.Vsp,))(8.(2>.$1.VR,VHIA,Vh,(2?.VLB,VdX,)VLF,(22.&40.Vsp,)(22.&40.Vsp,)(13.(30.$6.$6.)(31.$6.$6.(1=.VdX,)(1<.(1=.VdX,)+10.))(17.(30.$6.$6.)))Vm,R10.)(8.(32.(13.(30.$6.$6.)(31.$6.$6.Vlo,(22.&40.Vsp,))(13.(30.$6.$6.)(31.$6.$6.(1<.(1?.(1<.R11.+60.)+3.)(1>.(11.VR,)))(1<.(1<.(1?.(1<.R11.+60.)+3.)(1>.(11.VR,)))+<.))(17.(30.$6.$6.))))Vm,R10.)(33.$1.Vm,R10.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac cb8_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0350?D21667997106.89D35881667587.79D60189065437.89D65022331823.79L11131282904.76L12534749812.76L14055515366.75L14587988929.1 L1685717371.0  L18103702228.7 L21175043622.85L22530438548.3 L22736835928.76L23460203916.81L24023900370.0 L24584308084.76L25059345240.76L26314836056.76L26892418956.1 L27715613016.1 L28638398040.76L29428324939.5 L30595109876.76L32238087037.9 L33102925428.76L34453352390.3 L35653441506.7 L3569733545.3  L36622278772.76L36681741528.76L39130504436.76L39188636933.0 L40241890778.80L40244017112.76L40480035308.88L40622469209.2 L40834179097.83L41041959128.76L42411609006.0 L42630987508.76L43059266230.73L4424387092.75 L44603186136.76L45140830580.76L4666075286.1  L48658680692.76L50794956004.6 L51166431220.76L51655746932.2 L54672103924.76L57177756788.76L57413683421.93L57698627611.2 L58551761240.76L60098763854.3 L62018535662.1 L62109842520.76L62562328496.3 L62821685255.1 L63207547636.76L65572301272.76L66151427842.16L66269521432.88L6825927497.1  L7538573601.8  L7552230104.76 L9356559645.11 P37490721692.91P37492742104.91P43689334157.91P43691311561.91P57713046236.89Q10147393908.91Q10149569840.91Q10149575540.89Q10726261075.76Q11757758971.86Q11801279589.79Q11801279589.89Q15024872340.85Q15502880854.91Q15504892946.91Q15643324129.75Q18365925601.75Q18378753154.75Q18499383316.87Q18694146040.82Q19688736493.86Q20000941555.85Q20414270560.91Q20414272036.89Q20416550948.91Q21798041355.82Q21879645826.75Q22379711172.87Q22712450012.79Q23927705296.79Q23927705296.89Q24389563138.75Q25157988860.82Q25513505925.78Q25662358575.82Q27396422417.87Q27584944865.75Q27882953602.89Q27907200258.75Q27998746771.91Q28000660695.91Q28090132756.85Q28465177121.86Q28543176866.91Q28545156326.91Q29505479905.75Q30415036802.75Q31228709292.82Q31271525473.75Q31394594844.82Q32655500769.75Q33918256002.75Q3421936230.88 Q34347029405.90Q34966617690.89Q35014437530.82Q35717497884.82Q36425882626.75Q3830427394.75 Q39180574961.89Q39939554818.75Q40132823728.87Q40147765765.87Q41152393185.75Q41299363641.85Q42439443119.79Q42439443119.89Q42439449835.91Q42441394351.91Q44648843873.75Q44899125339.88Q4533518817.75 Q47434648660.87Q48117819567.91Q48119774443.91Q49513223883.88Q49698585326.77Q51087705995.89Q51235796833.75Q5129158642.89 Q52019411593.85Q52101170785.75Q52567672702.87Q5265442331.87 Q52724285538.78Q53100544631.85Q53969758199.82Q54485784450.75Q54487832473.90Q55415036769.89Q57035343601.91Q57037327601.89Q57037329077.91Q57228775306.88Q58019850249.85Q58125335435.89Q59256763233.75Q59564297647.91Q59566316011.91Q59582104523.91Q59584026511.91Q59843137889.75Q59865321072.79Q59865321072.89Q59865321524.91Q59867563120.91Q60511257090.75Q60755250508.91Q60757203208.91Q6186103236.89 Q62011970312.79Q62011970312.89Q62162878084.87Q6401106330.91 Q6403388894.91 Q64041402609.89Q64041668206.85Q6416456232.82 Q64255486968.82Q64681458566.91Q64683667394.91Q64683667846.79Q64683667846.89Q66522067074.75Q67182587492.87Q67528989526.79Q67933367285.87Q68358944923.79Q8576240156.89 Q9843367298.75 00000`01h02_04204604:04>04C04D04_05405@05D05P05Q05U05Y05]05a05f05j06<06@06c06g07307K07W07[07_07c07d07l08008:08A08K08O08P08T08k09N09R09V09[09_0:60::0:>0:B0:F0;L0;M0;Q0;[0;^0;b0;n0<20<60<:0<V0<`0<e0=D0=H0>30>M0>g0?@0?Y0@40@P0@l0AF0AM0Aa0Ab0Ac0B20BY0C@0CG0CN0Ca0Cf0Cm0DK0DZ0E60E`0F<0F=0FP0FU0GQ0H^0IJ0I]0Id0Jc0Jd0Ji0K00K10KD0K]0L60LE0LR0Lo0ML0MS0Mf0Mo0N60N70N>0NQ0No0OK0P50P>0P?0PR0Pe0QW0Qj0Qo0R40R;0RJ0SP0Sn0TL0Tj0U10U;0UB0UG0V50Vc0Vm0W>0WR0WY0WZ0X50X<0XA0XO0YZ0Z50Z>0ZQ0[70[R0\<0\f0]P0^:0^U0^i0_00_F0_\0`20`H0`O0`P0`Q0`R0`S0`f0aX0bJ0bh0cf0d<0dA0dB0dC0dm0eH0eO0eP0f@0g00hA0i10iD0iI0jT0jY0kl0lL0l_S1R3HIA1h2sp3TOP3sp13SPR3SP14SP1R2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp3TOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R2sp2lo3LOS3SLO5NEEDE3sp13SPR3SP14SP1R2HB5Ha_st5Hl_stS1R2ra2sp2lo3LOS3SLO5NEEDE3SPR2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S2spS2spS2spS3sp1SS1R2sp2lo3SLO5NEEDE3sp13SP1S2sp3sp13SPR3SP14SP1RS2sp3sp13SP1S2spS2sp3sp13SP1SS2spS2spS2spS2spS3sp1S2spS1R2lo3LOS3ALO3ACPS2spS1R2sp2lo3slo3SLO5NEEDE3SLL3sp13SP1S2spS2sp3sp13SP1S1R3HIA1h2sp2lo3TOP4HTOPS2sp3SPA3SPRS2spS2spS2spSS2sp3sp1S2spS1R2sp3sp1S1R3sp1S1R2sp3sp1S2spSS2spS1R2sp2lo3SLO5NEEDE3SPRS1R2sp2lo3LOS3SLO5NEEDE3ALO3ACV3SPRS2spS2spS3sp1S2spS1R2sp2lo3LOS3SLO5NEEDES2spS2spS2spS2spS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SPR3SP14SP1R2HB5Ha_st5Hl_st1x2HxFS2spS1R2lo3LOSS1RS2spS2sp3sp13SP1S2spS2spS2spS3sp12r04SP1M1q1r1H2H02q02H4S1R2sp3sp1S3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp13SP1S2spS1R2sp2lo3LOS3SLO5NEEDE3ALO3ACV3SPR3sp13SP1S1R3slo3sp12HB5Ha_st5Hl_stS1R3slo3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS2sp2lo3sp12HB5Ha_st5Hl_stS2sp2HBS1R2sp2lo3sp13SP12HBFFS2sp2lo3sp13SP1S1R2sp3sp13SPR4SP1M4SP1R2HB5Ha_st5Hl_stS1R2sp3sp13SPR4SP1M4SP1R2HB5Ha_st5Hl_stS2sp2loS2sp2loS1R2sp2lo3SLO5NEEDES3sp1S1R3EHIS1R2sp2lo3SLO5NEEDE3sp13SP12HBS2sp2lo3sp13SP1S1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stFS1R2sp2lo3SLO5NEEDES3sp1S2ra2sp2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R3HIA1h2ra2sp3TOP4HTOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R3HIA1h2sp3TOP3sp14HTOP3SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDES1R3EHIS2ra2sp2lo2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11FS3sp1S2sp2loFS1R2sp2lo3SLO5NEEDES1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS2sp2lo3sp13SP1S3sp14SP1R2HBS1R2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp3sp13SP12HB5Ha_st5Hl_stS2sp2loS1R2sp2lo3SLO5NEEDES1R5ALWF'S2sp2loSS2sp2loS1R2sp2lo3SLO5NEEDES2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R5ALWF'FS1R2sp2lo3SLO5NEEDES1R2sp2lo3SLO5NEEDES1R2sp2lo3LOS3SLO5NEEDE3sp13ALO3SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDES3sp1S3sp1S2sp2loS2sp2lo3sp13SP1S1R2ra2sp3slo3SSL2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3slo3SSL3sp12HB5Ha_st5Hl_stS2sp2loS1R3sp12HBS2sp2loS3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS1R3sp12HBS2sp3SPR2HB5Ha_stS3sp12HB5Ha_st5Hl_stS2sp2loFS1R2sp2lo3SLO5NEEDE3sp13SP1S2sp2loS3sp1S3sp12HB5Ha_stS1R2ra2sp2lo3SLO5NEEDE2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R2sp2lo3SLO5NEEDE3sp13SP1S1R5ALWF'S1R2sp2lo3SLO5NEEDES1R2sp2lo3SLO5NEEDE3sp12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP1S3sp12HB5Ha_st5Hl_stS2sp2loS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS2sp2loFFFFS1R2sp2lo3SLO5NEEDES1R2sp2lo3LOS3SLO5NEEDE3sp13ALO3SP12HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13ALO3SP12HB5Ha_st5Hl_stS2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2ra2sp2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R3sp12HB5Ha_st5Hl_stS3sp1FFS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3ELOFS1R3HIA1h2sp3slo3TOP3sp14HTOP3SP12HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp14HTOP3SP12HB5Ha_st5Hl_stS1R3HIA1h2ra2sp3slo3TOP4HTOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R3HIA1h2sp3slo3TOP3sp14HTOP3SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDES3sp1S1R2ra2sp2lo3SLO5NEEDE2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S3sp1S1R2ra2sp2lo3LOS3SLO5NEEDE3ALO2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s82s93s103s11S1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE". (* [comment removed for export] *)
  #[using="IMG LOS SLO NEEDE SSL SLL TOP SPA"] Lemma em_pro : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_P ()) "PdN,$3:.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(7.$1.VR,VHIA,Vh,VLB,VLF,Vm,)P,(29.$1.Vm,Vlo,(22.&40.Vsp,))P,(2:.$1.Vm,)P,(2<.$1.(11.VR,)Vm,Vslo,(22.&40.Vsp,))P,(>.$6.(1=.R?.)VN,)P,(3?.$1.Vm,VLB,R10.)P,(43.(9.(1<.(1=.VdX,)+10.)(1=.R11.))(9.(1<.(1=.R11.)+10.)(1=.VdX,)))P,(53.VdX,R12.Vlo,(22.&40.Vsp,))P,(54.(55.VR,)(56.$3.VLB,(57.VLF,))Vlo,(1=.R13.)+10.)P,P,(>.$48.(49.R14.)$58.)(54.(55.VR,)(56.$3.VLB,(57.VLF,))Vlo,(4;.R15.)(4<.+4.(4=.R15.)))P,(59.$1.(11.VR,)(36.$1.VR,VHIA,Vh,)Vm,R15.)P,(5:.R16.)(35.$1.(11.VR,)(36.$1.VR,VHIA,Vh,)(37.(51.(52.R17.)))(1:.(1;.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(16.&40.(1=.VdX,))(16.&40.VA,)(16.&40.VE,)(16.&40.VN,)(16.&40.=)R13.R12.R11.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(16.&40.$38.)Vfc,(12.(4.&40.))Vm,(20.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH ST MI SS EN MN SXN OSN CRN CRNL ODN IMN. unfold A_MPI_EXP_MOD. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP. pose proof HH as HH0. pose proof MI as MI0.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (presW_init_at R HIA h LB LF KEEP LF m (bv_unsigned sp) (bv_unsigned sp) WX h HH ltac:(intros b Hb; eapply In_mpd_keep; exact Hb) ltac:(intros fb Hfb; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NEEDE; lia)) as PRES.
    pose proof (snapA_refl asegs AL m (arl_stklo R) (bv_unsigned sp)) as SNP.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    ddestruct IMG' as (EGOT & ELO & EHI).
    (* [comment removed for export] *)
    lazymatch goal with |- evtA ?sg ?al ?cs ?P (MS ?Rg ?FF ?pc ?fcc ?rv m ?ro) =>
      enough (G : forall mm, mm = m -> evtA sg al cs P (MS Rg FF pc fcc rv mm ro)) by exact (G m eq_refl) end.
    intros mm Emm. rewrite <- Emm in HH, ST, MI, SS. rewrite <- Emm in PRES at 2. rewrite <- Emm in SNP at 2. rewrite <- Emm in MU at 2. rewrite <- Emm in WM at 2. clear Emm.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep_to [657212].
    (* [comment removed for export] *)
    zstep_to [657216]. carve_frame 320%nat ST.
    zstep_to [657268].
    (* [comment removed for export] *)
    zstep_to [657272]. zstep_to [657300].
    align32 (bv_unsigned sp + -320) sp1.
    assert (SP1 : bv_unsigned sp - 336 <= sp1 <= bv_unsigned sp - 320) by (clear - Hsp1 SPA SPR; subst sp1; lia).
    assert (SP1M : sp1 mod 32 = 0) by (clear - Hsp1 SPR; subst sp1; lia).
    clear Hsp1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    apply (munch_weaken _ [(lo, bv_unsigned sp); (Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)]) in MU;
      [| intros x Hx; cbn [outside] in *; clear - Hx; tauto].
    (* [comment removed for export] *)
    zstep_to [657332].
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite EGOT in GOT.
    (* [comment removed for export] *)
    zstep_to [657336]. zstep_to [657340]. zstep_to [657344]. zstep_to [657348]. zstep_to [657352]. clear GOT GSB AB.
    (* [comment removed for export] *)
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -320) ST ltac:(clear - SP1 SLO NEEDE; lia)) as [ST1 ST2]. clear ST.
    chunk_split FR 1%nat FRa SAVE.
    replace (bv_unsigned sp + -320 + 216) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
    release_frame FRa ST2 (bv_unsigned sp + -104). rename ST2 into STJ.
    destruct (stk_split asegs m1 sp1 (sp1 + 216) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs m1 sp1 (sp1 + 216) 16 STlo ltac:(clear; lia)) as [STa [jY SPY]].
    replace (sp1 + 216 - Z.of_nat 16) with (sp1 + 200) in STa, SPY by (clear; lia). clear STlo.
    apply (rw_cells_split_CB asegs m1 (sp1 + 200) [] 16 jY [] [8; 4; 4]%nat) in SPY; [| reflexivity]. cbn [mk_CB_cells app] in SPY.
    destruct (stk_carve asegs m1 sp1 (sp1 + 200) 48 STa ltac:(clear; lia)) as [STb [jM SPM]].
    replace (sp1 + 200 - Z.of_nat 48) with (sp1 + 152) in STb, SPM by (clear; lia). clear STa.
    apply (rw_cells_split_CB asegs m1 (sp1 + 152) [] 48 jM [] [8; 8; 8; 8; 8; 8]%nat) in SPM; [| reflexivity]. cbn [mk_CB_cells app] in SPM.
    destruct (stk_carve asegs m1 sp1 (sp1 + 152) 8 STb ltac:(clear; lia)) as [STc [jL SPL]].
    replace (sp1 + 152 - Z.of_nat 8) with (sp1 + 144) in STc, SPL by (clear; lia). clear STb.
    apply (rw_cells_split_CB asegs m1 (sp1 + 144) [] 8 jL [] [4; 4]%nat) in SPL; [| reflexivity]. cbn [mk_CB_cells app] in SPL.
    destruct (stk_carve asegs m1 sp1 (sp1 + 144) 144 STc ltac:(clear; lia)) as [STd [jslot SPILL]].
    replace (sp1 + 144 - Z.of_nat 144) with sp1 in STd, SPILL by (clear; lia). clear STc STd.
    apply (rw_cells_split_CB asegs m1 sp1 [] 144 jslot [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in SPILL; [| reflexivity].
    cbn [mk_CB_cells app] in SPILL.
    (* [comment removed for export] *)
    destruct (sshad_split asegs AL m1 slo (sp1 + 96) (bv_unsigned sp) SS ltac:(clear - SP1 SLO NEEDE SLL; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SSr].
    destruct (sshad_split asegs AL m1 (sp1 + 96) (sp1 + 192) (bv_unsigned sp) SSr ltac:(clear - SP1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSmid SShi].
    pose proof (sshad_chunk asegs AL m1 (sp1 + 96) (sp1 + 192) 11 (sp1 + 96) SSmid ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as SHC.
    clear SS SSr SSmid.
    pose proof (snapA_sub asegs AL m m1 _ _ (arl_stklo R) (sp1 + 96) SNP ltac:(clear; lia) ltac:(clear - SP1; lia)) as SNlo.
    pose proof (snapA_sub asegs AL m m1 _ _ (sp1 + 192) (bv_unsigned sp) SNP ltac:(clear - SP1 SLO NEEDE LOS; lia) ltac:(clear; lia)) as SNhi.
    clear SNP. unfold shadow_of in SHC. cbn [zcells] in SHC.
    replace (al_sb AL + (sp1 + 96) / 8) with (Z.shiftr (sp1 + 96) 3 + al_sb AL) in SHC by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
    (* [comment removed for export] *)
    zstep_to [657464].
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into mq end.
    norm_b8 SHC.
    dpose OSN as (OS1 & OS2 & OS3 & OS4 & OS5).
    pose proof (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES) as HPA. pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HPA) as HPX.
    assert (CRk : client_range L (KEEP ++ fdata LF) (bv_unsigned sp) (md_addr dN) 16).
    { pose proof (client_range_keep L LB LF lo dX (md_addr dN) 16 CRN OS2) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; clear - S Ha OS4; lia| right; left; exact D| right; right; exact B]. }
    assert (CRLk : md_own dN = LHeap -> client_range L (KEEP ++ fdata LF) (bv_unsigned sp) (md_p dN) (4 * md_n dN)).
    { intros EH. assert (NN : md_own dN <> LNull) by (rewrite EH; discriminate).
      assert (AP : md_own dX = LHeap -> md_p dN + 4 * md_n dN <= md_p dX \/ md_p dX + 4 * md_n dX <= md_p dN).
      { intros EX. destruct OS3 as [C|[C|[C|C]]]; [exfalso; subst dN; clear - SXN; lia| exfalso; exact (C EX)| exfalso; exact (NN C)| clear - C; lia]. }
      pose proof (client_range_keep L LB LF lo dX (md_p dN) (4 * md_n dN) (CRNL EH) AP) as C0.
      intros a Ha. destruct (C0 a Ha) as [S|[D|B]]; [left; pose proof (OS5 NN) as Q; clear - S Ha Q; lia| right; left; exact D| right; right; exact B]. }
    set (LBy := (sp1 + 144, 4) :: LB).
    assert (MDq : mpd_at asegs mq LBy dN).
    { eapply (mpd_at_heap_presx asegs L m mq LB (KEEP ++ fdata LF) LBy (bv_unsigned sp) WX dN); [exact MN| exact HPX| exact MI0| exact MI| exact CRk| exact CRLk| | | ].
      - cbn [disjoint_from]. split; [clear - SXN; lia| exact I].
      - intros EH. cbn [disjoint_from]. split; [pose proof (OS1 ltac:(rewrite EH; discriminate)) as Q; clear - Q; lia| exact I].
      - intros b Hb. right. pose proof MN as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own dN); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)). }
    assert (PNZ : md_own dN = LHeap -> 0 < md_p dN).
    { intros EH. pose proof MN as [(_ & _ & _ & _ & _ & OW) _]. rewrite EH in OW. ddestruct OW as (_ & HIN & _).
      pose proof (hm_blocks_low asegs R HIA h LB LF m HH0 (md_p dN) (4 * md_n dN) ltac:(apply in_or_app; left; exact HIN)) as BL.
      destruct (hm_apart asegs R HIA h LB LF m HH0) as [HF _]. rewrite Forall_forall in HF. destruct (HF _ ltac:(apply in_or_app; left; exact HIN)) as (P0 & _). cbn in P0. exact P0. }
    assert (OSq : aobj asegs AL CS mq (md_addr dN) 16).
    { eapply (presA_aobj asegs R CS); [exact CSOK| exact HPA| exact (proj1 ODN)| exact CRk| clear; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    assert (IMGCS : img_cs CS).
    { eapply img_cs_of; [exact ELO| exact (proj1 EHI)| exact EGOT| exact (proj2 EHI)|]. intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA h); assumption. }
    assert (OPq : 1 <= md_n dN -> aobj asegs AL CS mq (md_p dN) (4 * md_n dN)).
    { intros N1. pose proof MN as [(_ & _ & _ & _ & _ & OW) _].
      destruct (md_own dN) eqn:EOD; [exfalso; destruct OW as (_ & N0); clear - N0 N1; lia| |].
      - ddestruct OW as (_ & EIN & _). eapply hm_aobj_block; [exact HH| exact EIN].
      - eapply (AImgGlobals.aobj_img asegs AL); [exact IMGCS| eapply (hm_img_shadow asegs R HIA); exact HH| exact (IMN EOD)]. }
    assert (OYq : aobj asegs AL CS mq (sp1 + 200) 16).
    { pose proof (sshad_chunk asegs AL mq (sp1 + 192) (bv_unsigned sp) 1 (sp1 + 200) SShi ltac:(clear; lia) ltac:(clear - SP1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as SH.
      replace (shadow_of AL (sp1 + 200)) with (Z.shiftr (sp1 + 200) 3 + al_sb AL) in SH by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
      change 16 with (8 * Z.of_nat 2).
      eapply (aobj_of_zero_shadow_sh asegs AL CS mq (sp1 + 200) (zcells 2) (sp1 + 200) 0 2 CSOK SH); [eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia| clear; lia|].
      intros i Hi. apply cell_at_zcells. exact Hi. }
    assert (OQq : aobj asegs AL CS mq (sp1 + 144) 4).
    { assert (HB : (sp1 + 96) mod 8 = 0) by (clear - SP1M; Z.div_mod_to_equations; lia).
      lazymatch type of SHC with rw_cells _ _ _ ?cs => assert (HZ : cell_at cs 6 = Some (C1 (Z_to_bv 8 4))) by reflexivity end.
      pose proof SHC as H.
      replace (Z.shiftr (sp1 + 96) 3 + al_sb AL) with (shadow_of AL (sp1 + 96)) in H by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia).
      assert (HC : crange CS (sp1 + 144) 4) by (eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]).
      split; [exact HC|].
      intros a Ha. exists (Z_to_bv 8 4). split.
      - pose proof CSOK as OK. destruct OK as [C1' _]. destruct (C1' a (HC a Ha)) as (R0 & R1 & R2 & _).
        pose proof (rw_cells_read asegs mq _ _ 6 _ H HZ) as RD. cbn [csize cbytes] in RD.
        assert (ESA : shadow_of AL a = shadow_of AL (sp1 + 96) + Z.of_nat 6).
        { unfold shadow_of.
          assert (E8 : a / 8 = (sp1 + 96) / 8 + Z.of_nat 6); [| rewrite E8; lia].
          pose proof (Z.div_mod (sp1 + 96) 8 ltac:(lia)) as DB. rewrite HB in DB.
          symmetry. apply (Z.div_unique a 8 ((sp1 + 96) / 8 + Z.of_nat 6) (a - (sp1 + 96) - 8 * Z.of_nat 6)); lia. }
        rewrite ESA. apply (bytes_at_of_read1 asegs); [lia| lia| exact RD].
      - right. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite (Z.mod_small 4) by lia.
        pose proof (Z.div_mod (sp1 + 96) 8 ltac:(lia)) as DB. rewrite HB in DB.
        assert (EM : a mod 8 = a - (sp1 + 96) - 8 * Z.of_nat 6).
        { symmetry. apply (Z.mod_unique a 8 ((sp1 + 96) / 8 + Z.of_nat 6) (a - (sp1 + 96) - 8 * Z.of_nat 6)); lia. }
        rewrite EM. lia. }
    pose proof (proj1 (proj1 (rw_cells_app asegs mq (sp1 + 144) [C4 (Z_to_bv 64 0)] _) SPL)) as SPL0.
    lazymatch type of SPY with rw_cells _ _ _ [_; _; CB 4 ?pb] => set (padb := pb) in SPY end.
    assert (LPB : length padb = 4%nat) by (destruct SPY as [[WF _] _]; exact (proj1 (proj2 (proj2 WF)))).
    set (dY := mkMPD (sp1 + 200) 1 1 (sp1 + 144) [Z_to_bv 64 0] (le_bytes_to_word padb) LHeap).
    assert (E4 : le4 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 1)).
    { rewrite le4_split. change (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) with 1. f_equal. rewrite !le2_of_Z. rewrite <- (CellsX.Z_to_le_bytes_mod 2 65537). reflexivity. }
    assert (MY : mpd_at asegs mq LBy dY).
    { unfold mpd_at, mpi_at, dY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length].
      split; [| left; reflexivity].
      split.
      { unfold mpi_cells. eapply rw_cells_reshape; [exact SPY| cbn; repeat split|].
        cbn [cells_bytes cbytes]. rewrite le4_le_bytes_to_word by exact LPB. rewrite E4, <- !app_assoc. reflexivity. }
      split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      split; [clear - SP1 SLO LOS ALO ACP NEEDE; lia|].
      split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia|].
      split; [clear; lia|]. split; [left; reflexivity|]. split; [clear - SP1M; Z.div_mod_to_equations; lia|].
      eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 0))); [eapply rw_cells_reshape; [exact SPL0| cbn; split; [apply (length_le4 (Z_to_bv 64 0))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (EVY : mpd_val dY = 0) by (unfold mpd_val, dY; cbn [md_sg md_limbs limbs_val]; reflexivity).
    pose proof (A_mpi_cmp_mpi.A_mpi_cmp_mpi_spec AL IMG) as CMPc. unfold A_mpi_cmp_mpi.mpi_cmp_mpi_stmtA in CMPc.
    eapply evtA_cut.
    { eapply (CMPc CS) with (LB := LBy) (dX := dN) (dY := dY) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MDq | exact MY | exact MI | exact CSOK | exact OSq | exact OPq | exact ST1 | exact PNZ | exact OYq | reflexivity
              | exact (art_alwf asegs R HIA)
              | exact (hm_abase asegs R HIA h LB LF mq HH)
              | (intros _; exact OQq)
              | (intros _; unfold dY; cbn [md_p]; clear - SP1 SLO LOS ALO ACP NEEDE; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1 NEEDE; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
              | (destruct OS4 as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (right; unfold dY; cbn [md_addr]; clear; lia)
              | (intros _; right; unfold dY; cbn [md_p]; clear; lia)
              | (intros N1; assert (NN : md_own dN <> LNull) by (intros E0; pose proof MN as [(_ & _ & _ & _ & _ & OW) _]; rewrite E0 in OW; destruct OW as [_ N0]; clear - N0 N1; lia);
                 destruct (OS5 NN) as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (rewrite EN; reflexivity)
              | match goal with |- ?g => idtac "CMPPRE-LEFT:" g end ]. }
    rewrite EVY, Z.sub_0_r.
    clear MDq MY OSq OPq OYq OQq SPL0 CMPc.
    cbv beta. intros ms3 PO. unfold A_mpi_cmp_mpi.mpi_cmp_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & -> & MU2 & WM2 & MI3 & ST3).
    rewrite ?(unsigned_lit sp1) in MU2, ST3 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 657468)) with (Z_to_bv 64 657468 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (WC : w_client CS [(lo, sp1)]).
    { unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    assert (DJ : forall b n, (b + n <= lo \/ sp1 <= b) -> disjoint_from [(lo, sp1)] b n) by (intros b n D; cbn [disjoint_from]; split; [clear - D; lia| exact I]).
    assert (HH3 : HM asegs R HIA h LB LF m3).
    { eapply (hm_munch asegs R HIA h LB LF _ mq m3); [exact HH| exact MU2| exact WM2|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. apply w_writable_of_client_wrange. apply client_wrange_stack; clear - LOS SP1 TOP SLO NEEDE; lia. }
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SAVE; [| exact MU2| exact WM2| apply DJ; right; clear - SP1; lia].
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SPILL; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SPL; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SPM; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SPY; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    apply (stk_transport_disjoint asegs [(lo, sp1)] mq m3 _ _) in SThi; [| exact MU2| exact WM2| apply DJ; right; clear; lia].
    apply (rw_cells_transport asegs [(lo, sp1)] mq m3 _ _) in SHC; [| exact MU2| exact WM2|].
    2: { apply DJ. simpl_sizes.
         destruct (apart_shadow_client AL CS lo (sp1 - lo) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOK) as [Q|Q];
           [eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]
           | eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]
           | unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia
           | clear - SP1 SLO NEEDE; lia| clear; lia| |];
           clear - Q; lia. }
    assert (SSlo3 : sshad asegs AL m3 slo (sp1 + 96)).
    { eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear - SSL; lia| clear - SP1 TOP HTOP; lia]| exact MU2| exact WM2| exact SSlo]. }
    assert (SShi3 : sshad asegs AL m3 (sp1 + 192) (bv_unsigned sp)).
    { eapply (sshad_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU2| exact WM2| exact SShi]. }
    assert (SNlo3 : snapA asegs AL m m3 (arl_stklo R) (sp1 + 96)).
    { eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS0| clear; lia| clear - SP1 TOP HTOP; lia]| exact MU2| exact WM2| exact SNlo]. }
    assert (SNhi3 : snapA asegs AL m m3 (sp1 + 192) (bv_unsigned sp)).
    { eapply (snapA_munch asegs AL CS); [exact CSOK| exact WC| eapply crange_sub; [exact SCS| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]| exact MU2| exact WM2| exact SNhi]. }
    assert (PRES3 : presW asegs R HIA h KEEP LF (bv_unsigned sp) (bv_unsigned sp) WX m m3).
    { eapply (presW_munch asegs R HIA h); [exact PRES| exact MU2| exact WM2| exact WC|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. eapply (wcover_of_stack asegs R HIA h); [exact PRES| clear - LOS ALO; lia| clear - SP1; lia]. }
    assert (MU3 : munch [(lo, bv_unsigned sp); (Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)] m m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx; cbn [outside] in *; clear - Hx SP1; lia. }
    assert (WM3 : wmono asegs m m3) by (eapply wmono_trans; [exact WM| exact WM2]).
    clear HH MI ST1 SSlo SShi SNlo SNhi PRES MU WM MU2 WM2 WC DJ HPA HPX CRk CRLk.
    rename HH3 into HH, MI3 into MI, ST3 into ST1, SSlo3 into SSlo, SShi3 into SShi, SNlo3 into SNlo, SNhi3 into SNhi, PRES3 into PRES, MU3 into MU, WM3 into WM.
    zstep_to [657476].
    norm_b8 SHC.
    cb8_all SPILL. cb8_all SPM.
    apply (rw_cells_merge asegs _ _ [] [C4 (Z_to_bv 64 0); _] []) in SPL. cbn [app cells_size csize cells_bytes cbytes Nat.add] in SPL. cb8_all SPL.
    apply (rw_cells_merge asegs _ _ [_] [C4 (Z_to_bv 64 65537); _] []) in SPY. cbn [app cells_size csize cells_bytes cbytes Nat.add] in SPY. cb8_all SPY.
    pose proof (proj2 (rw_cells_app asegs _ sp1 _ _) (conj SPILL SPL)) as J1.
    pose proof (proj2 (rw_cells_app asegs _ sp1 _ _) (conj J1 SPM)) as J2.
    pose proof (proj2 (rw_cells_app asegs _ sp1 _ _) (conj J2 SPY)) as J3.
    cbn [app] in J3. clear J1 J2.
    apply evtA_done. unfold S1P.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists sp1, mx end.
    deexists 14.
    lazymatch type of J3 with rw_cells _ _ _ ?cs =>
      let ws := eval cbv beta iota delta [map] in (map (fun c => match c with C8 w => w | _ => Z_to_bv 64 0 end) cs) in exists ws end.
    split; [reflexivity|].
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact HH|].
    split; [exact SAVE|]. split; [exact J3|]. split; [reflexivity|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|].
    split; [exact SHC|]. split; [exact SSlo|]. split; [exact SShi|]. split; [exact SNlo|]. split; [exact SNhi|].
    split; [exact PRES|]. split; [exact MU| exact WM].
    all: match goal with |- ?g => idtac "PRO-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02M0@D3953997537.150 D60189065437.150L10378449024.2  L122855816.7    L1499716355.7   L1685717371.0   L18546069956.14 L22163852504.149L22530438548.3  L22972055896.149L24023900370.0  L254112248.9    L25741856728.149L29038974481.4  L29428324939.5  L29916034296.2  L31421052760.149L32238087037.9  L33232266840.149L34987518552.149L35653441506.7  L38948636245.0  L39188636933.0  L39332637397.0  L39565290688.1  L40093199506.1  L40480035308.149L40622469209.2  L42411609006.0  L42842486707.149L44245343745.7  L4613898543.9   L46388033089.1  L48958709976.149L52536714200.149L57408231128.149L57698627611.2  L5832837669.4   L60098763854.3  L60968405464.149L62821685255.1  L64052154934.7  L64900869464.149L66151427842.16 L66269521432.149L68463140952.149L7142300770.4   L8171953640.154 L9356559676.11  P37490721692.153P37492742104.153P43689334157.153P43691311561.153P57713046236.150Q10147393908.153Q10149569840.153Q10149575540.150Q10551319914.149Q11745175875.153Q11747458311.153Q11757758971.148Q11801279589.150Q15502880854.153Q15504892946.153Q15576119657.149Q16845279210.149Q18499383316.149Q19684542037.153Q19686527505.153Q19688736493.148Q20013594135.146Q21585342441.149Q22379711172.149Q23692537450.149Q23927705296.150Q25073575915.153Q25075822059.150Q25075823535.153Q26708728554.149Q27396422417.149Q27613060201.149Q27882953602.150Q27998746771.153Q28000660695.153Q28465177121.147Q28543176866.153Q28545156326.153Q30002764010.149Q30120763625.149Q3419689062.150 Q3421936230.149 Q34347029405.152Q3466069098.149 Q34966617690.151Q3539691113.149 Q36131575145.149Q39180574961.150Q40132823728.149Q40147765765.149Q40334656362.149Q41299363641.147Q42158767081.149Q42439443119.150Q42439449835.153Q42441394351.153Q44899125339.150Q45659743721.149Q4689296618.149 Q47434648660.149Q48117819567.153Q48119774443.153Q49513223883.150Q51087705995.150Q5129158642.150 Q51685755497.149Q52567672702.149Q5265442331.148 Q53100544631.147Q54195183337.149Q54487832473.152Q55415036769.150Q57035343601.153Q57037327601.150Q57037329077.153Q57228775306.149Q57230951818.150Q58125335435.150Q59564297647.153Q59566316011.153Q59582104523.153Q59584026511.153Q59865321072.150Q59865321524.153Q59867563120.153Q60221178729.149Q60268061674.149Q60755250508.153Q60757203208.153Q6186103236.150 Q62011970312.150Q62162878084.149Q62336919914.149Q63562097130.149Q6401106330.153 Q6403388894.153 Q64041402609.150Q64054320522.146Q64681458566.153Q64683667394.153Q64683667846.150Q64960112362.149Q66232119785.149Q67182587492.149Q6775323242.149 Q67933367285.149Q8576240156.151 Q9548403945.149 00000g01^01h02C02^02_03R03Z03f03n03o04Q04Y04e05705?05G05j06206:06R06S06T06U06Y06^06h06o07007807K07n08308;08C08K08L08[08e08m09109L09T0:00::0:B0:O0;\0<G0<a0=;0=T0=m0>H0>d0?@0?Z0?^0@>0@^0A20A30AZ0BA0BE0BI0BN0C80Cb0D@0DO0DS0DX0D\0EH0E^0F40FJ0FN0FS0FW0FX0G10GJ0GW0H40HQ0HU0HY0I70IU0J10J50J_0Jc0Jg0KY0K^0Kc0Kg0L60L:0LX0M60MT0M^0Mb0Mf0Mk0NY0OG0OQ0Oe0Of0Oj0Oo0P=0PX0P\0QB0Q]0RG0S10S[0TE0To0UC0UY0Uo0VE0V[0V\0V]0V^0Vb0Vf0WX0XJ0Xh0Y>0YC0YG0YK0YL0YM0Z70ZR0[B0\20\b0\f0\j0\o0]30]80]X0]\S1R3HIA1h2sp3TOP3sp12hc3SP13HTc3SPR4SP1R2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13SPR4SP1R2HB5Ha_st5Hl_stS3sp14SP1RS1R2sp2lo3SLO5NEEDE3sp13SP1S1R2sp2lo3SLO5NEEDE3sp13SP1SS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp13SP14HTOP1c2HcS2sp3sp1S2sp3sp13SP1S2sp3sp1SS1R2sp2dX2lo3SLO5NEEDE3sp13SP13DSXS2sp3sp1S1R2dX3sp11QS1R2lo3LOS3ALO3ACPS3dXc2NPS2sp3sp1S1R2sp2lo3slo3SLO5NEEDE3SLL3sp13SP1S2sp3sp1S2sp3sp1S1R3HIA1h2sp2lo3TOP4HTOPSSSS2spS3sp1S1R2sp3sp1S1R3sp1SS2sp3sp1S1R2sp2lo3SLO5NEEDES1R2sp2lo3SLO5NEEDE3sp13dXc3SP13DSPS3sp1S2sp3sp1S2sp3sp1S2sp3sp1FS2sp2lo3sp13SP1S1R2lo3LOSS2sp3sp1S2spS1R2sp2lo3SLO5NEEDE3sp13SP1S2sp3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R2sp3sp1S2sp3sp1S1R3sp13dXc1QS1R3HIA1h2sp2lo3LOS3SLO5NEEDE3TOP3sp12hc3SP13HTc3SPR4SP1R2HB5Ha_st5Hl_st1x2HxS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO3ACV3SPRS1R3slo3sp12HB5Ha_st5Hl_stS1R3slo3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS2sp2lo3sp12HB5Ha_st5Hl_stS2spS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp13SP12HBFS1R2sp3sp14SP1M3SPR4SP1R2HB5Ha_st5Hl_stS1R2sp3sp14SP1M3SPR4SP1R2HB5Ha_st5Hl_stS2spS2spS3sp1S1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HBS2sp2lo3sp13SP1S2spS3sp1S2spS1R3HIA1h2sp3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS2spS3sp1S2spFS1R2sp3sp12HB5Ha_st5Hl_stS1R2sp3sp12HB5Ha_st5Hl_stS3sp14SP1R2HBS1R2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp3sp13SP12HB5Ha_st5Hl_stS2spS2spS2sp2lo3sp13SP12HB5Ha_st5Hl_stS2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3sp12HB5Ha_st5Hl_stS2spS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS2spS2spS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS3sp1S3sp1S2spS2sp2lo3sp13SP1S2spS1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3slo3SSL3sp12HB5Ha_st5Hl_stS1R3sp12HBS2spS2spS3sp1S1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13ALO2HB5Ha_st5Hl_stS1R3sp12HBS3sp12HB5Ha_st5Hl_stFS2spS3sp1S3sp12HB5Ha_stS1R2sp2lo3SLO5NEEDE3sp13SP1S2spS1R2sp2lo3SLO5NEEDE3sp12HB5Ha_st5Hl_stS2sp3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stFFFS2spS2spS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS1R2sp2lo3LOS3SLO5NEEDE3sp13SP13ALO2HB5Ha_st5Hl_stS2sp2lo3sp13SP12HB5Ha_st5Hl_stS1R3sp12HB5Ha_st5Hl_stS3sp1S2spS2spFFS1R2sp2lo3SLO5NEEDE3sp13SP12HB5Ha_st5Hl_stS1R2sp2lo3SLO5NEEDE3sp13SP1S1R3HIA1h2sp3slo3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp3slo3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS2spS2spS3sp1S2spS3sp1S1R2sp2lo3sp13SP12HB5Ha_st5Hl_stS2sp". (* [comment removed for export] *)
  #[using="IMG SSMAP LOS SLO NEEDE SSL SLL TOP"] Lemma em_epi : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_P ()) "Pmo,$39.PRr,P,$6.P,$3:.SpPPHI,$6.PFR,$6.Psp1,$6.Pmc,P,(4.&40.)(5.(4.&8.))Phc,(0.$1.VR,VHIA,)PLBc,(2.$3.)PdXc,$3:.Pr,$6.Psl,(2.(4.&40.))Pxra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pxs1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pxs2,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs5,(4.&40.)Pxs7,(4.&40.)Pxs9,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(8.(9.(21.(22.&40.Vsp,)+150.)R20.)(9.R20.(21.(22.&40.Vsp,)+140.)))P,(>.$6.(23.R21.+20.)=)P,(7.$1.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2<.$1.(11.VR,)Vm,Vslo,(22.&40.Vsp,))P,(7.$1.VR,VHIA,R22.R21.VLF,R23.)P,(>.$6.(3;.$1.VR,VHIA,R23.)(3;.$1.VR,VHIA,Vh,))P,(>.$6.(<.$1.VR,VHIA,R24.)(<.$1.VR,VHIA,Vh,))P,(>.$6.(3<.$1.VR,VHIA,R25.)(3<.$1.VR,VHIA,Vh,))P,Px,$6.P,(36.$1.VR,VHIA,Vh,R1.)(36.$1.VR,VHIA,R28.R2.)P,(9.(3=.$1.VR,VHIA,R27.)(1<.(3=.$1.VR,VHIA,Vh,)R2;.))P,(9.(3>.$1.VR,VHIA,R28.)(1<.(3>.$1.VR,VHIA,Vh,)R2;.))P,(3?.$1.R2:.R28.R27.)P,(40.VLB,VdX,R29.R28.)P,Pb,$3.P,(41.$3.R1.(42.R2:.))(43.(41.$3.R2.(42.VdX,))(44.VR,(2?.VLB,VdX,)VLF,(45.$6.$6.R2.)(46.$6.$6.R2.)))P,A2.R31.R29.R2:.P,(47.(36.$1.VR,VHIA,R2=.)(1=.VdX,)+10.)P,(43.(9.(1<.(1=.VdX,)+10.)Vlo,)(9.(22.&40.Vsp,)(1=.VdX,)))P,P,(=.(>.$48.(49.R2=.)$4:.))(8.(47.(36.$1.VR,VHIA,R30.)(4;.R2>.)(4<.+4.(4=.R2>.)))(8.(;.=(4=.R2>.))(43.(9.(1<.(4;.R2>.)(4<.+4.(4=.R2>.)))Vlo,)(9.(22.&40.Vsp,)(4;.R2>.)))))P,(24.$1.R31.(1<.(22.&40.Vsp,)-68.)(13.$14.(25.Vs11,)(13.$14.(25.Vs10,)(13.$14.(25.Vs9,)(13.$14.(25.Vs8,)(13.$14.(25.Vs7,)(13.$14.(25.Vs6,)(13.$14.(25.Vs5,)(13.$14.(25.Vs4,)(13.$14.(25.Vs3,)(13.$14.(25.Vs2,)(13.$14.(25.Vs1,)(13.$14.(25.Vs0,)(13.$14.(25.Vra,)(17.$14.)))))))))))))))P,(24.$1.R32.R33.(26.(4.&40.)$14.$25.R2=.))P,(>.$27.(28.(4.&40.)R2>.)#1;.)P,(29.$1.R34.(1<.R35.+=8.)(1<.(22.&40.Vsp,)-68.))P,(29.$1.R35.Vlo,R36.)P,(2:.$1.R36.)P,(24.$1.R37.(1<.(1?.(1<.R38.+60.)+3.)(1>.(11.VR,)))$2;.)P,(2<.$1.(11.VR,)R38.Vslo,(1<.R39.+60.))P,(2<.$1.(11.VR,)R39.(1<.R3:.+<0.)(22.&40.Vsp,))P,(2=.$1.(11.VR,)Vm,R3:.(:.VR,)(1<.R3;.+60.))P,(2=.$1.(11.VR,)Vm,R3;.(1<.R3<.+<0.)(22.&40.Vsp,))P,(2>.$1.VR,VHIA,Vh,(2?.VLB,VdX,)VLF,(22.&40.Vsp,)(22.&40.Vsp,)(13.(30.$6.$6.)(31.$6.$6.(1=.VdX,)(1<.(1=.VdX,)+10.))(17.(30.$6.$6.)))Vm,R3<.)(4>.$1.(4?.$1.VR,VHIA,R3<.R42.)(50.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,R41.R40.R3?.Vlo,Vm,R42.)(1:.(1;.R37.(16.&40.R3>.)Vgp,Vtp,R36.R35.R34.Vsp,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.(16.&40.R39.)R26.(16.&40.(1<.(1?.(1<.R3>.+60.)+3.)(1>.(11.VR,))))R25.R24.R23.R22.R21.R20.R1?.)VF,(16.&40.+:0:>0.)Vfc,(12.(4.&40.))R3=.(20.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros SP1 SP1M HH0 SS0 HHc HTc HSc HFc HCSc HVc HFRc MXc OUTc FRAc RRc CRX DSX XLc SAVE SPILL LSL SThi STlo MIc SHC SSlo SShi SNlo SNhi PRES.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH0) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDE; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (hcs_stack asegs R HIA hc) as SCS0c. rewrite HSc in SCS0c.
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0c| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    repeat (destruct sl as [|? sl]; [discriminate LSL|]). destruct sl; [| discriminate LSL]. clear LSL. cbn [map] in SPILL.
    pose proof (munch_refl [(sp1 + 96, sp1 + 104); (Z.shiftr (sp1 + 96) 3 + al_sb AL, Z.shiftr (sp1 + 96) 3 + al_sb AL + 12)] mc) as MU.
    pose proof (wmono_refl asegs mc) as WM.
    unfold EM_POISON in SHC.
    (* [comment removed for export] *)
    zstep_to [658148]. zstep_to [658152]. zstep_to [658156].
    (* [comment removed for export] *)
    zstep_to [658160]. zstep_to [658164]. zstep_to [658168]. zstep_to [658172]. zstep_to [658176]. zstep_to [658180]. zstep_to [658184]. zstep_to [658188]. zstep_to [658192]. zstep_to [658196]. zstep_to [658200]. zstep_to [658204]. zstep_to [658208].
    norm_b8 SHC.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mq _) => rename mq into mf end.
    (* [comment removed for export] *)
    zstep_to [658212]. replace (bv_unsigned sp + -320 + 216) with (bv_unsigned sp + -104) in * by (clear; lia).
    zstep_to [658264]. zstep_to [658268]. zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold mpi_binop_postA.
    (* [comment removed for export] *)
    assert (STf : stk asegs mf lo (bv_unsigned sp)).
    { assert (STa : stk asegs mf lo (sp1 + 216)).
      { eapply (stk_merge asegs mf lo sp1); [exact STlo| | clear - SP1 SLO NEEDE; lia].
        lazymatch type of SPILL with rw_cells _ _ _ ?cs => replace (sp1 + 216) with (sp1 + Z.of_nat (cells_size cs)) by (cbn; clear; lia) end.
        apply stk_of_rw_cells. exact SPILL. }
      assert (STb : stk asegs mf lo (bv_unsigned sp + -104)) by (eapply (stk_merge asegs mf lo (sp1 + 216)); [exact STa| exact SThi| clear - SP1 SLO NEEDE; lia]).
      eapply (stk_merge asegs mf lo (bv_unsigned sp + -104)); [exact STb| | clear - SP1 SLO NEEDE; lia].
      lazymatch type of SAVE with rw_cells _ _ _ ?cs => replace (bv_unsigned sp) with (bv_unsigned sp + -104 + Z.of_nat (cells_size cs)) at 2 by (cbn; clear; lia) end.
      apply stk_of_rw_cells. exact SAVE. }
    (* [comment removed for export] *)
    destruct (sshad_split asegs AL m slo (sp1 + 96) (bv_unsigned sp) SS0 ltac:(clear - SP1 SLO NEEDE SLL; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [_ SSr].
    destruct (sshad_split asegs AL m (sp1 + 96) (sp1 + 192) (bv_unsigned sp) SSr ltac:(clear - SP1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSm0 _].
    pose proof (sshad_of_chunk_sh asegs AL mf 12 (sp1 + 96) _ SHC eq_refl ltac:(clear - SP1M; Z.div_mod_to_equations; lia) ltac:(clear - SP1R; lia)) as SSmf.
    replace (sp1 + 96 + 8 * Z.of_nat 12) with (sp1 + 192) in SSmf by (clear; lia).
    pose proof (hm_top asegs R HIA hc LBc LF _ HHc) as HTOPc.
    assert (SNmid : snapA asegs AL m mf (sp1 + 96) (sp1 + 192)).
    { apply snapA_of_sshad; [exact SSm0| exact SSmf| |].
      - intros c Hc. eapply SSMAP; [exact HH0| clear - Hc SP1 SLO NEEDE LOS TOP HTOP; lia].
      - intros c Hc. eapply SSMAP; [exact HHc| rewrite HSc; clear - Hc SP1 SLO NEEDE LOS TOP HTOP; lia]. }
    pose proof (snapA_join asegs AL _ _ _ _ _ (snapA_join asegs AL _ _ _ _ _ SNlo SNmid) SNhi) as SNall.
    pose proof (presA_lower_ssp asegs R _ _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h _ _ _ _ _ _ _ PRES) SNall) as HPf.
    (* [comment removed for export] *)
    assert (MXf : mpd_at asegs mf LBc dXc).
    { eapply mpd_at_munch_any; [exact MXc| exact MU| exact WM| |].
      - cbn [disjoint_from]. destruct OUTc as (OA & _). rewrite OA.
        destruct (apart_shadow_client AL (hcs asegs R HIA hc) X 16 (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOKc CRX
                    ltac:(eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]) ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - DSX SP1 SLO NEEDE; lia| split; [clear - Q; lia| exact I]]).
      - intros NN. ddestruct (XLc NN) as (CRP & NP & DSP). cbn [disjoint_from].
        destruct (apart_shadow_client AL (hcs asegs R HIA hc) (md_p dXc) (4 * md_n dXc) (sp1 + 96) (Z.shiftr (sp1 + 96) 3 + al_sb AL) 12 CSOKc CRP
                    ltac:(eapply crange_sub; [exact SCSc| clear - SP1 SLO NEEDE; lia| clear - SP1; lia]) ltac:(unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear; lia) ltac:(clear - NP; lia) ltac:(clear; lia)) as [Q|Q];
          (split; [clear - DSP SP1 SLO NEEDE; lia| split; [clear - Q; lia| exact I]]). }
    deexists 14. dexists mf, mo9, hc, LBc, dXc, r.
    split; [reflexivity|]. split; [assumption|]. split; [exact STf|]. split; [exact MF9|]. split; [exact HPf|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|]. split; [exact HVc|]. split; [exact HFRc|].
    split; [exact HHc|]. split; [exact MXf|]. split; [exact OUTc|]. split; [exact FRAc| exact RRc].
    all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WEM.
