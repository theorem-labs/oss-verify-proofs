(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_string U_mpi_addsub U_mpi_mul_stmt U_mpi_grow U_mpi_cmp U_mpi_bitlen U_mpi_core_sub U_mpi_core_add_if U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_mul_mod () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "ECP_RED_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_red.ecp_reducer_stmt"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "mul_mod_R"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_mul_mod_post"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Facts.grp_X_ok"; "Stdlib.ZArith.BinInt.Z.pow"; "Facts.mm_base"; "Facts.mm_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Facts.mm_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_red.relimb"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.sub_fp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"; "ecp_mul_mod_stmt"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_intop_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.mpi_cmp_mpi_stmt"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.mpi_cmp_int_stmt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Facts.ext_opnd"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ECP_RED_STACK : Z := 384.
(* [comment removed for export] *)
Definition ECP_MUL_MOD_STACK : Z := 608.

(* [comment removed for export] *)
Definition modp_table_ok (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Pe,$0.Plp,$0.Pws,(1.(2.&40.))P,(3.(4.$0.(4.$0.(1.(2.&40.))))(5.$0.(4.$0.(1.(2.&40.)))R3.(5.$0.(1.(2.&40.))R2.R1.))O2.)(6.(7.$0.(8.R4.+2.)=)(9.$0.LK,$0.(9.$0.LSTK,$0.(6.(:.(;.(<.(2.&40.)R4.))R2.)(6.(6.(:.=R1.)(:.R1.$=.))(>.O5.O4.O3.R6.O1.R2.R1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mul_mod_R (LB : list blk) (dX : mpd) (r : Z) (dX' : mpd) : Prop := -2^31 < r <= 0 /\ binop_keep LB dX dX'.

Definition ecp_mul_mod_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (dX : mpd) (G : Z) (g : ecp_grp) (MC lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Lc,$?.(9.(2.&40.)Lt0,(2.&40.)(9.(2.&40.)Lt1,(2.&40.)(9.(2.&40.)Lt2,(2.&40.)(9.(2.&40.)La1,(2.&40.)(9.(2.&40.)La2,(2.&40.)(9.(2.&40.)La3,(2.&40.)(9.(2.&40.)La4,(2.&40.)(9.(2.&40.)La5,(2.&40.)(9.(2.&40.)La6,(2.&40.)(9.(2.&40.)La7,(2.&40.)(9.(2.&40.)Lt3,(2.&40.)(9.(2.&40.)Lt4,(2.&40.)(9.(2.&40.)Lt5,(2.&40.)(9.(2.&40.)Lt6,(2.&40.)(9.P,(2.&40.)(10.(2.&8.))Lm',P,(2.&40.)(10.(2.&8.))(9.$11.Lmo',$11.(9.(12.O1?.O1>.O1=.)Lh',(12.O1?.O1>.O1=.)(9.(1.$13.)LLB',(1.$13.)(9.$14.LdX',$14.(9.$0.Lr,$0.(9.(2.&40.)Lcnt',(2.&40.)(6.(7.$?.R16.(15.(16.(17.O1;.O1:.O19.O18.R15.R14.R13.O17.O16.(18.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R;.R:.R9.R8.)O;.(19.O1;.)O:.(1:.(2.&40.))R7.(1;.O1?.))R6.))(6.(1<.O1?.R7.)(6.(1=.O1?.R7.O3.(1>.&40.O1:.))(6.(1?.O1.R6.)(6.(7.$0.(20.O1?.O1>.O1=.R5.)(20.O1?.O1>.O1=.O9.))(6.(21.O1?.O1>.O1=.R5.R4.R7.R6.)(6.(22.O1?.R7.R4.R3.)(6.(23.O8.O7.R4.R3.)(6.(24.O1?.O1>.O8.(1>.&40.O1:.)(25.(4.$0.$0.)(26.O7.)(27.(4.$0.$0.)(5.$0.$0.O4.(28.O4.+8.))(29.(4.$0.$0.))))O2.R7.)(6.(2:.O1?.O1>.R7.)(6.(2;.O1?.O1<.R7.R4.O6.O5.)(6.(2<.O1?.R7.O4.(27.$2=.(2>.R1.)(29.$2=.)))(2?.O8.O7.R2.R3.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_mul_mod_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ENTRY MSF MC STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph,(12.O8.O7.O6.)PLB,(1.$13.)PdX,$14.PdA,$14.PdB,$14.PG,$0.Pg,$31.Pcnt,(2.&40.)Plo,$0.P,(21.O8.O7.O6.R9.R8.R;.R:.)P,(2;.O8.O5.R<.R9.R5.R4.)P,(7.$0.(32.R5.)+1.)P,(7.$0.(33.(34.R6.))+1.)P,(35.O7.R<.R5.R8.+<0.)P,(36.(:.(28.R9.+<0.)R6.)(:.(1>.&40.R30.)R9.))P,(36.(:.(28.(37.R=.)+10.)R:.)(:.(28.R:.+<0.)(37.R=.)))P,P,(7.$38.(39.R>.)$3:.)(36.(:.(28.R<.+<0.)(3;.R?.))(:.(28.(3;.R?.)(3<.+4.(3=.R?.)))R<.))P,(22.O8.R13.R10.R?.)P,(22.O8.R14.R11.R?.)P,(22.O8.R15.R12.R?.)P,(3>.R12.R11.)P,(3>.R13.R11.)P,(3>.R13.R12.)P,(3?.(7.$38.(39.R15.)$40.))P,(41.R16.R15.R10.(1>.&40.R3:.))P,(41.R17.R15.R11.(1>.&40.R3;.))P,(35.O7.R19.R12.(37.R17.)+10.)P,P,(7.$38.(39.R18.)$3:.)(35.O7.R1;.R14.(3;.R19.)(3<.+4.(3=.R19.)))P,(35.O7.R1;.R14.(37.R18.)+10.)P,P,(7.$38.(39.R19.)$3:.)(35.O7.R1=.R16.(3;.R1:.)(3<.+4.(3=.R1:.)))P,(42.O7.R1=.(1>.&40.R40.)(20.O8.O7.O6.R1>.)R1<.)P,P,(3?.(7.$38.(39.R1=.)$43.))(36.(:.(28.(3;.R1>.)(3<.+4.(3=.R1>.)))R18.)(:.(1>.&40.R42.)(3;.R1>.)))P,(2<.O8.R22.O2.(27.$2=.(2>.R19.)(29.$2=.)))P,(:.(44.O7.)O2.)P,(:.(28.O2.+8.)(45.O7.))P,Pa,$0.P,(6.(:.O2.R1.)(46.R1.(28.O2.+8.)))(6.(3?.(47.O7.R2.))(48.O7.R2.))P,(36.(:.(28.O2.+8.)(37.R22.))(:.(28.(37.R22.)+10.)O2.))P,(36.(:.(28.O2.+8.)R20.)(:.(28.R20.+<0.)O2.))P,(1=.O8.R28.R1>.(1>.&40.R48.))P,(:.R1?.(49.(49.(1>.&40.R49.)O1.)(4:.O7.)))P,(:.(4;.O7.)R20.)P,(:.(1>.&40.R4;.)(20.O8.O7.O6.R29.))P,(7.$0.(8.(1>.&40.R4<.)+10.)=)P,(:.(45.O7.)(4;.O7.))P,(7.(2.&40.)R4<.(18.&40.(4<.O7.)))P,(1<.O8.R2?.)P,(2:.O8.O7.R30.)P,(4=.O7.O3.+8.)P,(7.(2.&40.)R4:.(18.&40.R2;.))P,(7.(2.&40.)R4:.(18.&40.(37.R2?.)))P,(7.(2.&40.)R4:.(18.&40.(37.R2?.)))P,(7.(2.&40.)R4:.(18.&40.(37.R2?.)))(4>.O8.R35.(4?.O8.O7.O6.O5.R57.R56.R55.R54.R50.R4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R38.R37.R34.R33.R32.R2?.R2>.O2.R2<.R36.R35.)(16.(17.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R38.(18.&40.O4.)R37.(1:.(2.&40.))R36.(1;.O8.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_static_own : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Pm,P,(2.&40.)(10.(2.&8.))PLB,(1.$13.)PG,$0.Pg,$31.Pd,$14.P,(2;.Vsegs,R6.R5.R4.R3.R2.)P,(7.$0.(32.R3.)+1.)P,(3.$14.R3.(51.R4.))(3?.(7.$38.(39.R4.)$3:.))")
(* [comment removed for export] *).
  Proof.
    intros MT m LB G g d HG H1 Hd. ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REST).
    ddestruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEPT & _).
    unfold grp_kept_mpds in KEPT. rewrite H1 in KEPT. cbn [Z.eqb Pos.eqb] in KEPT.
    exact (proj1 (Forall_forall _ _) KEPT d Hd).
  Qed.

  #[using="Type"] Lemma mpdr_at_LB_any : forall m LB LB' d, mpdr_at segs m LB d -> md_own d <> LHeap -> mpdr_at segs m LB' d.
  Proof.
    (intros m LB LB' d dd_H; ddestruct dd_H as (HR & HAL & HPOS & HL & HN & HO); intros NO).
    split; [exact HR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
    destruct (md_own d); [exact HO| exact (False_ind _ (NO eq_refl))| exact HO].
  Qed.

  #[using="Type"] Lemma mpdr_at_LB_one : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Pm,P,(2.&40.)(10.(2.&8.))PLB,(1.$13.)PLB',(1.(4.$0.$0.))Pd,$14.P,(52.Vsegs,R4.R3.R1.)P,P,(7.$38.(39.R2.)$3:.)(3.(4.$0.$0.)(5.$0.$0.(3;.R3.)(3<.+4.(3=.R3.)))R4.)(52.Vsegs,R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros m LB LB' d dd_H; ddestruct dd_H as (HR & HAL & HPOS & HL & HN & HO); intros HIN).
    split; [exact HR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
    destruct (md_own d); [exact HO| | exact HO]. ddestruct HO as (H1 & _ & H3 & H4). exact (conj H1 (conj (HIN eq_refl) (conj H3 H4))).
  Qed.

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10752852905.39L11870202122.39L16192518623.39L1693639593.39 L1816178427.39 L20405954314.39L22309273744.39L24794929803.39L35655924117.45L37627108106.39L38398251550.39L39057209360.39L39570250485.45L41891183626.39L47813685243.39L48815711238.47L48815712669.41L50129587451.39L54513366011.39L56826122491.39L59112853514.39L6199959035.39 L63368410378.39L67642961418.39L68546963963.3900000300600900<00?00B00E00H00S00V00Y00\00g00j00m01E01M01P01S01V01Y01\01_01b01eS1GS1GS1GS1GS1GS1GS1GS1GS1G3off3Ho2S1GS1GS1GS1G3off3Ho1S1GS1GS1G3POS3off3Ho13Ho21a2HxS1G1a2HaS1GS1GS1GS1GS1GS1GS1GS1G". (* [comment removed for export] *)
  #[using="Type"] Lemma ecp_group_at_presx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Pm,P,(2.&40.)(10.(2.&8.))Pm',P,(2.&40.)(10.(2.&8.))PLB,(1.$13.)PLB',(1.(4.$0.$0.))PSP,$0.PX,(1.$53.)PG,$0.Pg,$31.P,(2;.Vsegs,R9.R8.R6.R2.R1.)P,(24.Vsegs,VL,R7.R5.R4.R9.R8.)P,(1<.Vsegs,R:.)P,(1<.Vsegs,R:.)P,(35.VL,R:.R8.R6.+<0.)P,(54.R8.R7.+<0.)P,Pd,$14.P,(3.$14.R1.(51.R8.))P,(7.$38.(39.R2.)$3:.)(6.(3.(4.$0.$0.)(5.$0.$0.(3;.R3.)(3<.+4.(3=.R3.)))R>.)(54.R<.(3;.R3.)(3<.+4.(3=.R3.))))(2;.Vsegs,R10.R>.R<.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros MT m m' LB LB' SP X G g HG PX MI MI' CR DX HP.
    ddestruct HG as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & REST).
    assert (ST : forall d off, In d (grp_mpds g) -> md_addr d = G + off -> 0 <= off -> off + 16 <= 192 -> mpdr_at segs m LB d -> mpdr_at segs m' LB' d).
    { intros d off Hd Ha Ho1 Ho2 HDd. apply mpdr_at_LB_one with (LB := LB); [| intros O; exact (proj1 (HP d Hd O))].
      eapply mpdr_at_presx; [exact HDd| exact PX| exact MI| exact MI'| | |].
      - rewrite Ha. intros a Hx; apply CR; lia.
      - rewrite Ha. eapply disjoint_from_sub; [exact DX| lia| lia].
      - intros O. split; [| exact (proj2 (HP d Hd O))]. ddestruct HDd as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)). }
    split; [eapply heap_presx_rw_cells; [exact PX| exact HD| cbn [cells_size csize Nat.add grp_head_cells]; intros a Ha; apply CR; lia| cbn [cells_size csize Nat.add grp_head_cells]; eapply disjoint_from_sub; [exact DX| lia| cbn; lia]]|].
    refine (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _)))))).
    split; [apply (ST _ 8); [cbn; auto 10| exact EP| lia| lia| exact MP]|].
    split; [apply (ST _ 24); [cbn; auto 10| exact EA| lia| lia| exact MA]|].
    split; [apply (ST _ 40); [cbn; auto 10| exact EB| lia| lia| exact MB]|].
    split.
    { refine (conj EX (conj EY (conj EZ _))).
      split; [apply (ST _ 56); [cbn; auto 10| rewrite EX; lia| lia| lia| exact MX]|].
      split; [apply (ST _ 72); [cbn; auto 10| rewrite EY; lia| lia| lia| exact MY]|].
      apply (ST _ 88); [cbn; auto 10| rewrite EZ; lia| lia| lia| exact MZ]. }
    split; [apply (ST _ 104); [cbn; auto 10| exact EN| lia| lia| exact MN]|].
    split; [| exact REST].
    eapply heap_presx_rw_cells; [exact PX| exact HT| cbn [cells_size csize Nat.add grp_tail_cells]; intros a Ha; apply CR; lia| cbn [cells_size csize Nat.add grp_tail_cells]; eapply disjoint_from_sub; [exact DX| lia| cbn; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_blocks_in : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Pm,P,(2.&40.)(10.(2.&8.))PLB,(1.$13.)PG,$0.Pg,$31.Pd,$14.P,(2;.Vsegs,R6.R5.R4.R3.R2.)P,(3.$14.R2.(51.R3.))P,(7.$38.(39.R3.)$3:.)(3.(4.$0.$0.)(5.$0.$0.(3;.R4.)(3<.+4.(3=.R4.)))R7.)")
(* [comment removed for export] *).
  Proof.
    intros MT m LB G g d HG Hd O.
    ddestruct HG as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & REST).
    assert (H : mpdr_at segs m LB d).
    { unfold grp_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    ddestruct H as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L21408125392.19L36579640108.21L51794690462.16L67519459700.20L6788885418.20 L67996834984.1600000;00C00L00T00`00gS1A2cs1a2HaS2cs1P1aS2cs1k2HkS1A2cs1aS2cs1P1k1a1CS2cs2Hn". (* [comment removed for export] *)
  #[using="Type"] Lemma rw_ro_apart : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Pm,P,(2.&40.)(10.(2.&8.))PA,$0.Pcs,(1.$2=.)PP,$0.Pk,$0.P,(1<.Vsegs,R5.)P,(2<.Vsegs,R6.R5.R4.)P,(46.=(;.(55.R5.)))P,(46.=R4.)P,Pi,$0.P,(6.(:.=R1.)(46.R1.R6.))(7.$56.(57.Vsegs,(58.(28.R8.R2.)))$59.)(36.(:.(28.R9.(;.(55.R8.)))R7.)(:.(28.R7.R6.)R9.))")
(* [comment removed for export] *).
  Proof.
    intros m A cs P k MI [_ (W0 & W1 & W)] Hn Hk RO. apply pointwise_apart; [lia| lia|]. intros a Ha C.
    pose proof (W (a - A) ltac:(lia)) as V. replace (A + (a - A)) with a in V by lia.
    pose proof (RO (a - P) ltac:(lia)) as R. replace (P + (a - P)) with a in R by lia.
    destruct (m (wa a)) eqn:E.
    - rewrite (MI _ _ E) in R. discriminate.
    - rewrite (wview_not_ro segs m (wa a) V E) in R. discriminate.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11663807224.15L13807202080.15L57185660066.1700000100C00UFS1d2lo2SP3SP'2A41HS1d2lo3SP'2H02SP1H". (* [comment removed for export] *)
  #[using="Type"] Lemma opnd_sep_sp_mono : forall dX d lo SP SP', opnd_sep dX d lo SP -> SP' <= SP -> opnd_sep dX d lo SP'.
  Proof. (intros dX d lo SP SP' dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5); intros H). unfold opnd_sep. repeat split; auto; try lia. intros O. destruct (A5 O); lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16564321865.1600000BS2SP3SP'3top1H1a1C". (* [comment removed for export] *)
  #[using="Type"] Lemma mpd_writable_sp_mono' : forall LB SP SP' top d, mpd_writable L LB SP top d -> SP' <= SP -> mpd_writable L LB SP' top d.
  Proof.
    (intros LB SP SP' top d dd_H; ddestruct dd_H as (W1 & W2 & W3); intros H). split; [| split; [exact W2| exact W3]].
    intros a Ha. destruct (W1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="L DIMG"] Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n <-> disjoint_from W1 a n /\ disjoint_from W2 a n.
  Proof. induction W1 as [|[lo hi] W1 IH]; cbn; intros; [tauto|]. rewrite IH. tauto. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308579027.1900000FS1L1p1k1a2Ha1C2B51H2H0". (* [comment removed for export] *)
  #[using="DIMG"] Lemma blk_off_data : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Pp,$0.Pk,$0.Pa,$0.P,(21.Vsegs,VL,VHI,R7.R6.R5.R4.)P,(3.(4.$0.$0.)(5.$0.$0.R4.R3.)R7.)P,(6.(:.(44.VL,)R3.)(46.R3.(45.VL,)))(3?.(6.(:.R6.R4.)(46.R4.(28.R6.R5.))))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo p k a HH IN Ha C. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & _ & B5). cbn in B5. destruct DIMG. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L16564321865.33L17608453843.34L59314873579.36L61485347538.31L65502333741.3100000C00V00c00n00oS2SP3SP'3top2LE1a1CS2SP3SP'3top2LE1a1CS2dX1a2Ha1R1HS1L3SP'3ACLS". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mpd_writable_out : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Ph1,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PLB1,(1.$13.)Pm,P,(2.&40.)(10.(2.&8.))Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PSP,$0.PSP',$0.Ptop,$0.PdX,$14.PdX1,$14.P,(42.VL,R:.R5.R3.R2.)P,(22.Vsegs,R9.R;.R3.)P,(21.Vsegs,VL,VHI,R=.R;.R9.R8.)P,(22.Vsegs,R:.R<.R4.)P,(23.R>.R6.R=.R5.)P,Pb,$13.P,(3.$13.R1.(5:.R7.))(36.(3.$13.R2.(5:.R9.))(3?.(3.$13.R2.R11.)))P,(:.(4;.VL,)R:.)P,(:.R;.R<.)(42.VL,R11.R<.R;.R9.)")
(* [comment removed for export] *).
  Proof.
    (intros h1 LB LB1 m m1 mo1 SP SP' top dX dX1 dd_H; ddestruct dd_H as (W1 & W2 & W3); intros MA HH1 MA1 OUT FR ACL LE).
    dpose OUT as (EA & NS & K1 & K2 & K3). unfold mpd_writable. rewrite EA. split; [| split; [exact W2|]].
    - intros a Ha. destruct (W1 a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
      exists (B, k). split; [| exact R]. apply K2; [exact Hb|]. intros HX.
      unfold mpd_blk in HX. destruct (md_own dX) eqn:EO; try (destruct HX; fail). destruct HX as [E|[]]. injection E as E1 E2. subst B k.
      cbn in R. pose proof (W3 eq_refl). lia.
    - intros O1. eapply (new_limbs_apart_range segs L HI) with (SP := SP'); [exact HH1| exact MA1| exact OUT| exact FR| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| | lia| exact W3| exact O1].
      intros a Ha. destruct (W1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L17608453843.23L59314873579.2600000?00PS2SP3SP'2LE1a1CS2dX1A1n1a2Ha1R1H". (* [comment removed for export] *)
  #[using="Type"] Lemma client_range_out : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PLB,(1.$13.)PLB1,(1.$13.)PdX,$14.PdX1,$14.PSP,$0.PSP',$0.PA,$0.Pn,$0.P,(35.VL,R8.R4.R2.R1.)P,(23.R9.R7.R8.R6.)P,P,(7.$38.(39.R8.)$3:.)(36.(:.(28.R5.R4.)(3;.R9.))(:.(28.(3;.R9.)(3<.+4.(3=.R9.)))R5.))P,(:.R6.R7.)(35.VL,R;.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros LB LB1 dX dX1 SP SP' A n CR dd_H; ddestruct dd_H as (EA & NS & K1 & K2 & K3); intros AP LE a Ha).
    destruct (CR a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
    exists (B, k). split; [| exact R]. apply K2; [exact Hb|]. intros HX.
    unfold mpd_blk in HX. destruct (md_own dX) eqn:EO; try (destruct HX; fail). destruct HX as [E|[]]. injection E as E1 E2. subst B k.
    cbn in R. pose proof (AP eq_refl). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59656785403.1500000BS2SP3top2lo2LE1a1C". (* [comment removed for export] *)
  #[using="Type"] Lemma client_range_of_wrange : forall LB SP top lo A n,
    client_wrange L LB SP top A n -> lo <= SP -> client_range L LB lo A n.
  Proof.
    intros LB SP top lo A n W LE a Ha. destruct (W a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition grp_X_ok (LB : list blk) (dX : mpd) (g : ecp_grp) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "Pd,$14.P,(3.$14.R1.(51.O1.))P,(7.$38.(39.R2.)$3:.)(6.(3.(4.$0.$0.)(5.$0.$0.(3;.R3.)(3<.+4.(3=.R3.)))O3.)(6.(3?.(3.(4.$0.$0.)(5.$0.$0.(3;.R3.)(3<.+4.(3=.R3.)))(5:.O2.)))(36.(:.(28.(37.O2.)+10.)(3;.R3.))(:.(28.(3;.R3.)(3<.+4.(3=.R3.)))(37.O2.)))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma grp_X_ok_h1 : forall MT m LB G g dX LB', ecp_group_at segs MT m LB G g -> g_h g = 1 -> grp_X_ok LB' dX g.
  Proof. intros MT m LB G g dX LB' HG H1 d Hd O. exfalso. exact (grp_static_own MT m LB G g d HG H1 Hd O). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mm_inv (MT : list modp_ent) (h : HST segs L HI) (LB : list blk) (dX : mpd) (G : Z) (g : ecp_grp) (MC SP FRM lo : Z)
      (m : mem) (mo : Model) (h1 : HST segs L HI) (LB1 : list blk) (dX1 : mpd) (m1 : mem) (mo1 : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "(6.(21.Vsegs,VL,VHI,O5.O4.O2.O1.)(6.(22.Vsegs,O2.O4.O3.)(6.(23.O?.O>.O4.O3.)(6.Pb,$13.P,(3.$13.R1.(5:.O3.))(36.(3.$13.R2.(5:.O>.))(3?.(3.$13.R2.O?.)))(6.(7.(2.&40.)(5;.O3.)(5;.O>.))(6.(:.(3=.O>.)(3=.O3.))(6.(24.Vsegs,VL,O?.O:.(25.(4.$0.$0.)(26.O>.)(27.(4.$0.$0.)(5.$0.$0.O;.(28.O;.+8.))(29.(4.$0.$0.))))O7.O2.)(6.(2:.Vsegs,VL,O2.)(6.(1<.Vsegs,O2.)(6.(1?.O6.O1.)(6.(7.$0.(20.Vsegs,VL,VHI,O5.)(20.Vsegs,VL,VHI,O10.))(6.(2;.Vsegs,O11.O2.O4.O=.O<.)(6.(9.(2.&40.)Lcnt,(2.&40.)(2<.Vsegs,O2.O;.(27.$2=.(2>.R1.)(29.$2=.))))(1=.Vsegs,O2.O8.(49.O:.O9.)))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition mm_base (LB : list blk) (dX : mpd) (G MC SP FRM lo : Z) (top : Z) (g : ecp_grp) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "(6.(42.VL,O9.O5.O2.O8.)(6.(3?.(7.$38.(39.O8.)$40.))(6.Pb,$13.P,(3.$13.R1.(5:.O8.))(3.$13.R2.O9.)(6.(35.VL,O9.O5.O7.+<0.)(6.(36.(:.(28.(37.O8.)+10.)O7.)(:.(28.O7.+<0.)(37.O8.)))(6.P,(7.$38.(39.O8.)$3:.)(36.(:.(28.O7.+<0.)(3;.O8.))(:.(28.(3;.O8.)(3<.+4.(3=.O8.)))O7.))(6.(:.(44.VL,)O6.)(6.(:.(28.O6.+8.)(45.VL,))(6.Pa,$0.P,(6.(:.O6.R1.)(46.R1.(28.O6.+8.)))(6.(3?.(47.VL,R2.))(48.VL,R2.))(6.(36.(:.(28.O6.+8.)(37.O8.))(:.(28.(37.O8.)+10.)O6.))(6.(36.(:.(28.O6.+8.)O7.)(:.(28.O7.+<0.)O6.))(6.(5<.O9.O8.O1.)(6.(:.(4;.VL,)O3.)(6.(:.=O4.)(6.(46.(28.O3.O4.)O5.)(6.(:.O5.O2.)(6.(:.(45.VL,)(4;.VL,))(6.(36.(:.(28.(37.O8.)+10.)O3.)(:.(49.O5.O4.)(37.O8.)))(6.(36.(:.(28.O7.+<0.)O3.)(:.O5.O7.))(46.O5.(5=.+2.+40.)))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L1053036946.87  L12187787498.101L14583414824.102L16188889390.92 L22706553362.88 L32161193265.86 L38651952865.92 L40147641242.88 L44157186017.86 L46082630998.90 L46677474934.91 L52101693566.88 L52107990421.90 L52108576753.91 L52108576753.92 L54332326169.101L56765204236.90 L57051602729.91 L57053577632.87 L59308579027.93 L59310684262.91 L59315053158.94 L5952735238.90  L60380792584.94 L65481179362.92 L66717576061.88 L8970969341.92  00000100800B00J01J01U01b02502>02H02R03R03S03[03c03l04;04U04o06706C06O06_06i08108:08HSS1d3DN1S3dX11d2APS3dX12N1S1L2dX1G2MC2SP3FRM2lo2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1a2HaS2dX2MC3MCXS2MC3dX12n01lS1L2MC3MC13MC21a2HaS2dX1G2GXS2MC3dX11lS2MC3dX11lS1L2dX1G2MC2SP3FRM2lo2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1a2HaFS2dX1a1lS2dX1a1lS3dX13XN1S1G3POS1a2Ha2TBS1L2SP3FRM2lo3ACL3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS1L2dX1G2MC2SP3FRM2lo2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1a2Ha1n2n02H0S2dX1a1R3HoXS2dX1a3HoX1CS2SP3FRM3FR01a1CS2dX1d3APdS1L2dX1G2MC2SP3FRM2lo3dX12GX3MC13MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1n2n1S2MC1a2HaS1L2MC3MC13MC2". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_inv_binop : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Ph2,(12.Vsegs,VL,VHI,)PLB2,(1.$13.)PdX2,$14.Pm2,P,(2.&40.)(10.(2.&8.))Pmo2,$11.P,(5>.R14.R13.R12.R10.R?.R>.R=.(20.Vsegs,VL,VHI,R15.)R11.)P,(22.Vsegs,R=.R15.R14.)P,(5?.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(21.Vsegs,VL,VHI,R8.R7.R5.R4.)P,(22.Vsegs,R6.R8.R7.)P,(23.R>.R=.R9.R8.)P,Pb,$13.P,(3.$13.R1.(5:.R:.))(36.(3.$13.R2.(5:.R10.))(3?.(3.$13.R2.R11.)))P,(7.(2.&40.)(5;.R:.)(5;.R?.))P,(:.(3=.R10.)(3=.R;.))P,(24.Vsegs,VL,R12.(49.R18.R17.)(26.R11.)R10.R;.)P,(2:.Vsegs,VL,R<.)P,(1<.Vsegs,R=.)P,(1?.R12.R=.)P,(7.$0.(20.Vsegs,VL,VHI,R12.)(20.Vsegs,VL,VHI,R17.))P,(1=.Vsegs,R10.R1;.(49.R1=.R1<.))(5?.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R14.R13.R12.R11.R10.)")
(* [comment removed for export] *).
  Proof.
    (intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 h2 LB2 dX2 m2 mo2 dd_H; ddestruct dd_H as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU); intros MA dd_H; ddestruct dd_H as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1); intros HH2 MA2 OUT2 FR2 PAD2 NLE2 PX2 SOK2 MI2 MF2 HT2 ST2).
    dpose OUT1 as (EA1 & NS1 & K11 & K12 & K13). dpose OUT2 as (EA2 & NS2 & K21 & K22 & K23).
    assert (FR' : forall b, In b (mpd_blk dX2) -> In b (mpd_blk dX) \/ ~ In b LB).
    { intros b Hb. destruct (FR2 b Hb) as [H|H]; [exact (FR1 b H)|].
      destruct (in_dec (fun x y : blk => ltac:(decide equality; apply Z.eq_dec)) b (mpd_blk dX)) as [I|NI]; [left; exact I| right].
      intros C. exact (H (K12 b C NI)). }
    (* [comment removed for export] *)
    assert (CL : forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside (mpd_ivs dX ++ [(MC, MC + 8)]) a ->
                 client_addr L LB1 (SP - FRM) a /\ outside (mpd_ivs dX1) a).
    { intros a Ha Hc Ho. rewrite outside_app in Ho. destruct Ho as [HoX HoC].
      split.
      - destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
        exists (B, k). split; [| exact R]. apply K12; [exact Hb|]. intros HX.
        unfold mpd_blk in HX. unfold mpd_ivs in HoX. destruct (md_own dX); try (destruct HX; fail). destruct HX as [E|[]]. injection E as E1 E2. subst B k.
        cbn in R, HoX. lia.
      - unfold mpd_ivs. rewrite EA1. cbn. split; [unfold mpd_ivs in HoX; cbn in HoX; exact (proj1 HoX)|].
        destruct (md_own dX1) eqn:O1; cbn; [exact I| | exfalso; exact (NS1 eq_refl)].
        split; [| exact I].
        pose proof (new_limbs_apart segs L HI h1 LB LB1 m1 m1 mo1 SP dX dX1 a HH1 MA1 OUT1 FR1 ltac:(lia) (proj1 DIMG) (proj2 DIMG) Hc) as NL.
        apply NL; [| exact O1]. intros O C. unfold mpd_ivs in HoX. rewrite O in HoX. cbn in HoX. lia. }
    unfold mm_inv. refine (conj HH2 (conj MA2 (conj _ (conj FR' (conj (eq_trans PAD2 PAD1) (conj (Z.le_trans _ _ _ NLE1 NLE2) (conj _ (conj SOK2 (conj MI2 (conj _ (conj (eq_trans HT2 HT1) (conj _ (conj _ ST2))))))))))))).
    - eapply mpd_out_trans; [exact OUT1| exact OUT2| exact FR1| exact XIN].
    - eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_weaken2; [exact PX2|]. exact CL.
    - eapply mo_frame_trans; [exact MF1| exact MF2].
    - eapply ecp_group_at_presx; [exact GR1| exact PX2| exact MI1| exact MI2| | |].
      + (* [comment removed for export] *)
        intros a Ha. destruct (CL a) as [C _]; [| apply GCR; exact Ha| | exact C].
        { ddestruct GR1 as (_ & _ & POS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _). pose proof (rw_cells_bound _ _ _ _ HT) as TB.
          cbn [cells_size csize Nat.add grp_tail_cells] in TB. lia. }
        rewrite outside_app. split; [| cbn; lia]. unfold mpd_ivs. cbn. split; [lia|]. destruct (md_own dX) eqn:EO; cbn; [exact I| |]; split; try exact I; pose proof (GXL); try lia.
        all: destruct (Z_lt_dec a (md_p dX)); [lia|]; destruct (Z_le_dec (md_p dX + 4 * md_n dX) a); [lia|]; exfalso.
        * pose proof (GXL eq_refl). lia.
        * apply NST. reflexivity.
      + unfold mpd_ivs. rewrite EA1. cbn. split; [lia|]. destruct (md_own dX1) eqn:O1; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I].
        eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O1].
      + (* [comment removed for export] *)
        intros d Hd O. ddestruct (H1 d Hd O) as (INd & NXd & APd). pose proof (grp_blocks_in _ _ _ _ _ _ GR1 Hd O) as IN1.
        assert (NX1 : ~ In (md_p d, 4 * md_n d) (mpd_blk dX1)).
        { intros C. destruct (FR1 _ C) as [C'|C']; [exact (NXd C')| exact (C' INd)]. }
        split; [exact (K22 _ IN1 NX1)|].
        unfold mpd_ivs. rewrite EA1. cbn. split; [lia|]. destruct (md_own dX1) eqn:O1; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I].
        pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. rewrite O1 in HO. ddestruct HO as (XN1 & INX & _).
        destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [_ HAP1].
        pose proof (grp_blocks_in _ _ _ _ _ _ GR1 Hd O) as INd1. pose proof GR1 as GRx.
        assert (DN1 : 1 <= md_n d).
        { ddestruct GRx as (HD' & AL' & POS' & EP' & EA' & EB' & EN' & MP' & MA' & MB' & (EX' & EY' & EZ' & MX' & MY' & MZ') & MN' & HT' & REST').
          assert (Hm : mpdr_at segs m1 LB1 d) by (unfold grp_mpds in Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
          ddestruct Hm as (_ & _ & _ & _ & _ & HOd). rewrite O in HOd. exact (proj1 HOd). }
        pose proof (blocks_apart_neq _ _ _ HAP1 IN1 INX ltac:(intros E; apply NX1; unfold mpd_blk; rewrite O1, <- E; left; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as AP.
        cbn in AP. lia.
    - exists cnt1. eapply heap_presx_rw_cells; [exact PX2| exact CNT1| |]; cbn [cells_size csize Nat.add].
      + intros a Ha. right; left. split; [lia|]. apply (proj1 (MCS a ltac:(lia))).
      + unfold mpd_ivs. rewrite EA1. cbn. split; [lia|]. destruct (md_own dX1) eqn:O1; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I].
        pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. rewrite O1 in HO. ddestruct HO as (N1 & IN1 & _).
        destruct (Z_lt_dec (MC + 8) (md_p dX1 + 1)); [left; lia|]. destruct (Z_le_dec (md_p dX1 + 4 * md_n dX1) MC); [right; lia|]. exfalso.
        destruct (Z_le_dec (md_p dX1) MC).
        * exact (blk_off_data _ _ _ _ _ _ MC HH1 IN1 ltac:(lia) ltac:(lia)).
        * exact (blk_off_data _ _ _ _ _ _ (md_p dX1) HH1 IN1 ltac:(lia) ltac:(lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma relimb_self : forall d, relimb d (md_limbs d) = d.
  Proof. intros []; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition mm_fp (dX1 : mpd) (lo SP FRM MC : Z) : list ivl :=
    match md_own dX1 with LHeap => [(md_p dX1, md_p dX1 + 4 * md_n dX1)] | _ => [] end ++ [(lo, SP - FRM); (MC, MC + 8)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L1051139855.80 L12189822954.95L14166413299.79L14583414824.96L40141257579.82L45383801195.77L45641679881.73L53341988683.79L53560049319.77L54334492185.95L57049501343.73L57055874877.80L57055956670.87L58187242139.82L586883706.79  L586883706.80  L586884089.81  L58726018384.8 L59308743383.91L59315053158.89L59315300849.84L59315300849.86L59315300849.87L61216210403.84L61216670429.79L6281473712.8  L66716975790.80L66716975790.81L66716975917.81L66716975917.82L66716976044.83L66717008558.79L66717008558.80L66717008558.81L66717008685.80L66717008685.81L66717008685.82L66717008685.8300000100801601C01U01c01g02402H02Q02k03E03_04B04T04f05905Q05o06>06Z07b08108:08F08\08g09209>09J09V09n0:F0:^0;=0;\0<;0<ZSS1d3DN1S1L2dX1G2MC2SP3FRM2lo2ws2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GSS3dX12ws1d2APS1L2MC3MC13MC21a1RS2dX2MC2ws3MCXS2SPS1G2MC2ws3MCGS2dX2SP3FRM2lo2ws2SXS3dX13XN1S1L2SP3FRM2lo3ACL3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS4segs1L2HI1h2SP3FRM2lo3FR03SPT1a1RS2SP3FRM2lo1a1l2l0S2SP3FRM2lo1a1l2l0S2SP3FRM2lo1a2l02l1S1L4DIMG2MC3MC13MC21d2D5S1L2SP3FRM2lo3ACL1a1B1k1C1R2B4S2dX2ws1a3HoX1CS1L2SP3FRM2lo3ACL3DHI1a2Ha1RS2MC2ws1a3HoC1R2SP3FRM2lo3FR01C1L2dX1G2GX3MC23MCX3MCG3ACL4LOSP3DHI2SX2GSS2dX2ws1a1C3HoXS3dX11a1RS3dX11a1l2l0S1L2SP3FRM2lo3ACL1d2D4S2MC1a1l2l0S2MC1a1l2l0S2MC1a2l02l1S2MC1a2l02l1S2MC1a2l12l2S2MC2SP3FRM2lo2ws1a2Ho1nS2MC2SP3FRM2lo2ws1a2Ho1nS2MC2SP3FRM2lo2ws1a2Ho1nS2MC2SP3FRM2lo3dX12ws1a2Ho1n2n0S2MC2SP3FRM2lo3dX12ws1a2Ho1n2n0S2MC2SP3FRM2lo3dX12ws1a2Ho1n2n0S2MC2SP3FRM2lo3dX12ws1a2Ho1n2n0". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_inv_munch : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Pm2,P,(2.&40.)(10.(2.&8.))Pws,(1.(2.&40.))Pcnt',(2.&40.)P,(5>.R12.R11.R10.R>.R=.R<.R;.(20.Vsegs,VL,VHI,R13.)R?.)P,(22.Vsegs,R;.R13.R12.)P,(5?.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(60.(61.R9.R>.R10.R?.R11.)R8.R6.)P,(62.Vsegs,R9.R7.)P,(1<.Vsegs,R8.)P,P,(7.$38.(39.R<.)$3:.)(6.(63.Vsegs,R:.(3;.R=.)R9.)(7.$0.(;.(<.(2.&40.)R9.))(3=.R=.)))P,P,(3?.(7.$38.(39.R=.)$3:.))(7.(1.(2.&40.))R:.(64.R>.))P,(2<.Vsegs,R;.R16.(27.$2=.(2>.R9.)(29.$2=.)))P,(1=.Vsegs,R<.R14.(49.R16.R15.))(5?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(65.R10.R<.)R=.R>.)")
(* [comment removed for export] *).
  Proof.
    (intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 m2 ws cnt' dd_H; ddestruct dd_H as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU); intros MA dd_H; ddestruct dd_H as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1); intros MU WM MI2 HU HN CNT2 ST2).
    dpose OUT1 as (EA1 & NS1 & K11 & K12 & K13).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as (XCW1 & _ & XP1).
    assert (HW : forall a, ~ outside (mm_fp dX1 lo SP FRM MC) a ->
              (md_own dX1 = LHeap /\ md_p dX1 <= a < md_p dX1 + 4 * md_n dX1) \/ lo <= a < SP - FRM \/ MC <= a < MC + 8).
    { intros a Ho. unfold mm_fp in Ho. destruct (md_own dX1); cbn in Ho.
      - destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (SP - FRM))|]; [right; left; lia| |]; (destruct (Z_le_dec MC a); [destruct (Z_lt_dec a (MC + 8))|]); try (right; right; lia); exfalso; apply Ho; lia.
      - destruct (Z_le_dec (md_p dX1) a); [destruct (Z_lt_dec a (md_p dX1 + 4 * md_n dX1)); [left; split; [reflexivity| lia]|]|];
        (destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (SP - FRM))|]; [right; left; lia| |]; (destruct (Z_le_dec MC a); [destruct (Z_lt_dec a (MC + 8))|]); try (right; right; lia); exfalso; apply Ho; lia).
      - destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (SP - FRM))|]; [right; left; lia| |]; (destruct (Z_le_dec MC a); [destruct (Z_lt_dec a (MC + 8))|]); try (right; right; lia); exfalso; apply Ho; lia. }
    assert (DJ : forall A n,
              (md_own dX1 = LHeap -> A + n <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= A) ->
              (A + n <= lo \/ SP - FRM <= A) -> (A + n <= MC \/ MC + 8 <= A) -> disjoint_from (mm_fp dX1 lo SP FRM MC) A n).
    { intros A n D1 D2 D3. unfold mm_fp. destruct (md_own dX1); cbn; repeat split; auto. }
    assert (DSTR : disjoint_from (mm_fp dX1 lo SP FRM MC) (md_addr dX1) 16).
    { rewrite EA1. apply DJ; [intros O; rewrite <- EA1; exact (XP1 O)| lia| lia]. }
    assert (HH2 : HEAP segs L HI h1 LB1 m2 mo1).
    { apply (HEAP_munch segs L HI h1 LB1 m1 m2 mo1 lo _ HH1 ACL MU WM). intros a Ha NO.
      destruct (HW a NO) as [[O R]|[R|R]].
      - right; right. pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. rewrite O in HO. ddestruct HO as (_ & IN & _).
        exists (md_p dX1, 4 * md_n dX1). split; [exact IN| cbn; lia].
      - left. rewrite HT1. lia.
      - right; left. split; [lia| apply (proj1 (MCS a R))]. }
    unfold mm_inv. refine (conj HH2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj MI2 (conj MF1 (conj HT1 (conj _ (conj (ex_intro _ cnt' CNT2) ST2))))))))))))).
    - destruct (md_own dX1) eqn:O.
      + rewrite (HN ltac:(congruence)), relimb_self. eapply mpd_at_munch; [exact MA1| rewrite O; discriminate| exact MU| exact WM| exact DSTR| intros O'; congruence].
      + destruct (HU eq_refl) as [U L1]. eapply relimb_at; [exact MA1| exact O| | exact U| exact L1].
        pose proof MA1 as [(CH & _) _]. eapply rw_cells_transport; [exact CH| exact MU| exact WM| cbn [cells_size csize Nat.add mpi_cells length]; exact DSTR].
      + exfalso; exact (NS1 eq_refl).
    - eapply mpd_out_ext; [exact OUT1| reflexivity| cbn; exact NS1| apply relimb_blk].
    - rewrite relimb_blk. exact FR1.
    - cbn. exact PAD1.
    - cbn. exact NLE1.
    - eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. destruct (outside_dec (mm_fp dX1 lo SP FRM MC) a) as [Hw|Hw]; [exact Hw| exfalso].
      rewrite outside_app in Ho. destruct Ho as [HoX HoC]. cbn in HoC.
      destruct (HW a Hw) as [[O R]|[R|R]]; [| | lia].
      + refine (new_limbs_apart segs L HI h1 LB LB1 m1 m1 mo1 SP dX dX1 a HH1 MA1 OUT1 FR1 ltac:(lia) (proj1 DIMG) (proj2 DIMG) Hc _ O R).
        intros OX C. unfold mpd_ivs in HoX. rewrite OX in HoX. cbn in HoX. lia.
      + destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|]. cbn in C.
        destruct (in_dec (fun x y : blk => ltac:(decide equality; apply Z.eq_dec)) (B, k) (mpd_blk dX)) as [I|NI].
        * unfold mpd_blk in I. unfold mpd_ivs in HoX. destruct (md_own dX); try (destruct I; fail). destruct I as [E|[]]. injection E as E1 E2. subst B k. cbn in HoX. lia.
        * pose proof (proj1 (Forall_forall _ _) HBR1 _ (K12 _ Hb NI)) as (_ & _ & _ & B4 & _). cbn in B4. lia.
    - eapply statics_ok_munch; [exact SOK1| exact MU|]. intros a Ha NWR. destruct (outside_dec (mm_fp dX1 lo SP FRM MC) a) as [Hw|Hw]; [exact Hw| exfalso].
      destruct (HW a Hw) as [[O R]|[R|R]]; [| lia| exact (NWR (proj2 (MCS a R)))].
      pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. rewrite O in HO. ddestruct HO as (_ & IN & _).
      exact (blk_off_data _ _ _ _ _ _ a HH1 IN Ha R).
    - eapply ecp_group_at_munch; [exact GR1| exact MU| exact WM| exact MI1| exact MI2| |].
      + apply DJ; [| lia| lia]. intros O.
        eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O].
      + intros d Hd HO. ddestruct (H1 d Hd HO) as (INd & NXd & APd). pose proof (grp_blocks_in _ _ _ _ _ _ GR1 Hd HO) as IN1.
        pose proof (proj1 (Forall_forall _ _) HBR1 _ IN1) as (_ & _ & _ & D4 & D5). cbn in D4, D5.
        pose proof GR1 as GRx.
        assert (DN1 : 1 <= md_n d).
        { ddestruct GRx as (HD' & AL' & POS' & EP' & EA' & EB' & EN' & MP' & MA' & MB' & (EX' & EY' & EZ' & MX' & MY' & MZ') & MN' & HT' & REST').
          assert (Hm : mpdr_at segs m1 LB1 d) by (unfold grp_mpds in Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
          ddestruct Hm as (_ & _ & _ & _ & _ & HOd). rewrite HO in HOd. exact (proj1 HOd). }
        assert (NX1 : ~ In (md_p d, 4 * md_n d) (mpd_blk dX1)).
        { intros C. destruct (FR1 _ C) as [C'|C']; [exact (NXd C')| exact (C' INd)]. }
        apply DJ; [| clear - D4 ACL DN1; lia| pose proof DIMG; clear - D5 DIMG MC1 MC2 DN1; lia].
        intros O1. pose proof MA1 as [(_ & _ & _ & _ & _ & HO') _]. rewrite O1 in HO'. ddestruct HO' as (XN1 & INX & _).
        destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [_ HAP1].
        pose proof (blocks_apart_neq _ _ _ HAP1 IN1 INX ltac:(intros E; apply NX1; unfold mpd_blk; rewrite O1, <- E; left; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as AP.
        cbn in AP. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L41598391688.74L43548634088.6700000H00dS1L2SP3FRM2lo3dX13ACL2B4S1L2MC2SP3FRM2lo3MC23ACL3DHI". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_inv_callee : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Pm2,P,(2.&40.)(10.(2.&8.))PW,(1.$53.)P,(5>.R11.R10.R?.R=.R<.R;.R:.(20.Vsegs,VL,VHI,R12.)R>.)P,(22.Vsegs,R:.R12.R11.)P,(5?.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(60.R4.R7.R5.)P,(62.Vsegs,R8.R6.)P,(1<.Vsegs,R7.)P,(66.R7.(27.(4.$0.$0.)(5.$0.$0.R10.(49.R12.R11.))(29.(4.$0.$0.))))P,(1=.Vsegs,R9.R11.(49.R13.R12.))(5?.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R:.R;.)")
(* [comment removed for export] *).
  Proof.
    intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 m2 W BASE MA INV MU WM MI2 SUB ST2.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    pose proof (munch_weaken _ _ _ _ SUB MU) as MU'.
    rewrite <- (relimb_self dX1). eapply mm_inv_munch with (m1 := m1) (cnt' := cnt1); [exact BASE| exact MA| exact INV| | exact WM| exact MI2| | intros; reflexivity| | exact ST2].
    - eapply munch_weaken; [| exact MU']. unfold sub_fp, mm_fp. intros x Hx. rewrite outside_app in Hx. destruct Hx as [_ Hx]. cbn in Hx |- *. tauto.
    - intros O. pose proof MA1 as [(_ & _ & _ & HL & _ & HO) _]. rewrite O in HO. ddestruct HO as (N1 & IN & _ & U).
      destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _]. pose proof (proj1 (Forall_forall _ _) HBR1 _ IN) as (_ & _ & _ & B4 & _). cbn in B4.
      split; [| exact HL]. eapply u32arr_transport; [exact U| exact MU'| exact WM| cbn; rewrite HL; lia].
    - eapply rw_cells_transport; [exact CNT1| exact MU'| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L10307417967.128L1505727538.163 L17614601653.163L19101885067.126L26750611769.128L28307920045.128L28308183981.125L28312246799.148L3814621258.128 L53932173258.130L59899591961.128L61486973795.126L64096697315.162L9585927532.128 00000;01001J01b02J02S03=03F03T03m04:04\05005BS1L3SP'3DHIS1L2SP3FRM2lo3dX13SP'3FRA3FRC3ESP3FRL3ACL4LOSP3SPB2I4S3SP'3FRA3FRC3FRL3SPB1a2HaS2SP3FRM3SP'3ESP3FR03SPBS4segs1L2HI1h2SP3FRM3SP'3ESP3FR03SPT3SPBS3SP'3SPBS1L2SP3FRM2lo3SP'3ESP3ACP3ACL3FR04LOSP3SPUS3SP'3SPBS1L2lo3SP'3ACLS1L2lo3dX13SP'3ACL3SPB2I4S3SP'3SPA3SPBS1L2SP3FRM2lo3SP'3ESP3ACL4LOSP3SPBS2dX3SP'3FRA3FRC3FRXS1L2lo3STK3SP'3SLO". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_call_binop : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PENTRY,$0.PMSF,$0.PSTK,$0.PSP',$0.PR,P,(1.$13.)P,$14.P,$14.P,$14.P,$0.P,$14.SpPdA,$14.PdB,$14.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)PQ,P,$?.SpPFRA,$0.PFRC,(1.$2=.)P,(67.Vsegs,VL,VHI,R2:.R29.R28.R26.)P,PLB0,(1.$13.)Pd0,$14.PdA0,$14.PdB0,$14.Pr,$0.Pd1,$14.P,A6.R2=.R6.R5.R4.R3.R2.R1.(68.R7.R6.R2.)P,(5>.R3;.R3:.R39.R37.R36.R35.R34.(20.Vsegs,VL,VHI,R3<.)R38.)P,(22.Vsegs,R34.R3<.R3;.)P,(5?.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.)P,(7.$0.R2<.(49.R39.R38.))P,(2<.Vsegs,R32.R8.R7.)P,(:.R2>.R9.)P,(36.(:.(28.(37.R40.)+10.)R:.)(:.(28.R:.(;.(55.R9.)))(37.R40.)))P,(22.Vsegs,R35.R37.R2>.)P,(22.Vsegs,R36.R38.R2>.)P,(3>.R38.R30.)P,(3>.R39.R30.)P,(3>.R32.R31.)P,(41.R3;.R33.R40.R35.)P,(41.R3<.R33.R41.R36.)P,(35.VL,R3>.R42.(37.R35.)+10.)P,P,(7.$38.(39.R36.)$3:.)(35.VL,R40.R44.(3;.R37.)(3<.+4.(3=.R37.)))P,(35.VL,R40.R44.(37.R36.)+10.)P,P,(7.$38.(39.R37.)$3:.)(35.VL,R42.R46.(3;.R38.)(3<.+4.(3=.R38.)))P,(:.R46.(49.(49.R3;.R3<.)(4:.VL,)))P,(:.=(4:.VL,))P,(7.$0.(8.R3=.+10.)=)P,(7.(2.&40.)R38.(18.&40.(4<.VL,)))P,(4=.VL,R41.+8.)P,(7.(2.&40.)R34.(18.&40.(37.R51.)))P,(7.(2.&40.)R34.(18.&40.(37.R3?.)))P,(7.(2.&40.)R34.(18.&40.(37.R3?.)))P,Pm2,P,(2.&40.)(10.(2.&8.))Pmo2,$11.Ph2,(12.Vsegs,VL,VHI,)PLB2,(1.$13.)PdX2,$14.Pr,$0.Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(5?.R6;.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R61.R60.R12.R11.R10.R14.R13.)P,(2<.Vsegs,R15.R33.R32.)P,A6.R58.R60.R5?.R57.R56.R11.R12.P,(24.Vsegs,VL,R61.R5:.(26.R60.)R5?.R17.)(4>.Vsegs,R17.R37.(16.(17.R57.(18.&40.R5;.)R56.R55.R12.R11.R10.R51.R50.(18.&40.R13.)R?.R>.R=.R<.R;.R:.R9.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R8.R7.R6.R5.)R39.(19.R57.)R38.(1:.(2.&40.))R18.(1;.Vsegs,)))(4>.Vsegs,R48.R20.(16.(17.R40.(18.&40.R44.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(18.&40.R47.)R21.(1:.(2.&40.))R49.(1;.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until FRC. intros ST RK BASE MA INV ESP FR FRL FRX MAA MAB SXA SXB SAB OA OB CRA CRAL CRB CRBL SLO HLS SPA TP CA -> -> -> K.
    pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    assert (SPB : 0 <= SP' < 2^64) by lia.
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP' _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as XW1. rewrite <- HT1 in XW1.
    assert (XSL1 : md_own dX1 <> LNull -> md_p dX1 + 4 * md_n dX1 <= lo \/ SP' <= md_p dX1).
    { intros NN. destruct (md_own dX1) eqn:O; [exfalso; congruence| | exfalso; congruence].
      ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & _ & I4 & _). left. lia. }
    unfold mpi_binop_stmt in ST.
    eapply aevtM_cut.
    { eapply ST with (lo := lo) (h := h1) (LB := LB1) (dX := dX1) (dA := dA) (dB := dB); rewrite ?(unsigned_lit SP') by lia;
        first [ exact HH1 | exact MA1 | exact MAA | exact MAB | exact SXA | exact SXB | exact SAB | exact NS1 | exact OA | exact OB
              | exact CRA | exact CRAL | exact CRB | exact CRBL | exact XW1 | exact XSL1 | exact TP | exact SOK1 | exact CA | exact MI1
              | rewrite EA1; reflexivity | reflexivity
              | match goal with |- stk _ _ _ _ => rewrite ESP; exact ST1 end
              | rewrite HT1; lia
              | lia ]. }
    clear ST. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dX2 & r & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit SP') in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & RR).
    pose proof (RK _ _ _ _ _ _ RR) as (EA2 & PAD2 & FR2 & NLE2).
    eapply K; [| | exact RR| exact PX2].
    - eapply mm_inv_binop; [exact BASE| exact MA| exact INV| exact HH2| exact MA2| exact OUT2| exact FR2| exact PAD2| exact NLE2| rewrite <- ESP; exact PX2| exact SOK2| exact MI2| exact MF2| exact HT2| rewrite <- ESP; exact ST2].
    - eapply heap_presx_rw_cells; [exact PX2| exact FR| intros a Ha; left; lia|].
      unfold mpd_ivs. rewrite EA1. destruct (md_own dX1) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; congruence].
      split; [| exact I]. ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & _ & I4 & _). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L57051602729.94L59310684262.94L59315053158.97L5952735238.93 00000J00V00b012S1L2SP3FRM2lo3ACL3FR04LOSPS2dX1a1R3HoXS2dX1a3HoX1CS2SP3FRM3FR01a1C". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_inv_mulmod : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Ph2,(12.Vsegs,VL,VHI,)PLB2,(1.$13.)PdX2,$14.Pm2,P,(2.&40.)(10.(2.&8.))Pmo2,$11.Pcnt2,(2.&40.)P,(5>.R15.R14.R13.R11.R10.R?.R>.(20.Vsegs,VL,VHI,R16.)R12.)P,(22.Vsegs,R>.R16.R15.)P,(5?.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(21.Vsegs,VL,VHI,R9.R8.R6.R5.)P,(22.Vsegs,R7.R9.R8.)P,(23.R?.R>.R:.R9.)P,Pb,$13.P,(3.$13.R1.(5:.R;.))(36.(3.$13.R2.(5:.R11.))(3?.(3.$13.R2.R12.)))P,(7.(2.&40.)(5;.R;.)(5;.R10.))P,(:.(3=.R11.)(3=.R<.))P,(24.Vsegs,VL,R13.(49.R19.R18.)(25.(4.$0.$0.)(26.R12.)(27.(4.$0.$0.)(5.$0.$0.R1:.(28.R1:.+8.))(29.(4.$0.$0.))))R11.R<.)P,(2:.Vsegs,VL,R=.)P,(1<.Vsegs,R>.)P,(1?.R13.R>.)P,(7.$0.(20.Vsegs,VL,VHI,R13.)(20.Vsegs,VL,VHI,R18.))P,(2;.Vsegs,R25.R11.R13.R21.R20.)P,(2<.Vsegs,R12.R20.(27.$2=.(2>.R10.)(29.$2=.)))P,(1=.Vsegs,R13.R1>.(49.R20.R1?.))(5?.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R17.R16.R15.R14.R13.)")
(* [comment removed for export] *).
  Proof.
    (intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 h2 LB2 dX2 m2 mo2 cnt2 dd_H; ddestruct dd_H as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU); intros MA dd_H; ddestruct dd_H as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1); intros HH2 MA2 OUT2 FR2 PAD2 NLE2 PX2 SOK2 MI2 MF2 HT2 GR2 CNT2 ST2).
    dpose OUT1 as (EA1 & NS1 & K11 & K12 & K13). dpose OUT2 as (EA2 & NS2 & K21 & K22 & K23).
    assert (FR' : forall b, In b (mpd_blk dX2) -> In b (mpd_blk dX) \/ ~ In b LB).
    { intros b Hb. destruct (FR2 b Hb) as [H|H]; [exact (FR1 b H)|].
      destruct (in_dec (fun x y : blk => ltac:(decide equality; apply Z.eq_dec)) b (mpd_blk dX)) as [I|NI]; [left; exact I| right].
      intros C. exact (H (K12 b C NI)). }
    assert (CL : forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside (mpd_ivs dX ++ [(MC, MC + 8)]) a ->
                 client_addr L LB1 (SP - FRM) a /\ outside (mpd_ivs dX1 ++ [(MC, MC + 8)]) a).
    { intros a Ha Hc Ho. rewrite outside_app in Ho. destruct Ho as [HoX HoC].
      split.
      - destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
        exists (B, k). split; [| exact R]. apply K12; [exact Hb|]. intros HX.
        unfold mpd_blk in HX. unfold mpd_ivs in HoX. destruct (md_own dX); try (destruct HX; fail). destruct HX as [E|[]]. injection E as E1 E2. subst B k.
        cbn in R, HoX. lia.
      - rewrite outside_app. split; [| exact HoC].
        unfold mpd_ivs. rewrite EA1. cbn. split; [unfold mpd_ivs in HoX; cbn in HoX; exact (proj1 HoX)|].
        destruct (md_own dX1) eqn:O1; cbn; [exact I| | exfalso; exact (NS1 eq_refl)].
        split; [| exact I].
        pose proof (new_limbs_apart segs L HI h1 LB LB1 m1 m1 mo1 SP dX dX1 a HH1 MA1 OUT1 FR1 ltac:(lia) (proj1 DIMG) (proj2 DIMG) Hc) as NL.
        apply NL; [| exact O1]. intros O C. unfold mpd_ivs in HoX. rewrite O in HoX. cbn in HoX. lia. }
    unfold mm_inv. refine (conj HH2 (conj MA2 (conj _ (conj FR' (conj (eq_trans PAD2 PAD1) (conj (Z.le_trans _ _ _ NLE1 NLE2) (conj _ (conj SOK2 (conj MI2 (conj _ (conj (eq_trans HT2 HT1) (conj GR2 (conj (ex_intro _ cnt2 CNT2) ST2))))))))))))).
    - eapply mpd_out_trans; [exact OUT1| exact OUT2| exact FR1| exact XIN].
    - eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_weaken2; [exact PX2|]. exact CL.
    - eapply mo_frame_trans; [exact MF1| exact MF2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L10307074159.130L1051139855.129 L1507846670.170 L17614601653.170L19101885067.125L19808327423.130L22204372049.130L26750369337.130L28308183981.124L28308364205.130L28312246799.151L3814281034.130 L45531630318.130L53860901346.129L53938477558.130L57055874877.129L58407309155.168L59899703833.130L61486973795.125L64096697315.169L9585715820.130 00000;00@01j02D02\02j04=04e05O05X05a05o06=06Y08?08a09Z09g0:I0:]0:oS1L3SP'3DHIS3SP'S1L4DIMG2dX1G2MC2SP3FRM2lo3LB13dX13SP'3FRA3FRC3ESP3FRL3FRX2GX3MC13MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS3SPB1HS3SP'3FRA3FRC3FRL3SPB1a2HaS2SP3FRM3SP'3ESP3FR03SPBS1L2MC3SP'3MC2S1L2dX1G2MC2SP3FRM2lo3SP'3FRA3FRC3ESP3FRL2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS3SPBS4segs1L2HI1h2SP3FRM3SP'3ESP3FR03SPT3SPBS1L2SP3FRM2lo3SP'3ESP3ACP3ACL3FR04LOSP3SPUS3SP'3SPBS3SP'3SPBS1L2lo3SP'3ACLS1L2MC3SP'3MC1S2SP3FRM2lo3SP'3FR04LOSP3SPBS1L4DIMG2dX1G2MC2SP3FRM2lo3LB13dX13SP'3FRA3FRC3ESP3FRL2GX3MC13MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS3SPB1HS1L2SP3FRM2lo3SP'3ACL3FR04LOSP3SPBS1L2MC2SP3FRM2lo3SP'3FRA3FRC3ESP3FRL3MC23ACL4LOSP3DHI3SPBS3SP'3SPA3SPBS1L2SP3FRM2lo3SP'3ESP3ACL4LOSP3SPBS2dX3SP'3FRA3FRC3FRXS1L2lo3STK3SP'3SLO". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_call_mulmod : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PENTRY,$0.PMSF,$0.PSTK,$0.PSP',$0.PdA,$14.PdB,$14.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)PQ,P,$?.SpPFRA,$0.PFRC,(1.$2=.)P,(69.Vsegs,VL,VHI,R3:.R29.R28.R34.R27.)P,(5>.R39.R38.R37.R35.R34.R33.R32.(20.Vsegs,VL,VHI,R3:.)R36.)P,(22.Vsegs,R32.R3:.R39.)P,(7.$0.(32.R38.)+1.)P,(7.$0.(33.(34.R39.))+1.)P,(5?.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.)P,(7.$0.R2<.(49.R39.R38.))P,(2<.Vsegs,R32.R9.R8.)P,(:.R2>.R:.)P,(36.(:.(28.(37.R40.)+10.)R;.)(:.(28.R;.(;.(55.R:.)))(37.R40.)))P,(22.Vsegs,R35.R37.R2?.)P,(22.Vsegs,R36.R38.R2?.)P,(3>.R38.R31.)P,(3>.R39.R31.)P,(3>.R33.R32.)P,(41.R3;.R34.R40.R35.)P,(41.R3<.R34.R41.R36.)P,(35.VL,R3>.R42.(37.R36.)+10.)P,P,(7.$38.(39.R37.)$3:.)(35.VL,R40.R44.(3;.R38.)(3<.+4.(3=.R38.)))P,(35.VL,R40.R44.(37.R37.)+10.)P,P,(7.$38.(39.R38.)$3:.)(35.VL,R42.R46.(3;.R39.)(3<.+4.(3=.R39.)))P,(:.R46.(49.(49.R3;.R3<.)(4:.VL,)))P,(:.=(4:.VL,))P,(7.$0.(8.R3=.+10.)=)P,(7.(2.&40.)R39.(18.&40.(4<.VL,)))P,(4=.VL,R41.+8.)P,(7.(2.&40.)R35.(18.&40.R50.))P,(7.(2.&40.)R35.(18.&40.(37.R52.)))P,(7.(2.&40.)R35.(18.&40.(37.R41.)))P,(7.(2.&40.)R35.(18.&40.(37.R41.)))P,Pm2,P,(2.&40.)(10.(2.&8.))Pmo2,$11.Ph2,(12.Vsegs,VL,VHI,)PLB2,(1.$13.)PdX2,$14.Pr,$0.Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(5?.R6<.R6;.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R61.R12.R11.R10.R14.R13.)P,(2<.Vsegs,R15.R35.R34.)P,(68.R61.R60.R12.)P,(24.Vsegs,VL,R62.R5;.(25.(4.$0.$0.)(26.R61.)(27.(4.$0.$0.)(5.$0.$0.R69.(28.R69.+8.))(29.(4.$0.$0.))))R60.R17.)P,(6.(46.(6:.(5=.+2.+1?.))R13.)(:.R13.=))(4>.Vsegs,R18.R3:.(16.(17.R5:.(18.&40.R5=.)R59.R58.R13.R12.R11.R54.R53.(18.&40.R14.)R10.R?.R>.R=.R<.R;.R:.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R9.R8.R7.R6.)R3<.(19.R5:.)R3;.(1:.(2.&40.))R19.(1;.Vsegs,)))(4>.Vsegs,R49.R22.(16.(17.R42.(18.&40.R45.)R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(18.&40.R48.)R23.(1:.(2.&40.))R4:.(1;.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until FRC. intros ST BASE MA GH1 GPS INV ESP FR FRL FRX MAA MAB SXA SXB SAB OA OB CRA CRAL CRB CRBL SLO HLS SPA TP CA -> -> -> -> K.
    pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    assert (SPB : 0 <= SP' < 2^64) by lia.
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP' _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as XW1. rewrite <- HT1 in XW1.
    assert (XI : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling
                                     /\ (md_p dX1 + 4 * md_n dX1 <= hl_img_lo L \/ hl_img_hi L <= md_p dX1)).
    { intros O. exact (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1). }
    assert (XSL1 : md_own dX1 <> LNull -> md_p dX1 + 4 * md_n dX1 <= lo \/ SP' <= md_p dX1).
    { intros NN. destruct (md_own dX1) eqn:O; [exfalso; congruence| | exfalso; congruence]. pose proof (XI eq_refl). left. lia. }
    assert (GX1 : md_own dX1 = LHeap -> G + 192 <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= G).
    { intros O. eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O]. }
    assert (GCR1 : client_range L LB1 lo G 192).
    { eapply client_range_out; [intros a Ha; apply GCR; exact Ha| exact OUT1| exact GXL| lia]. }
    unfold ecp_mul_mod_stmt in ST.
    eapply aevtM_cut.
    { eapply ST with (lo := lo) (h := h1) (LB := LB1) (dX := dX1) (dA := dA) (dB := dB) (G := G) (g := g) (cnt := cnt1); rewrite ?(unsigned_lit SP') by lia;
        first [ exact HH1 | exact GR1 | exact GH1 | exact GPS | exact GCR1 | exact MA1 | exact MAA | exact MAB | exact SXA | exact SXB | exact SAB | exact NS1 | exact OA | exact OB
              | exact CRA | exact CRAL | exact CRB | exact CRBL | exact XW1 | exact XSL1 | exact CNT1 | exact MCS | exact TP | exact SOK1 | exact CA | exact MI1
              | rewrite EA1; reflexivity | reflexivity
              | rewrite EA1; exact GX | rewrite EA1; exact MCX | exact GX1 | exact MCG
              | match goal with |- stk _ _ _ _ => rewrite ESP; exact ST1 end
              | rewrite HT1; lia
              | lia ]. }
    clear ST. cbv beta. intros ms' mo' PO. unfold ecp_mul_mod_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dX2 & r & cnt2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit SP') in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & GR2 & CNT2 & RR).
    pose proof RR as [Hr2 RR']. dpose RR' as (EA2 & PAD2 & FR2 & NLE2).
    eapply K; [| | exact RR'| exact PX2| exact Hr2].
    - eapply mm_inv_mulmod; [exact BASE| exact MA| exact INV| exact HH2| exact MA2| exact OUT2| exact FR2| exact PAD2| exact NLE2| rewrite <- ESP; exact PX2| exact SOK2| exact MI2| exact MF2| exact HT2| exact GR2| exact CNT2| rewrite <- ESP; exact ST2].
    - eapply heap_presx_rw_cells; [exact PX2| exact FR| intros a Ha; left; lia|].
      rewrite disjoint_from_app. split.
      + unfold mpd_ivs. rewrite EA1. destruct (md_own dX1) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; congruence].
        split; [| exact I]. pose proof (XI eq_refl). lia.
      + cbn. split; [lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L10307417967.122L1505727538.157 L17614601653.157L18247599989.122L19101885067.120L26750611769.122L28307920045.122L28308183981.119L28312246799.142L3814621258.122 L53932173258.124L59899591961.122L61486973795.120L64096697315.15600000;00h01B01P01h02P02Y03F03O03]04604C04]051S1L3SP'3DHIS1L2lo3dX13SP'3FRA3FRC3FRL3SLO3HLS3ACL3SPB2I4S3SP'3FRA3FRC3FRL3SPB1a2HaS1L2lo3SP'3SLOS2SP3FRM3SP'3ESP3FR03SPBS4segs1L2HI1h2SP3FRM3SP'3ESP3FR03SPT3SPBS3SP'3SPBS1L2SP3FRM2lo3SP'3ESP3SLO3HLS3ACP3ACL3FR03SPUS3SP'3SPBS1L2lo3SP'3ACLS1L2lo3dX13SP'3ACL3SPB2I4S3SP'3SPA3SPBS1L2lo3SP'3SLO3HLS3ACL3SPBS2dX3SP'3FRA3FRC3FRX". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_call_intop : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PENTRY,$0.PMSF,$0.PSP',$0.PR,P,(1.$13.)P,$14.P,$14.P,$0.P,$0.P,$14.SpPdA,$14.Pb,$0.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)PQ,P,$?.SpPFRA,$0.PFRC,(1.$2=.)P,(6;.Vsegs,VL,VHI,R29.R28.R26.)P,PLB0,(1.$13.)Pd0,$14.PdA0,$14.Pb0,$0.Pr,$0.Pd1,$14.P,A6.R2=.R6.R5.R4.R3.R2.R1.(68.R7.R6.R2.)P,(5>.R3:.R39.R38.R36.R35.R34.R33.(20.Vsegs,VL,VHI,R3;.)R37.)P,(22.Vsegs,R33.R3;.R3:.)P,(5?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)P,(7.$0.R2<.(49.R38.R37.))P,(2<.Vsegs,R31.R8.R7.)P,(:.R2>.R9.)P,(36.(:.(28.(37.R3?.)+10.)R:.)(:.(28.R:.(;.(55.R9.)))(37.R3?.)))P,(22.Vsegs,R34.R36.R2>.)P,(3>.R36.R2?.)P,(41.R37.R30.R3<.R32.)P,(35.VL,R39.R3=.(37.R31.)+10.)P,P,(7.$38.(39.R32.)$3:.)(35.VL,R3;.R3?.(3;.R33.)(3<.+4.(3=.R33.)))P,(6.(:.(6:.(5=.+2.+1?.))R32.)(46.R32.(5=.+2.+1?.)))P,(:.R40.(49.(49.R36.+100.)(4:.VL,)))P,(:.=(4:.VL,))P,(7.$0.(8.R38.+10.)=)P,(7.(2.&40.)R33.(18.&40.(4<.VL,)))P,(4=.VL,R3;.+8.)P,(7.(2.&40.)R2?.(18.&40.(37.R4;.)))P,(7.(2.&40.)R2?.(18.&40.(37.R3:.)))P,(7.(2.&40.)R2?.(18.&40.R3:.))P,Pm2,P,(2.&40.)(10.(2.&8.))Pmo2,$11.Ph2,(12.Vsegs,VL,VHI,)PLB2,(1.$13.)PdX2,$14.Pr,$0.Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(5?.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R12.R11.R10.R14.R13.)P,(2<.Vsegs,R15.R2>.R2=.)P,A6.R53.R5:.R59.R52.R51.R11.R12.P,(24.Vsegs,VL,R5;.R55.(26.R5:.)R59.R17.)(4>.Vsegs,R17.R32.(16.(17.R52.(18.&40.R56.)R51.R50.R12.R11.R10.R4<.R4;.(18.&40.R13.)R?.R>.R=.R<.R;.R:.R9.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R8.R7.R6.R5.)R34.(19.R52.)R33.(1:.(2.&40.))R18.(1;.Vsegs,)))(4>.Vsegs,R42.R1;.(16.(17.R3;.(18.&40.R3?.)R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(18.&40.R41.)R1<.(1:.(2.&40.))R43.(1;.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until FRC. intros ST RK BASE MA INV ESP FR FRL FRX MAA SXA OA CRA CRAL HB SLO HLS SPA TP CA -> -> -> K.
    pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    assert (SPB : 0 <= SP' < 2^64) by lia.
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP' _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as XW1. rewrite <- HT1 in XW1.
    assert (XSL1 : md_own dX1 <> LNull -> md_p dX1 + 4 * md_n dX1 <= lo \/ SP' <= md_p dX1).
    { intros NN. destruct (md_own dX1) eqn:O; [exfalso; congruence| | exfalso; congruence].
      ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & _ & I4 & _). left. lia. }
    unfold mpi_intop_stmt in ST.
    eapply aevtM_cut.
    { eapply ST with (lo := lo) (h := h1) (LB := LB1) (dX := dX1) (dA := dA) (b := b); rewrite ?(unsigned_lit SP') by lia;
        first [ exact HH1 | exact MA1 | exact MAA | exact SXA | exact NS1 | exact OA | exact CRA | exact CRAL | exact XW1 | exact HB | exact XSL1
              | exact TP | exact SOK1 | exact CA | exact MI1
              | rewrite EA1; reflexivity | reflexivity
              | match goal with |- stk _ _ _ _ => rewrite ESP; exact ST1 end
              | rewrite HT1; lia
              | lia ]. }
    clear ST. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dX2 & r & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit SP') in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & RR).
    pose proof (RK _ _ _ _ _ _ RR) as (EA2 & PAD2 & FR2 & NLE2).
    eapply K; [| | exact RR| exact PX2].
    - eapply mm_inv_binop; [exact BASE| exact MA| exact INV| exact HH2| exact MA2| exact OUT2| exact FR2| exact PAD2| exact NLE2| rewrite <- ESP; exact PX2| exact SOK2| exact MI2| exact MF2| exact HT2| rewrite <- ESP; exact ST2].
    - eapply heap_presx_rw_cells; [exact PX2| exact FR| intros a Ha; left; lia|].
      unfold mpd_ivs. rewrite EA1. destruct (md_own dX1) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; congruence].
      split; [| exact I]. ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & _ & I4 & _). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma mm_call_cmp : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PENTRY,$0.PSP',$0.PdY,$14.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)PQ,P,$?.SpP,(6<.Vsegs,R24.)P,(5?.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)P,(22.Vsegs,R28.R2:.R24.)P,P,(7.$38.(39.R25.)$3:.)(46.=(3;.R26.))P,(7.(2.&40.)R1=.(18.&40.(37.R36.)))P,(7.(2.&40.)R1=.(18.&40.(37.R27.)))P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)(4>.Vsegs,R39.R15.(16.(17.R35.(18.&40.R37.)R34.R33.R>.R=.R<.R2?.R2>.(18.&40.(6=.(49.(6>.R3;.)(6>.R36.))))R;.R:.R9.R8.R7.R6.R5.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R4.R3.R2.R1.)R17.(19.R35.)R16.(1:.(2.&40.))R3:.(1;.Vsegs,)))(4>.Vsegs,R2<.R8.(16.(17.R28.(18.&40.R2:.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(18.&40.R2;.)R9.(1:.(2.&40.))R2=.(1;.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until Q. intros ST INV MY PY -> -> K.
    dpose INV as (HH1 & MA1 & OUT1 & _ & _ & _ & _ & _ & MI1 & _). dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    unfold mpi_cmp_mpi_stmt in ST.
    eapply aevtM_cut_evt; [exact MK| eapply ST with (LB := LB1) (dX := dX1) (dY := dY); [exact MA1| exact MY| | exact PY| exact MI1| rewrite EA1; reflexivity| reflexivity] |].
    { intros O. ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & I3 & _). exact I3. }
    cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _). apply K.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L22704459657.121L28312458259.99 L28314212397.102L28314327212.121L3820915914.102 L38640302148.8  L40155795159.103L44155690288.102L53136232046.102L53938477558.104L56041779361.121L59355459711.104L59905880473.10200001A01j02302<02J02c03403@03V03n04?04L04YS1L2dX1G2MC2SP3FRM2lo3FRA3FRC3FRL3SLO2GX3MC23MCX3MCG3ACL3FR03DHI2SX2GS3SPB2xx3HxxS1L2SP3FRM2lo3SP'3ESP3SLO3ACP3ACL3FR03SPUS3SP'3SPBS3SP'3SPBS1L2lo3SP'3ACLS2dX2SP3FRM2lo3SP'3ESP2SXS1L3dX13SP'2I32I4S2lo3SP'3SLOS1L2lo3SP'3ACP3ACL3SPBS1L2lo3dX13SP'3ACL3SPB1HS3SP'3FRA3FRC3FRLS1L3dX13SP'1HS3SP'3SPA3SPB". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_call_cmpint : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.PENTRY,$0.PSP',$0.Pz,$0.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)PQ,P,$?.SpPFRA,$0.PFRC,(1.$2=.)P,(6?.VL,Vsegs,R26.)P,(5>.R36.R35.R34.R32.R31.R30.R2?.(20.Vsegs,VL,VHI,R37.)R33.)P,(22.Vsegs,R2?.R37.R36.)P,(5?.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)P,(7.$0.R29.(49.R34.R33.))P,(2<.Vsegs,R2=.R7.R6.)P,(:.R2;.R8.)P,(36.(:.(28.(37.R3;.)+10.)R9.)(:.(28.R9.(;.(55.R8.)))(37.R3;.)))P,(6.(:.(6:.(5=.+2.+1?.))R2<.)(46.R2<.(5=.+2.+1?.)))P,(:.R37.(49.R2>.+20.))P,(7.$0.(8.R2?.+10.)=)P,(7.(2.&40.)R26.(18.&40.(37.R3?.)))P,(7.(2.&40.)R26.(18.&40.R30.))P,Pm2,P,(2.&40.)(10.(2.&8.))Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(5?.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R?.R43.)P,(2<.Vsegs,R10.R1?.R1>.)(4>.Vsegs,R45.R21.(16.(17.R41.(18.&40.R43.)R40.R3?.R10.R?.R>.R3;.R3:.(18.&40.(6=.(49.(6>.R47.)R42.)))R=.R<.R;.R:.R9.R8.R7.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R6.R5.R4.R3.)R23.(19.R41.)R22.(1:.(2.&40.))R11.(1;.Vsegs,)))(4>.Vsegs,R35.R11.(16.(17.R31.(18.&40.R33.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(18.&40.R34.)R12.(1:.(2.&40.))R36.(1;.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until FRC. intros ST BASE MA INV ESP FR FRL FRX HZ SLO SPA -> -> K.
    pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & _ & _ & _ & _ & _ & MI1 & _ & _ & _ & _ & ST1). dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    assert (SPB : 0 <= SP' < 2^64) by lia.
    assert (XI : md_own dX1 = LHeap -> 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (_ & _ & I3 & I4 & _). lia. }
    assert (XS1 : md_p dX1 + 4 * md_n dX1 <= lo \/ SP' <= md_p dX1).
    { pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. destruct (md_own dX1) eqn:O; [destruct HO as [-> ->]; left; lia| pose proof (XI eq_refl); left; lia| exfalso; congruence]. }
    unfold mpi_cmp_int_stmt in ST.
    eapply aevtM_cut_evt; [exact MK| eapply ST with (LB := LB1) (dX := dX1) (z := z) (lo := lo); rewrite ?(unsigned_lit SP') by lia;
      first [ exact MA1 | exact MI1 | exact HZ | exact XS1
            | match goal with |- stk _ _ _ _ => rewrite ESP; exact ST1 end
            | rewrite EA1; reflexivity | reflexivity
            | intros O; pose proof (XI O); lia
            | rewrite EA1; clear - SX ESP FR0; lia
            | lia ] |].
    cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU & WM & MI2 & ST2).
    rewrite ?(unsigned_lit SP') in MU, ST2 by lia.
    apply K.
    - eapply mm_inv_callee; [exact BASE| exact MA| exact INV| exact MU| exact WM| exact MI2| unfold sub_fp; cbn; intros xx Hxx; subst SP'; lia| rewrite <- ESP; exact ST2].
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L10182617272.58L45641679881.52L53559852582.55L53862983770.55L57049501343.52L61216221966.5800001>01B01S01g02A02KS1L4DIMG2dX1G2MC2SP3FRM2lo3LB13dX12GX3MC13MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1HS2SPS2dX2SP3FRM2lo2SXS2SP3FRM2lo3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS3dX11a2Ha". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_self_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.P,(5>.R?.R>.R=.R;.R:.R9.R8.(20.Vsegs,VL,VHI,R10.)R<.)P,(22.Vsegs,R8.R10.R?.)P,(5?.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(6.(3>.R6.R6.)(6.(41.R6.R6.R;.(49.R=.R<.))(6.(35.VL,R7.R;.(37.R6.)+10.)P,(7.$38.(39.R6.)$3:.)(35.VL,R8.R<.(3;.R7.)(3<.+4.(3=.R7.))))))")
(* [comment removed for export] *).
  Proof.
    intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 BASE MA INV. pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & _). dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as (XCW1 & _ & XP1).
    assert (XI : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling
                                     /\ (md_p dX1 + 4 * md_n dX1 <= hl_img_lo L \/ hl_img_hi L <= md_p dX1)).
    { intros O. exact (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1). }
    split; [left; reflexivity|]. split; [| split].
    - split; [| split; [exact XP1| split; [left; reflexivity| split; [rewrite EA1; lia|]]]].
      + intros NN. destruct (md_own dX1) eqn:O; [exfalso; congruence| exact (XP1 eq_refl)| exfalso; congruence].
      + intros NN. destruct (md_own dX1) eqn:O; [exfalso; congruence| pose proof (XI eq_refl); lia| exfalso; congruence].
    - eapply client_range_of_wrange; [exact XCW1| lia].
    - intros O a Ha. right; right. exists (md_p dX1, 4 * md_n dX1). split; [exact (proj1 (XI O))| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L1051139855.67 L12188118728.76L12933239261.74L13635500955.6 L15959008136.9 L27811309638.77L30615961706.79L30720216852.78L33670901889.76L45641679881.63L48299285212.74L48736977073.78L48815712669.74L51163419001.78L53860951877.72L57049501343.63L57055874877.67L58211865829.80L6279008304.9  L8929561634.79 00000100701J01]02;02E02O03l03o04305J05[05o06906O06i07C07O07j08;SS1d2N1S1L4DIMG2dX1G2MC2SP3FRM2lo1d3off4IMGC2O02O12GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1HS2dX1G3off2O02O12GXS1G2SP3FRM2lo3off2O02O13FR02GSS3dX11d2APS1d2N13PB1S4segs1L2dX1G2MC2SP3FRM2lo3dX12m11d4IMGC2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS3DHO2R02R12I51HS1dS2SPS1L4DIMG2dX1G2MC2SP3FRM2lo3dX11d3off4IMGC2O02O12GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1HS1d3DHL2N12P03PB1S1G1d3off2O02O11a2HaS1d2N13PB1S2SP3FRM2lo1d3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS1L2SP3FRM2lo3ACL3FR04LOSPS1L1d3PB12R1S1L2SP3FRM2lo1d4IMGC3ACL2R1S1d3DHL2N12P03PB1". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_grp_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Pd,$14.Poff,$0.P,Pa,$0.P,(7.$56.(57.Vsegs,(58.R1.))$59.)P,(6.(:.=R2.)(46.R2.(5=.+2.+40.)))(6.(:.(70.VL,)R3.)(46.R3.(71.VL,)))P,(:.(71.VL,)(4;.VL,))P,(5>.R13.R12.R11.R?.R>.R=.R<.(20.Vsegs,VL,VHI,R14.)R10.)P,(22.Vsegs,R<.R14.R13.)P,(5?.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(52.Vsegs,R9.R;.R7.)P,(3?.(7.$38.(39.R8.)$3:.))P,(36.(7.$0.(33.R9.)+1.)(7.$0.(33.R9.)-1.))P,(7.$0.(37.R:.)(28.R17.R9.))P,(:.=R:.)P,(:.(28.R;.+10.)+<0.)(6.(22.Vsegs,R?.R11.R=.)(6.(3>.R10.R=.)(6.(41.R10.R=.R15.(49.R17.R16.))(6.(35.VL,R11.R15.(37.R=.)+10.)P,(7.$38.(39.R=.)$3:.)(35.VL,R12.R16.(3;.R>.)(3<.+4.(3=.R>.)))))))")
(* [comment removed for export] *).
  Proof.
    intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 d off ROIMG IMGC BASE MA INV MD DOWN DSG ED O0 O1. pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & _ & _ & _ & _ & MI1 & _). dpose OUT1 as (EA1 & NS1 & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as (XCW1 & _ & XP1).
    assert (XI : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling
                                     /\ (md_p dX1 + 4 * md_n dX1 <= hl_img_lo L \/ hl_img_hi L <= md_p dX1)).
    { intros O. exact (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1). }
    assert (GX1 : md_own dX1 = LHeap -> G + 192 <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= G).
    { intros O. eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O]. }
    pose proof MA1 as [(CH1 & _) _]. unfold mpi_cells in CH1.
    dpose MD as (_ & _ & _ & DHL & DHN & DHO). unfold MPI_MAX_LIMBS in DHN.
    assert (DST : md_own d <> LNull -> 1 <= md_n d /\ 0 < md_p d /\ (forall i, 0 <= i < 4 * md_n d -> ro_addr segs (wa (md_p d + i)) = true)
                                      /\ hl_img_lo L <= md_p d /\ md_p d + 4 * md_n d <= hl_img_hi L).
    { intros NN. destruct (md_own d) eqn:OD; [exfalso; congruence| exfalso; congruence|].
      ddestruct DHO as (N1 & _ & P0 & PB & PRO). dpose PB as (PB0 & PB1 & _). rewrite u32s_length in PB1.
      pose proof (ROIMG _ (PRO 0 ltac:(lia)) ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
      pose proof (ROIMG _ (PRO (4 * md_n d - 1) ltac:(lia)) ltac:(lia)) as R1.
      refine (conj N1 (conj P0 (conj PRO (conj (proj1 R0) _)))). lia. }
    split; [split; [exact MD| exact DSG]|]. split; [right; rewrite EA1, ED; clear - GX O0 O1; lia|]. split; [| split].
    - split; [| split; [| split; [| split]]].
      + intros NN. ddestruct (DST NN) as (N1 & P0 & PRO & _).
        pose proof (rw_ro_apart m1 _ _ (md_p d) (4 * md_n d) MI1 CH1 ltac:(cbn; lia) ltac:(lia) PRO) as AP. cbn [cells_size csize Nat.add length] in AP. lia.
      + intros O. rewrite ED. pose proof (GX1 O). lia.
      + destruct (md_own dX1) eqn:OX; [right; left; congruence| | exfalso; congruence].
        destruct (md_own d) eqn:OD; [right; right; left; reflexivity| exfalso; congruence|].
        right; right; right. ddestruct (DST ltac:(congruence)) as (_ & _ & _ & R0 & R1). dpose (XI eq_refl) as (_ & _ & _ & _ & I5). pose proof DIMG. lia.
      + rewrite ED. clear - GS O0 O1 FR0. lia.
      + intros NN. ddestruct (DST NN) as (_ & _ & _ & R0 & R1). clear - R0 R1 IMGC ACL. lia.
    - rewrite ED. eapply client_range_out; [intros a Ha; apply GCR; lia| exact OUT1| intros O; pose proof (GXL O); lia| lia].
    - intros O. exfalso. exact (DOWN O).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ext_opnd (LB : list blk) (dX e : mpd) (MC SP lo : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "(6.(36.(:.(28.(37.O5.)+10.)(37.O4.))(:.(28.(37.O4.)+10.)(37.O5.)))(6.(41.O5.O4.O1.O2.)(6.(35.VL,O6.O1.(37.O4.)+10.)(6.P,(7.$38.(39.O4.)$3:.)(35.VL,O6.O1.(3;.O4.)(3<.+4.(3=.O4.)))(36.(:.(28.O3.+8.)(37.O4.))(:.(28.(37.O4.)+10.)O3.))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L12833543004.86L19604368837.84L30615961706.92L37273016624.84L37273016624.92L38238378935.84L45643516203.71L45706085618.17L4605449051.91 L4605515095.95 L48648084466.17L48736977073.91L49101071220.89L51163419001.91L57051483808.90L57051857853.71L57053776820.85L59308567803.83L59314873579.89L61765524811.83L6540301278.6  L65502346886.85L66811105477.89L68687814432.89L68687814432.93L7135969354.90 L8929561634.92 L8954595322.87 L9218444818.90 00001@01K01[03003N03T03X03e04105P05b06:06B06R07307M07n08709Q09^0:20:50:=0:E0:M0:U0:m0;50;AS1L2dX1G2MC2SP3FRM2lo1e4ESEP2S43EMC2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS4EPOS1HS2dX1e4ESEPS1e4EPOS3EN13PB1S1L2dX1G2MC2SP3FRM2lo1e4ESEP2S43EMC2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS4EPOS1a2Ha1CS1L2SP2lo1e3ACL4EPOS2B41a2Ha1CS2lo1eS2SPS2MC1e3EN12n0S2dX3dX11e1DS1L2dX1G2MC2SP3FRM2lo3dX11e4ESEP2S43EMC2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS4EPOS3PB12R02R12I5S1L2MC1e3MC13MC21nS1e4EPOS3EHL3EN13EP03PB1S2dX1e1HS1e4EPOS3EN13PB1S1L2SP3FRM2lo1e3ACL3FR04LOSP4EPOSS1L2SP3FRM2lo3ACL3FR04LOSPS1L2SP3FRM2lo1e3ACL3FR04LOSP4EPOSS2dX4ESEPS1L2dX1G2MC2SP3FRM2lo1e4ESEP2S43EMC2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS3XN14EPOS2E12E21HS2dX2MC1e3EMCS2SP3FRM2lo1e2S43FR0S1eS2MC1e1lS2dX1e1DS2dX1e1DS2MC1e1lS1e4EPOS3EHL3EN13EP03PB1S1e1a2HaS1e4EPOS3EN1". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_ext_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod ()) "PMT,(1.$50.)Ph,(12.Vsegs,VL,VHI,)PLB,(1.$13.)PdX,$14.PG,$0.Pg,$31.PMC,$0.PSP,$0.PFRM,$0.Plo,$0.Pm,P,(2.&40.)(10.(2.&8.))Pmo,$11.Ph1,(12.Vsegs,VL,VHI,)PLB1,(1.$13.)PdX1,$14.Pm1,P,(2.&40.)(10.(2.&8.))Pmo1,$11.Pe,$14.P,Pa,$0.P,(7.$56.(57.Vsegs,(58.R1.))$59.)P,(6.(:.=R2.)(46.R2.(5=.+2.+40.)))(6.(:.(70.VL,)R3.)(46.R3.(71.VL,)))P,(5>.R11.R10.R?.R=.R<.R;.R:.(20.Vsegs,VL,VHI,R12.)R>.)P,(22.Vsegs,R:.R12.R11.)P,(5?.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(1<.Vsegs,R<.)P,(22.Vsegs,R=.R15.R6.)P,(72.R16.R15.R7.R12.R11.R?.)(6.(22.Vsegs,R:.R<.R8.)(6.(3>.R;.R8.)(6.(41.R;.R8.R10.(49.R12.R11.))(6.(35.VL,R<.R10.(37.R8.)+10.)P,(7.$38.(39.R8.)$3:.)(35.VL,R=.R11.(3;.R9.)(3<.+4.(3=.R9.)))))))")
(* [comment removed for export] *).
  Proof.
    (intros MT h LB dX G g MC SP FRM lo m mo h1 LB1 dX1 m1 mo1 e ROIMG BASE MA INV MI0 ME dd_H; ddestruct dd_H as (ESEP & (S1 & S2 & S3 & S4 & S5) & CRE & CREL & EMC)).
    pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & _ & _ & PX1 & _ & MI1 & _). dpose OUT1 as (EA1 & NS1 & K11 & K12 & K13).
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (unlock _ (lock MA)) as MA0. destruct MA0 as [(_ & _ & _ & _ & _ & XHO) _].
    pose proof (mpd_writable_out h1 LB LB1 m m1 mo1 SP SP _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as (XCW1 & _ & XP1).
    assert (XI : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling
                                     /\ (md_p dX1 + 4 * md_n dX1 <= hl_img_lo L \/ hl_img_hi L <= md_p dX1)).
    { intros O. exact (mpdr_blk_facts segs L m1 LB1 dX1 (proj1 MA1) O HBR1). }
    pose proof ME as [(ECH & EAL & EPOS & EHL & EHN & EHO) ESG].
    (* [comment removed for export] *)
    assert (ECS : client_range L LB SP (md_addr e) 16).
    { intros a Ha. destruct (CRE a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    assert (EIN1 : md_own e = LHeap -> In (md_p e, 4 * md_n e) LB1 /\ (md_own dX = LHeap -> md_addr e = md_addr e /\
                   (md_p dX + 4 * md_n dX <= md_p e \/ md_p e + 4 * md_n e <= md_p dX))).
    { intros OE. rewrite OE in EHO. ddestruct EHO as (EN1 & EIN & _).
      assert (AP : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= md_p e \/ md_p e + 4 * md_n e <= md_p dX).
      { intros OX. destruct S3 as [E|[E|[E|E]]]; [exfalso; subst e; lia| exfalso; exact (E OX)| exfalso; congruence| exact E]. }
      split; [| intros OX; split; [reflexivity| exact (AP OX)]].
      apply K12; [exact EIN|]. intros HX. unfold mpd_blk in HX. destruct (md_own dX) eqn:OX; try (destruct HX; fail).
      destruct HX as [E|[]]. injection E as E1 E2. try rewrite OX in XHO. destruct XHO as (XN1 & _). pose proof (AP eq_refl). lia. }
    assert (ME1 : mpd_at segs m1 LB1 e).
    { split; [| exact ESG]. apply mpdr_at_LB_one with (LB := LB); [| intros OE; exact (proj1 (EIN1 OE))].
      eapply (mpdr_at_presx segs L); [exact (proj1 ME)| exact PX1| exact MI0| exact MI1| exact ECS| |].
      - rewrite disjoint_from_app. split; [| cbn; lia]. unfold mpd_ivs. destruct (md_own dX) eqn:OX; cbn; (split; [lia|]); [exact I| | exfalso; congruence].
        split; [| exact I]. exact (S2 eq_refl).
      - intros OE. destruct (EIN1 OE) as [IN1 AP]. pose proof EHO as EHO'. rewrite OE in EHO'. ddestruct EHO' as (_ & EIN0 & _). split; [exact EIN0|].
        rewrite disjoint_from_app. split; [| cbn].
        + unfold mpd_ivs. destruct (md_own dX) eqn:OX; cbn; (split; [pose proof (S1 ltac:(congruence)); lia|]); [exact I| | exfalso; congruence].
          split; [| exact I]. destruct (AP eq_refl) as [_ D]. lia.
        + split; [| exact I]. rewrite OE in EHO. ddestruct EHO as (EN1 & EIN & _).
          destruct (Z_le_dec (MC + 8) (md_p e)); [right; lia|]. destruct (Z_le_dec (md_p e + 4 * md_n e) MC); [left; lia|]. exfalso.
          pose proof (unlock _ (lock (proj1 INV))) as HH1'. clear - n n0 HH1' IN1 EN1 MC1 MC2 DIMG.
          apply (blk_off_data _ _ _ _ _ _ (Z.max (md_p e) MC) HH1' IN1); lia. }
    split; [exact ME1|]. split; [right; rewrite EA1; exact ESEP|]. split; [| split].
    - split; [| split; [| split; [| split]]].
      + intros NN. rewrite EA1. exact (S1 NN).
      + intros OX. (* [comment removed for export] *)
        eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact ECS| lia| exact S2| exact OX].
      + destruct (md_own dX1) eqn:OX; [right; left; congruence| | exfalso; congruence].
        destruct (md_own e) eqn:OE; [right; right; left; reflexivity| |].
        * destruct (EIN1 eq_refl) as [IN1 _].
          pose proof (proj1 (Forall_forall _ _) HBR1 _ IN1) as (B0 & _ & _ & B4 & _). cbn in B0, B4.
          assert (CRL : client_range L LB SP (md_p e) (4 * md_n e)).
          { intros a Ha. destruct (CREL eq_refl a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
          try rewrite OE in EHO. destruct EHO as (EN1 & _).
          enough (D : md_p e + 4 * md_n e <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= md_p e) by (right; right; right; lia).
          eapply (new_limbs_apart_range segs L HI) with (SP := SP); [exact HH1| exact MA1| exact OUT1| exact FR1| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact CRL| lia| | exact OX].
          intros OX0. destruct (EIN1 eq_refl) as [_ AP]. destruct (AP OX0) as [_ D]. lia.
        * right; right; right. try rewrite OE in EHO. ddestruct EHO as (EN1 & _ & EP0 & EPB & EPRO). dpose EPB as (PB0 & PB1 & _). rewrite u32s_length in PB1.
          pose proof (ROIMG _ (EPRO 0 ltac:(lia)) ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
          pose proof (ROIMG _ (EPRO (4 * md_n e - 1) ltac:(lia)) ltac:(lia)) as R1.
          dpose (XI eq_refl) as (_ & _ & _ & _ & I5). pose proof DIMG. lia.
      + clear - S4 FR0. lia.
      + intros NN. pose proof (S5 NN). lia.
    - eapply client_range_out; [exact CRE| exact OUT1| exact S2| lia].
    - intros OE a Ha. right; right. exists (md_p e, 4 * md_n e). split; [exact (proj1 (EIN1 OE))| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Facts.
