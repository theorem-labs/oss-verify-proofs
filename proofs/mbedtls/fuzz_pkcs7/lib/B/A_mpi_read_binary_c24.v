(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_read_binary P_mpi_core_read_be P_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA
     A_mpi_core_read_be A_mpi_zeroize_and_free A_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_resize_clear_c24 A_mpi_read_binary_stmt_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_read_binary_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear_c24.mpi_resize_clear_coreA_r_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_RESIZE_CLEAR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_read_be.mpi_core_read_be_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_read_be.A_MPI_CORE_READ_BE"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_r_c"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear.A_WRAP_CALLOC_RC"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear.A_ASAN_MEMSET_RC"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_read_be.A_ASAN_MEMCPY"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"].


(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09d3d0]).
Local Ltac zchk_new ::= constr:([0x09d370; 0x09d374; 0x09d378]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis RC : mpi_resize_clear_coreA_r_c asegs R HIA A_MPI_RESIZE_CLEAR.   (* [comment removed for export] *)
  Hypothesis RBE : mpi_core_read_be_stmtA asegs R HIA A_MPI_CORE_READ_BE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  Ltac rb_c24 OUT :=
    lazymatch goal with |- cnt24 ?LBx <= _ =>
      match goal with HHx : HM _ _ _ _ LBx _ _ |- _ =>
        eapply Z.le_trans; [exact (mpd_out_cnt24 _ _ _ _ (HND _ _ _ _ HHx) OUT)|] end end;
    rewrite cnt24_mpd_blk; cbn [md_own md_n];
    repeat match goal with H : ?o = LNull |- context [match ?o with _ => _ end] => rewrite H end;
    unfold chars_to_limbs, chars_to_limbs4 in *;
    match goal with |- context [w24 ?x] => pose proof (w24_range x) end; lia.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@C16256374831.206C17025492443.191C17025492443.205D11189028015.125D11189028015.126D21352466598.192D21361286062.206D2780638174.160 D35881667587.125D35881667587.126D50796826103.192D60109446735.206D62126113208.206D64663832884.161D64663832884.162D66259669316.206D939044794.206  K15589905402.125K15589905402.126K26954661751.206K42587433812.125K42587433812.126K45236282491.191K61093937827.191K61093937827.205L1086194813.4   L11612041415.3  L11741095640.118L11741095640.167L12325571988.0  L14563034913.4  L14670936645.6  L15384870889.34 L15599769723.3  L15756354262.4  L16256253080.7  L1685717371.0   L18758880466.4  L18758923363.3  L19042705481.5  L19354909044.119L1952400095.2   L19815123504.162L19947928356.193L19947928356.207L20371264721.34 L21156439898.2  L21373347848.1  L22250994847.34 L22253145629.23 L22700019210.1  L22961942245.0  L23100341967.167L24026900734.9  L25382082548.119L2686898818.7   L26892418956.1  L26924648792.119L26924648792.167L26957866193.4  L27155496209.23 L27157122963.34 L27474368965.34 L27904923810.171L27907458660.171L28119316683.10 L28119316683.20 L29428324939.5  L2977718986.3   L30741553502.0  L30845506093.23 L30847934639.34 L31378308326.121L31392867444.119L35653441506.7  L35715707057.4  L36677107144.208L37414286068.119L3828906950.207 L38948636245.0  L39172636981.0  L39280637297.0  L40281191306.3  L40834179097.121L42243601453.11 L42243601453.20 L42594106808.2  L43061363337.119L43442376564.118L43654564952.119L43654564952.167L4391286538.3   L44854121702.34 L44955438685.4  L45240669919.23 L45242252545.3  L45242771039.5  L46122776823.12 L46160487540.167L46164672060.164L47888100315.4  L48132467214.7  L49245667698.3  L49631015752.1  L5070353710.5   L50790809970.7  L50837052601.0  L51481567664.3  L51709126206.170L52391401406.174L52391401406.194L52419075592.0  L5255787696.164 L52641081140.8  L52756228405.2  L53519189168.117L547707976.3    L5479049730.1   L5541654300.23  L5543419294.34  L55715119632.117L5697346430.2   L5697878975.23  L5699963711.5   L59308585216.2  L59308585216.5  L59308586248.2  L59321100241.5  L59499841752.119L59499841752.167L59848891180.4  L60098763854.3  L60447862057.2  L60649149552.7  L61097676998.2  L62018535662.1  L64194470200.2  L65121243056.117L65337638689.5  L656136024.1    L66610753222.10 L7298577381.3   L7510805464.119 L7510805464.167 L774765788.5    L7947746100.9   L7947925514.3   L808147016.10   L808147016.20   L9239535009.34  O16256374831.206O17025492443.191O17025492443.205O20591522593.191O2698786721.191 O35848755045.205O55942222111.191O6457969035.191 P14577917531.191P19054760943.205P19855291478.160P2113986537.159 P21162824304.160P26954661751.206P5693344027.191 P61093937827.191P61093937827.205P63293724078.159P7313320607.191 Q12370813529.170Q14791076917.127Q14792959895.147Q15275161522.124Q15641568065.171Q15643065735.171Q15643324129.121Q15899828075.159Q17207350632.171Q18364007745.171Q18365925601.122Q18366716807.171Q18694146040.124Q21162824304.160Q21352466598.193Q21352466598.194Q21361286062.206Q21798041355.124Q25157988860.124Q25513505925.124Q25513505925.125Q25604052563.122Q25604052563.123Q25662358575.124Q26207421841.171Q26207721832.172Q26209999703.169Q31228709292.124Q31394594844.124Q31654082872.171Q32653584449.171Q32655242887.171Q32655500769.122Q33915850274.171Q33917472996.171Q33918256002.122Q35014437530.124Q35343253744.194Q35717497884.124Q36985131745.193Q36985131745.194Q37623098549.169Q37821600610.124Q37821600610.125Q3829644388.171 Q3830427394.122 Q3832210082.171 Q39117889904.170Q39212284437.172Q39939554818.122Q39939812708.171Q39941338018.171Q4143427880.124 Q43925228937.172Q44648843873.122Q44649109767.171Q44650596289.171Q49698585326.123Q49698585326.124Q51233520321.171Q51235796833.122Q51236054023.171Q53276980114.193Q53276980114.194Q53969758199.124Q5483094696.169 Q5485174314.170 Q5485600919.171 Q59408344986.124Q60511567613.172Q60697995187.172Q6143569392.170 Q61802139820.124Q6416456232.124 Q64255486968.124Q64706792026.160Q66259669316.206Q66522067074.122Q66522325988.171Q66523987234.171Q67528989526.125Q67528989526.126Q8882534411.169 Q9540949240.169 Q9840922658.171 Q9843367298.121 Q9843625700.171 00000100200301702G02H02l03F04<05>06206_06`07C07m08Q09F0:J0;W0;X0<Z0=e0>A0>B0>C0>L0>Y0?30?T0?U0?V0?h0@^0@_0@m0A@0AA0AJ0AV0AW0B10B80BR0C70Cf0De0Df0Dj0EH0E[0E^0E_0F@0FY0G30GH0GL0Gf0HG0HH0He0IP0JD0K;0L20L30LK0L]0Lh0Li0M:0MU0Mo0NI0Ni0O20Oa0P;0Pg0Ph0Pi0Pj0Q30QO0QP0Qe0Qf0RV0S00SJ0Sk0T80T[0T\0T]0T^0Th0UI0Ui0VI0VJ0Ve0W10W50W60WM0WN0W[0X<0Xb0YI0YJ0Yj0ZG0ZP0Zf0[00[30[J0[o0\E0\F0\G0\R0\X0\i0\o0]G0]a0^B0^C0^M0^S0^T0^U0^X0^_0_O0_P0_S0_o0`00`J0`k0a>0aP0a]0a^0b20bU0bV0bW0bX0bY0bZ0b[0b\0b]0cH0d00e10eH0f@0fA0f_0f`0fa0gK0gf0hN0iD0j:0j;0j\0k=0kW0lA0l\0m=0mW0n80nS0nT0nU0nV0o40o50oP10=11311N11i11j12E12`13;13W13k14F14g15H15b16O17<17b18>18?18@18A18B18]19V1:X1;E1;k1<X1<Y1=41=Z1>G1?41?51?P1?j1@K1@l1AQ1B61BW1C11CR1CS1CT1D01DK1Df1EA1EB1E]1F;1FV1FW1G21G31G41GR1H81He1IR1JK1KM1Kh1LC1M01MV1NCFFFS1R5NEEDR2ra2sp1X5limbs3ibs2lo2X03len3LOS3SLO3SPR2XB3HB05Ha_st5Hl_stS1R5NEEDR2ra2sp2s01X5limbs3ibs2lo2X03len3LOS3SLO3SPR2XB3HB05Ha_st5Hl_st2s12s22s3FS2ra2sp1X5limbs3ibs3len2XB2p26limbs2S2ra2sp1X5limbs3ibs3len2XBS1R3HIA1h2ra2sp1X5limbs3ibs3len3TOP2XB3HB05Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X5limbs3ibs3len3TOP2XB3HB05Ha_st5Hl_st2s12s22s3S1R5NEEDR2ra2sp1X5limbs3ibs2lo2X03len3LOS3SLO3SPR2XBS1R2ra2sp1X5limbs3ibs2lo3len3LOS2XB2p26limbs2FS2ra2sp1X5limbs1B3ibs3len2XB3x132HxS2ra2sp1X5limbs1B3ibs2X03len3SPR2XB3x132HxS2ra2sp1X5limbs3ibs3len2XB2p26limbs2S1R3HIA2ra2sp1X5limbs3ibs2lo3len2h22XB2p26limbs24TOP2S1R5NEEDR2ra2sp1X1P5limbs1B3ibs2lo3len3BLO3SLO2XB2P03HB05Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs1B3ibs2lo3len3BLO3SLO2XB2P03HB05Ha_st5Hl_st2s12s22s3FS1R5NEEDR2ra2sp1X1P5limbs3ibs2lo3len3SLO2XB2P03DSX3HB05Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs3ibs2lo3len3SLO2XB2P03DSX3HB05Ha_st5Hl_st2s12s22s3S1X5limbs1B3ibs2B03len2XB2C0FFS3ibs3lenS3ibs3len3NR2S2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB6limbs2SFS3ibs3len4CTL03N1'S1R5NEEDR2sp3ibs2lo3len3SLO3SPR2p26limbs24LEN23P203PS2FS1R2lo3LOS3ALOS1R3HIA1h1d2h24HFR2SS3ibs3lenS3ibs3len2L1FS2ra2sp1X5limbs3ibs3len2XBS1P3B0'S2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs2lo3len2XB3x293PC1S2ra2sp1X5limbs3ibs2lo3len2XB2p26limbs23xs33LX3S1R5NEEDR2sp1B3ibs2lo3len3SLO3SPR2p26limbs24LEN23P202L13BX23PS2FS2p2S2sp3ibs3len4LENE2p26limbs22L1S2sp3ibs3len3SPR2L0S1ySS2ra2sp1X5limbs3ibs3len2XB6limbs2S1R3HIA1h3ibs3len3BUD3CTLS2ra2sp1X5limbs3ibs3len2XBS1R1n1P2lo3LOS3ALO2PCS2spS2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB6limbs2FS1R2sp3ibs2lo3len3SLO3NRA3SPRS1R2sp3ibs2lo3len3SLO3NRA3SPR2p26limbs23P20S1R2sp3ibs2lo3len3LOS3ALO3SPR2p26limbs24LEN23P203P2CS1R5NEEDR2ra2sp1X5limbs3ibs2lo2X03len3SLO3SPR2XB6limbs2S1R5NEEDR2ra2sp1X5limbs3ibs2lo2X03len3SLO3SPR2XB6limbs2FS1R3HIA1h2sp3ibs3len3TOPS1R2lo3LOS3ALO3ACPS3ibs3len1HSS2sp1B3ibs2B03lenS2sp1B3ibs2B03len2p26limbs2S2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XBS1R3HIA1h2sp2lo3TOP4HTOP2h24TOP2S3ibs3lenS2LB2ra2sp1X5limbs3ibs3len2XB2p26limbs23xs33LX3S2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB2p26limbs23xs33LX3SSSS1R3HIA1hS1R2ra2sp1X5limbs3ibs3len2XBFS1R2sp3ibs2lo3len3SLOFS1R5NEEDR2ra2sp1X5limbs3ibs2lo2X03len3SLO3SPR2XBS2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB6limbs2S3ibs3len3NR2S2sp3ibs3len3SPR2p26limbs24LEN23P20FFFS1B3ibs2B0S1R2sp1n1P5limbs2lo2LL3LOS3ALO2PCS2ra2sp1X5limbs3ibs2X02XB6limbs2S2ra2sp1X5limbs3ibs2X02XB6limbs2FS1R5NEEDR2sp2lo3LOS3SLO3ALOS3ibs3len2p2S2spFS1R5NEEDR2sp2lo3LOS3SLOSS2p24PAL23P20S2ra2sp1X5limbs3ibs3len2XB6limbs2S2LB2ra2sp1X5limbs3ibs3len2XB6limbs21HS2LB2ra2sp1X5limbs3ibs3len2XB3x293PC11HSS2ra2sp1X5limbs3ibs2X02XB6limbs2S1R3ibs2lo3len3LOS3ALO2p23P2CS3ibs3lenS2ra2sp1X5limbs3ibs2XBS1R3HIA2h2S1XS2sp1B3ibs3len4BEND3SPRS2sp1B3ibs3len4BEND3SPR2p26limbs23P20S2ra2sp1X5limbs3ibs2XBFFS2sp2lo3LO0S1a2HaS3ibs3len2C01a2HaS1i2HiS3ibs3len6limbs22C04LEN2S2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB6limbs2FS1R2lo3LOSS1n2NRFFS1RS1R3ACPS2ra2sp1X5limbs1B3ibs2X02B03len4BEND3SPR2XB4LENEFS1XS1R3HIA1h3ibs3len2h23CTL3HV2FS2ra2sp1X5limbs3ibs3len2XBS2ra2sp1X5limbs3ibs3len2XB6limbs2S1R5NEEDR2sp2lo3SLOS1B3ibs3len2BB3CTLS3ibs3len3NR2FS2sp3ibs3len3SPA3SPRS2sp3ibs3len3SPR2p26limbs24PAL23P20FFFFFFFFS1R2sp1X5limbs3ibs2lo3len3LOS3ALO3ACP2XB2C0S2sp1X5limbs3ibs2lo3len2XB2p26limbs23PS2S1R5NEEDR2sp1X1P5limbs1B3ibs2lo3len2BX3BLO3SLO2XB2P03DSX3CTL4CTL0S2sp1X5limbs3ibs3len2XBS1R5NEEDR2sp1X1P5limbs3ibs2lo3len3SLO2XB2P03DSX3CTL4CTL0FS2sp1X5limbs3ibs2lo3len3LO02XBFFS2sp1X1P5limbs1B3ibs2lo3len3BLO2XB2P04CTL0S1X5limbs3ibs3len2XB3X022C0S2ra2sp1X5limbs3ibs3ALX2X03len2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3LOS3SLO3ALO3ACP3SPR2XBFS2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3LOS3SLO2XBS1X5limbs3ibs3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XBS2sp1X5limbs3ibs2lo3len2XB6limbs2S1R1X5limbs3ibs3len4IMG'2XBFFFS1X5limbs3ibs3len2XB2p26limbs2FS1R1X5limbs3ibs3len4IMG'2XBS2ra2sp1X5limbs3ibs2lo3len2XB3HB05Ha_st5Hl_stS2sp2s01X5limbs3ibs2lo3len2XB3HB05Ha_st5Hl_st2s12s22s3S2sp1X5limbs3ibs3len2XB3HB0S2sp1X5limbs3ibs3len2XB3HB0FS1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2S1R1X5limbs3ibs3len5ALWF'2XBS1X5limbs3ibs3len2XBS1X5limbs3ibs3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XBS1R1X5limbs3ibs3len5ALWF'2XBFFFFS1X5limbs3ibs3len2XB6limbs2S1R5NEEDR2ra2sp1X5limbs3ibs2lo3len3SLO2XB3HB05Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs3ibs2lo3len3SLO2XB3HB05Ha_st5Hl_st2s12s22s3S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2FS1X5limbs3ibs3len2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2FS1X5limbs3ibs3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XBS2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs3len3SPR2XB3HB05Ha_stS2sp1X5limbs3ibs3len3SPR2XB3HB05Ha_stS2sp1X5limbs3ibs2lo3len2XB6limbs2S2sp1X5limbs3ibs2lo3len2XBS2sp1X5limbs3ibs2lo3len2XB6limbs2FFS1R1X5limbs3ibs3len5ALWF'2XBS1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2FS1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs2X03len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2FS1R1X5limbs3ibs3len4IMG'2XBFFS1X5limbs3ibs3len2XB2p26limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2ra2sp1X5limbs3ibs2lo3len3SLO2XB3HB05Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs3ibs2lo3len3SLO2XB3HB05Ha_st5Hl_st2s12s22s3S1X5limbs3ibs3len2XB6limbs2S1X5limbs3ibs3len2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2S1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XBS1R5NEEDR2sp1X5limbs3ibs2lo3len3SLO2XB6limbs2". (* [comment removed for export] *)
  #[using="IMG RC RBE NEEDR HND DIMG"] Lemma A_mpi_read_binary_walk_r_c : mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY.
  Proof.
    unfold mpi_read_binary_stmtA_r_c, A_MPI_READ_BINARY. intros until d.
    intros HH HKmo MX HNS XWP HB B0 BEND BCR BX BXP BLO B47 ST LOS SLO TOP SPA TPV MI RA OX OB BUD XUW BUDF C24H -> -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (arl_need_rt_amem R) as NRA.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (HND _ _ _ _ HH) as ND. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
    pose proof XWP as XW.
    destruct dX as [X sg n P limbs pad own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    ddestruct MX as (HXS & ALX & X0 & LL & NR & HOWN). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in NR.
    assert (PB : 0 <= P /\ P + 4 * n <= alloc_ceiling
                 /\ (own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr asegs m P limbs /\ 1 <= n)
                 /\ (own = LNull -> P = 0 /\ n = 0)).
    { destruct own; [| | exfalso; exact (HNS eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0' & _ & BC & _). cbn in B0', BC.
        split; [clear - B0'; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0'| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL). clear HOWN.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    set (len := Z.of_nat (length ibs)) in *. assert (LENE : len = Z.of_nat (length ibs)) by reflexivity.
    pose proof (bytes_at_bound _ _ _ _ HB) as BB.
    pose proof (client_wrange_keep L LB LF _ _ (mkMPD X sg n P limbs pad own) X 16 CW DXP) as CWk.
    pose proof (client_range_keep L LB LF lo (mkMPD X sg n P limbs pad own) B len BCR BXP) as BCRk.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (len ≫ 2 + Z.b2z (0 <? Z.land len 3)) with (chars_to_limbs4 len)
      by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 2) with 4; symmetry; apply chars_to_limbs4_eq; clear - BB; lia).
    assert (CTL : 0 <= chars_to_limbs4 len /\ 4 * chars_to_limbs4 len <= len + 3 /\ len <= 4 * chars_to_limbs4 len) by (unfold chars_to_limbs4; clear - BB; lia).
    assert (CTL0 : chars_to_limbs4 len = 0 <-> len = 0) by (unfold chars_to_limbs4; clear - BB; lia).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HP1 : presA asegs R (mpd_keep LB (mkMPD X sg n P limbs pad own)) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (MA1 : mpdr_at asegs m1 LB (mkMPD X sg n P limbs pad own)).
    { eapply mpdr_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact PNULL|].
      intros E. ddestruct (PHEAP E) as (B0' & HIN & HP16 & HXL & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof RC as SPR'. unfold mpi_resize_clear_coreA_r_c, A_MPI_RESIZE_CLEAR in SPR'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPR' with (h := h) (LB := LB) (LF := LF) (dX := mkMPD X sg n P limbs pad own) (nl := chars_to_limbs4 len) (lo := lo) (d := d);
        cbn [md_addr md_own md_p md_n];
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity.
      all: first [ eapply mpd_writableA_sp_mono; [exact (conj CW DXP : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) (mkMPD X sg n P limbs pad own))| clear; lia]
                 | intros HO; left; destruct own; [exfalso; exact (HO eq_refl)| clear - PC ALO LOS; lia| exfalso; exact (HNS eq_refl)]
                 | unfold grow_PHI, MPI_RB_PHI in *; clear - BUD CTL BB; lia
                 | rewrite resize_clear_FR_val; unfold MPI_RB_FR, fr_charge in BUDF; clear - BUDF D0; lia
                 | clear - CTL BB BEND B0 NR LOS SLO NEEDR TOP SPA SPR; lia
                 | match goal with |- ?g => idtac "RC-PRE-LEFT:" g end ]. }
    clear SPR'.
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    unfold mpi_binop_postA in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MA2 & OUT2 & FRESH2 & R2).
    cbn [md_addr md_own md_p md_n] in HP2, FRESH2, OUT2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    match type of HH2 with HM _ _ _ ?hh ?LBB _ _ => rename hh into h2; rename LBB into LB2 end.
    match type of MA2 with mpd_at _ _ _ ?dd => rename dd into dX2 end.
    clear HXS MA1.
    presA_transport HP2.
    assert (HPX2 : presA asegs R (mpd_keep LB (mkMPD X sg n P limbs pad own)) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
    { eapply presA_trans; [exact HP1|]. eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    clear HP1 HP2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OX. apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OB.
    assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    pose proof (hm_top asegs R HIA h2 LB2 LF m2 HH2) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]).
    ddestruct R2 as (R2 & ADDR2 & FRESHr).
    destruct dX2 as [X2 sg2 n2 p2 limbs2 pad2 own2]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X2.
    pose proof MA2 as [(CH2 & XAL2 & X02 & LEN2 & NR2 & OWN2) SG2].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CH2, XAL2, X02, LEN2, NR2, OWN2, SG2. unfold mpi_cells in CH2. unfold MPI_MAX_LIMBS in NR2.
    destruct R2 as [(-> & -> & N2 & LIMBS2 & NULL2)|(-> & -> & N2 & LIMBS2 & NULL2)].
    2: { (* [comment removed for export] *)
      unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in *.
      zstep.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      zstep.
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold mpi_read_binary_postA_c. cbn [md_addr md_own md_p md_n]. deexists 14. dexists m2, mo9, h2, LB2, (mkMPD X 1 n2 p2 limbs2 pad2 own2), (-16).
      split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact MF9|]. split; [exact HPX2|].
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [unfold grow_PHI, MPI_RB_PHI in *; clear - HV2 CTL BB; lia|].
      split; [rewrite resize_clear_FR_val in HFR2; unfold MPI_RB_FR, fr_charge; clear - HFR2 D0; lia|].
      split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [right; reflexivity|]. split; [intros E; discriminate E|]. split; [exact FRESH2|]. rb_c24 OUT2. }
    (* [comment removed for export] *)
    subst n2.
    zstep.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (chars_to_limbs4 len))) with (Z_to_bv 64 (chars_to_limbs4 len))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR2; lia); rewrite Z.mod_small by (clear - NR2; lia); reflexivity).
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST2 (bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    assert (R0 : read_be_ret (chars_to_limbs4 len) len = 0) by (unfold read_be_ret; destruct (Z.ltb_spec (chars_to_limbs4 len) (chars_to_limbs4 len)); [clear - H; lia| reflexivity]).
    dpose OUT2 as (_ & NST2 & _). cbn [md_own] in NST2.
    pose proof RBE as SPB. unfold mpi_core_read_be_stmtA, A_MPI_CORE_READ_BE, MPI_CORE_READ_BE_STACK_A in SPB.
    destruct own2 as [| |]; [| | exfalso; exact (NST2 eq_refl)].
    - (* [comment removed for export] *)
      destruct OWN2 as [-> C0]. assert (L0 : len = 0) by (apply CTL0; exact C0).
      assert (EL : limbs2 = []) by (destruct limbs2; [reflexivity| exfalso; cbn in LEN2; clear - LEN2 C0; lia]). subst limbs2.
      assert (U0 : u32arr asegs m2 0 []).
      { split; [split; [clear; lia| split; [cbn; clear; lia| intros i Hi; cbn in Hi; exfalso; clear - Hi; lia]]
              | split; [clear; lia| split; [cbn; clear; lia| intros i Hi; cbn in Hi; exfalso; clear - Hi; lia]]]. }
      pose proof (munch_refl [(lo, bv_unsigned sp); (0, 0 + 4 * chars_to_limbs4 len)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
      acallxA_sp (bv_unsigned sp)
        (eapply SPB with (h := h2) (LB := LB2) (LF := LF) (X := 0) (n := chars_to_limbs4 len) (B := B) (blen := len) (lo := lo) (xs := []) (bs := ibs);
         try eassumption; try reflexivity;
         first [ exact U0
               | rewrite C0; clear; cbn; lia
               | split; [intros a Ha; exfalso; clear - Ha C0; lia| intros a Ha; exfalso; clear - Ha C0; lia]
               | intros a Ha; exfalso; clear - Ha C0; lia
               | clear - C0 L0 BB B0 BEND BLO B47 LOS SLO NEEDR NRA TOP2 SPA SPR LO0; lia
               | cbn [length Z.of_nat Z.mul Z.add]; clear - B0 LO0; lia
               | match goal with |- ?g => idtac "RBE0-PRE-LEFT:" g end ]).
      clear SPB.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-RBE0-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : HM asegs R HIA h2 LB2 LF m3 |- _ => rename H into HH3 end.
      match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold mpi_read_binary_postA_c. cbn [md_addr md_own md_p md_n]. deexists 14.
      dexists m3, mo9, h2, LB2, (mkMPD X 1 0 0 [] pad2 LNull), (read_be_ret (chars_to_limbs4 len) len).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF9|].
      split.
      { eapply presA_trans; [exact HPX2|]. apply presA_nil_any. rewrite <- HS2.
        eapply (presA_weaken asegs R LB2 _ LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2) [(0, 0 + 4 * chars_to_limbs4 len)]);
          [| intros b Hb; eapply mpd_keep_out; [exact OUT2| exact Hb]| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; rewrite C0; clear; intros y _; lia].
        eapply (presA_drop_below asegs R HIA h2 LB2 LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH3| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB2 LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia | exact MU2 | exact WM2].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; rewrite C0; intros a Ha; exfalso; clear - Ha; lia| apply Forall_nil]. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [unfold grow_PHI, MPI_RB_PHI in *; clear - HV2 CTL BB; lia|].
      split; [rewrite resize_clear_FR_val in HFR2; unfold MPI_RB_FR, fr_charge; clear - HFR2 D0; lia|].
      split; [exact HH3|].
      split. { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [| split; [exact XAL2| split; [exact X02| split; [reflexivity| split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]]]]].
        match goal with H : rw_cells asegs m3 X _ |- _ => rewrite C0 in H; exact H end. }
      split; [eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; discriminate| reflexivity]|].
      split; [left; exact R0|]. split; [intros _; split; [reflexivity| symmetry; exact C0]|].
      split; [cbn [mpd_blk md_own]; intros b []|]. rb_c24 OUT2.
    - (* [comment removed for export] *)
      ddestruct OWN2 as (N1' & PIN2 & PAL2 & U2).
      pose proof (hm_aobj_block asegs R HIA h2 LB2 LF m2 p2 (4 * chars_to_limbs4 len) HH2 PIN2) as OP2.
      destruct (hm_apart asegs R HIA h2 LB2 LF m2 HH2) as [HFB _]. rewrite Forall_forall in HFB.
      destruct (HFB _ ltac:(apply in_app_iff; left; exact PIN2)) as (P20 & _ & P2C & _). cbn in P20, P2C.
      assert (HINP2 : In (p2, 4 * chars_to_limbs4 len) (LB2 ++ fdata LF)) by (apply in_app_iff; left; exact PIN2).
      assert (L1 : 1 <= len) by (clear - CTL0 N1' BB; lia).
      assert (BX2 : B + len <= p2 \/ p2 + 4 * chars_to_limbs4 len <= B).
      { eapply (new_limbs_apartA R LB LF lo (mkMPD X sg n P limbs pad own) (mkMPD X 1 (chars_to_limbs4 len) p2 limbs2 pad2 LHeap) B len);
          cbn [md_addr md_own md_p md_n]; [exact FRESH2| reflexivity| exact N1'| exact BCR| exact BXP| clear - ALO LOS; lia| clear - L1; lia]. }
      assert (XX2 : X + 16 <= p2 \/ p2 + 4 * chars_to_limbs4 len <= X).
      { eapply (new_limbs_apartA R LB LF (bv_unsigned sp) (mkMPD X sg n P limbs pad own) (mkMPD X 1 (chars_to_limbs4 len) p2 limbs2 pad2 LHeap) X 16);
          cbn [md_addr md_own md_p md_n]; [exact FRESH2| reflexivity| exact N1'| | exact DXP| clear - ALO LOS SLO NEEDR; lia| clear; lia].
        eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (PS2 : p2 + 4 * chars_to_limbs4 len <= lo) by (clear - P2C ALO LOS; lia).
      pose proof (munch_refl [(lo, bv_unsigned sp); (p2, p2 + 4 * chars_to_limbs4 len)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
      acallxA_sp (bv_unsigned sp)
        (eapply SPB with (h := h2) (LB := LB2) (LF := LF) (X := p2) (n := chars_to_limbs4 len) (B := B) (blen := len) (lo := lo) (xs := limbs2) (bs := ibs);
         try eassumption; try reflexivity;
         first [ right; clear - PAL2 P20; lia
               | eapply client_wrange_block; [exact HINP2| clear; lia| clear; lia]
               | clear - L1 LENE LEN2 NR2 N1' BX2 PS2 PAL2 P20 P2C BB B0 BEND BLO B47 LOS SLO NEEDR NRA TOP2 SPA SPR LO0 ALO; lia
               | match goal with |- ?g => idtac "RBE1-PRE-LEFT:" g end ]).
      clear SPB.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-RBE1-SIDE:" g end.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : HM asegs R HIA h2 LB2 LF m3 |- _ => rename H into HH3 end.
      match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : u8arr asegs m3 p2 ?xs |- _ => fail | _ => idtac end.
      match goal with H : u32arr asegs m3 p2 ?xs, H' : length ?xs = length limbs2 |- _ => rename H into U3; rename H' into LX3; rename xs into xs3 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold mpi_read_binary_postA_c. cbn [md_addr md_own md_p md_n]. deexists 14.
      dexists m3, mo9, h2, LB2, (mkMPD X 1 (chars_to_limbs4 len) p2 xs3 pad2 LHeap), (read_be_ret (chars_to_limbs4 len) len).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF9|].
      split.
      { eapply presA_trans; [exact HPX2|]. apply presA_nil_any.
        (* [comment removed for export] *)
        assert (HPL2 : presA asegs R (mpd_keep LB (mkMPD X sg n P limbs pad own)) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(p2, p2 + 4 * chars_to_limbs4 len)] m2 m3).
        { rewrite <- HS2.
          eapply (presA_weaken asegs R LB2 _ LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2) [(p2, p2 + 4 * chars_to_limbs4 len)]);
            [| intros b Hb; eapply mpd_keep_out; [exact OUT2| exact Hb]| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
          eapply (presA_drop_below asegs R HIA h2 LB2 LF _ lo (bv_unsigned sp) _ m2 m3); [exact HH3| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB2 LF _ _ _ _ m2 m3 (hcs asegs R HIA h2) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia | exact MU2 | exact WM2].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (p2 + 4 * chars_to_limbs4 len - p2) with (4 * chars_to_limbs4 len) by lia; eapply hcs_block; [exact HH3| exact PIN2]| apply Forall_nil]. }
        destruct (FRESH2 (p2, 4 * chars_to_limbs4 len) (or_introl eq_refl)) as [HOLD|HFR].
        + (* [comment removed for export] *)
          unfold mpd_blk in HOLD. cbn [md_own md_p md_n] in HOLD.
          destruct own; [destruct HOLD| | destruct HOLD]. destruct HOLD as [E|[]]. injection E as E1 E2.
          ddestruct (PHEAP eq_refl) as (_ & HIN & _).
          eapply (presA_drop_freed asegs R HIA h LB LF _ [] P (4 * n) m1 m2 m3);
            [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
            | replace (P, P + 4 * n) with (p2, p2 + 4 * chars_to_limbs4 len) by (rewrite E1, E2; reflexivity); exact HPL2].
          intros b xb Hb Hr. unfold mpd_keep in Hb. cbn [md_own md_p md_n] in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          split; [exact Hb|]. intros E'. rewrite E' in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        + (* [comment removed for export] *)
          cbn [fst snd] in HFR. eapply presA_drop_fresh; [exact HPL2| exact HFR| clear - ALO LOS SLO NEEDR; lia]. }
      split; [exact HT2|]. split; [exact HS2|]. split; [exact HF2|]. split; [exact HK9|]. split; [exact HCS2|].
      split; [unfold grow_PHI, MPI_RB_PHI in *; clear - HV2 CTL BB; lia|].
      split; [rewrite resize_clear_FR_val in HFR2; unfold MPI_RB_FR, fr_charge; clear - HFR2 D0; lia|].
      split; [exact HH3|].
      split. { split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [match goal with H : rw_cells asegs m3 X _ |- _ => exact H end|].
        split; [exact XAL2|]. split; [exact X02|]. split; [rewrite LX3; exact LEN2|]. split; [unfold MPI_MAX_LIMBS; clear - NR2; lia|].
        split; [exact N1'|]. split; [exact PIN2|]. split; [exact PAL2| exact U3]. }
      split; [eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; discriminate| reflexivity]|].
      split; [left; exact R0|]. split; [intros _; split; [reflexivity| unfold chars_to_limbs, chars_to_limbs4; reflexivity]|].
      split; [exact FRESH2|]. rb_c24 OUT2.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG RC RBE NEEDR HND DIMG"] Lemma A_mpi_read_binary_walk_c : mpi_read_binary_stmtA_c asegs R HIA A_MPI_READ_BINARY.
  Proof.
    unfold mpi_read_binary_stmtA_c. intros until d. intros HH HKmo MX HNS XWP.
    eapply A_mpi_read_binary_walk_r_c; [exact HH| exact HKmo| exact (proj1 MX)| exact HNS| exact (mpd_writableA_of_P _ _ _ _ _ _ XWP)].
  Qed.
End Walk.

Lemma A_mpi_read_binary_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_c24 ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$2.R3.R2.$6.)P,(7.$2.R4.R3.$8.)P,(9.=(:.R5.))P,Ph,(;.$2.R6.R5.)PLB,(<.$=.)PLF,(<.$=.)Pm,P,(>.&40.)(?.(>.&8.))P,(10.$2.R:.R9.R4.R3.R2.R1.)(11.$12.(13.(14.$12.$12.)$12.(15.$12.$12.)R4.))P,(16.(9.(17.(18.R7.))(19.(18.R7.)))(9.(1:.(18.R7.))(1;.(18.R7.))))(1<.$2.R8.R7.$1=.)")
(* [comment removed for export] *).
Proof. intros. eapply A_mpi_read_binary_walk_c; eauto. Qed.

Lemma A_mpi_read_binary_spec_r_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_c24 ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$2.R3.R2.$6.)P,(7.$2.R4.R3.$8.)P,(9.=(:.R5.))P,Ph,(;.$2.R6.R5.)PLB,(<.$=.)PLF,(<.$=.)Pm,P,(>.&40.)(?.(>.&8.))P,(10.$2.R:.R9.R4.R3.R2.R1.)(11.$12.(13.(14.$12.$12.)$12.(15.$12.$12.)R4.))P,(16.(9.(17.(18.R7.))(19.(18.R7.)))(9.(1:.(18.R7.))(1;.(18.R7.))))(1>.$2.R8.R7.$1=.)")
(* [comment removed for export] *).
Proof. intros. eapply A_mpi_read_binary_walk_r_c; eauto. Qed.

(* [comment removed for export] *)
Lemma A_mpi_read_binary_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_c24 ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(1?.$12.(20.R3.)$21.)P,(1?.$12.(22.R4.)$23.)P,(1?.$12.(24.R5.)$25.)P,(1?.$12.(26.R6.)$27.)P,(1?.$12.(28.R7.)$29.)P,Pm,P,(>.&40.)(?.(>.&8.))P,(2:.R9.R1.)(2;.R2.)P,(9.=(2<.R9.))P,(9.=(2=.R:.))P,(9.=(:.R;.))P,Ph,(;.$2.R<.R;.)PLB,(<.$=.)PLF,(<.$=.)Pm,P,(>.&40.)(?.(>.&8.))P,(10.$2.R10.R?.R4.R3.R2.R1.)(11.$12.(13.(14.$12.$12.)$12.(15.$12.$12.)R4.))P,(16.(9.(17.(18.R=.))(19.(18.R=.)))(9.(1:.(18.R=.))(1;.(18.R=.))))(1<.$2.R>.R=.$1=.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_read_binary_spec_c; eauto.
  - eapply A_mpi_resize_clear_core_r_c; eauto. eapply A_zeroize_and_free_spec; eauto.
  - eapply A_mpi_core_read_be_spec; eauto.
Qed.
