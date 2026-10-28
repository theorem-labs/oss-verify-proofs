(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AJ AKinvS AKinvM HMLib ASplit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SRz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AKinvSplit () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.mwc_postS"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_RAR_MAP"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"].

Section ARUN_1. Context {hAR : arun}.
Section MapWithCallbackSplit.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  (* [comment removed for export] *)
  Variables (K Kok : Model -> Prop).
  Hypothesis KL : kinv AL CS K.
  Hypothesis KokL : kinv AL CS Kok.

  Variables (addr size name : Z).
  Let nZ := (size + 4095) / 4096 * 4096.

  (* [comment removed for export] *)
  Hypothesis LEDGER : ltac2:(CDefT.buildp (gd_tbl_AKinvSplit ()) "Pmo,$0.P,A1.VK,R1.(1.(2.$3.(4.(5.(6.R2.))(7.&40.Vaddr,)(7.&40.VnZ,))$8.)(9.(2.$3.(:.(;.(6.R2.))(7.&40.Vaddr,)(7.&40.VnZ,))$8.)(2.$3.(4.(<.(=.(>.&40.)(>.&40.))(5.(6.R2.))(;.(6.R2.)))(7.&40.Vaddr,)(7.&40.VnZ,))$8.)))")
(* [comment removed for export] *).
  Hypothesis T_commit : ltac2:(CDefT.buildp (gd_tbl_AKinvSplit ()) "Pmo,$0.P,A1.VK,R1.P,(2.$3.(:.(;.(6.R2.))(7.&40.Vaddr,)(7.&40.VnZ,))$8.)A1.VKok,(?.+32.Vaddr,VnZ,R3.)")
(* [comment removed for export] *).
  Hypothesis T_fresh : ltac2:(CDefT.buildp (gd_tbl_AKinvSplit ()) "Pmo,$0.P,A1.VK,R1.P,(2.$3.(4.(<.(=.(>.&40.)(>.&40.))(5.(6.R2.))(;.(6.R2.)))(7.&40.Vaddr,)(7.&40.VnZ,))$8.)A1.VKok,(10.+32.Vaddr,VnZ,R3.)")
(* [comment removed for export] *).

  Hypothesis ROOM : forall mo, K mo -> fixrw_grantable 0x32 addr nZ mo.
  (* [comment removed for export] *)
  Hypothesis SCAR : scar_site AL CS K addr nZ.

  (* [comment removed for export] *)
  Local Notation POST := (mwc_postS K Kok addr size).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02J0@L10163305637.135L12737330739.143L13654651853.143L13654982357.126L15272425173.125L16159242360.99 L16342829433.132L16343007577.151L16343007577.168L16344773208.169L16344781844.133L16346877028.132L16357739241.131L16570333557.126L16570397805.143L17125266570.147L17901851861.124L18290309477.98 L18290309604.99 L18928394225.152L18928394225.169L18928473206.88 L18930958230.89 L18938958913.132L20135978148.147L20503951697.131L20514386657.151L20514386657.168L20653459879.131L20653739733.147L20655590071.95 L20668206230.178L20668305040.149L20709756104.131L20763562167.133L20763562167.153L20763562167.170L21130222074.131L21675095703.168L22172207656.122L22174304845.141L22700267513.138L22700267513.139L22700267513.168L22700267513.175L22700267513.203L23031571949.141L23033669000.122L2418826082.170 L2419054369.134 L2419054380.134 L29038649379.178L30154055423.143L33411638105.145L33751206853.97 L35821110645.124L36107676821.99 L37669248118.168L38832701421.142L38832701429.123L40788849258.90 L41674788627.137L41689647518.136L41689647581.173L41941576815.151L42150857613.143L42150857667.178L42151020997.149L42152890098.131L42153265536.147L42155085282.95 L42509344912.90 L42509560615.151L42511597162.97 L43410297717.125L45129184312.166L47331153942.131L47341753254.151L47341753254.168L47439662351.133L47439662351.153L47439662351.170L47545421154.97 L47801265973.132L47801265973.152L47801265973.169L49363582006.131L5194284791.139 L52747662605.145L52747662613.128L52760426621.156L52760524367.168L53512949285.132L53512949285.152L53512949285.169L54580387064.133L54684059677.156L54684091951.168L54688272109.144L54688272117.127L5476994423.140 L55777059364.133L55777059364.97 L55777061170.92 L55777068136.169L55779016521.132L55779358569.151L55783357012.132L55895014023.168L57467681890.151L57467681890.168L57473955794.131L57553800561.178L58744438605.144L58744438613.127L58748615101.156L58748647311.168L58852426124.177L59113944898.133L59113944898.153L59113944898.170L59314955108.132L59314955108.152L59314955108.169L60560988749.142L60560988757.123L61641781463.132L61652286311.151L61652286311.152L61652286311.169L61654442929.91 L61654445610.97 L62008757933.145L62008757941.128L62021586415.168L62021682141.156L62211500318.172L63220242529.131L63226945260.132L63230809041.151L63230809041.168L63231024113.132L63233220816.169L63233230492.133L64038322146.171L6437205593.143 L65860310473.126L65860310473.155L65860310473.172L67163524134.133L67165663331.133L945261379.131  L951468275.151  L951468275.168  00000U00V00o01H01a02;02W03303O03k04G04c05?05X06106206K06b07907R07k08=08O08h08i08j08k08l09Q0:60:T0;90;^0;_0<;0<W0=30=40=50=N0=g0>m0@30A90B?0CE0C^0D70D`0EI0F20F30FX0G<0GS0Gl0HF0He0I>0IW0In0JG0J`0K90KX0L:0L\0M>0M`0NB0N]0O;0OZ0P20PK0Q60QS0R00RM0Ri0SE0Sa0T80TZ0U<0U^0U_0V;0VT0Vm0WF0W_0X80XQ0Xj0YF0Y_0Z80ZQ0Zj0[F0[b0\80\M0\i0]E0]a0^=0^V0_20_N0_j0_k0`D0`]0a60aO0b90bR0bk0cD0ce0dF0dg0e@0eY0f50fQ0fm0gI0ga0h60hO0hh0iA0iZ0j?0j^0k=0k\0l;0lZ0m90mU0n>0n?0ni0oS10=10f11O11P11Q11RS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1x2C12C2S3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1x2C1S3hAR4addr4size2nZ1x2C2S3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZS3hAR4addr4size2nZS3hAR4addr4size2nZ2SP3FRBFFFFS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2A02SZ2CE2NZS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBFS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMFFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A03FRB1A2cs2H2S3hAR4addr4size2nZ1x2HxS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2A01x2C1S3hAR4addr4size2nZ2SP2CE2Hn3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1H2H0S3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2CE2Hn3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2lo5LOIMGS3hAR4addr4size2nZ2A02SZ2CE2NZS3hAR4addr4size2nZ2SP2A02Ha3FRBS3hAR4addr4size2nZ2A02HaS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2SZ2CE5LOIMG2NZ3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ1x2HxS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBFS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ3HanS3hAR4addr4size2nZ2CES3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRB1x2HxS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SZ2NZS3hAR4addr4size2nZ2HnS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFS3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFFF". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOK KL KokL LEDGER T_commit T_fresh ROOM SCAR"] Lemma map_with_callback_split : ltac2:(CDefT.buildp (gd_tbl_AKinvSplit ()) "PTA,$11.PTB,$11.Pra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pa0,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)PSP,$12.PF,(13.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(14.(>.&8.))Pmo,$0.Plo,$12.P,(15.+65?000.Vaddr,)P,(2.$12.(16.Vaddr,+1000.)=)P,(1.(17.=Vsize,)(15.Vsize,(18.+2.+28.)))P,(15.(19.Vaddr,VnZ,)(1:.VhAR,))P,(1.(17.=Vname,)(17.Vname,(18.+2.+2?.)))P,Px,(>.&40.)P,(1.(15.Vaddr,(1;.&40.R1.))(17.(1;.&40.R1.)(19.Vaddr,VnZ,)))(2.$3.(1<.$1=.R2.)$1>.)P,(1?.$1=.R9.$20.(21.$22.(23.(7.&40.$24.))(25.$22.)))P,(1?.$1=.R:.$24.(21.$22.(23.(7.&40.+1000.))(25.$22.)))P,(1?.$1=.R;.$26.(21.$22.(23.(7.&40.$27.))(25.$22.)))P,(1?.$1=.R<.$28.(21.$22.(29.(7.&8.=))(25.$22.)))P,(1?.$1=.R=.$2:.(21.$22.(23.(7.&40.=))(25.$22.)))P,(1?.$1=.R>.$2;.(21.$22.(23.(7.&40.+1.))(25.$22.)))P,(1?.$1=.R?.$2<.(21.$22.(23.(7.&40.$2=.))(25.$22.)))P,(1?.$1=.R10.$2=.(21.$22.(2>.(7.&40.=))(25.$22.)))P,(2?.$1=.R11.R?.R14.)P,(15.(1:.VhAR,)R10.)P,(15.R11.(30.R16.+190.))P,(15.R17.(18.+2.+3?.))P,(31.VCS,R13.(30.R18.R13.))P,(32.$1=.R16.)P,A1.VK,R16.P,(33.R18.R17.)P,A1.R39.(25.$34.)P,A1.R39.(25.$34.)P,Pc',$35.P,(36.VK,VKok,Vaddr,Vsize,$8.R3:.R1?.R39.R38.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R1>.R1=.R1:.R1<.R1.)(37.$1=.R2.R3<.)P,Pc',$35.P,(36.VK,VKok,Vaddr,Vsize,$1>.R3;.R20.R3:.R39.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R1?.R1>.R1;.R1=.R1.)(37.$1=.R2.R3>.)(37.$1=.(38.(39.(3:.R3;.(7.&40.R20.)R3:.R39.R38.R37.R36.R35.R34.R25.(7.&40.Vaddr,)(7.&40.Vsize,)(7.&40.Vname,)R24.R23.R22.R21.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R1?.(7.&40.$3;.)R1>.(3<.(>.&40.))R1=.(3=.$1=.))R1<.)(3>.R3=.R3<.))")
(* [comment removed for export] *).
  Proof.
    intros TA TB ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a5 a6 a7 SP F fc m mo lo
      A0 AAL SZ CE NM NONE GOT PGS GOTF DEC LIM SEAL GOTD DYI ST LOIMG SPL SPH SCS MI HK HJ TA0 TB0 HS HF.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    ddestruct SCAR as (Kh & KhL & SBND & SJW & SC1 & SC2).
    assert (NZ : size <= nZ < size + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (Z.div_mod (size + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (size + 4095) 4096 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    pose proof aceil_bounds as ACB.
    assert (Ha : 0 <= addr < 2^64) by lia. assert (Hn : 0 <= nZ < 2^64) by lia. assert (Han : addr + nZ <= 2^64) by lia.
    (* [comment removed for export] *)
    assert (WMABS : forall mx : mem, (forall x : word, addr <= bv_unsigned x < addr + nZ -> mx x = None) ->
                      wmono asegs mx (apply_unmaps mx [(wa addr, Z_to_bv 64 nZ)])).
    { intros mx ABSx x Hx.
      destruct (Z.lt_ge_cases (bv_unsigned x) addr) as [C1|C1].
      { unfold wview in *. rewrite (unmaps_outside mx addr nZ Ha Hn Han x ltac:(lia)). exact Hx. }
      destruct (Z.le_gt_cases (addr + nZ) (bv_unsigned x)) as [C2|C2].
      { unfold wview in *. rewrite (unmaps_outside mx addr nZ Ha Hn Han x ltac:(lia)). exact Hx. }
      exfalso. apply Hx. rewrite (wview_high mx x ltac:(lia)). apply ABSx. lia. }
    assert (UNABS : forall mx : mem, forall x : word, addr <= bv_unsigned x < addr + nZ -> apply_unmaps mx [(wa addr, Z_to_bv 64 nZ)] x = None).
    { intros mx x Hx. rewrite apply_unmaps_spec by lia. unfold in_range.
      replace (addr <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x <? addr + nZ) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    (* [comment removed for export] *)
    eapply (evtA_srzJ_KJ AL CS K _ (t_alt2 TA TB) _ mo KL HK); [exact HJ| |].
    { eapply (map_pre AL IMG ALWF CS CSOK); try eassumption; lia. }
    cbn beta. intros ms1 mo1 PRE HK1 MM1 HJ1.
    ddestruct PRE as (x5 & x6 & x7 & x28 & x29 & x30 & x31 & xa6 & mm & fr & -> & MU & WM & MI1 & FRM & FR & ST1).
    cbn [ms_mem MSsvc] in HJ1.
    destruct (LEDGER mo1 HK1) as [RF CASES].
    ddestruct (SC1 mo1 HK1) as (MC1 & NC1 & KH1).
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    (* [comment removed for export] *)
    assert (TR : forall A cs, ro_cells asegs m A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs mm A cs).
    { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU|]. cbn [disjoint_from]. split; [lia| exact I]. }
    pose proof (TR _ _ GOT ltac:(unfold A_GOT_PAGESZ; lia) ltac:(unfold A_GOT_PAGESZ; cbn; lia)) as GOTm.
    pose proof (TR _ _ PGS ltac:(unfold A_PAGESZ_CELL; lia) ltac:(unfold A_PAGESZ_CELL; cbn; lia)) as PGSm.
    pose proof (TR _ _ GOTF ltac:(unfold A_GOT_CFLAGS; lia) ltac:(unfold A_GOT_CFLAGS; cbn; lia)) as GOTFm.
    pose proof (TR _ _ LIM ltac:(unfold A_MMAP_LIMIT; lia) ltac:(unfold A_MMAP_LIMIT; cbn; lia)) as LIMm.
    pose proof (TR _ _ SEAL ltac:(unfold A_GOT_SEALED2; lia) ltac:(unfold A_GOT_SEALED2; cbn; lia)) as SEALm.
    pose proof (TR _ _ GOTD ltac:(unfold A_GOT_DYING; lia) ltac:(unfold A_GOT_DYING; cbn; lia)) as GOTDm.
    pose proof (TR _ _ DYI ltac:(unfold A_DYING; lia) ltac:(unfold A_DYING; cbn; lia)) as DYIm.
    (* [comment removed for export] *)
    assert (SPIN2 : forall (Kx : Model -> Prop) (KxL : kinv AL CS Kx) y5 y6 y7 y28 y29 y30 y31 ya6 (m2 : mem) (mo2 : Model) (r : Z),
               Kx mo2 -> 0 <= r < 2^64 -> r <> addr ->
               ro_cells asegs m2 A_GOT_DYING [C8 (Z_to_bv 64 A_DYING)] -> ro_cells asegs m2 A_DYING [C4 (Z_to_bv 64 0)] ->
               stk asegs m2 lo (SP + -64) -> mem_inv asegs m2 ->
               spinningJ asegs (mkCfg (map_norep_answered r SP gp tp y5 y6 y7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 ya6 F fc addr size m2) mo2)).
    { intros Kx KxL y5 y6 y7 y28 y29 y30 y31 ya6 m2 mo2 r HKx R0 RNE G1 G2 ST2 MI2.
      eapply (evtA_spinJ_K asegs AL CS Kx _ _ mo2 KxL HKx).
      { eapply (map_norep_post_spin AL IMG ALWF CS CSOK) with (lo := lo); try eassumption; lia. }
      cbn beta. (intros ms5 mo5 dd_H; ddestruct dd_H as (r' & F' & mm' & ->); intros HK5 _).
      apply spinningJ_here; [reflexivity| vm_compute; reflexivity| exact (ki_halted KxL mo5 HK5)]. }
    lazymatch goal with |- srealizesJ _ (mkCfg ?MS1 _) _ =>
    (* [comment removed for export] *)
    assert (SUCC : forall mo2, fixrw_outcome 0x32 addr nZ mo1 (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) mo2 ->
                     srealizesJ asegs (mkCfg (nret MS1 (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) mo2) TB)
    end.
    { intros mo2 OUT.
      assert (K2 : Kok mo2 /\ J (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) mo2).
      { inversion OUT; subst.
        - split; [apply T_commit; [exact HK1| assumption]| apply (J_fixrw_commit mm mo1 HJ1 addr nZ); lia].
        - split; [apply T_fresh; [exact HK1| assumption]| apply (J_fixrw_fresh mm mo1 HJ1 addr nZ); [lia| lia| lia| assumption]]. }
      destruct K2 as [K2 J2]. clear OUT.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
      pose proof (rw_cells_zeros_other asegs mm addr nZ Ha Hn Han _ _ FR ltac:(cbn; lia)) as FRz.
      pose proof (rw_cells_zeros_other asegs mm addr nZ Ha Hn Han _ _ FRM ltac:(cbn; lia)) as FRMz.
      pose proof (stk_zeros asegs mm addr nZ Ha Hn Han _ _ ST1) as STz.
      pose proof (rw_cells_zeros_new asegs mm addr nZ Ha Hn Han) as NEWz.
      assert (MUz : munch [(lo, SP); (addr, addr + nZ)] m (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (munch_zeros mm addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
        eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
      assert (MIz : mem_inv asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (mem_inv_zeros asegs mm addr nZ Ha Hn Han MI1). intros x Hx. apply (NONE x Hx). }
      assert (GOTFz : ro_cells asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]).
      { eapply (ro_cells_zeros_other asegs mm addr nZ Ha Hn Han); [exact GOTFm|]. cbn. unfold A_GOT_CFLAGS. lia. }
      assert (LIMz : ro_cells asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) A_MMAP_LIMIT [C8 (Z_to_bv 64 0)]).
      { eapply (ro_cells_zeros_other asegs mm addr nZ Ha Hn Han); [exact LIMm|]. cbn. unfold A_MMAP_LIMIT. lia. }
      pose proof (wmono_zeros asegs mm addr nZ Ha Hn Han _ WM) as WMz.
      set (mz := apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody mz.
      eapply (evtA_srzJ_KJ AL CS Kok _ TB _ mo2 KokL K2); [exact J2| |].
      { eapply (map_post_ok AL IMG ALWF CS CSOK) with (m0 := mz); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & mm3 & -> & MU3 & WM3 & MI3 & ST3).
      apply HS. unfold mwc_postS. deexists 17. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [exact MUz|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WMz| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact HJ3|]. split; [exact HK3|].
      eapply rw_cells_transport; [exact NEWz| exact MU3| exact WM3| cbn [disjoint_from cells_size csize]; rewrite ?Z2Nat.id by lia; split; [lia| exact I]]. }
    eapply (srzJ_mmap_fixrw_split3 asegs) with (addr := addr) (nZ := nZ) (flags := 0x32) (A := TA) (TB := TB).
    { exact (ki_halted KL mo1 HK1). }
    { exact (ki_top KL mo1 HK1). }
    { unfold mmap_fixrw_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      repeat split; try reflexivity; try lia.
      - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
        pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
        replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
        apply Z.div_unique with (r := 4095); lia.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
      - left. reflexivity. }
    { exact RF. }
    { exact MC1. }
    { apply ROOM. exact HK1. }
    - (* [comment removed for export] *)
      intros e HIn. apply (srzJ0_spin asegs). destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      eapply (evtA_spinJ_K asegs AL CS K _ _ mo1 KL HK1).
      { eapply (map_refused_pre AL IMG ALWF CS CSOK) with (m0 := mm); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3.
      ddestruct PO as (y5 & y6 & y7 & y28 & y29 & y30 & y31 & ya6 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FRH3 & ST3).
      ddestruct (SC1 mo3 HK3) as (MC3 & _ & _).
      assert (TR3 : forall A cs, ro_cells asegs mm A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs m3 A cs).
      { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU3|]. cbn [disjoint_from]. split; [lia| exact I]. }
      eapply (spinningJ_mmap_norep_live asegs) with (addr := addr) (nZ := nZ).
      { exact (ki_halted KL mo3 HK3). }
      { exact (ki_top KL mo3 HK3). }
      { unfold mmap_norep_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        repeat split; try reflexivity; try lia.
        - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
          pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
          replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
          apply Z.div_unique with (r := 4095); lia.
        - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
      { apply contained_not_free; [rewrite unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia| exact MC3]. }
      intros e He.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      assert (RV : exists r, errno_ret e = Z_to_bv 64 r /\ 0 <= r < 2^64 /\ r <> addr).
      { destruct He as [-> | ->]; [exists (2^64 - 12)| exists (2^64 - 17)]; (split; [apply bv_eq; vm_compute; reflexivity| lia]). }
      ddestruct RV as (r & -> & R0 & RNE).
      eapply (SPIN2 K KL); try eassumption.
      + apply TR3; [exact GOTDm| unfold A_GOT_DYING; lia| unfold A_GOT_DYING; cbn; lia].
      + apply TR3; [exact DYIm| unfold A_DYING; lia| unfold A_DYING; cbn; lia].
    - (* [comment removed for export] *)
      intros e HIn. destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
      (* [comment removed for export] *)
      assert (ABS : forall x : word, addr <= bv_unsigned x < addr + nZ -> mm x = None).
      { intros x Hx. exact (J_absent mm mo1 addr nZ HJ1 ltac:(unfold JF; lia) SBND SJW (map_contains_covers _ addr nZ ltac:(lia) ltac:(lia) ltac:(lia) MC1) NC1 x Hx). }
      pose proof (J_fixrw_destroyed mm mo1 HJ1 addr nZ ltac:(lia) ltac:(lia) ltac:(lia)) as HJu.
      pose proof (rw_cells_unmaps_other asegs mm addr nZ Ha Hn Han _ _ FR ltac:(cbn; lia)) as FRu.
      pose proof (rw_cells_unmaps_other asegs mm addr nZ Ha Hn Han _ _ FRM ltac:(cbn; lia)) as FRMu.
      pose proof (stk_unmaps_other asegs mm addr nZ Ha Hn Han _ _ ST1 ltac:(lia)) as STu.
      assert (MUu : munch [(lo, SP); (addr, addr + nZ)] m (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (munch_unmaps mm addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
        eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
      pose proof (mem_inv_unmaps asegs mm addr nZ Ha Hn Han MI1) as MIu.
      assert (WMu : wmono asegs m (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)])) by (eapply wmono_trans; [exact WM| exact (WMABS mm ABS)]).
      pose proof (UNABS mm) as ABSu.
      assert (TRu : forall A cs, ro_cells asegs mm A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 ->
                                 ro_cells asegs (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) A cs).
      { intros A cs H H1 H2. eapply (ro_cells_unmaps_other asegs mm addr nZ Ha Hn Han); [exact H|]. lia. }
      pose proof (TRu _ _ GOTm ltac:(unfold A_GOT_PAGESZ; lia) ltac:(unfold A_GOT_PAGESZ; cbn; lia)) as GOTu.
      pose proof (TRu _ _ PGSm ltac:(unfold A_PAGESZ_CELL; lia) ltac:(unfold A_PAGESZ_CELL; cbn; lia)) as PGSu.
      pose proof (TRu _ _ SEALm ltac:(unfold A_GOT_SEALED2; lia) ltac:(unfold A_GOT_SEALED2; cbn; lia)) as SEALu.
      pose proof (TRu _ _ GOTDm ltac:(unfold A_GOT_DYING; lia) ltac:(unfold A_GOT_DYING; cbn; lia)) as GOTDu.
      pose proof (TRu _ _ DYIm ltac:(unfold A_DYING; lia) ltac:(unfold A_DYING; cbn; lia)) as DYIu.
      set (mu := apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody mu.
      eapply (evtA_srzJ_KJ AL CS Kh _ TA _ _ KhL KH1); [exact HJu| |].
      { eapply (map_refused_pre AL IMG ALWF CS CSOK) with (m0 := mu); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (y5 & y6 & y7 & y28 & y29 & y30 & y31 & ya6 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FRH3 & ST3).
      cbn [ms_mem MSsvc] in HJ3.
      destruct (SC2 mo3 HK3) as (FR3 & _).
      assert (TR3 : forall A cs, ro_cells asegs mu A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs m3 A cs).
      { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU3|]. cbn [disjoint_from]. split; [lia| exact I]. }
      eapply (srzJ_mmap_norep_hole_split asegs) with (addr := addr) (nZ := nZ) (A := TA).
      { exact (ki_halted KhL mo3 HK3). }
      { exact (ki_top KhL mo3 HK3). }
      { unfold mmap_norep_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        repeat split; try reflexivity; try lia.
        - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
          pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
          replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
          apply Z.div_unique with (r := 4095); lia.
        - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
      { exact FR3. }
      + (* [comment removed for export] *)
        apply (srzJ0_spin asegs). rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
        replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        eapply (SPIN2 Kh KhL); try eassumption; try lia.
        * apply TR3; [exact GOTDu| unfold A_GOT_DYING; lia| unfold A_GOT_DYING; cbn; lia].
        * apply TR3; [exact DYIu| unfold A_DYING; lia| unfold A_DYING; cbn; lia].
      + (* [comment removed for export] *)
        destruct (SC2 mo3 HK3) as (_ & K4).
        pose proof (J_norep_grant m3 mo3 HJ3 addr nZ ltac:(lia) ltac:(lia) ltac:(lia) FR3) as HJ4.
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
        (* [comment removed for export] *)
        pose proof (rw_cells_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ FRM3 ltac:(cbn; lia)) as FRM4.
        pose proof (rw_cells_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ FRH3 ltac:(cbn; lia)) as FRH4.
        pose proof (stk_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ ST3 ltac:(lia)) as ST4.
        assert (MU4 : munch [(lo, SP); (addr, addr + nZ)] m (apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)])).
        { eapply (munch_unmaps m3 addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
          eapply munch_trans; [exact MUu|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
        pose proof (mem_inv_unmaps asegs m3 addr nZ Ha Hn Han MI3) as MI4.
        assert (ABS3 : forall x : word, addr <= bv_unsigned x < addr + nZ -> m3 x = None).
        { intros x Hx. rewrite (MU3 x); [apply ABSu; exact Hx| cbn [outside]; split; [lia| exact I]]. }
        assert (WM4 : wmono asegs m (apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)])).
        { eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WM3| exact (WMABS m3 ABS3)]. }
        set (m4 := apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody m4.
        eapply (evtA_srzJ_KJ AL CS K _ TA _ _ KL K4); [exact HJ4| |].
        { eapply (map_norep_post_ok AL IMG ALWF CS CSOK) with (m0 := m4); try eassumption; try lia.
          apply munch_refl. apply wmono_refl. }
        cbn beta. intros ms5 mo5 PO HK5 MM5 HJ5.
        ddestruct PO as (z5 & z6 & z7 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z28 & z29 & z30 & z31 & mm5 & -> & MU5 & WM5 & MI5 & ST5).
        apply HF. unfold mwc_postS. deexists 17. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply munch_trans; [exact MU4|]. eapply munch_weaken; [|exact MU5]. unfold sub_fp; cbn [outside]; intros; lia. }
        split; [eapply wmono_trans; [exact WM4| exact WM5]|].
        split; [exact MI5|]. split; [exact ST5|]. split; [exact HJ5| exact HK5].
    - (* [comment removed for export] *) exact SUCC.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MapWithCallbackSplit.

End ARUN_1.
