(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA AW_DepotA AW_DepotB AW_Poison AW_AllocB AW_MallocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Large AW_MallocC AW_SecB AW_CallocA AW_CallocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
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
Ltac2 gd_tbl_AW_CallocSecC () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rounded"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.A_POISON"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.CSecC.CSegSC.cssegC1_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "ARUN_1.CSecC.CSegSC.cssegC2_post"].

Section ARUN_1. Context {hAR : arun}.
Section CSecC.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Section CSegSC.
    Variables (SP n lo T CTX TID SB PA a ms : Z).
    Let STK := SP + -2136.
    Let SPA := SP + -2136 + -56.            (* [comment removed for export] *)
    Let AB := a + 4096.
    Let UB := AB + rz_size n.
    Let CHB := AB + rz_size n + -16.
    Let r8 := (nfix n + 7) / 8 * 8.
    Let rd := nfix n / 8 * 8.
    Let S1 := 0x7fff8000 + AB / 8.                (* [comment removed for export] *)
    Let S2 := 0x7fff8000 + (UB + r8) / 8.         (* [comment removed for export] *)
    Let k2 := (a + ms - (UB + r8)) / 8.
    Let SUB := 0x7fff8000 + UB / 8.
    Let PGS := 0x7fff8000 + Z.shiftr (UB + rd) 3.
    Hypothesis NB : 0 <= n < 2^32.
    Hypothesis FP : from_primary n = false.
    Hypothesis LOIMG : ACEIL <= lo.
    Hypothesis SPL : lo <= SP - 4096.
    Hypothesis SPH : SP + 16 <= 2^47.
    Hypothesis SPA16 : SP mod 16 = 0.
    Hypothesis T0 : Timg T. Hypothesis T1 : T + 4096 <= ACEIL. Hypothesis TAL : T mod 4096 = 0.
    Hypothesis CX0 : 0x65f000 <= CTX. Hypothesis CX1 : CTX + 0x10000 <= ACEIL.
    Hypothesis TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T.
    Hypothesis TIDB : 0 <= TID < 2^31.
    Hypothesis A0 : 0x65f000 <= a. Hypothesis AAL : a mod 4096 = 0. Hypothesis EMS : ms = map_size (needed2 n).
    Hypothesis ACE : a + ms <= ACEIL.
    Hypothesis ABAND : a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a.
    Hypothesis SB0 : 0 <= SB. Hypothesis SB1 : SB + 2^37 + 4096 <= ACEIL.
    Hypothesis APT : a + ms <= SB \/ SB + 2^37 + 4096 <= a.
    Hypothesis ABT : a + ms <= T \/ T + 4096 <= a.
    Hypothesis ABC : a + ms <= CTX \/ CTX + 0x10000 <= a.
    Hypothesis TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T.
    Hypothesis CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L18926556999.67L18926670282.66L18926759668.63L18928824262.61L18930958230.62L19935078135.4 L2040146651.1  L20506973870.3 L23075198487.5 L25047882783.4 L26594310986.1 L36550732658.5 L37341276942.12L48023213069.1 L61028696700.64L61028858315.68L61030806750.62L61030954876.74L61031316550.73L61477106382.2 L63368119078.63L63368132624.6500000j01d02^03X04R04^04a04j05:05B05E05R06006306m07g08a09R0:C0:J0;D0<>S3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS1n2NB2DN2MNS1aS1n2DN2MNS1a2ms2r82DM3DR8S1n1H2H0S1nS1n3NFX2D82M8S1n1a2ms2r83N2E3MSZ2DM3R8R3DR8S1aS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA3CHB2r82rd2S12S23PGS3SUBS3hAR2SP1n1T1a2ms3STK3SPA3CHB2r82rd2S12S23PGS3SUBS1n3NLOS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGS". (* [comment removed for export] *)
    #[using="hAR SP T STK SPA CHB S1 S2 SUB PGS NB FP AAL EMS"] Lemma sgeom : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecC ()) "(0.(1.+?<01.Vn,)(0.(2.$3.(4.Vn,)Vn,)(0.(2.$3.(5.Vn,)+800.)(0.(2.$3.(6.Vn,)(7.(8.Vn,)+1000.))(0.(0.(1.Vn,(8.Vn,))(1.(8.Vn,)(7.Vn,+7.)))(0.(2.$3.(9.(8.Vn,)+8.)=)(0.(0.(1.(7.(6.Vn,)+1000.)Vms,)(:.Vms,(7.(6.Vn,)+2000.)))(0.(2.$3.(9.Vms,+1000.)=)(0.(0.(1.Vn,Vr8,)(1.Vr8,(7.Vn,+7.)))(0.(2.$3.(9.Vr8,+8.)=)(0.(1.Vr8,(8.Vn,))(0.(0.(1.=Vrd,)(1.Vrd,Vn,))(0.(2.$3.(9.Vrd,+8.)=)(0.(:.Vn,(7.Vrd,+8.))(0.(2.$3.(9.VAB,+1000.)=)(0.(2.$3.(9.VUB,+8.)=)(0.(1.+8.Vk2,)(2.$3.(7.(7.VUB,Vr8,)(;.+8.Vk2,))(7.Va,Vms,)))))))))))))))))))")
(* [comment removed for export] *).
    Proof.
      dpose (sec_sizes n NB FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
      assert (MSZ : needed2 n + 4096 <= ms < needed2 n + 8192 /\ ms mod 4096 = 0).
      { rewrite EMS. unfold map_size. pose proof (Z.div_mod (needed2 n + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed2 n + 4095) 4096 ltac:(lia)).
        split; [clear - H H0 N2B; lia|]. rewrite Z.add_mod, Z_mod_mult, Z.add_0_l by lia. reflexivity. }
      pose proof (Z.div_mod (nfix n + 7) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (nfix n + 7) 8 ltac:(lia)) as M8.
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MN.
      pose proof (Z.div_mod a 4096 ltac:(lia)) as DA. rewrite AAL, Z.add_0_r in DA.
      pose proof (Z.div_mod ms 4096 ltac:(lia)) as DM. rewrite (proj2 MSZ), Z.add_0_r in DM.
      pose proof (Z.div_mod (rounded n) 8 ltac:(lia)) as DR. rewrite RN8, Z.add_0_r in DR.
      assert (R8E : r8 = (nfix n + 7) / 8 * 8) by reflexivity. assert (RDE : rd = nfix n / 8 * 8) by reflexivity.
      assert (ABE : AB = a + 4096) by reflexivity. assert (UBE : UB = AB + rz_size n) by reflexivity. assert (K2E : k2 = (a + ms - (UB + r8)) / 8) by reflexivity.
      clearbody r8 rd AB UB k2. subst AB UB.
      assert (R8B : n <= r8 <= n + 7 /\ r8 mod 8 = 0) by (split; [rewrite R8E; clear - D8 M8 NFX NB; lia| rewrite R8E; apply Z_mod_mult]).
      assert (R8R : r8 <= rounded n).
      { unfold rounded, round_up. rewrite R8E, NFX. replace (Z.max n 8) with n by (clear - NLO; lia). clear. lia. }
      assert (RDB : 0 <= rd <= n /\ rd mod 8 = 0 /\ n < rd + 8) by (rewrite RDE; rewrite NFX in *; split; [clear - DN MN NB; lia| split; [apply Z_mod_mult| clear - DN MN; lia]]).
      pose proof (Z.div_mod r8 8 ltac:(lia)) as DR8. rewrite (proj2 R8B), Z.add_0_r in DR8.
      assert (K2 : 8 <= k2 /\ a + 4096 + rz_size n + r8 + 8 * k2 = a + ms).
      { rewrite K2E, RZ. replace (a + ms - (a + 4096 + 2048 + r8)) with ((512 * (ms / 4096) - 768 - r8 / 8) * 8) by (clear - DM DR8; lia).
        rewrite Z.div_mul by lia. clear - DA DM DR8 MSZ N2E R8R RNB RZ. lia. }
      split; [exact NLO|]. split; [exact NFX|]. split; [exact RZ|]. split; [exact N2E|]. split; [exact RNB|]. split; [exact RN8|].
      split; [exact (proj1 MSZ)|]. split; [exact (proj2 MSZ)|]. split; [exact (proj1 R8B)|]. split; [exact (proj2 R8B)|]. split; [exact R8R|].
      split; [exact (proj1 RDB)|]. split; [exact (proj1 (proj2 RDB))|]. split; [exact (proj2 (proj2 RDB))|].
      split. { rewrite DA at 1. replace (4096 * (a / 4096) + 4096) with ((a / 4096 + 1) * 4096) by (clear; lia). apply Z_mod_mult. }
      split. { rewrite RZ. rewrite DA at 1. replace (4096 * (a / 4096) + 4096 + 2048) with ((512 * (a / 4096) + 768) * 8) by (clear; lia). apply Z_mod_mult. }
      clear - K2. exact K2.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Ltac geo GEO := cbn [disjoint_from cells_size csize Nat.add length repeat]; rewrite ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia);
                    clear - GEO; decompose [and] GEO; repeat split; lia.
    Ltac geoh GEO H := cbn [disjoint_from cells_size csize Nat.add length repeat]; clear - GEO H; decompose [and] GEO; repeat split; lia.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition cssegC1_post (gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b0 : byte) (b1 : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecC ()) "Lms',$<.(=.(>.&40.)Ly5,(>.&40.)(=.(>.&40.)Ly6,(>.&40.)(=.(>.&40.)Ly7,(>.&40.)(=.(>.&40.)Lya3,(>.&40.)(=.(>.&40.)Lya4,(>.&40.)(=.(>.&40.)Lya5,(>.&40.)(=.(>.&40.)Lya6,(>.&40.)(=.(>.&40.)Lya7,(>.&40.)(=.(>.&40.)Ly28,(>.&40.)(=.(>.&40.)Ly29,(>.&40.)(=.(>.&40.)Ly30,(>.&40.)(=.(>.&40.)Ly31,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(0.(2.$<.R>.(10.(11.(12.&40.+47?4<.)(12.&40.(7.VSPA,-80.))O7.(12.&40.$13.)R=.R<.R;.(12.&40.(14.Vms,+1000.))(12.&40.(4.Vn,))(12.&40.VUB,)(12.&40.Vrd,)(12.&40.=)R:.R9.R8.R7.R6.(12.&40.VAB,)(12.&40.(6.Vn,))(12.&40.VUB,)(12.&40.VCHB,)(12.&40.Vrd,)(12.&40.VSTK,)(12.&40.(;.VTID,(15.+2.+20.)))(12.&40.(7.(7.VUB,(4.Vn,))+7.))(12.&40.VT,)(12.&40.+1.)R5.R4.R3.R2.)O6.(12.&40.$16.)O5.(17.(>.&40.))R1.(18.$19.)))(0.(1:.(1;.(1<.$3.$3.)(1=.$3.$3.Vlo,(7.VSPA,-80.))(1;.(1<.$3.$3.)(1=.$3.$3.(7.VCHB,+8.)(7.VCHB,+10.))(1;.(1<.$3.$3.)(1=.$3.$3.VS1,(7.VS1,+100.))(1;.(1<.$3.$3.)(1=.$3.$3.VS2,(7.VS2,Vk2,))(1>.(1<.$3.$3.))))))O1.R1.)(0.(1?.$19.O1.R1.)(0.(20.$19.R1.)(0.(21.$19.R1.VCHB,(1;.$22.(23.O3.)(1;.$22.(23.(12.&8.O2.))(1;.$22.(24.(12.&40.=))(1;.$22.(25.(12.&40.(4.Vn,)))(1;.$22.(26.(12.&40.(27.(;.VTID,(15.+2.+20.))O4.)))(1>.$22.)))))))(0.(21.$19.R1.VS1,(1;.$22.(28.#100.(29.(>.&8.)(12.&8.+?:.)#100.))(1>.$22.)))(0.(21.$19.R1.VS2,(1;.$22.(28.(2:.Vk2,)(29.(>.&8.)(12.&8.+?:.)(2:.Vk2,)))(1>.$22.)))(2;.$19.R1.Vlo,(7.VSPA,-80.))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L11480693016.1  L11963167616.26 L12364544331.30 L13053391865.30 L13577440422.26 L14394589950.0  L17120848823.0  L18928480195.123L18928656380.125L22282470256.30 L23180146931.33 L24888640626.2  L2513005359.3   L26069473969.30 L26275543149.2  L26601925816.30 L27848808849.2  L27882308574.2  L27991817377.3  L28842485356.26 L2980825940.30  L29869605421.26 L3072638866.26  L31659743062.2  L34454583295.30 L34554831375.26 L35243480167.33 L38235734261.1  L3826741602.26  L39049007132.31 L39218935524.32 L41013457876.26 L41855637219.26 L43085192576.4  L43591259855.26 L44238746145.30 L44242070305.0  L44282459030.3  L46569381820.30 L4747819224.26  L479555979.26   L49301304832.33 L49378257077.30 L50541853227.26 L53867763805.30 L54274957729.0  L55588686165.0  L57250463165.2  L60442537825.30 L61028859847.124L61744303959.0  L62445146182.2  L6484288559.30  L68630024387.30 L6926174842.26  L8411154290.30  L8923956413.14  00000300V01W02D02g02h02i03c04]05O06B06F06S07N07V08>08E08I08T09909i0:N0:m0;10<20<T0=G0=K0=m0>U0?C0?k0@N0@^0AA0Ai0Aj0B40Bd0CJ0Cm0D^0E_0FE0GF0GG0GH0GN0H60I00I10I70Ij0Jn0KU0LU0MAS1aS3hAR2SP1n1a2ms3SPA2AB2UB2r82k23ACES3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO1H2H32H42H52H62H73H15S3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21H2H52H7S3hAR2SP1n1a2ms3SPA2AB2UB2r82k23ACESSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k22H32H43H13S3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21A1k2Hk2H83H10S2SPS2SP3SPA4SPAHS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k22H32H42H52H62H73H13S2SP3SPHS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k22H6S2SP2loS2SPS2SP2lo3SPLS3hAR2SP1n1a2ms3SPA2AB2UB2r82k25ABANDS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21H2H52H72H8S3hAR2SP1n1a2ms3SPA2AB2UB2r82k22A02DAS3hAR2SP1n1a2ms3SPA2AB2UB2r82k2S2SPS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO1H2H32H42H52H62H73H15S3hAR2SP1n1a2ms3SPA2AB2UB2r82k22DAS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k21A1k2Hk3H13S2loS3hAR2SP1n1a2ms3SPA2AB2UB2r82k22A0S3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k22H3S3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k22DA3DR81HS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82k25LOIMGS3hAR2SP1n1a2ms3SPA2AB2UB2r82k23NLOS2SP2lo3SPA4SPALS3hAR2SP1n1a2ms3SPA2AB2UB2r82k23K2BS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k22H4SS1n2ms3MSZS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21H2H52H72H8S3hAR2SP1n1a2ms3SPA2AB2UB2r82k22DA3DR8S3hAR2SP1n1a2ms3SPA2AB2UB2r82k23R8BS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21A1k2Hk1H2H2S3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO1H2H42H52H62H72H83H15S3hAR2SP1n1a2ms3SPA2AB2UB2r82k23K2E2DMS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO1H2H42H52H62H72H83H15SSS1a2DAS3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k22H4S3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGSSS1a2A0S3hAR2SP1n1a2ms3SPA2AB2UB2r82S12S22k21H2H42H52H62H7S3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO1H2H32H42H52H62H73H152H2S3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82k24SPALS3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k21H2H32H42H52H62H72H83H13S3hAR2SP1n2lo1a2ms3SPA2AB2UB2r82S12S22k23GEO". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK ASB SUB PGS NB FP LOIMG SPL SPH SPA16 TIDB A0 AAL EMS ACE ABAND SB0 SB1 APT"] Lemma cssegC1 : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecC ()) "Pgp,(>.&40.)Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Px11,(>.&40.)Px12,(>.&40.)Px13,(>.&40.)Px14,(>.&40.)Px15,(>.&40.)Px16,(>.&40.)Px17,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pb0,(>.&8.)Pw8,(>.&40.)PF,(2<.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))Pid,$3.Pb1,$3.Pncks,$3.Psh1,(2=.(>.&8.))Psh2,(2=.(>.&8.))P,(0.(1.=R5.)(:.R5.(15.+2.+1?.)))P,(0.(1.=R5.)(:.R5.+100.))P,(2>.VCS,Va,Vms,)P,(21.$19.R9.VCHB,(1;.$22.(23.R=.)(1;.$22.(23.(12.&8.R7.))(1;.$22.(24.(12.&40.=))(1;.$22.(25.(12.&40.(4.Vn,)))(1;.$22.(26.R<.)(1>.$22.)))))))P,(21.$19.R:.Va,(1;.$22.(26.(12.&40.Va,))(1;.$22.(26.(12.&40.Vms,))(1;.$22.(26.(12.&40.(6.Vn,)))(1;.$22.(26.(12.&40.R7.))(1>.$22.))))))P,(2?.$19.R;.(7.$30.+20.)(1;.$22.(26.(12.&40.VSB,))(1>.$22.)))P,(31.R<.VPA,)P,(32.R=.)P,(21.$19.R>.VS1,(1;.$22.(28.#100.R:.)(1>.$22.)))P,(21.$19.R?.VS2,(1;.$22.(28.(2:.Vk2,)R:.)(1>.$22.)))P,(2;.$19.R10.Vlo,(7.VSPA,-80.))P,(2>.VCS,Vlo,(14.VSP,Vlo,))P,(20.$19.R12.)(33.$19.VAL,VCS,(34.R26.R15.R14.R12.R17.R11.R13.)(10.(11.(12.&40.+47>40.)(12.&40.(7.VSPA,-80.))R26.(12.&40.$13.)R25.R24.R23.(12.&40.=)(12.&40.(4.Vn,))(12.&40.R12.)R22.R21.R20.R1?.R1>.R1=.R1<.(12.&40.VAB,)(12.&40.(6.Vn,))(12.&40.VUB,)(12.&40.VCHB,)(12.&40.$30.)(12.&40.VSTK,)(12.&40.(;.VTID,(15.+2.+20.)))(12.&40.(7.VUB,(4.Vn,)))(12.&40.VT,)(12.&40.+1.)R1;.R1:.R19.R18.)R15.(12.&40.+47>40.)R14.(17.(>.&40.))R13.(18.$19.)))")
(* [comment removed for export] *).
    Proof.
      intros gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 b0 w8 F fc m id b1 ncks sh1 sh2
        IDB B1B BCS HDR HH SBC LS PS SH1 SH2 ST SCS MI.
      facts.
      dpose sgeom as (NLO & NFX & RZ & N2E & RNB & RN8 & MSZ & MSAL & R8B & R8AL & R8R & RDB & RDAL & RDH & ABAL & UBAL & K2B & K2E).
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2136 + -56) with (SP + (-137) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SPAAL2 : (SPA + -128) mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2136 + -56 + -128) with (SP + (-145) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      assert (SCSA2 : crange CS lo (SPA + -128 - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      assert (ABE : AB = a + 4096) by reflexivity. assert (UBE : UB = AB + rz_size n) by reflexivity.
      assert (S1E : S1 = 0x7fff8000 + AB / 8) by reflexivity. assert (S2E : S2 = 0x7fff8000 + (UB + r8) / 8) by reflexivity.
      pose proof (Z.div_mod a 4096 ltac:(lia)) as DA. rewrite AAL, Z.add_0_r in DA.
      pose proof (Z.div_mod r8 8 ltac:(lia)) as DR8. rewrite R8AL, Z.add_0_r in DR8.
      (* [comment removed for export] *)
      assert (GEO : rz_size n = 2048 /\ AB = a + 4096 /\ UB = a + 6144 /\ 0x65f000 <= a /\ a + ms <= ACEIL /\ UB + r8 + 8 * k2 = a + ms /\ n <= r8 /\ 8 <= k2 /\ 0xfc01 <= n
                    /\ S1 = 0x7fff8000 + a / 8 + 512 /\ S2 = 0x7fff8000 + a / 8 + 768 + r8 / 8 /\ 0 <= a / 8 /\ a / 8 + ms / 8 <= 0xffffeff00000
                    /\ lo <= SPA - 512 /\ ACEIL <= lo /\ (a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a)).
      { rewrite S1E, S2E, UBE, ABE, RZ. pose proof (Z.div_mod ms 4096 ltac:(lia)) as DM. rewrite MSAL, Z.add_0_r in DM.
        clear - DA DM DR8 A0 ACE K2E R8B K2B NLO SPAL LOIMG ABAND RZ UBE ABE. rewrite UBE, ABE, RZ in K2E. repeat split; lia. }
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (sec_midA AL IMG ALWF CS CSOK) with (W := []) (PA := PA) (SB := SB) (ncks := ncks);
          [ exact NB | exact FP | exact ABE | exact AAL | exact A0 | exact EMS | exact ACE | exact SB0 | exact SB1 | exact APT | exact TIDB | exact IDB | exact B1B | exact BCS
          | exact HDR | exact HH | exact SBC | exact LS | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m1 & -> & MU1 & WM1 & MI1 & HDR1 & ST1)).
      fold UB in MU1, HDR1 |- *. fold CHB in MU1, HDR1 |- *. fold r8.
      assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ m m1 PS MU1); intros A k Hk; unfold CHB, UB, AB; geoh GEO Hk).
      assert (SH11 : rw_cells asegs m1 S1 [CB (Z.to_nat (rz_size n / 8)) sh1]).
      { rewrite RZ. change (Z.to_nat (2048 / 8)) with 256%nat. eapply rw_cells_transport; [exact SH1| exact MU1| exact WM1| unfold CHB, UB; geo GEO]. }
      (* [comment removed for export] *)
      eapply evtA_cut.
      { rewrite S1E in SH11.
        eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (m0 := m1);
          [ | | | | | | | exact SH11 | exact PS1 | exact ST1 | exact LOIMG | clear - SPAL; lia | clear - SPAH; lia | exact SPAAL2 | exact SCSA2 | apply munch_refl | apply wmono_refl | exact MI1 ].
        - rewrite ABE. clear - DA. replace (a + 4096) with ((512 * (a / 4096) + 512) * 8) by lia. apply Z_mod_mult.
        - rewrite RZ. reflexivity.
        - rewrite RZ. clear; lia.
        - clear; lia.
        - rewrite RZ, ABE. clear - GEO. decompose [and] GEO. lia.
        - left. clear; lia.
        - eapply (crange_sub CS a ms); [exact BCS| rewrite ABE; clear; lia| rewrite ABE, RZ; clear - GEO; decompose [and] GEO; lia]. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (z0 & z1 & z2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m2 & -> & MU2 & WM2 & MI2 & SHP1 & ST2)).
      replace (ret_pc (Z_to_bv 64 0x47f18)) with (Z_to_bv 64 0x47f18) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      rewrite RZ in SHP1, MU2. change (Z.to_nat (2048 / 8)) with 256%nat in SHP1. change (2048 / 8) with 256 in MU2. rewrite <- S1E in SHP1, MU2.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (sec_midB AL IMG ALWF CS CSOK) with (ms := ms); [exact NB| exact FP| | | | exact MI2].
        - rewrite ABE; clear - A0; lia. - clear - GEO MSZ; decompose [and] GEO; lia. - clear - MSZ; lia. }
      cbn beta. intros ms3 ->. fold r8. fold UB.
      replace (AB + (ms - 4096) - (UB + r8)) with (8 * k2) by (clear - GEO; decompose [and] GEO; lia).
      assert (PS2 : poison_statics m2) by (eapply (poison_statics_transport _ m1 m2 PS1 MU2); intros A k Hk; geoh GEO Hk).
      assert (SH22 : rw_cells asegs m2 (0x7fff8000 + (UB + r8) / 8) [CB (Z.to_nat (8 * k2 / 8)) sh2]).
      { rewrite Z.mul_comm, Z.div_mul by (clear; lia). rewrite <- S2E.
        eapply rw_cells_transport; [| exact MU2| exact WM2| geo GEO]. eapply rw_cells_transport; [exact SH2| exact MU1| exact WM1| unfold CHB, UB; geo GEO]. }
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (m0 := m2);
          [ | | | | | | | exact SH22 | exact PS2 | exact ST2 | exact LOIMG | clear - SPAL; lia | clear - SPAH; lia | exact SPAAL2 | exact SCSA2 | apply munch_refl | apply wmono_refl | exact MI2 ].
        - clear - GEO DR8 DA. decompose [and] GEO. replace (UB + r8) with ((512 * (a / 4096) + 768 + r8 / 8) * 8) by lia. apply Z_mod_mult.
        - rewrite Z.mul_comm. apply Z_mod_mult.
        - clear - GEO; decompose [and] GEO; lia.
        - clear; lia.
        - clear - GEO. decompose [and] GEO. lia.
        - left. clear; lia.
        - eapply (crange_sub CS a ms); [exact BCS| clear - GEO; decompose [and] GEO; lia| clear - GEO; decompose [and] GEO; lia]. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & SHP2 & ST4)).
      replace (ret_pc (Z_to_bv 64 0x47f2c)) with (Z_to_bv 64 0x47f2c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      rewrite (Z.mul_comm 8 k2), Z.div_mul in SHP2, MU4 by (clear; lia). rewrite <- S2E in SHP2, MU4.
      (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (sec_midC AL IMG ALWF CS CSOK); [exact NB| exact FP| exact MI4]. }
      cbn beta. intros ms5 ->. fold rd. fold UB.
      unfold cssegC1_post. deexists 12. exists m4. split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_weaken; [| exact MU4]. replace (S2 + 8 * k2 / 8) with (S2 + k2) by (rewrite (Z.mul_comm 8 k2), Z.div_mul by (clear; lia); reflexivity).
               unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
      split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM4]]|]. split; [exact MI4|].
      split. { eapply rw_cells_transport; [| exact MU4| exact WM4| unfold CHB, UB; geo GEO]. eapply rw_cells_transport; [exact HDR1| exact MU2| exact WM2| unfold CHB, UB; geo GEO]. }
      split. { eapply rw_cells_transport; [exact SHP1| exact MU4| exact WM4| geo GEO]. }
      split; [exact SHP2|]. exact ST4.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition cssegC2_post (ra gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b1 : Z) (pgb : byte)
        (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecC ()) "Lms',$<.(=.(>.&40.)Lt0,(>.&40.)(=.(>.&40.)Lt1,(>.&40.)(=.(>.&40.)Lt2,(>.&40.)(=.(>.&40.)La1,(>.&40.)(=.(>.&40.)La2,(>.&40.)(=.(>.&40.)La3,(>.&40.)(=.(>.&40.)La4,(>.&40.)(=.(>.&40.)La5,(>.&40.)(=.(>.&40.)La6,(>.&40.)(=.(>.&40.)La7,(>.&40.)(=.(>.&40.)Lt3,(>.&40.)(=.(>.&40.)Lt4,(>.&40.)(=.(>.&40.)Lt5,(>.&40.)(=.(>.&40.)Lt6,(>.&40.)(=.(>.&40.)Lj0,(>.&40.)(=.(>.&40.)Lj1,(>.&40.)(=.(>.&40.)Lj2,(>.&40.)(=.(>.&40.)Lj4,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(0.(2.$<.R14.(10.(11.O14.(12.&40.VSP,)O13.(12.&40.$13.)R13.R12.R11.O=.O<.(12.&40.VUB,)R10.R?.R>.R=.R<.R;.R:.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.R9.R8.R7.R6.)O12.(35.O14.)O11.(17.(>.&40.))R1.(18.$19.)))(0.(1:.(1;.(1<.$3.$3.)(1=.$3.$3.Vlo,VSP,)(1;.(1<.$3.$3.)(1=.$3.$3.VPGS,(7.VPGS,+1.))(1;.(1<.$3.$3.)(1=.$3.$3.(7.VT,+:?0.)(7.VT,+;08.))(1;.(1<.$3.$3.)(1=.$3.$3.(7.VT,+;58.)(7.VT,+;60.))(1;.(1<.$3.$3.)(1=.$3.$3.VCHB,(7.VCHB,+2.))(1;.(1<.$3.$3.)(1=.$3.$3.VAB,(7.VAB,+10.))(1>.(1<.$3.$3.))))))))O1.R1.)(0.(1?.$19.O1.R1.)(0.(20.$19.R1.)(0.(21.$19.R1.VCHB,(1;.$22.(23.(12.&8.$36.))(1;.$22.(23.(12.&8.(37.O?.+?3.)))(1;.$22.(24.(12.&40.=))(1;.$22.(25.(12.&40.(4.Vn,)))(1;.$22.(26.(12.&40.(27.(;.VTID,(15.+2.+20.))O10.)))(1>.$22.)))))))(0.(21.$19.R1.VAB,(1;.$22.(26.(12.&40.$38.))(1;.$22.(26.(12.&40.VCHB,))(1>.$22.))))(0.(21.$19.R1.VPGS,(1;.$22.(23.(39.Vn,O>.))(1>.$22.)))(0.(21.$19.R1.(7.VT,+:?0.)(1;.$22.(26.R5.)(1;.$22.(26.R4.)(1;.$22.(26.R3.)(1>.$22.)))))(0.(21.$19.R1.(7.VT,+;58.)(1;.$22.(26.R2.)(1>.$22.)))(2;.$19.R1.Vlo,VSP,)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0290@L10184719229.41 L10239745294.35 L10411599780.35 L10729109122.35 L11034691602.41 L11305282180.35 L11369523398.2  L11380347005.3  L11480693016.1  L11564273983.45 L11963020033.35 L12044241256.35 L12190185686.41 L12587123443.44 L12587123452.45 L12657976027.41 L13577292839.35 L13944824677.41 L14883623720.3  L15036699472.251L15099036752.44 L15099036753.44 L15099036766.45 L15247168331.41 L15585609264.41 L15687369743.41 L17497049875.41 L17882144253.41 L18939253232.175L18941041780.167L19457912907.41 L20070261741.3  L21175256044.3  L2149977192.41  L21888640297.41 L22377909701.43 L23449247685.41 L23462114031.242L23642742085.41 L24035990205.7  L24888640626.2  L24922515638.41 L25309584093.242L25319937932.3  L26112146379.41 L26275543149.2  L26395605637.41 L27015343992.35 L27848808849.2  L27991817377.3  L28842600173.35 L29105961052.3  L29786741737.10 L29869490860.35 L30846768868.3  L31423381068.41 L31659743062.2  L31747570154.0  L31839289911.41 L31921856614.44 L31921856615.44 L31921856617.45 L32366633738.41 L34504207265.248L34833095572.35 L35243480295.44 L35853332965.41 L37116625474.35 L38235734261.1  L3826594275.35  L38285503208.41 L39046678806.3  L39783231976.41 L40156106605.2  L40480664211.41 L41013343061.35 L41855489634.35 L42088112013.41 L42333736060.19 L42333736060.20 L42333736189.15 L4276959689.0   L44280364546.35 L44332321676.41 L44343137695.35 L44803356841.3  L4485222595.35  L45053108443.41 L46947602201.41 L46969862548.35 L47235967338.4  L48063988754.3  L49002707954.247L49535152582.44 L49535152585.45 L49858401057.0  L49890578593.3  L51168184294.44 L51168184297.45 L51563618454.41 L51568748816.35 L51729363575.35 L52016865375.45 L5423397493.2   L54702911965.255L55667075291.41 L56559209730.2  L57248903173.41 L58180284812.41 L58858159141.6  L60646110233.41 L60779458884.0  L60900111436.41 L60999025285.41 L61028858315.176L61028859847.3  L61484355281.35 L61653547298.253L62012458031.41 L62445146182.2  L62515090251.41 L63063788605.2  L63368132624.177L63988471514.257L64446151349.41 L64473983707.41 L64860697064.41 L65181476846.0  L67484541264.44 L67484541265.44 L67484541278.45 L67995507890.1  L6926322427.35  L7888185264.41  L8694109837.41  L8718464266.41  L9717231777.0   00000e01i02S03:04<05D05H05S05V06a07F07l08[09Q0:I0;R0<@0=I0=T0>T0?\0@d0A`0BK0C@0Ck0DV0EK0FK0GK0H60HA0HL0I;0Ij0Jd0L60Ln0N@0NZ0N^0P10Pi0Q10Q\0Qd0R]0Sk0T20T=0Td0To0U=0VG0VM0Wc0Wg0Wh0XW0YR0ZL0[S0\>0]>0^E0_;0`D0aK0aO0b30bb0bn0c]0ce0dT0e>0ec0g50gX0h?0hX0hY0i>0j90kG0kL0km0m90n20o90oE0oP10L11A12F12G12R13D14F15\16D17H18?18G19G1:S1:Z1;f1<d1=81>11>21?E1@Q1AQ1AT1B:1C:1D81D>1Di1Do1Eo1Fo1GZ1Hc1IR1IS1J[1Kc1L_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R2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO2H22H32H52H62H73H193H213H22S3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGS2H22H42H52H62H73H15S3hAR1n1a2ms3ACE3MSZS3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3H153H183H20SS3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO2H42H52H62H72H82H93H193H203H213H22S3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO2H22H32H52H62H73H193H213H22S3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGS2ws2HLS1aS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2T1S3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGS2ws2HLS3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGS2H42H52H62H82H93H15S1a2A0S3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGSS1a2DAS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGS2ws2HLS3hAR2SP1n1T1a2ms3STK3SPA2AB2UB3CHB2r82rd2S12S22k23SUB3PGS2ws2HLS3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGSS3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO2H32H52H62H73H193H213H22S3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3H18SS3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO1A1k2Hk2H32H52H62H73H25S3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO1A1k2H12H42H62H72H83H26S3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS1A1k2H23H173H22S2SPS3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB4SPALS3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3H153H20S3hAR2SP1n2lo1T1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3GEO2H32H42H52H62H72H82H93H193H213H22S3hAR2SP1n2lo1a2ms3STK3SPA2AB2UB3CHB2rd3PGS3H16S". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK ASB r8 S1 S2 k2 SUB NB FP LOIMG SPL SPH SPA16 T0 T1 CX0 CX1 TC A0 AAL EMS ACE ABAND SB0 SB1 APT ABT ABC TNS CTXNS"] Lemma cssegC2 : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecC ()) "Pra,(>.&40.)Pgp,(>.&40.)Px1,(>.&40.)Px5,(>.&40.)Px6,(>.&40.)Px7,(>.&40.)Px10,(>.&40.)Px11,(>.&40.)Px12,(>.&40.)Px13,(>.&40.)Px14,(>.&40.)Px15,(>.&40.)Px16,(>.&40.)Px17,(>.&40.)Px28,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pq0,(>.&40.)Pq1,(>.&40.)Pq2,(>.&40.)Pq3,(>.&40.)Pq4,(>.&40.)Pq5,(>.&40.)Pq6,(>.&40.)Pq7,(>.&40.)Pq8,(>.&40.)Pq9,(>.&40.)Pq10,(>.&40.)Pq11,(>.&40.)Pp0,(>.&40.)Pp1,(>.&40.)Pp2,(>.&40.)Pp3,(>.&40.)Pmg0,(>.&40.)Pmg1,(>.&40.)Pj0,(>.&40.)Pj1,(>.&40.)Pj2,(>.&40.)Pj4,(>.&40.)Pb0,(>.&8.)Ppgb,(>.&8.)PF,(2<.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))Pid,$3.Pb1,$3.Psize,$3.Pfr0,(2=.(>.&8.))Pfr1,(2=.(>.&8.))Pfr2,(2=.(>.&8.))Pfr3,(2=.(>.&8.))Pfr4,(2=.(>.&8.))Pws,(2=.(>.&40.))P,(0.(1.=R9.)(:.R9.(15.+2.+1?.)))P,(0.(1.=R9.)(:.R9.+100.))P,(2>.VCS,Va,Vms,)P,(2?.$19.R=.(7.$30.+20.)(1;.$22.(26.(12.&40.VSB,))(1>.$22.)))P,(3:.R>.VT,VCTX,)P,(2>.VCS,VT,+1000.)P,(2>.VCS,VCTX,+10000.)P,(32.R11.)P,(3;.R12.)P,(2?.$19.R13.$3<.(1;.$22.(26.(12.&40.$3=.))(1>.$22.)))P,(2?.$19.R14.$3>.(1;.$22.(23.(12.&8.+1.))(1>.$22.)))P,(21.$19.R15.VCHB,(1;.$22.(23.R19.)(1;.$22.(23.(12.&8.R13.))(1;.$22.(24.(12.&40.=))(1;.$22.(25.(12.&40.(4.Vn,)))(1;.$22.(26.(12.&40.(27.(;.VTID,(15.+2.+20.))R14.)))(1>.$22.)))))))P,(21.$19.R16.VAB,(1;.$22.(26.R20.)(1;.$22.(26.R1?.)(1>.$22.))))P,(21.$19.R17.VPGS,(1;.$22.(23.R1:.)(1>.$22.)))P,(21.$19.R18.(7.VT,+:?0.)(1;.$22.(26.R20.)(1;.$22.(26.R1?.)(1;.$22.(26.R1>.)(1>.$22.)))))P,(21.$19.R19.(7.VT,+;58.)(1;.$22.(26.R1>.)(1>.$22.)))P,(3?.R1:.VSPA,R16.=(12.&40.+48470.)(12.&40.Vn,)(12.&40.VSTK,)(12.&40.$30.)(12.&40.+1.)(12.&40.+1.)(12.&40.VSTK,)(12.&40.(7.VSP,-59.))R2=.R2<.R2;.R2:.R29.)P,(21.$19.R1;.(7.VSTK,-38.)(1;.$22.(28.#8.R13.)(1;.$22.(26.R26.)(1;.$22.(26.R27.)(1;.$22.(26.R28.)(1;.$22.(26.R29.)(1;.$22.(26.(12.&40.+699<4.))(1>.$22.))))))))P,(21.$19.R1<.(7.VSP,-40.)(1;.$22.(26.R30.)(1;.$22.(26.R31.)(1;.$22.(26.R32.)(1;.$22.(26.R33.)(1;.$22.(26.R34.)(1;.$22.(26.R35.)(1;.$22.(26.R36.)(1;.$22.(26.R48.)(1>.$22.))))))))))P,(21.$19.R1=.(7.VSTK,-8.)(1;.$22.(28.#8.R16.)(1>.$22.)))P,(21.$19.R1>.VSTK,(1;.$22.(26.(12.&40.(7.VSTK,+10.)))(1;.$22.(26.(12.&40.R1;.))(1>.$22.))))P,(40.$19.R1?.(7.VSTK,+10.)R16.)P,(2.$41.(42.(>.&40.)R17.)#1>.)P,(21.$19.R21.(7.VSTK,+100.)(1;.$22.(28.#708.R1<.)(1>.$22.)))P,(21.$19.R22.(7.VSTK,+808.)(1;.$22.(26.(12.&40.VSP,))(1>.$22.)))P,(21.$19.R23.(7.VSTK,+810.)(1;.$22.(28.#8.R1=.)(1>.$22.)))P,(2;.$19.R24.Vlo,(7.VSPA,-80.))P,(2>.VCS,Vlo,(14.VSP,Vlo,))P,(20.$19.R26.)(33.$19.VAL,VCS,(43.R53.R52.R29.R28.R26.R25.R2:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R27.)(10.(11.R51.(12.&40.(7.VSPA,-80.))R52.(12.&40.$13.)R50.R4?.R4>.(12.&40.(14.Vms,+1000.))(12.&40.(4.Vn,))R4=.R4<.R4;.R4:.R49.R48.R47.R46.(12.&40.VAB,)(12.&40.(6.Vn,))(12.&40.VUB,)(12.&40.VCHB,)(12.&40.Vrd,)(12.&40.VSTK,)(12.&40.(;.VTID,(15.+2.+20.)))(12.&40.(7.(7.VUB,(4.Vn,))+7.))(12.&40.VT,)(12.&40.+1.)R45.R44.R43.R42.)R29.(12.&40.+47?4<.)R28.(17.(>.&40.))R27.(18.$19.)))")
(* [comment removed for export] *).
    Proof.
      intros ra gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 t4 t5 t6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 p0 p1 p2 p3 mg0 mg1 j0 j1 j2 j4 b0 pgb
        F fc m id b1 size fr0 fr1 fr2 fr3 fr4 ws
        IDB B1B BCS SBC AS TCS CTXCS PS FS GOTFL PPART HDR MG PGC STH ST4 AFR FR16 FR7 FJ STKC HTR HL F1800 TFB F8 ST SCS MI.
      facts.
      dpose sgeom as (NLO & NFX & RZ & N2E & RNB & RN8 & MSZ & MSAL & R8B & R8AL & R8R & RDB & RDAL & RDH & ABAL & UBAL & K2B & K2E).
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2136 + -56) with (SP + (-137) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      assert (ABE : AB = a + 4096) by reflexivity. assert (UBE : UB = AB + rz_size n) by reflexivity. assert (CHBE : CHB = AB + rz_size n + -16) by reflexivity.
      assert (RDE : rd = nfix n / 8 * 8) by reflexivity. assert (PGSE0 : PGS = 0x7fff8000 + Z.shiftr (UB + rd) 3) by reflexivity.
      pose proof (Z.div_mod a 4096 ltac:(lia)) as DA. rewrite AAL, Z.add_0_r in DA.
      assert (AB0 : 0x65f000 <= AB) by (rewrite ABE; clear - A0; lia).
      assert (AB1 : AB + needed2 n <= ACEIL) by (rewrite ABE; clear - ACE MSZ; lia).
      assert (AB16 : AB mod 16 = 0) by (rewrite ABE; clear - DA; replace (a + 4096) with ((256 * (a / 4096) + 256) * 16) by lia; apply Z_mod_mult).
      assert (RNG' : (AB + needed2 n <= 0x7fff8000) \/ (0x10007fff8000 <= AB /\ AB + needed2 n <= ACEIL)) by (rewrite ABE; clear - ABAND ACE MSZ; lia).
      assert (ACS : crange CS AB (needed2 n)) by (eapply (crange_sub CS a ms); [exact BCS| rewrite ABE; clear; lia| rewrite ABE; clear - MSZ; lia]).
      assert (SHR : Z.shiftr (UB + rd) 3 = a / 8 + 768 + nfix n / 8).
      { rewrite Z.shiftr_div_pow2 by (clear - A0 RDB UBE ABE RZ; lia). change (2^3) with 8. rewrite UBE, ABE, RZ, RDE.
        clear - DA. replace (a + 4096 + 2048 + nfix n / 8 * 8) with ((512 * (a / 4096) + 768 + nfix n / 8) * 8) by lia. rewrite Z.div_mul by lia.
        replace a with ((512 * (a / 4096)) * 8) at 2 by lia. rewrite Z.div_mul by lia. lia. }
      assert (MIN4 : Z.min (nfix n) 4096 = 4096) by (rewrite NFX; clear - NLO; lia).
      assert (GEO : rz_size n = 2048 /\ AB = a + 4096 /\ UB = a + 6144 /\ CHB = a + 6128 /\ 0x65f000 <= a /\ a + ms <= ACEIL /\ needed2 n + 4096 <= ms /\ n + 4096 <= needed2 n
                    /\ 0xfc01 <= n /\ nfix n = n /\ PGS = 0x7fff8000 + a / 8 + 768 + nfix n / 8 /\ 0 <= nfix n / 8 /\ 8 * (nfix n / 8) <= n /\ 0 <= a / 8 /\ a / 8 + ms / 8 <= 0xffffeff00000
                    /\ lo <= SPA - 512 /\ ACEIL <= lo /\ SPA = SP + -2192 /\ STK = SP + -2136 /\ lo <= SP - 4096 /\ (a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a)
                    /\ T + 4096 <= ACEIL /\ (a + ms <= T \/ T + 4096 <= a) /\ (T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T) /\ Timg T).
      { pose proof (Z.div_mod ms 4096 ltac:(lia)) as DM. rewrite MSAL, Z.add_0_r in DM. pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MN.
        rewrite PGSE0, SHR. clear - DA DM DN MN A0 ACE MSZ NLO NFX N2E RNB SPAL LOIMG SPL ABAND T1 ABT TNS T0 RZ UBE ABE CHBE. repeat split; lia. }
      unfold cssegC2_post.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (sec_pg AL IMG ALWF CS CSOK ASB) with (W := []) (pgb := pgb);
          [ exact NB | exact AB0 | exact AB16 | exact RNG' | exact ACS | | exact PS | exact GOTFL | exact PPART | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ].
        exact PGC. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z22 & m1 & -> & MU1 & WM1 & MI1 & PG1 & ST1)).
      fold rd in MU1, PG1. fold UB in MU1, PG1. fold PGS in MU1, PG1.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (sec_st AL IMG ALWF CS CSOK) with (W := []) (fill := 0);
          [ exact NB | exact FP | clear; lia | | exact CX0 | exact CX1 | exact T0 | exact T1 | exact CTXCS | exact TCS | exact TC | | | | exact ST1 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI1 | reflexivity ].
        - eapply (allocA_statics_transport _ m m1 T CTX AS MU1). { intros A k Hk. geoh GEO Hk. } cbn [disjoint_from]. clear - GEO CX1 CTXNS ABC. decompose [and] GEO. repeat split; lia.
        - eapply rw_cells_transport; [exact STH| exact MU1| exact WM1| geo GEO].
        - eapply rw_cells_transport; [exact ST4| exact MU1| exact WM1| geo GEO].
        - unfold allocA_frame in *. eapply rw_cells_transport; [exact AFR| exact MU1| exact WM1| geo GEO]. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (u1 & u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & k0 & k1 & k2' & k4 & m2 & -> & MU2 & WM2 & MI2 & STH2 & ST42 & ST2)).
      cbn [Z.eqb] .
      assert (MU02 : munch [(lo, SPA + -128); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912)] m m2).
      { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (sec_fin2 AL IMG ALWF CS CSOK) with (W := []) (mg0 := mg0) (mg1 := mg1);
          [ exact NB | exact AB0 | exact AB16 | exact AB1 | exact B1B | exact ACS | | | | | exact ST2 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI2 | reflexivity ].
        - fold CHB. eapply rw_cells_transport; [exact HDR| exact MU02| exact WM02| geo GEO].
        - intros _. eapply rw_cells_transport; [exact MG| exact MU02| exact WM02| geo GEO].
        - eapply (fin_statics_transport _ m m2 FS MU02). intros A k Hk; geoh GEO Hk.
        - unfold allocA_frame in *. eapply rw_cells_transport; [exact AFR| exact MU02| exact WM02| geo GEO]. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & -> & MU4 & WM4 & MI4 & HDR4 & MG4 & ST5)).
      replace (ret_pc (Z_to_bv 64 0x48470)) with (Z_to_bv 64 0x48470) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      fold UB in HDR4, MU4, MG4 |- *. fold CHB in MU4, HDR4, MG4 |- *.
      specialize (MG4 ltac:(rewrite RZ; clear; lia)).
      assert (MU04 : munch [(lo, SPA); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (CHB, CHB + 2); (AB, AB + 16)] m m4).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU02]. unfold sub_fp; cbn [outside]; clear; intros x Hx; decompose [and] Hx; repeat split; auto; lia. }
        eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM04 : wmono asegs m m4) by (eapply wmono_trans; [exact WM02| exact WM4]).
      assert (DJ1 : forall A k, (A + k <= lo \/ SPA <= A) -> lo <= A -> disjoint_from [(lo, SPA); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (CHB, CHB + 2); (AB, AB + 16)] A k).
      { intros A k H1 H2. cbn [disjoint_from]. clear - H1 H2 GEO. decompose [and] GEO. repeat split; lia. }
      assert (DJI : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (CHB, CHB + 2); (AB, AB + 16)] A k).
      { intros A k H1. cbn [disjoint_from]. clear - H1 GEO. decompose [and] GEO. repeat split; lia. }
      (* [comment removed for export] *)
      replace (Z_to_bv 64 SPA) with (Z_to_bv 64 (STK + -8 + -48)) by (subst SPA STK; f_equal; lia).
      eapply evtA_cut.
      { eapply (acalloc_ok_sec AL IMG ALWF CS CSOK) with (SP := STK + -8) (W := [(PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (CHB, CHB + 2); (AB, AB + 16)]) (m0 := m) (fr := fr4);
          [ | exact SB0 | clear - SB1; lia | | | | | exact LOIMG | subst STK; clear - SPL; lia | subst STK; clear - SPH; lia | | | | exact WM04 | exact MI4 ].
        - clear - GEO. decompose [and] GEO. lia.
        - clear - GEO APT. decompose [and] GEO. lia.
        - eapply ro_cells_transport; [exact SBC| exact MU04| apply DJI; unfold A_INSTANCE; cbn; clear; lia].
        - replace (STK + -8 + -48) with SPA by (subst STK SPA; lia). eapply rw_cells_transport; [exact FR16| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia].
        - replace (STK + -8 + -48) with SPA by (subst STK SPA; lia). exact ST5.
        - subst STK. clear - SPA16. replace (SP + -2136 + -8) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16.
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst STK; clear; lia].
        - eapply munch_weaken; [| exact MU04]. unfold sub_fp; cbn [outside]. subst SPA STK. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
      cbn beta. (intros ms5 dd_H; ddestruct dd_H as (v11 & -> & ST6)).
      replace (ret_pc (Z_to_bv 64 0x699c4)) with (Z_to_bv 64 0x699c4) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      (* [comment removed for export] *)
      assert (ST7 : stk asegs m4 lo (SP + -64)).
      { assert (FJ1 : rw_cells asegs m4 (STK + -8) [CB 8 fr3])
          by (eapply rw_cells_transport; [exact FJ| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]).
        pose proof (stk_release asegs m4 lo (STK + -8) _ ST6 FJ1 ltac:(subst STK; clear - SPL; lia)) as RJ. cbn [cells_size csize Nat.add] in RJ.
        replace (STK + -8 + Z.of_nat 8) with STK in RJ by lia.
        assert (STKC1 : rw_cells asegs m4 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)])
          by (eapply rw_cells_transport; [exact STKC| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]).
        pose proof (stk_release asegs m4 lo STK _ RJ STKC1 ltac:(subst STK; clear - SPL; lia)) as R0. cbn [cells_size csize Nat.add] in R0.
        assert (HTR1 : u64arr asegs m4 (STK + 16) ws)
          by (eapply u64arr_transport; [exact HTR| exact MU04| exact WM04| apply DJ1; rewrite ?HL; cbn; clear - GEO; decompose [and] GEO; lia]).
        assert (TRC : rw_cells asegs m4 (STK + Z.of_nat 16) [CB (length (u64s ws)) (u64s ws)]).
        { replace (STK + Z.of_nat 16) with (STK + 16) by lia. apply rw_cells_of_u8arr. destruct HTR1 as [HB HW]. split; [exact HB|]. rewrite u64s_length, HL. rewrite HL in HW. replace (Z.of_nat (8 * 30)) with (8 * Z.of_nat 30) by (clear; lia). exact HW. }
        pose proof (stk_release asegs m4 lo _ _ R0 TRC ltac:(subst STK; clear - SPL; lia)) as R1. cbn [cells_size csize Nat.add] in R1. rewrite u64s_length, HL in R1.
        assert (F1800' : rw_cells asegs m4 (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) [CB 1800 fr1]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) with (STK + 256) by lia.
          eapply rw_cells_transport; [exact F1800| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]. }
        pose proof (stk_release asegs m4 lo _ _ R1 F1800' ltac:(subst STK; clear - SPL; lia)) as R2. cbn [cells_size csize Nat.add] in R2.
        assert (TFB' : rw_cells asegs m4 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) [C8 (Z_to_bv 64 SP)]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) with (STK + 2056) by lia.
          eapply rw_cells_transport; [exact TFB| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]. }
        pose proof (stk_release asegs m4 lo _ _ R2 TFB' ltac:(subst STK; clear - SPL; lia)) as R3. cbn [cells_size csize Nat.add] in R3.
        assert (F8' : rw_cells asegs m4 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) [CB 8 fr2]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) with (STK + 2064) by lia.
          eapply rw_cells_transport; [exact F8| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]. }
        pose proof (stk_release asegs m4 lo _ _ R3 F8' ltac:(subst STK; clear - SPL; lia)) as R4. cbn [cells_size csize Nat.add] in R4.
        lazymatch type of R4 with stk _ _ _ ?hi => replace hi with (SP + -64) in R4 by (subst STK; clear; lia) end. exact R4. }
      assert (FR7' : rw_cells asegs m4 (SP + -64) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra])
        by (eapply rw_cells_transport; [exact FR7| exact MU04| exact WM04| apply DJ1; cbn; clear - GEO; decompose [and] GEO; lia]).
      (* [comment removed for export] *)
      eapply evtA_mono.
      { replace (STK + -8) with (SP + -2144) by (subst STK; lia).
        eapply (calloc_epi AL IMG ALWF CS CSOK); [exact FR7'| exact ST7| exact LOIMG| clear - SPL; lia| clear - SPH; lia| exact SPA16| exact SCS| exact MI4]. }
      cbn beta. intros ms6 (-> & ST8).
      assert (MU24 : munch [(lo, SPA); (CHB, CHB + 2); (AB, AB + 16)] m2 m4).
      { eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; subst SPA; clear; intros x Hx; decompose [and] Hx; repeat split; auto; lia. }
      assert (WM24 : wmono asegs m2 m4) by (exact WM4).
      assert (MU14 : munch [(lo, SPA); (T + 2800, T + 2824); (T + 2904, T + 2912); (CHB, CHB + 2); (AB, AB + 16)] m1 m4).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; subst SPA; clear; intros x Hx; decompose [and] Hx; repeat split; auto; lia. }
        eapply munch_weaken; [| exact MU24]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM14 : wmono asegs m1 m4) by (eapply wmono_trans; [exact WM2| exact WM24]).
      deexists 14. dexists k0, k1, k2', k4, m4. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU04]. unfold sub_fp; cbn [outside]. subst SPA. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
      split; [exact WM04|]. split; [exact MI4|]. split; [exact HDR4|]. split; [exact MG4|].
      split; [eapply rw_cells_transport; [exact PG1| exact MU14| exact WM14| geo GEO]|].
      split; [eapply rw_cells_transport; [exact STH2| exact MU24| exact WM24| geo GEO]|].
      split; [eapply rw_cells_transport; [exact ST42| exact MU24| exact WM24| geo GEO]|].
      exact ST8.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End CSegSC.
End CSecC.

End ARUN_1.
