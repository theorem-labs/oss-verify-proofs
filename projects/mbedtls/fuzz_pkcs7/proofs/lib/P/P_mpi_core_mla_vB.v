(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_mpi_core_mla P_mpi_mul_int_W P_mpi_core_mla_v1.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac wrvf_tac H L L1 FS FS1 i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write sg mm A l i v H ltac:(lia)) as H';
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length (upd l (Z.to_nat i) v)) = r) by (rewrite upd_length; exact L) end;
        pose proof (same_from_upd _ _ _ v FS) as FS1;
        store_done; try clear H; rename H' into H
      end
  end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mla_vB () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.MpiCoreAux.sxz"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "OSSVerify.KrLib.Lib.MpiCoreAux.w32"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.zx32"; "OSSVerify.KrLib.Lib.Mem.sx32"].

Tactic Notation "wrvf" constr(H) constr(L) ident(L1) constr(FS) ident(FS1) constr(i) := wrvf_tac H L L1 FS FS1 i.

(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word) (junk : list byte).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld <= 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls <= 2^64.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 s0]).
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at psegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr psegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -16)).
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01N0@L10139654587.101L10427974186.92 L10507282770.89 L1105161481.96  L13434842651.100L13434842651.88 L13434842651.92 L13434842651.96 L13993216237.100L14942038703.78 L14946019732.86 L14946019733.82 L14946019739.90 L14946072212.86 L14946072213.82 L14946072219.90 L15677068312.97 L16330313339.88 L18045970546.86 L18045970546.87 L18045970546.90 L18045970546.91 L18045970546.94 L18045970546.95 L18045970546.98 L18045970546.99 L20034682142.92 L21907662621.102L24050514656.87 L24050514656.91 L24050514656.95 L24050514656.99 L24465853174.92 L25212929194.84 L28144623146.86 L28144669456.87 L29564657049.88 L30355778244.92 L35767299818.88 L35830355218.93 L37992812548.97 L40723173726.97 L41777576810.96 L43279095115.90 L43279177840.91 L4416665002.84  L4479655122.97  L44924202532.94 L44924248848.95 L48112150531.92 L48112150540.88 L48112150541.84 L49278847658.103L50590728892.86 L50590728892.90 L50590728892.94 L50590728892.98 L50590729146.84 L50590729146.88 L50590729146.92 L50590729146.96 L50778407376.86 L50778407377.82 L50778407391.90 L50782946027.78 L5197161674.96  L52097208374.92 L52097208376.84 L52097208377.88 L53315723119.85 L53315723119.89 L53315723119.93 L53315723119.97 L54611980505.93 L54760331351.101L58048235828.88 L58048235829.84 L58048235835.92 L58933983108.86 L58933983109.82 L58933983115.90 L58937996479.78 L60213275675.92 L64010872373.100L66855543958.103L6759914232.84  L68018037424.82 L68022627504.83 L8927280810.92  L8927555236.86  L8927555237.82  L8927555243.90  L9119218788.102 L9127648021.93  00000O00b01B02=03D04J05Q06X07S07T07U07V07W07X07Y07Z07o08X09H0:80:i0;Z0<K0=<0=f0>P0?J0@=0@>0@?0@@0@A0@j0AR0BH0C>0Cg0DP0Dc0ED0Ec0F60FI0G?0H50HG0Hh0IW0JF0K40Kb0LO0Ln0N<0OK0PZ0Ql0S:0TI0UX0Vj0Vk0Vl0Vm0Vn0WM0X;0Xh0YV0Z`0[k0]60^A0^U0^j0_S0`;0`d0a:0aP0af0b;0bY0c80cM0d50dj0e_0e`0ea0eb0ec0f;0fYS2ra2sl3ds02ss1j2Hj3Hj83ds63wv7S2ra1D3ds02ss1j3ds6S2ra1S1b3ds02ss1j2ds3wc43ws43wd4S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1j2Hj3Hj83ds53LX53wv63LX6S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j3wd72Hj3Hj83ws73wc73ds7S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j2ds3wc43ws43wd42Hj3Hj8S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j3wd52Hj3Hj83ws53wc53ds5S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j3wd62Hj3Hj83ws63wc63ds6S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1j2Hj3Hj83ds63LX63wv73LX7FFFFFFFS2ra3ds02ss1j3ds53wv6S2ra2sl1b3ds02ss1j3wd52Hj3Hj83ws53wc53ds5S2ra1D2sl2ld1b3ds02ss2DB1j2ds3wc43ws43wd42Hj3Hj8S2ra1D2sl2ld1b3ds02ss2DB1j2ds3wc43ws43wd42Hj3Hj8S2ra1D2sl2ld1b3ds02ss2DB1j3wd52Hj3Hj83ws53wc53ds5S2ra1D2sl2ld1b3ds02ss2DB1j3wd52Hj3Hj83ws53wc53ds5S2ra1D2sl2ld1b3ds02ss2DB1j3wd62Hj3Hj83ws63wc63ds6S2ra1D2sl2ld1b3ds02ss2DB1j3wd62Hj3Hj83ws63wc63ds6S2ra1D2ld1b3ds02ss2DB1j3wd72Hj3ws73wc73ds7S2ra1D2ld1b3ds02ss2DB1j3wd72Hj3ws73wc73ds7S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1j2ds2Hj3Hj83LX43wv53LX5S2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1j2Hj3Hj83ds73LX73wv8FFFFS2ra2sl1b3ds02ss1j3wd62Hj3Hj83ws63wc63ds6S2ra2sl1b3ds02ss1j2ds3wc43ws43wd42Hj3Hj8S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds53LX5S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds53LX5S2ra2sl1b3ds02ss1j3wd52Hj3Hj83ws53wc53ds5S2ra2sl1b3ds02ss1j3wd62Hj3Hj83ws63wc63ds6S2ra1D3ds02ss1j3ds5S2ra1S1b3ds02ss1j3wd53ws53wc53ds5S2ra2sl3ds02ss1j2Hj3Hj83ds53wv6S2ra1D3ds02ss1j3ds8S2ra1D3ds02ss1j3ds7S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds63LX6S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds63LX6S2ra1D3ds02ss1j2dsS2ra1S1b3ds02ss1j3wd63ws63wc63ds6S2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1j2Hj3Hj83ds73LX7S2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1j2Hj3Hj83ds73LX7S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd63ws63wc63ds6S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd53ws53wc53ds5S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j2ds3wc43ws43wd4S2ra2sl3ds02ss1j2Hj3Hj83ds73wv8S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j2ds3wc43ws43wd43Hj83LX45HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd53Hj83ws53wc53ds53LX55HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd63Hj83ws63wc63ds63LX65HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd72Hj3Hj83ws73wc73ds73LX75HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j2ds3wc43ws43wd43Hj83LX45HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd53Hj83ws53wc53ds53LX55HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd63Hj83ws63wc63ds63LX65HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3wd72Hj3Hj83ws73wc73ds73LX75HBarrFFFFS2ra2sl3ds02ss1j2Hj3Hj83ds53wv6S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd63ws63wc63ds6S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j2ds3wc43ws43wd4S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd53ws53wc53ds5S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j2ds3wc43ws43wd42Hj3Hj8S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j3wd52Hj3Hj83ws53wc53ds5S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j3wd62Hj3Hj83ws63wc63ds6S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j3wd72Hj3Hj83ws73wc73ds7S2ra3ds02ss1j2ds3wv5S2ra3ds02ss1j3ds63wv7S2ra2dl2sl1b3ds02ss3Hsl1j3wd53ws53wc53ds5S2ra2dl2sl1b3ds02ss3Hsl1j2ds3wc43ws43wd4S2ra2dl2sl1b3ds02ss3Hsl1j3wd63ws63wc63ds6S2ra1b3ds02ss2HB1j3ds6S2ra1b3ds02ss2HB1j3ds5S2ra1b3ds02ss2HB1j3ds7S2ra1b3ds02ss2HB1j2dsS2ra2sl3ds02ss1j2ds2Hj3Hj83wv5S2ra2sl3ds02ss1j2Hj3Hj83ds63wv7S2ra3ds02ss1j3ds73wv8S2ra2sl1b3ds02ss1j2ds3wc43ws43wd42Hj3Hj8S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj83LX4S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj83LX4FFFFS2ra3ds02ss1j2Hj3ds73wv8S2ra2sl3ds02ss1j2ds2Hj3Hj83wv5". (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SPR LO SX SSX HB"] Lemma vx8_segB : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_vB ()) "Pj,$0.Pds,(1.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pc,$0.Pwc,(2.&40.)Pws4,(2.&40.)Pwd4,(2.&40.)Pwd5,(2.&40.)Pwd6,(2.&40.)Pwd7,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt3,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa6,(2.&40.)Pwps,(2.&40.)Pwpd,(2.&40.)PQ,P,$4.SpP,(5.=R14.)P,(5.(6.(7.+8.R15.)+8.)Vsl,)P,(8.(2.&40.)R5.(9.&40.(6.VS,(7.+20.R16.))))P,(8.(2.&40.)R5.(9.&40.(6.VD,(7.+20.R17.))))P,(:.(;.$<.R16.VD,R17.)(:.(8.$0.(=.(>.(2.&40.)R17.))Vld,)(:.(?.(10.(11.$0.$0.)(12.$0.$0.VD,(6.VD,(7.+4.Vdl,)))(10.(11.$0.$0.)(12.$0.$0.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(15.(11.$0.$0.))))Vm,R16.)(:.(16.$<.Vm,R16.)(:.(17.$<.R16.)(18.$<.R16.Vlo,(6.(14.&40.Vsp,)-10.)))))))P,(19.(:.(8.$0.VS,VD,)(8.(1.(2.&40.))Vss,Vds0,))(:.(1:.$<.Vm,VS,(1;.Vss,))(19.(5.(6.VS,(7.+4.Vls,))VD,)(5.(6.VD,(7.+4.Vld,))VS,))))P,(1<.$<.R18.(6.(14.&40.Vsp,)-10.)(10.$1=.(1>.#8.Vjunk,)(10.$1=.(1?.Vs0,)(15.$1=.))))P,(:.(20.(2.&40.)(21.(6.(7.+8.R1;.)+4.))R1:.Vds0,)(:.(:.(5.=R18.)(22.R18.(23.+2.+20.)))(:.(8.$0.(14.&40.R17.)(24.R18.))(8.$0.(6.(25.R1:.(6.(7.+8.R1;.)+4.))(7.(23.+2.(7.+20.(6.(7.+8.R1;.)+4.)))R18.))(6.(25.Vds0,(6.(7.+8.R1;.)+4.))(7.(25.Vss,(6.(7.+8.R1;.)+4.))Vb,))))))P,(8.$0.(26.Vss,(21.(6.(7.+8.R1<.)+4.)))(27.R17.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R1=.)+4.)))(27.R17.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R1>.)+5.)))(27.R17.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R1?.)+6.)))(27.R17.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R20.)+7.)))(27.R17.))P,Pds8,(1.(2.&40.))Pm8,P,(2.&40.)(3.(2.&8.))Pc8,$0.Pwc8,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)Pys0,(2.&40.)P,(:.(;.$<.R:.VD,R;.)(:.(8.$0.(=.(>.(2.&40.)R;.))Vld,)(:.(?.(10.(11.$0.$0.)(12.$0.$0.VD,(6.VD,(7.+4.Vdl,)))(10.(11.$0.$0.)(12.$0.$0.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(15.(11.$0.$0.))))Vm,R:.)(:.(16.$<.Vm,R:.)(:.(17.$<.R:.)(18.$<.R:.Vlo,(6.(14.&40.Vsp,)-10.)))))))P,(1<.$<.R;.(6.(14.&40.Vsp,)-10.)(10.$1=.(1>.#8.Vjunk,)(10.$1=.(1?.Vs0,)(15.$1=.))))P,(:.(20.(2.&40.)(21.(6.(7.+8.R2>.)+8.))R=.Vds0,)(:.(:.(5.=R;.)(22.R;.(23.+2.+20.)))(:.(8.$0.(14.&40.R:.)(24.R;.))(8.$0.(6.(25.R=.(6.(7.+8.R2>.)+8.))(7.(23.+2.(7.+20.(6.(7.+8.R2>.)+8.)))R;.))(6.(25.Vds0,(6.(7.+8.R2>.)+8.))(7.(25.Vss,(6.(7.+8.R2>.)+8.))Vb,))))))(28.$<.R1<.(29.(2:.Vra,(9.&40.(6.(14.&40.Vsp,)-10.))Vgp,Vtp,R25.R:.R9.R4.Vs1,R;.R22.(9.&40.(6.(6.VS,(7.+20.R2?.))+20.))R21.R20.(9.&40.(6.(6.VD,(7.+20.R2?.))+20.))R1?.(9.&40.Vb,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(9.&40.+22;:0.)Vfc,(2;.(2.&40.))R=.(2<.$<.)))(28.$<.R?.(29.(2:.Vra,(9.&40.(6.(14.&40.Vsp,)-10.))Vgp,Vtp,R18.R17.(2=.R1=.)(2>.R19.)Vs1,R1>.R15.R11.R14.R13.R10.R12.(9.&40.Vb,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.(2>.R1<.)(2>.R1;.)(2>.R1:.))VF,(9.&40.+22:?<.)Vfc,(2;.(2.&40.))R20.(2<.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q. (intros Hj Hj8 -> -> dd_H; ddestruct dd_H as (HX & LX4 & MU & WM & MI & ST); intros AS FR dd_H; ddestruct dd_H as (FS4 & R4 & WC4 & VI4); intros Us4 Ud4 Ud5 Ud6 Ud7 K).
    rename c into c4. rename wc into wc4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX4 LX5 FS4 FS5 (8 * j + 4).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS5 LX5 L0 LS LO SSX sl (8 * j + 5) ws5 Us5.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws4 wd4 wc4 b c4 HB R4 WC4 c5 wc5 wv5 R5 V5 WC5.
    adv ds5 LX5 FS5 VI4 Ud4 Us4 V5 VI5 (8 * j + 5). clear LX4 FS4 VI4 V5 Ud4 Us4 WC4 R4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX5 LX6 FS5 FS6 (8 * j + 5).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS6 LX6 L0 LS LO SSX sl (8 * j + 6) ws6 Us6.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws5 wd5 wc5 b c5 HB R5 WC5 c6 wc6 wv6 R6 V6 WC6.
    adv ds6 LX6 FS6 VI5 Ud5 Us5 V6 VI6 (8 * j + 6). clear LX5 FS5 VI5 V6 Ud5 Us5 WC5 R5.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX6 LX7 FS6 FS7 (8 * j + 6).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS7 LX7 L0 LS LO SSX sl (8 * j + 7) ws7 Us7.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws6 wd6 wc6 b c6 HB R6 WC6 c7 wc7 wv7 R7 V7 WC7.
    adv ds7 LX7 FS7 VI6 Ud6 Us6 V7 VI7 (8 * j + 7). clear LX6 FS6 VI6 V7 Ud6 Us6 WC6 R6.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
    wrvf HX LX7 LX8 FS7 FS8 (8 * j + 7).                                (* [comment removed for export] *)
    zstep.                                                              (* [comment removed for export] *)
    absc ws7 wd7 wc7 b c7 HB R7 WC7 c8 wc8 wv8 R8 V8 WC8.
    adv ds8 LX8 FS8 VI7 Ud7 Us7 V8 VI8 (8 * j + 8). clear LX7 FS7 VI7 V8 Ud7 Us7 WC7 R7.
    zstep.                                                              (* [comment removed for export] *)
    fgt 6%positive.
    replace (Z_to_bv 64 (D + 32 * j + 28 + 4)) with (Z_to_bv 64 (D + 32 * j + 32)) by (f_equal; lia).
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      eapply K; [exact (conj HX (conj LX8 (conj MUx (conj WMx (conj MIx STx)))))| exact FR| exact (conj FS8 (conj R8 (conj WC8 VI8)))] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
