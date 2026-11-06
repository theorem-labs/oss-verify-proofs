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
Ltac2 gd_tbl_P_mpi_core_mla_vA () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.MpiCoreAux.sxz"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "OSSVerify.KrLib.Lib.MpiCoreAux.w32"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.Mem.zx32"; "OSSVerify.KrLib.Lib.Mem.sx32"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "02;0@L10427974186.116L13070516654.95 L13070568592.96 L13434842651.101L13434842651.105L13434842651.109L13434842651.93 L1420117640.101 L14946019728.95 L14946019729.91 L14946019735.99 L14946072208.95 L14946072209.87 L14946072215.99 L14946074135.83 L14946074139.111L16330004219.115L16520824786.106L18045970546.100L18045970546.103L18045970546.104L18045970546.107L18045970546.108L18045970546.91 L18045970546.92 L18045970546.99 L18141028864.88 L18141132984.87 L1827804442.122 L18952277586.77 L19368835740.106L19939270080.106L22468046122.101L22468046122.88 L22548403282.94 L22864966381.121L23306017550.81 L23310098099.97 L24050514656.100L24050514656.104L24050514656.108L24050514656.92 L25212623914.113L26596365384.85 L26638004089.109L26641820354.85 L28206054607.99 L28206133744.100L28773689435.105L29511263268.84 L29511263268.89 L29851128232.103L29851212944.104L30356058692.117L33376215241.98 L3434045531.110 L34768961894.122L35767299818.114L36543246862.105L36547327922.83 L39168565370.101L39905670369.105L40477458450.87 L40481539496.121L413118588.89   L41324718745.87 L41777576810.118L41857917842.110L4416665002.112 L44269456157.97 L47805270506.86 L47805270506.97 L47879335954.102L48112150536.97 L48112150537.89 L48112150542.105L48112150543.101L48116425783.77 L48947581522.77 L48952198895.83 L50268390233.105L50268609497.111L50590728892.103L50590728892.107L50590728892.91 L50590728892.99 L50590729146.101L50590729146.105L50590729146.89 L50590729146.97 L50778407379.99 L50778407380.95 L50778407381.91 L50778461779.83 L5192556914.111 L52097208378.101L52097208379.105L52097208380.89 L52097208381.97 L52101585922.77 L5273141370.77  L53315723119.102L53315723119.106L53315723119.90 L53315723119.98 L53826610794.105L53826610794.90 L55614773766.97 L56114100799.97 L58044089615.77 L58048235824.97 L58048235825.89 L58048235830.105L58048235831.101L58933983104.95 L58933983105.91 L58933983111.99 L58934026247.83 L59314841581.108L59314841581.110L59314841581.112L59314841581.114L59314841581.80 L59314841581.82 L59314841581.84 L59314841581.86 L59793597649.98 L60208966050.109L60788827511.110L60817779844.82 L61377762158.89 L64007054210.113L64996716654.89 L66241619821.109L8927553067.111 L8927555232.95  L8927555233.87  L8927555239.99  L9123297746.115 00000Q01G02=03D04K05R06W07@07A07B07C07D07E07F07G07H08108R09a0;60<K0=`0?50@B0AO0B^0CR0DF0D[0E50EJ0Ei0F<0FN0Fm0Gg0HA0H_0H`0Ha0Hb0Hc0IL0If0JE0J_0KU0LK0M40MF0MX0NN0OD0Om0PA0PV0Q50QV0R50RO0S80Sk0TE0Td0UK0Ue0VF0Vg0WH0X10XC0XV0Y70Ye0ZQ0[?0[m0\L0\\0\l0]U0^>0_M0`\0ah0c70dF0eU0fa0h00h10h20h30h40h]0iK0j90je0kS0l20lB0mM0nX0oa10l11?11Q12J13313M14614]15F15o16E16[17117F18I19L1:O1;N1<D1=31=i1>_1?=1?f1@E1@W1A11AZ1BA1C;1C<1C=1C>1C?1CaS2ra1D1b3ds02ss1j3wd33ws33wc33ds3S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds13LX1S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds13LX1S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j2Hj3Hj83wd13ws13wc13ds1S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j2Hj3Hj83wd23ws23wc23ds2S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j2Hj3Hj83wd33ws33wc33ds3S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln2LO2SX1j2ds2wc2Hj3Hj83ws03wd0S2ra2sl1b3ds02ss1j2Hj3Hj83wd23ws23wc23ds2FFFFFFFFS2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra1S1b3ds02ss1j3wd23ws23wc23ds2S2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd13ws13wc13ds1S2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd23ws23wc23ds25HBarrS2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd23ws23wc23ds25HBarrS2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd33ws33wc33ds35HBarrS2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd33ws33wc33ds35HBarrS2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2ds2wc2Hj3Hj83ws03wd0S2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2ds2wc2Hj3Hj83ws03wd0S2ra2sp1D2dl1S2sl2ld2ls2lo1b3ds02ss2Ln2LS2DB2SB3NZS2LO1j2Hj3Hj83wd13ws13wc13ds1S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj82LXS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj82LXS2ra3ds02ss1j3ds33wv4S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra3ds02ss1j3ds13wv2S2ra2sl3ds02ss1j2Hj3Hj83ds13wv2S2ra1D3ds02ss1j3ds2S2ra1D3ds02ss1j2dsS2ra1S1b3ds02ss1j2ds2wc3ws03wd0S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds33LX33wv4S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2sl3ds02ss1j2ds2Hj3Hj83wv1FFFFS2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2sl3ds02ss1j2Hj3Hj83ds23wv3S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds23LX2S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds23LX2S2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra1D3ds02ss1j2dsS2ra1D3ds02ss1j2dsS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds33LX3S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds33LX3S2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra3ds02ss1j2ds3wv1S2ra3ds02ss1j3ds23wv3S2ra2sl3ds02ss1j2Hj3Hj83ds33wv4S2ra1D1b3ds02ss1j3wd33ws33wc33ds3S2ra2sl3ds02ss1j2Hj3Hj83ds13wv2S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2sl1b3ds02ss1j2Hj3Hj83wd23ws23wc23ds2S2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1j2Hj3Hj83ds13LX13wv2S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2sl3ds02ss1j2Hj3Hj83ds33wv4S2ra2sl1b3ds02ss1j2ds2wc2Hj3Hj83ws03wd0S2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra1D1b3ds02ss1j3wd33ws33wc33ds3S2ra1S1b3ds02ss1j3wd33ws33wc33ds3S2ra1D1b3ds02ss1j3wd33ws33wc33ds3S2ra2sl1b3ds02ss1j2Hj3Hj83wd13ws13wc13ds1S2ra1D3ds02ss1j2dsS2ra1D3ds02ss1j3ds1S2ra1S1b3ds02ss1j3wd13ws13wc13ds1S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd13ws13wc13ds1S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j2ds2wc3ws03wd0S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd33ws33wc33ds3S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd23ws23wc23ds2S2ra2dl2sl2ld2ls3ds02ss2Ln1j2dsS2ra3ds02ss1j2dsS2ra3ds02ss1j2dsS2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd23ws23wc23ds23LX25HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd33ws33wc33ds33LX35HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j2ds2wc3Hj82LX3ws03wd05HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd13ws13wc13ds13LX15HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd23ws23wc23ds23LX25HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd33ws33wc33ds33LX35HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j2ds2wc3Hj82LX3ws03wd05HBarrS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hsl2Ln3SPR2LO1j3Hj83wd13ws13wc13ds13LX15HBarrFFFFS2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd23ws23wc23ds2S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd33ws33wc33ds3S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j2ds2wc3ws03wd0S2ra2dl2sl2ld2ls1b3ds02ss2Ln1j3wd13ws13wc13ds1S2ra2dl2sl2ld2ls3ds02ss2Ln1j2dsS2ra3ds02ss1j2dsS2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j2Hj3Hj83wd23ws23wc23ds2S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j2Hj3Hj83wd33ws33wc33ds3S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j2ds2wc2Hj3Hj83ws03wd0S2ra2sp1D2dl2sl2ld2ls2lo1b3ds02ss3Hdl3Hsl2Ln2LO2SX1j2Hj3Hj83wd13ws13wc13ds1S2ra1D3ds02ss1j3ds3S2ra1D3ds02ss1j2dsS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1j2ds2Hj3Hj82LX3wv13LX1S2ra2sl1b3ds02ss1j2Hj3Hj83wd13ws13wc13ds1S2ra2dl2sl3ds02ss3Hsl1j2dsS2ra2dl2sl1b3ds02ss3Hsl1j3wd13ws13wc13ds1S2ra2dl2sl1b3ds02ss3Hsl1j2ds2wc3ws03wd0S2ra2dl2sl1b3ds02ss3Hsl1j3wd33ws33wc33ds3S2ra2dl2sl1b3ds02ss3Hsl1j3wd23ws23wc23ds2S2ra1b3ds02ss2HB1j3ds2S2ra1b3ds02ss2HB1j3ds1S2ra1b3ds02ss2HB1j3ds3S2ra1b3ds02ss2HB1j2dsS2ra2dl2sl2ld2ls1b3ds02ss3Hdl3Hsl2Ln1j2Hj3Hj83wd33ws33wc33ds33LX41NS2ra2dl2sl2ld2ls1b3ds02ss3Hdl3Hsl2Ln1j2Hj3Hj83wd33ws33wc33ds33LX41NS2ra2dl2sl2ld2ls1b3ds02ss3Hdl3Hsl2Ln1j2Hj3Hj83wd33ws33wc33ds33LX41NS2ra2dl2sl2ld2ls1b3ds02ss3Hsl2Ln1j2Hj3Hj83wd33ws33wc33ds33LX41NS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj82LX1NS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1j2ds2Hj3Hj82LX1NS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj82LX1NS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2ds2Hj3Hj82LX1NS2ra2sl3ds02ss1j2ds2Hj3Hj83wv1S2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2sl3ds02ss1j2Hj3Hj83ds23wv3S2ra1S3ds02ss1j2dsS2ra2sl3ds02ss1j2ds2Hj3Hj8S2ra2sl1b3ds02ss1j2Hj3Hj83wd33ws33wc33ds3S2ra2sl1b3ds02ss1j2ds2wc2Hj3Hj83ws03wd0S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln2L01j2Hj3Hj83ds23LX23wv3FFFFS2ra1b3ds02ss1j2Hj3wd33ws33wc33ds3". (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX SSX HB"] Lemma vx8_segA : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_vA ()) "Pj,$0.Pds,(1.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pc,$0.Pwc,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pxs0,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa6,(2.&40.)Pwps,(2.&40.)Pwpd,(2.&40.)PQ,P,$4.SpP,(5.=R14.)P,(5.(6.(7.+8.R15.)+8.)Vsl,)P,(8.(2.&40.)R5.(9.&40.(6.VS,(7.+20.R16.))))P,(8.(2.&40.)R5.(9.&40.(6.VD,(7.+20.R17.))))P,(:.(;.$<.R16.VD,R17.)(:.(8.$0.(=.(>.(2.&40.)R17.))Vld,)(:.(?.(10.(11.$0.$0.)(12.$0.$0.VD,(6.VD,(7.+4.Vdl,)))(10.(11.$0.$0.)(12.$0.$0.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(15.(11.$0.$0.))))Vm,R16.)(:.(16.$<.Vm,R16.)(:.(17.$<.R16.)(18.$<.R16.Vlo,(6.(14.&40.Vsp,)-10.)))))))P,(19.(:.(8.$0.VS,VD,)(8.(1.(2.&40.))Vss,Vds0,))(:.(1:.$<.Vm,VS,(1;.Vss,))(19.(5.(6.VS,(7.+4.Vls,))VD,)(5.(6.VD,(7.+4.Vld,))VS,))))P,(1<.$<.R18.(6.(14.&40.Vsp,)-10.)(10.$1=.(1>.#8.Vjunk,)(10.$1=.(1?.Vs0,)(15.$1=.))))P,(:.(20.(2.&40.)(21.(7.+8.R1;.))R1:.Vds0,)(:.(:.(5.=R18.)(22.R18.(23.+2.+20.)))(:.(8.$0.(14.&40.R17.)(24.R18.))(8.$0.(6.(25.R1:.(7.+8.R1;.))(7.(23.+2.(7.+20.(7.+8.R1;.)))R18.))(6.(25.Vds0,(7.+8.R1;.))(7.(25.Vss,(7.+8.R1;.))Vb,))))))P,Pds4,(1.(2.&40.))Pm4,P,(2.&40.)(3.(2.&8.))Pc4,$0.Pwc4,(2.&40.)Pws4,(2.&40.)Pwd4,(2.&40.)Pwd5,(2.&40.)Pwd6,(2.&40.)Pwd7,(2.&40.)Pwv4,(2.&40.)Pyt1,(2.&40.)P,(:.(;.$<.R:.VD,R;.)(:.(8.$0.(=.(>.(2.&40.)R;.))Vld,)(:.(?.(10.(11.$0.$0.)(12.$0.$0.VD,(6.VD,(7.+4.Vdl,)))(10.(11.$0.$0.)(12.$0.$0.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(15.(11.$0.$0.))))Vm,R:.)(:.(16.$<.Vm,R:.)(:.(17.$<.R:.)(18.$<.R:.Vlo,(6.(14.&40.Vsp,)-10.)))))))P,(1<.$<.R;.(6.(14.&40.Vsp,)-10.)(10.$1=.(1>.#8.Vjunk,)(10.$1=.(1?.Vs0,)(15.$1=.))))P,(:.(20.(2.&40.)(21.(6.(7.+8.R29.)+4.))R=.Vds0,)(:.(:.(5.=R;.)(22.R;.(23.+2.+20.)))(:.(8.$0.(14.&40.R:.)(24.R;.))(8.$0.(6.(25.R=.(6.(7.+8.R29.)+4.))(7.(23.+2.(7.+20.(6.(7.+8.R29.)+4.)))R;.))(6.(25.Vds0,(6.(7.+8.R29.)+4.))(7.(25.Vss,(6.(7.+8.R29.)+4.))Vb,))))))P,(8.$0.(26.Vss,(21.(6.(7.+8.R2:.)+4.)))(27.R:.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R2;.)+4.)))(27.R:.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R2<.)+5.)))(27.R:.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R2=.)+6.)))(27.R:.))P,(8.$0.(26.Vds0,(21.(6.(7.+8.R2>.)+7.)))(27.R:.))(28.$<.R1<.(29.(2:.Vra,(9.&40.(6.(14.&40.Vsp,)-10.))Vgp,Vtp,R2:.R9.(2;.R?.)(2<.R;.)Vs1,R10.R22.R1>.R21.R20.R1=.R1?.(9.&40.Vb,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.(2<.R>.)(2<.R=.)(2<.R<.))VF,(9.&40.+22:?<.)Vfc,(2=.(2.&40.))R12.(2>.$<.)))(28.$<.R:.(29.(2:.Vra,(9.&40.(6.(14.&40.Vsp,)-10.))Vgp,Vtp,R18.R17.R16.R11.Vs1,R19.R10.R<.R?.R>.R;.R=.(9.&40.Vb,)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R15.R14.R13.R12.)VF,(9.&40.+22:38.)Vfc,(2=.(2.&40.))R1;.(2>.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q. (intros Hj Hj8 -> -> dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros AS FR dd_H; ddestruct dd_H as (FS & HC & WC & VI); intros K).
    replace (8 * j) with (8 * j + 0) in FS, VI by lia.
    (* [comment removed for export] *)
    rdsf AS MU WM HX FS LX L0 LS LO SSX sl (8 * j + 0) ws0 Us0.       (* [comment removed for export] *)
    rdd HX FS (8 * j + 0) wd0 Ud0.                                      (* [comment removed for export] *)
    rdd HX FS (8 * j + 1) wd1 Ud1.                                      (* [comment removed for export] *)
    rdd HX FS (8 * j + 2) wd2 Ud2.                                      (* [comment removed for export] *)
    rdd HX FS (8 * j + 3) wd3 Ud3.                                      (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX LX1 FS FS1 (8 * j + 0).                                  (* [comment removed for export] *)
    rdsf AS MU WM HX FS1 LX1 L0 LS LO SSX sl (8 * j + 1) ws1 Us1.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws0 wd0 wc b c HB HC WC c1 wc1 wv1 R1 V1 WC1.
    adv ds1 LX1 FS1 VI Ud0 Us0 V1 VI1 (8 * j + 1). clear LX V1 Ud0 Us0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX1 LX2 FS1 FS2 (8 * j + 1).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS2 LX2 L0 LS LO SSX sl (8 * j + 2) ws2 Us2.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws1 wd1 wc1 b c1 HB R1 WC1 c2 wc2 wv2 R2 V2 WC2.
    adv ds2 LX2 FS2 VI1 Ud1 Us1 V2 VI2 (8 * j + 2). clear LX1 FS1 VI1 V2 Ud1 Us1 WC1 R1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
    wrvf HX LX2 LX3 FS2 FS3 (8 * j + 2).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS3 LX3 L0 LS LO SSX sl (8 * j + 3) ws3 Us3.      (* [comment removed for export] *)
    zstep. zstep. zstep.                                                (* [comment removed for export] *)
    absc ws2 wd2 wc2 b c2 HB R2 WC2 c3 wc3 wv3 R3 V3 WC3.
    adv ds3 LX3 FS3 VI2 Ud2 Us2 V3 VI3 (8 * j + 3). clear LX2 FS2 VI2 V3 Ud2 Us2 WC2 R2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
    wrvf HX LX3 LX4 FS3 FS4 (8 * j + 3).                                (* [comment removed for export] *)
    rdsf AS MU WM HX FS4 LX4 L0 LS LO SSX sl (8 * j + 4) ws4 Us4.      (* [comment removed for export] *)
    rdd HX FS4 (8 * j + 4) wd4 Ud4.                                     (* [comment removed for export] *)
    rdd HX FS4 (8 * j + 5) wd5 Ud5.                                     (* [comment removed for export] *)
    rdd HX FS4 (8 * j + 6) wd6 Ud6.                                     (* [comment removed for export] *)
    rdd HX FS4 (8 * j + 7) wd7 Ud7.                                     (* [comment removed for export] *)
    zstep. zstep.                                                       (* [comment removed for export] *)
    absc ws3 wd3 wc3 b c3 HB R3 WC3 c4 wc4 wv4 R4 V4 WC4.
    adv ds4 LX4 FS4 VI3 Ud3 Us3 V4 VI4 (8 * j + 4). clear LX3 FS3 VI3 V4 Ud3 Us3 WC3 R3.
    fgt 6%positive.
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      eapply K; [exact (conj HX (conj LX4 (conj MUx (conj WMx (conj MIx STx)))))| exact FR| exact (conj FS4 (conj R4 (conj WC4 VI4)))
                | exact Us4| exact Ud4| exact Ud5| exact Ud6| exact Ud7] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
