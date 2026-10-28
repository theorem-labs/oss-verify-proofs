(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_exit_run1 U_exit_run2 U_exit_run3 U_stdio_write_run1 U_stdio_write_run2 U_stdio_write U_code_3c000_3d000.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
Ltac xpeel := repeat first [ rdn_peel1 | rewrite rdn_fx_slot_writes_out by (zlen; lia) ].
Ltac xrdn := xpeel; rdn_solve.
Ltac xsok_peel :=
  repeat first [ eapply store_ok_mono; [apply wbytes_grows|]
               | eapply store_ok_mono; [apply fx_slot_writes_grows|] ].
Ltac xsok SOK := xsok_peel; exact SOK.
Ltac xsok_stack SOK := xsok_peel; eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.
Ltac xmem := unfold mem_w3a, mem_w2, mem_fx, fx_spills, mem_w1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_exit () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_common"; "RocqVerifyHarness.AgentSubmission.U.U_exit_base.file_clean"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.stdout_pending"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.exit_pre"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L10337663006.71L11056883230.71L11969108712.56L13060692382.56L14066986910.71L15199722910.71L15348793192.71L17572381086.71L19320507752.71L20524656744.71L23575054312.56L27564627432.71L27904486814.56L28728285086.56L29003517854.71L29377749608.71L32129488232.56L33216670120.71L34586645352.71L34894927976.71L35417004446.71L36115921768.71L37626525086.71L40071973224.71L41166925726.71L43122870174.71L43753111966.71L47094085352.71L48331756008.56L48925459304.56L52304724766.71L52304727387.49L52470052766.56L52763986600.71L55150628766.71L55183527838.71L57071226782.56L60547074152.56L64520920680.71L65114099688.56L66178826654.71L67111600542.56L68472745064.71L7527391576.71 L9520818078.56 00000D00X00Y00m01A01U01V01j01k01l01m01n02B02V02j02k02l02m02n02o03C03D03X03Y03m04A04U04V04W04X04l05@05T05U05i06=06Q06R06S06T06h07<07=07>07RS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSS2sp7ec_splo7ec_sphiSSSSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSSSSSS2sp7ec_splo7ec_sphiSS2sp7ec_splo7ec_sphiSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSSSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSSSS2sp7ec_splo7ec_sphiS2sp7ec_splo7ec_sphiSSS2sp7ec_splo7ec_sphi". (* [comment removed for export] *)
Theorem ref_exit_clean : ltac2:(CDefT.buildp (gd_tbl_P_exit ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$3.Psp,(1.&40.)Ptp,(1.&40.)Pcode,(1.&40.)Ptid,$4.Pwp2,(1.&40.)Prp2,(1.&40.)Pwp1,(1.&40.)Prp1,(1.&40.)P,(5.R;.R:.R8.R7.R6.R5.R4.R3.)P,(6.R;.+4<>20.R3.R2.)P,(7.(2.(1.&40.))(8.R;.)(9.(1.&40.)))P,(7.(:.(;.(1.&40.)(1.&40.)))(<.R<.)(=.(;.(1.&40.)(1.&40.))))(>.$?.(10.(11.$12.R?.(13.&40.+3?74<.$14.)R>.(15.$?.))R=.)(16.(17.&40.R:.(18.&40.+??.))(19.R=.)))")
(* [comment removed for export] *).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  ddestruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  ddestruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_atexit as [b AT].
  ddestruct (wfx b regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs 9) (getr regs 18) (getr regs 19))
    as (regsx & RUNX & RXsp & RXs0 & RXra & RXs1 & RXtp & RXgp); try assumption.
  1:{ unfold mem_w1; store_ok_peel; exact ec_sok. }
  1:{ unfold mem_w1; rdn_solve. }
  1:{ apply atexit_st_w1; assumption. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUNX |]. clear RUNX.
  (* [comment removed for export] *)
  ddestruct (w2 regsx (mem_fx b (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs 9) (getr regs 18) (getr regs 19))
              (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (xmem; first [xsok ec_sok | xrdn]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  rewrite RXtp, RXgp in *.
  (* [comment removed for export] *)
  ddestruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  ddestruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  ddestruct (w3a regs2 (mem_w2 (mem_fx b (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs 9) (getr regs 18) (getr regs 19))
                        sp code (getr regs 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ xmem; xsok ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; xmem; xrdn. }
  1:{ repeat split; xmem; zaddr_goal; xrdn. }
  1:{ repeat split; xmem; zaddr_goal; xrdn. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_3c07c | exact E_3c07c | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "02S0@L10163412696.117L10337663006.83 L10723524894.92 L11056855162.116L11969108712.76 L13060692382.76 L13599392450.92 L14066986910.83 L14184771461.117L15033117063.93 L15199722910.83 L15348752652.116L16490436692.117L17572421626.116L17593528453.117L18143576276.117L19045050187.116L19320507752.83 L1947413893.117 L20515131221.117L20524693004.116L20843143704.117L20936806773.93 L21568122046.93 L21998215124.117L22129476461.117L23031949530.93 L23061819960.116L23575054312.76 L23683636357.117L23828548044.93 L24415375932.92 L25218365854.92 L25270055469.117L25589643053.117L27564592012.116L27680781997.117L27801986005.117L27849832922.93 L27904486814.76 L28156692968.92 L28327265421.117L28728285086.76 L29003485690.116L29003517854.83 L29029589869.117L29377749608.83 L30400290939.93 L3161963013.117 L31655292266.92 L32129488232.76 L32509086407.83 L3255035205.117 L33127914251.83 L33216706508.116L33367326440.92 L33547951917.117L33683981990.117L34217022808.117L34306671524.92 L34335519192.116L34335519192.117L34586645352.83 L34894927592.92 L34894927976.83 L35278767047.93 L35416967162.116L36115948812.116L36225099473.92 L37324790061.117L37329648901.117L37626525086.83 L37626526494.92 L38260775313.117L38526606893.117L3887989805.117 L38944686700.93 L39549896877.117L40071972840.92 L40071973224.83 L40157499619.116L40157499619.117L40964493086.92 L41166922014.92 L41166925726.83 L41927220165.117L42096661182.83 L43122842106.116L43753086970.116L44240694616.117L44626230443.83 L44705284510.83 L45281490152.92 L45342107055.92 L45389991813.117L45466169217.93 L46764746245.117L47094048908.116L47661246258.83 L4789394224.117 L48191718533.117L4823325885.93  L48331756008.76 L48607568906.117L48925459304.76 L49344422957.117L50174544645.117L50456832872.83 L50883810605.117L51819977855.93 L52210083494.93 L52304724766.83 L52304727387.69 L52470052766.76 L52763986600.83 L55150596602.116L55183495674.116L55663233768.92 L55847891080.93 L56645989040.117L56729606430.92 L57071226782.76 L57733405990.117L58171705773.117L58743286031.93 L590758488.117  L59541752689.117L60269093976.117L60547074152.76 L62013451349.117L63571206430.92 L64420204564.117L64465191437.117L64520945676.116L65114099688.76 L6531387271.92  L66178826654.83 L6624388802.83  L66360353054.92 L6645262318.93  L66723894883.116L66723894883.117L67111600542.76 L6715713797.117 L67828290388.117L67851598475.116L68289592280.117L68472745064.83 L68472779276.116L68650816852.117L7228564909.117 L7527391576.83  L7729740501.117 L8112896600.116 L8112896600.117 L8308817768.92  L8605377227.116 L9105080952.117 L919068811.116  L9252062725.117 L9298915924.117 L9520818078.76  L9634720450.92  00000900U01101M01V02202F02b02k03403P03Y03b04>04G04P04d04m05605J05S05\05e06906B06V06_07;07D07M07m08A08m09609J09S09g0:;0:D0:`0:i0;50;Q0;m0<I0<R0<[0<\0<e0=>0=G0=H0=Q0=R0=[0=d0=m0>A0>J0>V0>j0?>0?G0?P0?Y0?n0@J0@S0@_0@h0A10AM0Ai0B20BF0BZ0Bc0Bl0C50C>0CR0Cf0DB0D^0E:0EC0EX0F40FP0FY0FZ0G60G?0GS0G\0H00H90HB0HW0H`0Hi0IB0IK0IT0I]0If0Io0J80JL0J`0K50KQ0Km0LI0LR0Ln0MJ0MS0Mh0N10NM0Ni0O=0OQ0OZ0Oc0Ol0P50P>0PR0Pn0Q70QC0QL0QU0Qi0RE0RZ0S60S?0SS0Sg0TC0TL0TU0TV0T_0Th0U10U:0UC0UL0U`0V40VH0VQ0Ve0W90W:0WC0WL0Wh0X<S7pendingS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pendingS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_sploS7pending2sp7ec_splo7ec_sphiS7pendingS7pendingS7pending2sp7ec_splo7ec_sphiS7pendingS7pendingS2sp7pending7ec_splo7ec_sphiS7pendingS7pendingS2sp7pending7ec_sphiS7pendingS7pendingS2sp7pending7ec_sploS7pendingS7pendingS7pendingS2sp7pending7ec_sphiS7pendingS2sp7pending7ec_sploS7pendingS2sp7pending7ec_splo7ec_sphiS7pendingS7pendingS2sp2wb2wp7pending7ec_splo5RANGES2sp7pending7ec_sphiS2sp2wb2wp7pending7ec_splo7ec_sphi5RANGE3LENS7pendingS2sp7pending7ec_sploS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sploS7pendingS7pending2sp7ec_splo7ec_sphiS7pendingS2sp7pendingS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pending2sp7ec_splo7ec_sphiS7pendingS7pendingFS7pendingS2wb2wp7pending5RANGE3LENS7pendingFS7pendingFS7pendingS7pendingS7pendingS2sp7pending7ec_sphiS7pendingS2sp7pendingS2sp7pending7ec_sphiS2sp7pending7ec_sphiS7pendingS7pendingS7pendingS2wb2wp7pending5RANGES2sp7pending7ec_splo7ec_sphiS7pendingS2sp7pendingS7pendingS7pendingS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sploS7pendingS7pendingS7pendingS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sploS2sp7pending7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pending2sp7ec_splo7ec_sphiS7pendingS2wb2wp7pending5RANGES2sp7pending7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pendingFS7pending2sp7ec_splo7ec_sphiS7pendingS2sp7pending7ec_sphiS7pendingS2sp7pending7ec_sploS7pendingS7pendingS2wb2wp7pending5RANGES7pendingS7pendingS2wb2wp7pending5RANGE3LENS7pendingS7pendingS7pendingS7pendingS7pendingS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sploS2wb2wp7pending5RANGES7pending2sp7ec_splo7ec_sphiS7pending2sp7ec_splo7ec_sphiS7pending2sp7ec_splo7ec_sphiS7pendingS2sp7pending7ec_splo7ec_sphiS2sp7pending7ec_splo7ec_sphiS7pendingS2wb2wp7pending5RANGES7pendingS2sp7pending7ec_splo7ec_sphiS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_sphiS2sp7pending7ec_sploS7pendingS7pendingS7pendingS7pendingS7pendingS2sp7pending7ec_sploS2sp7pending7ec_splo7ec_sphiS7pendingS2sp7pendingS7pendingS7pendingS2sp7pending7ec_sploS7pending2sp7ec_splo7ec_sphiS2wb2wp7pending5RANGES2sp7pending7ec_splo7ec_sphiS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sploS7pending2sp7ec_splo7ec_sphiS7pendingS7pendingFS7pendingS7pendingS7pendingS7pendingS7pendingS7pendingS2sp7pending7ec_sploS2sp7pending7ec_sphiS2sp7pending7ec_sphiS7pendingS2sp7pending7ec_sphiS2sp7pending7ec_sploFS7pendingS7pendingS7pending2sp7ec_splo7ec_sphiS2sp7pending7ec_sphi". (* [comment removed for export] *)
Theorem ref_exit_flush : ltac2:(CDefT.buildp (gd_tbl_P_exit ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$3.Psp,(1.&40.)Ptp,(1.&40.)Pcode,(1.&40.)Ptid,$4.Pwp2,(1.&40.)Prp2,(1.&40.)Pwb,$4.Pwp,$4.Pbufp,(1.&40.)Pbufsz,(1.&40.)Prp1,(1.&40.)Pcan,(1.&40.)Ppending,(:.(1.&8.))P,(5.R10.R?.R=.R<.R;.R:.R9.R8.)P,(1:.R10.R8.R7.R6.R5.R4.R3.R2.)P,(7.(2.(1.&40.))(8.R10.)(9.(1.&40.)))P,(7.(:.(;.(1.&40.)(1.&40.)))(<.R11.)(=.(;.(1.&40.)(1.&40.))))P,(7.(2.$1;.)(1<.(1=.R12.)(18.&40.+1.))(1>.$1;.(1?.(18.&40.+1.))))(>.$?.(10.(11.$12.R15.(13.&40.+3?74<.$14.)R14.(15.$?.))R13.)(20.(21.+1.R6.)(16.(17.&40.R10.(18.&40.+??.))(19.R13.))))")
(* [comment removed for export] *).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  ddestruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  ddestruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_atexit as [b AT].
  ddestruct (wfx b regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (seg_rom RSEGS) sp code (getr regs 9) (getr regs 18) (getr regs 19))
    as (regsx & RUNX & RXsp & RXs0 & RXra & RXs1 & RXtp & RXgp); try assumption.
  1:{ unfold mem_w1; store_ok_peel; exact ec_sok. }
  1:{ unfold mem_w1; rdn_solve. }
  1:{ apply atexit_st_w1; assumption. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUNX |]. clear RUNX.
  (* [comment removed for export] *)
  ddestruct (w2 regsx (mem_fx b (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs 9) (getr regs 18) (getr regs 19))
              (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (xmem; first [xsok ec_sok | xrdn]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  rewrite RXtp, RXgp in *.
  (* [comment removed for export] *)
  ddestruct (w3b1 regs2 (mem_w2 (mem_fx b (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs 9) (getr regs 18) (getr regs 19))
                         sp code (getr regs 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ xmem; xsok ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; xmem; xrdn. }
  1:{ repeat split; xmem; zaddr_goal; xrdn. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x41940) with (0x41940 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_fx b (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs 9) (getr regs 18) (getr regs 19))
                               sp code (getr regs 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x4ce20 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x41940 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; xmem; xsok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; xmem; zaddr_goal; xrdn
    | (* [comment removed for export] *) split; subst mem3; xmem; xrdn
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia                       (* [comment removed for export] *)
    | lia | u_norm; lia | u_norm; lia
    | lia | u_norm; lia                       (* [comment removed for export] *)
    | subst mem3; xmem; xpeel; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    ddestruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    ddestruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; xmem; zaddr_goal; xrdn | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; xmem; zaddr_goal; xrdn | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_3c07c | exact E_3c07c | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit : ltac2:(CDefT.buildp (gd_tbl_P_exit ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$3.Pcode,(1.&40.)Ppending,(:.(1.&8.))P,(22.R5.R4.R3.R2.R1.)(>.$?.(10.(11.$12.R6.(13.&40.+3?74<.$14.)R5.(15.$?.))R4.)(20.(21.+1.R2.)(16.(17.&40.R3.(18.&40.+??.))(19.R4.))))")
(* [comment removed for export] *).
Proof.
  (intros regs mem model code pending dd_H; ddestruct dd_H as (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES)).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z : ltac2:(CDefT.buildp (gd_tbl_P_exit ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmodel,$3.Pcode,(1.&40.)Ppending,(:.(1.&8.))P,(22.R5.R4.R3.R2.R1.)(>.$?.(10.(11.$12.R6.(18.&40.+3?74<.)R5.(15.$?.))R4.)(20.(21.+1.R2.)(16.(17.&40.R3.(18.&40.+??.))(19.R4.))))")
(* [comment removed for export] *).
Proof.
  intros. replace (Z_to_bv 64 0x3f74c) with (0x3f74c : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
