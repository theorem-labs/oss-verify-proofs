(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import StrFun.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STRW_tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HA_F_memcpy () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Heap.StrFun.copied"; "Corelib.Init.Datatypes.list"; "Proofs.INV"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "memcpy_post"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "stdpp.bitvector.definitions.bv_extract"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"].

Definition rsegs := asegs.

Definition memcpy_entry := 0x0ea9c0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O17.O16.O15.O14.R?.R>.R=.O13.O12.O5.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.O17.)O6.(9.(2.&40.))R1.(:.$;.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.&40.O5.)(12.(11.&40.O5.)(11.&40.O3.)))(13.(>.$?.$?.)))O1.R1.)(4.(14.$;.O1.R1.)(4.(15.$;.R1.)(4.(16.$;.R1.(11.&40.O5.)(=.$17.(18.(19.(11.&40.O3.))O2.)(13.$17.)))(1:.$;.R1.(11.&40.O4.)O2.)))))))))))))))))))))")
(* [comment removed for export] *).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "(4.(1:.$;.O3.(11.&40.Va1,)Vsrc,)(4.(1;.$;.O3.(11.&40.Va0,)O2.)(4.(1<.Vsrc,O2.(19.O1.))(4.(15.$;.O3.)(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.&40.Va0,)(12.(11.&40.Va0,)(11.&40.Va2,)))(13.(>.$?.$?.)))Vm,O3.)(14.$;.Vm,O3.))))))")
(* [comment removed for export] *).

  Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
  Ltac inv_tac :=
    lazymatch goal with
    | |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
        lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
          first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
    end.

  (* [comment removed for export] *)
  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L14960463391.59L15007238884.62L17614059739.64L17627789829.67L27137092668.65L35854508628.64L35854985538.64L37460500211.67L37460828367.65L53519152272.60L55911282436.61L56033789200.62L5670485634.67 L58422563556.65L58424662383.66L59310683863.61L60319515480.67L64943576677.64L67361222914.68L67363322505.69L8471139633.62 L8471139633.65 L8471139760.60 L8701968733.64 L9537802130.64 00000A00]01001]02=02j03T03m04I04W05405Z05m06@06S06d07707T07g08:08H08V08d09709JS2a23src3LEN1r2RrS2a23src3LEN1P1r2HP2Hr2Rr2K1S2a23src3LEN1P1r2HPS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2Rr3Hl42K1S2a23src3LEN1P1r2HP2Hr2Rr3Hl42K1S2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2Rr3Hl42K1S2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2Rr3Hl4S2a23src3LEN1P1r2HP2Hr2RrS2a23src3LEN1P1r2HP2Hr2Rr2K1S2a23src3LEN1rS2a23src3LEN1P1r2HP2Hr2Rr3Hl4S2a02a12a23src3LEN2AB1P1r2Hr2Rr3Hl42K1S2a23src3LEN1P1r2HPS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1r2K2S2a12a23src3LEN1P1rS2a23src3LEN1P1r2HP2Hr2Rr3Hl4S2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1rS2a23src3LEN1rS2a23src3LEN1rS2a23src3LEN1P1r2HPS2a12a23src3LEN1P1r". (* [comment removed for export] *)
  Lemma mc_a8c : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+4.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:=80.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_2 by lia.
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
      window P 2%nat HW.
      ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
      st1 HW 0%nat. st1 HW 1%nat.
      zstep. zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + zstep. fin.
      + window (P + 2)%Z 1%nat HW1.
        ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
      zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
      + zstep. fin.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L15232684526.64L17614059739.64L22209901305.66L22212000114.65L30652131693.64L3174382116.64 L35854508628.64L35854985538.64L43819961571.64L52585647649.64L55913543746.59L58422563556.65L58424662383.66L60321612658.64L67361222914.65L67363322505.66L68039493266.64L8701968733.64 L9537802130.64 00000C00V00i01<01O01b02H02n03G03`04904L04_05205E05X05k06>06QS2a23src3LEN1P1r2HPS2a23src3LEN1P1r2HPS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a23src3LEN1P1r2HP2Hr2RrS2a23src3LEN1P1r2HP2Hr2RrS2a23src3LEN1P1r2HP2Hr2RrS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a12a23src3LEN1P1r". (* [comment removed for export] *)
  Lemma mc_a60 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.(12.R>.+4.)(20.(11.&40.R=.)+4.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:=54.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 4%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    use (mc_a8c _ _ (P + 4)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14960463391.59L1954409626.61 L39327911311.60L52585996226.61L53512850223.60L59308586639.61L7486163061.61 00000A00T00b01>01L01\028S2a23src3LEN1r2RrS2a23src3LEN1P1r2HPS2a23src3LEN1rS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1rS2a23src3LEN1r1KS2a23src3LEN1P1r2HP2Hr2Rr2Hl". (* [comment removed for export] *)
  Lemma mc_a58 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+8.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:=4<.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - use (mc_a60 m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L14887710883.68L17614059739.68L22209901305.70L22212000114.69L28933012513.68L31172317970.68L3174232370.68 L331373769.70  L333469506.69  L33947626002.68L35854508628.68L35854985538.68L36981015021.68L40553280942.68L41159228708.68L42519607010.69L42521705833.70L4379120953.70 L4381220530.69 L55913543746.59L58422563556.69L58424662383.70L59048792025.70L59050886226.69L60321612658.68L67361222914.69L67363322505.70L68039493266.68L8701968733.68 L933003762.68  L9537802130.68 00000I00\00o01B01[01n02A02T02g03:03`04F04Y04l05?05R05e06806K06d07707J07]08008C08V08i09<09O09b0:5S2a23src3LEN1P1r2HP2Hr2RrS2a23src3LEN1P1r2HPS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HP2Hr2RrS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HP2Hr2RrS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a12a23src3LEN1P1rS2a12a23src3LEN1P1r". (* [comment removed for export] *)
  Lemma mc_a0c : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.(12.R>.+8.)(20.(11.&40.R=.)+8.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:=00.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 8%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
    use (mc_a58 _ _ (P + 8)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14960463391.59L1954409626.61 L39327911311.60L52585996226.61L53512850223.60L59308586639.61L7486163061.61 00000A00T00b01>01L01\028S2a23src3LEN1r2RrS2a23src3LEN1P1r2HPS2a23src3LEN1rS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1rS2a23src3LEN1r1KS2a23src3LEN1P1r2HP2Hr2Rr2Hl". (* [comment removed for export] *)
  Lemma mc_734 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+8.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>::28.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a60 m1 bs P).
    - zstep. use (mc_a8c m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14960463391.59L1954409626.61 L21589288373.61L28933189058.61L53512850223.60L59308586639.61L8599378191.60 00000A00T01001L01Z01j028S2a23src3LEN1r2RrS2a23src3LEN1P1r2HPS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1rS2a23src3LEN1r1KS2a23src3LEN1r". (* [comment removed for export] *)
  Lemma mc_a04 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+10.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:<?8.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_734 m1 bs P).
    - use (mc_a0c m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14960463391.59L1954409626.61 L21589288373.61L28933189058.61L53512850223.60L59308586639.61L8599378191.60 00000A00T01001L01Z01j028S2a23src3LEN1r2RrS2a23src3LEN1P1r2HPS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1rS2a23src3LEN1r1KS2a23src3LEN1r". (* [comment removed for export] *)
  Lemma mc_72c : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+10.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>::20.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a0c m1 bs P).
    - use (mc_734 m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0?L14124842244.76L14831506370.77L14833604681.78L17614059739.76L22209901305.78L22212000114.77L25467773476.76L31172317970.76L3174232370.76 L331373769.78  L333469506.77  L33947626002.76L34542207534.76L35828976930.77L35831072425.78L35854508628.76L35854985538.76L37417757316.76L38919300617.78L38921399682.77L41159228708.76L42519607010.77L42521705833.78L43789150489.78L4379120953.78 L43791245970.77L4381220530.77 L47056395501.76L50705750049.76L51026294307.76L52273755634.77L52275854969.78L55687891801.78L55689986258.77L55913543746.59L58422563556.77L58424662383.78L59048792025.78L59050886226.77L59669457796.76L60321612658.76L63275709282.77L63277807849.78L65081149156.76L65297434404.76L65797790514.77L65799884985.78L67361222914.77L67363322505.78L68039493266.76L68107253092.76L7849922052.76 L8701758027.76 L8701968733.76 L933003762.76  L9537802130.76 00000C00V00i01<01O01b02502H02[02n03A03T03g04:04M05305Y05l06?06R06e07807K07^08108D08W08j09C09\09o0:B0:U0:h0;A0;T0;g0<:0<M0<`0=30=F0=Y0=l0>?0>R0>e0?80?K0?^0@10@D0@W0@j0A=0APS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2RrS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HP2Hr2RrS2a23src3LEN1P1r2HP2Hr2RrS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a23src3LEN1P1r2HP2Hr2RrS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a02a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a12a23src3LEN1P1rS2a23src3LEN1P1r2HPS2a23src3LEN1P1r2HPS2a12a23src3LEN1P1rS2a12a23src3LEN1P1r". (* [comment removed for export] *)
  Lemma mc_978 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.(12.R>.+10.)(20.(11.&40.R=.)+10.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:<6<.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 16%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
    ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
    ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
    zstep.
    st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
    zstep.
    st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
    zstep.
    use (mc_a04 _ _ (P + 16)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L14960463391.59L15232684526.69L17614059739.66L1954409626.61 L30652131693.69L3174382116.69 L35856676733.69L39327911311.60L52585647649.69L53512850223.60L55913379676.61L59308586639.61L7486163061.61 00000A00[00n01A01[02502e03303V03d04@04P04lS2a23src3LEN1r2RrS2a23src3LEN1P1r2HP2q03Lq0S2a23src3LEN1P1r2HPS2a23src3LEN1P1r2HPS2a02a23src3LEN1P1r2q03Lq0S2a12a23src3LEN1P1r2q03Lq0S2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2Rr2Hl2q03Lq0S2a23src3LEN1rS2a23src3LEN1P1r2HP2Hr2Rr2Hl2q03Lq0S2a23src3LEN1rS2a23src3LEN1P1r2HP2Hr2Rr2HlS2a23src3LEN1r1KS2a23src3LEN1P1r2HP2Hr2Rr2Hl". (* [comment removed for export] *)
  Lemma mc_848 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(5.$?.(12.R>.(20.(11.&40.R=.)+8.))(11.&40.Va2,))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R?.R10.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>:;3<.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
      use (mc_a8c _ _ (P + 4)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L17614059739.69L1954350798.60 L21589299169.60L2766356686.82 L28933012513.75L29010566698.60L29010765213.75L30652198372.76L30654293615.77L31478707699.75L3172197403.72 L35854985538.75L35856676734.75L36981015021.75L40553280942.75L41159228708.75L55913389320.60L68515850823.67L8699810932.72 00000A00R00S01G01H01Y02802W03603]04504i05]06<06[07:07S08908QS2a23src3LEN1P2HPS2a23src3LEN1P2HPFS2a23src3LEN1P1r2HP2Hr2Rr2K82q03Lq02q13Lq11q2r01H2H0FS2a23src3LEN1r2RrS2a23src3LEN1r2Rr2q03Lq02q13Lq1S2a02a23src3LEN1P2q03Lq02q13Lq1S2a02a23src3LEN1P2q03Lq02q13Lq1S2a23src3LEN1P1r2HP2Hr2K82q03Lq02q13Lq1S2a12a23src3LEN1P2q03Lq0S2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2K82q03Lq02q13Lq1S2a02a12a23src3LEN2AB3SEP1P1r2HP2Hr2K82q03Lq02q13Lq1S2a02a23src3LEN1P2q03Lq02q13Lq1S2a23src3LEN1P2HP2q03Lq02q13Lq1S2a12a23src3LEN1P2q03Lq02q13Lq1S2a23src3LEN1P1r2HP2Hr2K8S2a23src3LEN1P1r2HP2Hr2Rr2K81q2r01H2H0S2a23src3LEN1P2HP2q03Lq0". (* [comment removed for export] *)
  Lemma mc_828 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pr,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R?.R>.R=.)P,(1?.=R>.)P,(5.$?.(12.R?.R>.)(11.&40.Va2,))P,(4.(1?.=R?.)(24.R?.+10.))P,(5.(2.&40.)R?.(21.&40.(12.(11.&40.Va1,)R11.)))P,(5.(2.&40.)R?.(21.&40.R11.))P,(5.(2.&40.)R?.(21.&40.(12.(11.&40.Va0,)R13.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,Va0,R12.R11.R10.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>:;1<.)Vfc,(9.(2.&40.))R16.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
    zstep. zstep. if_cases K8; zify_cond K8.
    - use (mc_848 m1 bs P (Z_to_bv 64 r)).
    - window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
      use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L17614059739.76L25467319239.89L30413233184.89L30629262582.89L30652198372.89L30654293615.90L3172197403.79 L34542670797.89L3525611882.89 L35854985538.88L35856676728.88L35986998188.89L41160876824.82L42332822672.89L47055932686.89L49618201255.89L55913379906.59L61589165561.90L61591264882.89L65299093785.85L67728738874.89L8699810932.79 L8699810934.85 L8699810935.82 L9468518585.90 L9470618418.89 00000F01801j02Y03K04=04Z05L06N07P08R09J09n0:f0;X0<M0<f0=X0>J0?50?d0@A0@l0AP0BB0C4S2a23src3LEN1K1P2HK2HPS2a12a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq32KlS2a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a12a23src3LEN1K1P2HK2q03Lq0S2a23src3LEN1K1P2HK2HP2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a12a23src3LEN2AB3SEP1K1P2HK2HP2Hr2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a12a23src3LEN2AB3SEP1K1P2HK2HP2Hr2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a12a23src3LEN2AB3SEP1K1P2HK2HP2Hr2q03Lq02q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P2HK2HP2Hr2q03Lq02q13Lq12q23Lq22q33Lq32KlS2a12a23src3LEN1K1P2HK2q03Lq02q13Lq1S2a23src3LEN1K1P2HK2HP2Hr2q03Lq02q13Lq12q23Lq22q33Lq32KlS2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P2HK2Hr2q03Lq02q13Lq12q23Lq22q33Lq32KlS2a23src3LEN1K1P2HK2HP2HrS2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a12a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq2S2a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P2HK2HP2q03Lq0S2a23src3LEN1K1P2HK2HP2q03Lq02q13Lq12q23Lq2S2a23src3LEN1K1P2HK2HP2q03Lq02q13Lq1S2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3S2a02a23src3LEN1K1P2HK2q03Lq02q13Lq12q23Lq22q33Lq3". (* [comment removed for export] *)
  Lemma mc_7f8 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "PK,$25.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(5.$25.(19.(26.(11.&40.Va2,)R;.))R>.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(1?.+10.(26.(11.&40.Va2,)R>.))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R10.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R11.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(21.&40.+?.)R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>::><.)Vfc,(9.(2.&40.))R14.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
    window P 16%nat HW.
    ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
    zstep. zstep.
    st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
    - use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L1952252736.57 L23620210391.57L33001337551.57L46756385821.57L8528200964.57 00000A00O00a01601TS2a23src3LEN1P2HPS2a23src3LEN1PS2a23src3LEN1P3K16S2a23src3LEN1P2HP3K16S2a02a12a23src3LEN2AB3SEP1P2HP". (* [comment removed for export] *)
  Lemma mc_7ec : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(4.(1?.=R=.)(1?.R=.(11.&40.Va2,)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R>.)))P,(5.(2.&40.)R=.(21.&40.(26.(11.&40.Va2,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R10.R?.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>::>0.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K16; zify_cond K16.
    - use (mc_828 m1 bs P (n - P)%Z).
    - zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L14946186646.94 L15526911750.94 L16246187601.60 L17625870649.94 L17627852546.94 L17799441610.103L25465216029.96 L28450517914.82 L30629262582.95 L30652198372.95 L30654293615.96 L3207237953.95  L34540583959.96 L34949646288.103L3523526320.96  L3525611882.95  L35986998188.95 L37371927852.95 L42330731338.96 L42332822672.95 L42778715608.81 L42778738477.95 L44141951062.91 L45238635437.95 L45494427840.95 L47055932686.95 L47058035412.96 L47747482048.81 L50707785240.96 L51430137632.81 L54463712011.95 L5668449992.82  L5670546306.85  L5670546307.88  L5670546308.91  L59059322704.85 L61025648849.88 L61589165561.96 L61591264882.95 L65019182622.96 L7503760135.95  L9468518585.96  L9470618418.95  00000100200K01R02Y03c04Z05505i06`07W08N09E0:L0;F0<M0=J0>A0??0@<0@R0AI0B90B:0C10Ch0D_0E20E30EF0F:0FU0G70G`0HP0I20I[0JR0KI0KJ0L>0M50MlFFS2a23src3LEN1K1P2HK2HP2HrS2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42Kl3K161q1r1H2H0S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2LwS2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq43K161q1r1H2H0S2a23src3LEN1K1P1w2HK2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq43K16S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a23src3LEN1K1P2HK2HPS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq3FS2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P2HKFS2a23src3LEN1K1P2HKS2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2LwS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq1S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq2S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq3S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq1S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq2S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4FS2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4". (* [comment removed for export] *)
  Lemma mc_770 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "PK,$25.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(5.$25.(19.(26.(11.&40.Va2,)R;.))R>.)P,(1>.R>.R=.R<.)P,(1?.+2.R=.)P,(1?.+12.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.(26.R?.+2.))Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(12.(11.&40.Va1,)R10.)+>.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))(21.&40.+11.)R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.Vt4,Vt5,Vt6,)VF,(21.&40.+>::64.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 2)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
    st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L11445594946.64L1954168185.64 L1954412143.63 L23207601716.64L24496052053.64L32189479286.63L35854578228.64L35854985538.64L37961114563.64L47747482048.63L47747893974.64L55913381321.58L57481181359.64L57716083907.64L58422563556.65L58424662383.66L64329521941.64L8712226349.64 00000F00\00m01@01S01a02G02m03F03R03c04704M04c05905O05P05fS2a23src3LEN1P1w2HP2LwS2a23src3LEN1P1w2HP2LwS2a23src3LEN1P2HPS2a23src3LEN1P1w2LwS2a23src3LEN1P1w2LwS2a23src3LEN1PS2a02a12a23src3LEN2AB3SEP1P1w2HP2Hr2LwS2a02a12a23src3LEN2AB3SEP1P1w2HP2Hr2LwS2a23src3LEN1P1w2HP2Hr2LwS2a23src3LENS2a23src3LEN1w2LwS2a23src3LEN1P2HP2HrS2a12a23src3LEN1P1w2LwS2a23src3LEN1P1w2Hr2LwS2a02a23src3LEN1P1w2LwS2a02a23src3LEN1P1w2LwFS2a02a23src3LEN1P1w2Lw". (* [comment removed for export] *)
  Lemma mc_754 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(1?.+20.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.R?.)Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va1,)R10.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>::48.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L14946186646.94 L16246187601.60 L17799441610.103L25465216029.96 L27869909680.95 L28902232586.82 L29547073601.88 L30629262582.95 L30652198372.95 L30654293615.96 L3124580614.94  L32871115528.81 L32871133693.95 L34239283936.81 L34540583959.96 L34949646288.103L3523526320.96  L3525611882.95  L35986998188.95 L38442233144.82 L38444329074.85 L38444329075.88 L38444329076.91 L41527505799.95 L42330731338.96 L42332822672.95 L45238635437.95 L46717093062.91 L47055932686.95 L47058035412.96 L47747482048.81 L50707785240.96 L54463712011.95 L56355875692.95 L57286117777.95 L61589165561.96 L61591264882.95 L61736020672.85 L63927126121.94 L63929341522.94 L65019182622.96 L9468518585.96  L9470618418.95  00000100J01T02K03B03]04F05:06106h06i07?08608I09@0:G0;A0<H0=E0=`0>B0>k0?[0@O0AM0BJ0BK0C;0D20Di0E<0E=0F10Fh0G_0HV0IM0Io0K60L=0L>0M50MlFS2a23src3LEN1K1P2HK2HP2HrS2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42Kl3K161q1r1H2H0S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a12a23src3LEN1K1P1w2HK2LwS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq2S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4FS2a23src3LEN1K1P2HK2HPS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P2HKS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq43K161q1r1H2H0S2a23src3LEN1K1P1w2HK2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a23src3LEN1K1P1w2HK2HP2LwS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq1S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq2S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq43K16S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlFS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq3S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P2HKFS2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq1S2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4FS2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4". (* [comment removed for export] *)
  Lemma mc_878 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "PK,$25.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(5.$25.(19.(26.(11.&40.Va2,)R;.))R>.)P,(1>.R>.R=.R<.)P,(1?.+1.R=.)P,(1?.+13.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.(26.R?.+1.))Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(12.(11.&40.Va1,)R10.)+?.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))(21.&40.+12.)R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.Vt4,Vt5,Vt6,)VF,(21.&40.+>:;6<.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 1)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
    st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L1954168185.64 L1954412143.63 L32189479286.63L35854578228.64L47575940095.64L47747482048.63L47747893974.64L49684669621.64L55495042850.64L55913381321.58L58422498925.64L60842786339.64L61231522292.64L64329521941.6400000F00W00e01K01a01m02>02Q02g03;03Q03g04:04;S2a23src3LEN1P1w2HP2LwS2a23src3LEN1P2HPS2a23src3LEN1PS2a02a12a23src3LEN2AB3SEP1P1w2HP2Hr2LwS2a12a23src3LEN1P1w2LwS2a23src3LENS2a23src3LEN1w2LwS2a23src3LEN1P1w2LwS2a23src3LEN1P1w2HP2LwS2a23src3LEN1P2HP2HrS2a02a23src3LEN1P1w2LwS2a23src3LEN1P1w2Hr2LwS2a23src3LEN1P1w2LwF". (* [comment removed for export] *)
  Lemma mc_864 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(1?.+20.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.R?.)Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va1,)R10.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>:;58.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    st HW 0%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep. zstep.
    use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L13559082540.95 L14946186646.94 L16246187601.60 L17799441610.103L20461994225.95 L25465216029.96 L25516933792.85 L27324926471.95 L29060250920.81 L29060294621.95 L30629262582.95 L30652198372.95 L30654293615.96 L34540583959.96 L34949646288.103L3523526320.96  L3525611882.95  L35986998188.95 L36029045281.88 L39837713106.85 L39837713107.88 L39837713108.91 L39839811480.82 L42330731338.96 L42332822672.95 L43938066182.94 L45238635437.95 L45838477930.82 L47055932686.95 L47058035412.96 L47747482048.81 L48411116489.94 L48412876274.94 L49862951696.95 L50707785240.96 L51556470438.91 L54463712011.95 L61589165561.96 L61591264882.95 L65019182622.96 L7338841760.81  L9468518585.96  L9470618418.95  00000g00h01A02K03B04904[05O05e06\07P08G09>0:50;?0<90=@0>=0>f0?H0@10@a0A<0B:0C70C80C90CT0DK0EB0EU0F\0Gc0HZ0H[0IK0J?0K60Km0Kn0LA0M80MoS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4FS2a23src3LEN1K1P2HK2HP2HrS2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42Kl3K161q1r1H2H0S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a12a23src3LEN1K1P1w2HK2Lw2q13Lq1S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P2HK2HPS2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42Kl3K161q1r1H2H0S2a23src3LEN1K1P1w2HK2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq2S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq1S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq2S2a23src3LEN1K1P1w2HK2HP2Lw2q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P1w2HK2HP2LwS2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq43K16S2a23src3LEN1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlFFS2a12a23src3LEN1K1P1w2HK2LwS2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P2HKS2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a12a23src3LEN2AB3SEP1K1P1w2HK2HP2Hr2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq42KlFS2a12a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq3S2a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4FS2a23src3LEN1K1P2HKS2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4S2a02a23src3LEN1K1P1w2HK2Lw2q13Lq12q23Lq22q33Lq32q43Lq4". (* [comment removed for export] *)
  Lemma mc_90c : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "PK,$25.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(5.$25.(19.(26.(11.&40.Va2,)R;.))R>.)P,(1>.R>.R=.R<.)P,(1?.+3.R=.)P,(1?.+11.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.(26.R?.+3.))Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(12.(11.&40.Va1,)R10.)+=.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))(21.&40.+10.)R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.Vt4,Vt5,Vt6,)VF,(21.&40.+>:<00.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 3)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
    st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + use (mc_978 _ _ (P + 16)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L12904082803.64L19265887139.64L1954168185.64 L1954412143.63 L22593628578.64L30723275572.64L32189479286.63L35854578228.64L35854985538.64L43772821919.64L47747482048.63L47747893974.64L51735867829.64L52099707821.64L55913381321.58L58422563556.65L58424662383.66L64329521941.64L67361222914.65L67363322505.6600000I00_01501F01\01o02=02c03I03_03k04<04O04e05905O05e05f06<06RS2a23src3LEN1P1w2HP2Hr2LwS2a23src3LEN1P1w2Hr2LwS2a23src3LEN1P1w2HP2LwS2a23src3LEN1P2HPS2a23src3LEN1P1w2HP2LwS2a23src3LEN1P1w2LwS2a23src3LEN1PS2a02a12a23src3LEN2AB3SEP1P1w2HP2Hr2LwS2a02a12a23src3LEN2AB3SEP1P1w2HP2Hr2LwS2a12a23src3LEN1P1w2LwS2a23src3LENS2a23src3LEN1w2LwS2a23src3LEN1P1w2LwS2a02a23src3LEN1P1w2LwS2a23src3LEN1P2HP2HrS2a02a23src3LEN1P1w2LwS2a02a23src3LEN1P1w2LwFS2a02a23src3LEN1P1w2LwS2a02a23src3LEN1P1w2Lw". (* [comment removed for export] *)
  Lemma mc_8e8 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pw,(1=.(2.&8.))Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(1?.+20.(26.(11.&40.Va2,)R>.))P,(5.(1=.(2.&8.))R>.(27.(2.&8.)#4.(28.(2.&8.)(19.R?.)Vsrc,)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va1,)R10.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R11.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R12.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.(29.&20.&40.(2:.&40.~&20.(2;.R12.)))R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>:;=<.)Vfc,(9.(2.&40.))R15.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L17614059739.62L1954349123.66 L1954350020.67 L32189484253.67L32189484890.66L46067125452.66L46067126091.67L47747445867.67L47747446764.66L55913379906.57L59836705152.66L59836705287.6700000A00Y01101F01[02302K02^03103E03F03GS2a23src3LEN1P2HPS2a23src3LEN1P2HP2q03Lq0S2a23src3LEN1P2HP2q03Lq0S2a23src3LEN1P2q03Lq0S2a23src3LEN1P2q03Lq0S2a23src3LEN1P2Hr2q03Lq0S2a23src3LEN1P2Hr2q03Lq0S2a23src3LEN2q03Lq0S2a23src3LEN2q03Lq0S2a23src3LEN1P2HP2HrFF". (* [comment removed for export] *)
  Lemma mc_740 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(1?.=R=.)P,(1?.+20.(26.(11.&40.Va2,)R>.))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va1,)R?.)))P,(5.(2.&40.)R>.(21.&40.(26.(11.&40.Va2,)R10.)))P,(5.(2.&40.)R>.(21.&40.(12.(11.&40.Va0,)R11.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,Va0,R11.R10.R?.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.Vt4,Vt5,Vt6,)VF,(21.&40.+>::34.)Vfc,(9.(2.&40.))R14.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
    window P 4%nat HW. ld4 HW 0%nat q0.
    zstep. zstep. if_cases K3; zify_cond K3.
    - use (mc_864 m1 bs P q0). by_win HW 0%nat.
    - zstep. zstep. if_cases K2; zify_cond K2.
      + use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
      + use (mc_754 m1 bs P q0). by_win HW 0%nat.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L1952251972.57 L1952252736.58 L34949646288.65L41711908335.58L46069222603.57L50707785240.58L58165550833.65L8528200964.58 L8528201216.57 00000A00R01401501G01H01f02;02YS2a23src3LEN1P2HPS2a23src3LEN1P2HPS2a23src3LEN1P2HP3K323K161q1r1H2H0FS2a23src3LEN1P3K32FS2a23src3LEN1P2HP3K161q1r1H2H0S2a23src3LEN1P2HP3K32S2a02a12a23src3LEN2AB3SEP1P2HP". (* [comment removed for export] *)
  Lemma mc_71c : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(4.(1?.=R=.)(1?.R=.(11.&40.Va2,)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R>.)))P,(5.(2.&40.)R=.(21.&40.(26.(11.&40.Va2,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R10.R?.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>::10.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K32; zify_cond K32.
    - use (mc_740 m1 bs P).
    - zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_978 m1 bs P).
      + use (mc_72c m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L14527800125.57L55713077998.57L8530359458.56 00000D00U00VS2a02a23src3LEN1P2HPS2a02a23src3LEN1PF". (* [comment removed for export] *)
  Lemma mc_714 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(1>.R>.R=.R<.)P,(4.(1?.=R=.)(1?.R=.(11.&40.Va2,)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R>.)))P,(5.(2.&40.)R=.(21.&40.(26.(11.&40.Va2,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R10.R?.R>.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.Vt4,Vt5,Vt6,)VF,(21.&40.+>::08.)Vfc,(9.(2.&40.))R13.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_7ec m1 bs P).
    - use (mc_71c m1 bs P).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L15007267655.57L17614059739.59L19628429323.59L35854508628.59L35987008627.61L39332109038.60L43984391875.61L44096333846.61L44098420809.60L49682117334.60L49684208265.61L58422962257.61L58425049102.60L8530298113.61 L9535722215.60 L9537829560.61 00000F00\00]01@01V01l02B02^03703M03`04604O05205H05^S2a23src3LEN1K1P2HK2HPS2a23src3LEN1K1P2HK2HPFS2a02a12a23src3LEN2AB3SEP1K1P2HK2HPS2a23src3LEN1K1P2HK2HPS2a12a23src3LEN1K1P2HKS2a12a23src3LEN1K1P2HKS2a12a23src3LEN1K1P2HK2HP2K1S2a12a23src3LEN1K1P2HK2HPS2a12a23src3LEN1K1P2HKS2a23src3LEN1K1P2HKS2a02a23src3LEN1K1P2HKS2a02a12a23src3LEN1K1P2HKS2a02a12a23src3LEN2AB3SEP1K1P2HK2HPS2a12a23src3LEN1K1P2HKS2a12a23src3LEN1K1P2HK". (* [comment removed for export] *)
  Lemma mc_6e4 : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "PK,$25.Pm1,P,(2.&40.)(3.(2.&8.))Pbs,(1=.(2.&8.))PP,$?.Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)P,(5.$25.(19.(26.(11.&40.Va2,)R;.))R>.)P,(1>.R>.R=.R<.)P,(4.(1?.=R=.)(24.R=.(11.&40.Va2,)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va1,)R>.)))P,(5.(2.&40.)R=.(21.&40.(26.(11.&40.Va2,)R?.)))P,(5.(2.&40.)R=.(21.&40.(12.(11.&40.Va0,)R10.)))P,(5.(2.&40.)R=.(21.&40.(12.(12.(11.&40.Va1,)R11.)+1.)))(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,Va0,R11.R10.R?.R>.(21.&40.+1.)R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.Vt4,Vt5,Vt6,)VF,(21.&40.+>:9=8.)Vfc,(9.(2.&40.))R14.(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
    st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_714 _ _ (P + 1)%Z).
    - zstep. zstep. if_cases K1; zify_cond K1.
      + use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
      + zstep. use (mc_714 _ _ (P + 1)%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L21981031364.45L25708206614.61L25708207259.54L25708256798.47L25712457666.47L35283523713.47L35296064472.54L35296064853.61L35296112989.47L39334206190.46L39334206190.47L43545014749.47L43549202433.47L55163157952.47L5960583647.61 L5960585042.54 L5960601047.47 L5964801035.47 L8385880958.47 00000<00=00>00?00@00A00B00C00D00S00e01:01R01^01_01`01a01b021S2a23src3LENFFFFFFFFS2a12a23src3LENS2a02a12a23src3LENS2a02a12a23src3LEN2ABS2a02a12a23src3LEN2AB2K0S2a23src3LENFFFFS2a12a23src3LEN". (* [comment removed for export] *)
  Lemma memcpy_body : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pjunk,(1=.(2.&8.))P,(16.$;.Vm,(11.&40.Va0,)(=.$17.(18.(19.(11.&40.Va2,))R1.)(13.$17.)))P,(1:.$;.Vm,(11.&40.Va1,)Vsrc,)P,(15.$;.Vm,)(22.$;.(23.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Va0,Va1,Va2,Vsrc,Vm,)(6.(7.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,Va0,Va1,Va2,Va3,Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(21.&40.+>:9<0.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof using AB LEN SEP.
    intros junk DST0 SRC MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
    change 0%nat with (Z.to_nat 0) in CP. clear DST0.
    zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
      + use (mc_71c m junk 0%Z).
      + use (mc_7ec m junk 0%Z).
    - zstep. if_cases K0; zify_cond K0.
      + zstep. use (mc_714 m junk 0%Z).
      + zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Proofs.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L32139438783.4400000IS2a02a12a23src3LEN1B2B21R". (* [comment removed for export] *)
Lemma memcpy_spec : ltac2:(CDefT.buildp (gd_tbl_HA_F_memcpy ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Psrc,(1=.(2.&8.))Pjunk,(1=.(2.&8.))P,(1:.$;.R3.(11.&40.R1:.)R2.)P,(5.$25.(2=.(2.&8.)R3.)(19.(11.&40.R1:.)))P,(16.$;.R5.(11.&40.R1=.)(=.$17.(18.(19.(11.&40.R1;.))R3.)(13.$17.)))P,(2>.(1?.(12.(11.&40.R1=.)(11.&40.R1<.))(11.&40.R1>.))(1?.(12.(11.&40.R1>.)(11.&40.R1<.))(11.&40.R1=.)))P,(15.$;.R7.)(22.$;.(23.R29.R28.R27.R26.R22.R21.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.R20.R1?.R1>.R7.R8.)(6.(7.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(21.&40.+>:9<0.)R9.(9.(2.&40.))R8.(:.$;.)))")
(* [comment removed for export] *).
Proof.
  intros until junk. intros SRC LEN DST SEP MI.
  eapply memcpy_body; try eassumption.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
