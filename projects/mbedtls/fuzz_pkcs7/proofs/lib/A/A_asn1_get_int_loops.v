(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_get_int_loops () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "asn1_get_int_postA"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.land"].


Definition A_ASN1_GET_INT : Z := 0x0994e8.
Definition A_ASN1_GET_TAGGED_INT : Z := 0x0994f4.

(* [comment removed for export] *)
Notation ASN1_GET_INT_STACK_A := 16 (only parsing).

Definition asn1_get_int_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP VALP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+10.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-7?.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1<.R1.)(13.$1:.)))(5.(1=.O19.R4.O2.(12.&40.O17.))(5.(5.(18.O4.R2.)(18.R2.O3.))P,(6.$4.R3.=)(18.(10.O4.+3.)R3.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_int_stmtA {L : heap_layout} (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP VALP P END BUF lo : Z) (bs : list byte) (valv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m VALP [C4 valv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= VALP \/ VALP + 4 <= PP) ->
  (Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP) ->
  PP mod 8 = 0 -> VALP mod 4 = 0 -> 0 < PP -> 0 < VALP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_INT_STACK_A -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (VALP + 4 <= lo \/ bv_unsigned sp <= VALP) ->
  (Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  (* [comment removed for export] *)
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m PP 8 -> aobj segs AL CS m VALP 4 -> aobj segs AL CS m BUF (Z.of_nat (length bs)) ->
  crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 VALP ->
  evtA segs AL CS (asn1_get_int_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Ltac shadow_merge_slow c k HK Kz :=
  step_to_if;
  lazymatch goal with
  | |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with true by (symmetry; eapply (shadow_slow_takenN c _ k _ HK Kz); first [qlia | lia]); cbv iota
  end.

Ltac shadow_merge_regs2 c k HK nk nt :=
  lazymatch goal with
  | |- evtA ?segs ?L ?CS ?Q (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      let pk := eval vm_compute in (bv_key (Z_to_bv 5 nk)) in
      let pt := eval vm_compute in (bv_key (Z_to_bv 5 nt)) in
      eapply (evtA_cut segs L CS
                (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro) Q)
  end;
  [ let Kz := fresh "Kz" in
    if_cases Kz; zify_cond Kz;
    [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; eexists; reflexivity
    | apply evtA_done; eexists; eexists; reflexivity ]
  | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
    intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].

Ltac shadow_merge_regs1 c k HK nk :=
  lazymatch goal with
  | |- evtA ?segs ?L ?CS ?Q (MS ?R ?F (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc ?rv ?m ?ro) =>
      let pk := eval vm_compute in (bv_key (Z_to_bv 5 nk)) in
      eapply (evtA_cut segs L CS
                (fun ms' => exists vk : word, ms' = MS (tset pk vk R) F (Z_to_bv 64 fast) fc rv m ro) Q)
  end;
  [ let Kz := fresh "Kz" in
    if_cases Kz; zify_cond Kz;
    [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; reflexivity
    | apply evtA_done; eexists; reflexivity ]
  | let ms' := fresh "ms'" in let vk := fresh "vk" in
    intros ms' (vk & ->); cbv beta iota delta [tset]; try clear HK; try clear k ].

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : VALP mod 4 = 0.
  Hypothesis SPL : lo <= bv_unsigned sp - 16.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : VALP + 4 <= lo \/ bv_unsigned sp <= VALP.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - 16, bv_unsigned sp)].
  Notation POST := (asn1_get_int_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHPP := (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)).
  Notation SHVAL := (Z_to_bv 64 (Z.shiftr VALP 3 + al_sb AL)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L13952552502.87L20628580025.87L22370308963.87L31399144472.87L32049487064.83L3832212994.88 L61492657120.87L61543885275.87Q15641571297.88Q9840925826.88 00000D00_01:01I01X01n02B02C02M02[S2sp2PP4VALP2bs1r2HrS2sp2PP4VALP1P3END2bs2p'2HpS2sp2PP4VALP1P3END2bs2p'2HpS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2lo2bs3SPLS2sp2PP4VALP2bs1r2HrFS2sp2lo2bsS2sp2lo2bs3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK bs SPL LO0 SCS"] Lemma ret_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Pr,$4.Pp',$4.Pv,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(5.(17.-7?.R11.)(18.R11.=))P,(5.(18.VP,R11.)(18.R11.VEND,))P,P,(6.$4.R13.=)(18.(10.VP,+3.)R13.)P,(19.$1?.R5.VPP,(=.$1:.(1;.(16.&40.R13.))(13.$1:.)))P,(19.$1?.R6.VVALP,(=.$1:.(1<.R13.)(13.$1:.)))P,(19.$1?.R7.(10.(12.&40.Vsp,)-10.)(=.$1:.(20.#8.R6.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1=.$1?.R8.Vlo,(10.(12.&40.Vsp,)-10.))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R9.)P,(14.$1?.Vm,R:.)P,(15.$1?.R;.)(21.$1?.VAL,VCS,(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R18.R17.R16.Vs0,Vs1,R15.R14.R13.R12.R11.R10.(16.&40.R1;.)R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.Vt5,Vt6,)VF,(16.&40.+99628.)Vfc,(:.(2.&40.))R<.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
    intros r p' v x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 mm junk Hr Hp Hr0 HPP HVAL FR ST MU WM MI. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish; try eassumption; try lia; try reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170?K1295369951.96 K24753660756.96K26917854431.96K44164039966.96K53511889236.96L1295030843.2  L24753455024.2 L25810914902.95L26782575016.93L26921733691.2 L28250535790.93L33809058945.93L38386303801.93L39899883613.93L4100984287.87 L41202929119.87L42896855358.81L43937898498.86L44168742175.3 L49432666050.87L53271535775.87L53511716272.2 L5371699359.87 L54865338993.93L55345854604.84L55347555812.81L57892315391.83L61399516333.93L62908422684.85L62909071722.83L63602515135.93L64346457091.93Q1011560053.92 Q10637069494.92Q10649498890.93Q12164396561.95Q12757461271.90Q13731010443.92Q15930096381.90Q17701933584.93Q20743605642.94Q20880934901.90Q20883032012.94Q26295627581.94Q28496781288.95Q29850408660.90Q32705542026.92Q32705701774.95Q32706126680.92Q33781087993.93Q36351087501.87Q37216054521.93Q38979907496.95Q39600066516.93Q40014758561.94Q40015105031.87Q40016855704.90Q43610544776.87Q4453582353.95 Q45360061705.92Q4637430978.92 Q51715465488.94Q56472221555.95Q57202208522.93Q61556549392.94Q61847600945.93Q67471690124.94Q68390477037.90Q7036224171.94 Q8945570120.92 Q9487243258.96 00000j01S02G03=03j03k03l04J04i04j05N05o06G06H06`07809i09j09k0;50;M0;N0;f0<@0=J0>T0?N0?m0@e0A]0C>0D\0Dn0E>0EN0F50FW0Fg0G40GD0Gf0Gg0Gh0H50HV0He0I70II0I[0J50JW0Jn0KU0KV0L60LV0M60MC0Md0N40NF0Nf0O80O90OV0PD0P[0Q@0QR0Q_0RNS2sp4VALP2lo2bs3SPL3DS21k3rem3val2Hk4Hrem1b2HB5Ha_st5Hl_stS2PP4VALP2bs2D11k3rem1c2Hk2HB5Ha_st5Hl_stS2sp2PP2lo2bs3SPL3DS11k3rem1c2Hk4Hrem2HB5Ha_st5Hl_stS4VALP3BUF2bs2D31k3rem3val2Hk1b2HB5Ha_st5Hl_st2PP2D21cS2PP4VALP2bs2D11k3rem3val2Hk1b2HB5Ha_st5Hl_stFFS2sp2PP4VALP3BUF2bs1k3rem1c2HkS2sp2PP4VALP1P2bs1k3rem1c2Hk2HcFS2sp2PP4VALP2bs1k3rem3val2Hk4Hrem2KLS2sp2PP4VALP3END2bs1k3rem1c2Hk2HES2sp2PP4VALP2bs1k3rem2HkFS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP2bs1k3rem2HkS2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t52t61F2fc1m2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3LO03DS13DS23DS33rem1c3val3x163x283x292mm2Hk4Hrem2Hc2HEFFS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3rem1c2Hk4Hrem2Hc2HE3SPRS2sp2PP4VALP2bs1k3rem2HkFS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP2bs1k3rem1c2HkS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3rem1c2Hk4Hrem2Hc2HE3SPRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3rem1c2Hk4Hrem2Hc2HE3SPRS2sp2PP4VALP3END3BUF2bs2B33PPB4VALB1k3rem1c2Hk4Hrem2HE3SPRS2sp2PP4VALP1P2bs1k3rem1c2Hk2HcS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB1k3rem1c2Hk4Hrem2Hc3SPRS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB1k3rem1c2Hk4Hrem2Hc3SPRS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3rem1c2Hk4Hrem2Hc2HE3SPR2KLS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3rem1c2Hk4Hrem2Hc2HE3SPRS4VALP2bs1k3rem2HkS2PP2bs1k3rem2HkS2PP2bs1k3rem2HkS4VALP2bs1k3rem3val2Hk1b2HB5Ha_st5Hl_stS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HES2PP2bs1k3rem2HkS2bs1k3rem2HkS2PP2bs1k3rem2HkS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HEFFS2bs1k3rem2HkS2PP2bs1k3rem1c2Hk2HB5Ha_st5Hl_stS2bs1k3rem1c2HkS4VALP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs4VALB1k3rem2Hk2HBS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HES2PP2bs3PPB1k3rem2Hk2HBS4VALP2bs1k3rem3val2Hk1b2HB5Ha_st5Hl_stFS1P3BUF2bs2B11k3rem1c2Hk4Hrem2HcS1P3BUF2bs2B11k3rem1c2Hk4Hrem2HcS1P3BUF2bs2B11k3rem1c2Hk4Hrem2HcS2bs1k3rem2HkS2PP2bs1k3rem1c2Hk2HB5Ha_st5Hl_stS2PP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs4VALB1k3rem2Hk2HB5Ha_stS4VALP2bs1k3rem2HkFS2PP2bs3PPB1k3rem2Hk2HB5Ha_stS2sp2PP4VALP2bs3PPB4VALB3AL11k3rem2Hk4Hrem3SPRS4VALP2bs4VALB1k3rem2HkS1P3BUF2bs2B14BUF01k3rem1c2Hk4Hrem2HcS4VALP2bs1k3rem2HkS2bs1k3rem2HkS2sp2PP4VALP2bs1k3rem3val2Hk1b2HB5Ha_st5Hl_st1c". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop3_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Pk,$23.Prem,$4.Pc,$4.Premw,(2.&40.)Pval,(2.&40.)Pv,(2.&40.)Px16,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(6.$23.(24.R:.)R;.)P,(18.+1.R;.)P,(18.(10.VP,+2.)R;.)P,(18.(10.R<.R=.)VEND,)P,(6.(2.&40.)R<.(16.&40.R>.))P,(19.$1?.R7.VPP,(=.$1:.(1;.(16.&40.R>.))(13.$1:.)))P,(19.$1?.R8.VVALP,(=.$1:.(1<.R<.)(13.$1:.)))P,(25.$1?.R9.VBUF,Vbs,)P,(19.$1?.R:.(10.(12.&40.Vsp,)-10.)(=.$1:.(20.#8.R9.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1=.$1?.R;.Vlo,(10.(12.&40.Vsp,)-10.))P,(26.$1?.VAL,VCS,R<.VPP,+8.)P,(26.$1?.VAL,VCS,R=.VVALP,+4.)P,(26.$1?.VAL,VCS,R>.VBUF,(27.(28.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R?.)P,(14.$1?.Vm,R10.)P,(15.$1?.R11.)(21.$1?.VAL,VCS,(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(29.VPP,+3.)(2:.VAL,)))(16.&40.(10.R19.+1.))(16.&40.(10.(2;.VVALP,+7.)+3.))Vs0,Vs1,(16.&40.VPP,)(16.&40.R19.)R18.(16.&40.VVALP,)(16.&40.(10.(29.VVALP,+3.)(2:.VAL,)))R17.R15.(16.&40.(2:.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.Vt5,Vt6,)VF,(16.&40.+99718.)Vfc,(:.(2.&40.))R12.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros rem c remw val v x16 x28 x29 mm junk Hk Hrem Hc HE -> HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI; [lia|].
    al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF c.
    (* [comment removed for export] *)
    get_byte bs (c - BUF) b NB. read_at HBUF NB (c - BUF) RDb.
    shadow_byte OVAL VALP 4 as k4 RD4 HK4.
    zstep. clear RD4. zstep. clear RDb. zstep.
    shadow_merge_regs1 VALP k4 HK4 28.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      replace (Z_to_bv 64 (c + 2)) with (Z_to_bv 64 (c + 1 + 1)) by (f_equal; lia).
      eapply (IH (rem - 1) (c + 1)); try eassumption; try lia. f_equal; lia.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. eapply ret_walk with (r := 0) (p' := c + 1); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?K1295369951.94 K44164039966.94K53511889236.94L1295030843.2  L3010814544.90 L40381378750.90L4100984287.85 L41202929119.85L44168742175.3 L53511716272.2 L5371699359.85 L58963567568.82L58963946870.84Q1013654193.90 Q10637069494.90Q10649498890.91Q12164396561.93Q13731010443.90Q17701933584.91Q26295627581.91Q32703445838.90Q32705701774.91Q32706111784.88Q33781087993.91Q38979907496.93Q39600066516.91Q45360061705.90Q4637449906.88 Q51715465488.92Q56472221555.91Q57202208522.91Q61847600945.91Q67471690124.91Q7036224171.91 Q8945589048.88 Q9487243258.94 00000V01501S01T01m01n02=02L02M02N02]03103E03N03U03\04404;04B04F04O04X04a05205J05K05R05[06206;06<06\06j07307707US2sp4VALP2lo2bs3SPL3DS22HB5Ha_st5Hl_stS4VALP3BUF2bs2D32HB5Ha_st5Hl_stS2PP4VALP2bs2D12HB5Ha_st5Hl_stFS2sp2PP4VALP2bs4remw4HremFS2sp2PP4VALP2bsS2sp2PP4VALP2bsFFS2sp2PP4VALP2bsS2sp2PP4VALP2bs4VALBS2sp2PP4VALP2bs4VALBS4VALP2bsS2PP2bsS2PP2bsS4VALP2bs2HB5Ha_st5Hl_stS2PP2bsS2PP2bsS2bsS4VALP2bsS4VALP2bsS4VALP2bsS4VALP2bs4VALB2HBS4VALP2bs2HB5Ha_st5Hl_stFS2PP2bsS4VALP2bsS4VALP2bs4VALB2HB5Ha_stS4VALP2bsFS2sp2PP4VALP2bs3PPB4VALB3AL13SPRS4VALP2bs4VALBS4VALP2bsS2bsS2sp2PP4VALP2bs2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma j3_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Pcur,$4.Prem,$4.Premw,(2.&40.)Pv,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(6.$4.(12.&40.R<.)R=.)P,(5.(18.+1.R>.)(18.R>.+4.))P,(18.(10.VP,+2.)R10.)P,(18.(10.R11.R10.)VEND,)P,(19.$1?.R6.VPP,(=.$1:.(1;.(16.&40.R12.))(13.$1:.)))P,(19.$1?.R7.VVALP,(=.$1:.(1<.R10.)(13.$1:.)))P,(25.$1?.R8.VBUF,Vbs,)P,(19.$1?.R9.(10.(12.&40.Vsp,)-10.)(=.$1:.(20.#8.R8.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1=.$1?.R:.Vlo,(10.(12.&40.Vsp,)-10.))P,(26.$1?.VAL,VCS,R;.VPP,+8.)P,(26.$1?.VAL,VCS,R<.VVALP,+4.)P,(26.$1?.VAL,VCS,R=.VBUF,(27.(28.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R>.)P,(14.$1?.Vm,R?.)P,(15.$1?.R10.)(21.$1?.VAL,VCS,(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(29.VPP,+3.)(2:.VAL,)))R19.R18.Vs0,Vs1,(16.&40.VPP,)R17.R1;.(16.&40.VVALP,)R16.R15.R14.(16.&40.(2:.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.Vt5,Vt6,)VF,(16.&40.+996>8.)Vfc,(:.(2.&40.))R11.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
    intros cur rem remw v x6 x7 x11 x14 x15 x16 x28 x29 mm junk HL Hrem Hcur HE HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI.
    subst rem. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_byte OVAL VALP 4 as k4 RD4 HK4.
    zstep. clear RD4. zstep. zstep.
    shadow_merge_regs2 VALP k4 HK4 11 15.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply loop3_walk with (rem := bv_unsigned remw) (c := cur); try eassumption; try lia.
    reflexivity. symmetry; apply Z_to_bv_bv_unsigned.
    all: match goal with |- ?g => idtac "J3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L22925878376.87L22925884053.84L32295377219.90L32295378378.95L41202929119.85L43098250791.89L43098252061.95L47832354315.95L47832363825.89L47909761398.96L48748508004.90L48748509165.95L65169320714.86L66321485854.95L66321493284.89L68515083543.88L68515999329.86Q10649498890.91Q10649603773.90Q13735187840.90Q15930096381.93Q17701933584.91Q27441842022.93Q27968400810.95Q27968497955.93Q27968515113.90Q39600066516.91Q40965794845.90Q43608314141.90Q45355851522.90Q57202208522.91Q58791244926.93Q58791407863.95Q60030975100.93Q61847600945.91Q7174379670.93 Q8188910703.95 00001;02F02]03403K04j06I06`07707V08508T09M09j0:G0;=0<30<B0<Q0<`0<l0=;0=K0=i0>G0>e0>f0?G0?S0?b0?c0?d0?e0@F0@n0AQ0B2S2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03cur4remw4Hcur2HE3SPR2RR2KES2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF03cur4remw4Hcur2HE3SPR2RR2KES2sp2PP4VALP2bs4remw2RRS2sp2PP4VALP2bs4remw2RRS2sp2PP4VALP2bs4remw2RRS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS33cur4remw4Hcur2HE3SPR2RR2K4S2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS33cur4remw4Hcur2HE3SPR2RR2KES2sp2PP4VALP2bs4remw2RRS2sp2PP4VALP2bs4remw2RRS2sp2PP4VALP3BUF2bs3cur4remw2RRS2sp2PP4VALP2bs4remw4Hrem2RR2K4S2sp2PP4VALP2bs4remw4Hrem2RR2K4S2sp2PP4VALP3END3BUF2bs2B33PPB4VALB3cur4remw2HE3SPR2RR2KES2sp2PP4VALP1P2bs3cur4remw2RRS2sp2PP4VALP1P2bs3cur4remw2RRS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB3cur4remw4Hcur3SPR2RRS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB3cur4remw4Hcur3SPR2RRS2PP2bs4remw2RRS2PP2bs4remw2RRS2PP2bs4remw2RRS2bs4remw2RRS2PP2bs4remw2RRS2bs3cur4remw2RRS1P3BUF2bs2B13cur4remw4Hcur2RRS1P3BUF2bs2B13cur4remw4Hcur2RRS1P3BUF2bs2B13cur4remw4Hcur2RRFS3END3BUF2bs2B33cur4remw2HE2RR2KES2bs4remw2RRS2PP2bs4remw2RRFFFS3END3BUF2bs2B33cur4remw2HE2RR2KES2sp2PP4VALP2bs3PPB4VALB3AL14remw3SPR2RRS1P3BUF2bs2B14BUF03cur4remw4Hcur2RRS3END3BUF2bs2B33cur4remw2HE2RR2KE". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma j2_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Pcur,$4.Prem,$4.Premw,(2.&40.)Pv,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(6.$4.(12.&40.R;.)R<.)P,(18.+1.R=.)P,(18.(10.VP,+2.)R?.)P,(18.(10.R10.R?.)VEND,)P,(19.$1?.R6.VPP,(=.$1:.(1;.(16.&40.R11.))(13.$1:.)))P,(19.$1?.R7.VVALP,(=.$1:.(1<.R?.)(13.$1:.)))P,(25.$1?.R8.VBUF,Vbs,)P,(19.$1?.R9.(10.(12.&40.Vsp,)-10.)(=.$1:.(20.#8.R8.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1=.$1?.R:.Vlo,(10.(12.&40.Vsp,)-10.))P,(26.$1?.VAL,VCS,R;.VPP,+8.)P,(26.$1?.VAL,VCS,R<.VVALP,+4.)P,(26.$1?.VAL,VCS,R=.VBUF,(27.(28.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R>.)P,(14.$1?.Vm,R?.)P,(15.$1?.R10.)(21.$1?.VAL,VCS,(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(29.VPP,+3.)(2:.VAL,)))R18.R17.Vs0,Vs1,(16.&40.VPP,)R16.R1:.(16.&40.VVALP,)R15.R14.(16.&40.-64.)(16.&40.(2:.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.Vt5,Vt6,)VF,(16.&40.+996;8.)Vfc,(:.(2.&40.))R11.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
    intros cur rem remw v x6 x7 x11 x14 x15 x28 x29 mm junk HL Hrem Hcur HE HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI.
    subst rem. al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (bv_unsigned_in_range 64 remw) as RR. unfold bv_modulus in RR.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K4; zify_cond K4.
    { rewrite ?unsigned_lit in K4 by lia. eapply ret_walk with (r := -100) (p' := cur); try eassumption; try lia. }
    rewrite ?unsigned_lit in K4 by lia.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE.
    { rewrite ?unsigned_lit in KE by lia. eapply j3_walk with (cur := cur) (rem := bv_unsigned remw); try eassumption; try lia. }
    rewrite ?unsigned_lit in KE by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    shadow_chk1 OBUF cur.
    (* [comment removed for export] *)
    get_byte bs (cur - BUF) b NB. read_at HBUF NB (cur - BUF) RD.
    zstep. clear RD. zstep. if_cases KN; zify_cond KN.
    { eapply ret_walk with (r := -100) (p' := cur); try eassumption; try lia. }
    eapply j3_walk with (cur := cur) (rem := bv_unsigned remw); try eassumption; try lia.
    all: match goal with |- ?g => idtac "J2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@K1295369951.100 K24753660756.97 K26917854431.97 K44164039966.100K44164039966.97 K53511889236.100L12220615756.94 L1295030843.2   L13182178067.96 L18051262765.93 L22923653376.82 L22925878376.85 L24753455024.2  L26701802538.94 L26921733691.2  L28250535790.94 L28303549132.93 L36054549391.96 L38398870713.96 L39899883613.94 L4100984287.91  L41202929119.88 L44168742175.3  L47909761398.94 L49432666050.88 L49442338618.82 L53271535775.88 L53511716272.2  L5371699359.91  L58966060494.88 L58966062776.91 L64346457091.94 L64516188264.93 L65169320714.84 L68515083543.86 L68515999329.84 L9573028719.94  Q1011557109.96  Q10649498890.94 Q10649600032.93 Q12164396561.99 Q13735189277.93 Q15930096381.91 Q17701933584.94 Q26295627581.97 Q27441842022.91 Q27968400810.93 Q27968497955.91 Q27970480060.88 Q28496781288.96 Q32703604663.97 Q32703620918.94 Q32705542922.96 Q33781087993.97 Q37216054521.94 Q38979907496.99 Q39600066516.94 Q40968284040.88 Q43610544776.88 Q4453582353.96  Q45355848095.93 Q4635742380.94  Q51715465488.98 Q56474318666.97 Q57202208522.94 Q58791244926.91 Q58791407863.93 Q60030975100.91 Q61556549392.95 Q61847600945.94 Q67471690124.97 Q7036224171.97  Q7174379670.91  Q8188910703.93  Q8943621414.94  Q9487243258.100 Q9487243258.97  00000d01O02E02m03W04>04a04b06G06H07V08d08e09H09I09i0;W0<:0<R0<S0<k0=C0=D0=d0?20Ai0BA0BB0BZ0C70CT0E60EN0FJ0GF0HB0H^0I00I@0IP0J10JA0JN0J^0Jk0K<0K`0LD0Lh0MK0M]0Mo0NA0N[0O20OS0OT0P80PE0Ph0Q80QJ0Qj0R<0R=0R>0R?0Rc0S@0Sn0TE0TW0U@0Ud0V10VX0WCS2sp4VALP2lo2bs3SPL3DS21k3rem2Hk4Hrem2HB5Ha_st5Hl_stS2PP4VALP2bs2D11k3cur3rem2Hk2HB5Ha_st5Hl_stS2sp2PP2lo2bs3SPL3DS11k3cur3rem2Hk4Hrem2HB5Ha_st5Hl_stS4VALP3BUF2bs2D31k3rem2Hk2HB5Ha_st5Hl_stS2PP3BUF2bs2D21k3cur3rem2Hk2HB5Ha_st5Hl_stS2PP4VALP2bs2D11k3rem2Hk2HB5Ha_st5Hl_stS2sp2PP4VALP3END2bs1k3cur3rem2Hk2HEFS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur3rem2Hk4Hrem4Hcur2HE3SPR2KLFS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3cur3rem2Hk4Hrem4Hcur2HE3SPRS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3cur3rem2Hk4Hrem4Hcur2HE3SPRFS2sp2PP4VALP1P2bs1k3cur3rem2Hk4HcurFS2sp2PP4VALP2bs1k3rem2Hk4Hrem2KLS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32B42D12D22D33PPB4VALB4BUF03SPL3LO03DS13DS23DS31k3cur3rem2Hk4Hrem4Hcur2HE3SPRS2sp2PP4VALP1P2bs1k3cur3rem2Hk4HcurS2sp2PP4VALP2bs1k3rem2HkFS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP2bs1k3rem2HkFS2sp2PP4VALP3BUF2bs1k3cur3rem2HkS2sp2PP4VALP1P3END3BUF2bs2B12B32B43PPB4VALB4BUF01k3cur3rem2Hk4Hrem4Hcur2HE3SPRS2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t52t61F2fc1m2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3LO03DS13DS23DS33cur3rem2x62x73x153x283x292mm2Hk4Hrem4Hcur2HES2sp2PP4VALP2bs1k3rem2HkFS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP2bs4VALB1k3rem2HkS2sp2PP4VALP2bs4VALB1k3rem2HkS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur3rem2Hk4Hrem4Hcur2HE3SPRS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP3END3BUF2bs2B33PPB4VALB1k3cur3rem2Hk4Hrem2HE3SPRS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB1k3cur3rem2Hk4Hrem4Hcur3SPRS2sp2PP4VALP1P3BUF2bs2B13PPB4VALB1k3cur3rem2Hk4Hrem4Hcur3SPRS2sp2PP4VALP2bs1k3cur3rem2HkS4VALP2bs1k3rem2HkS2PP2bs1k3rem2HkS2PP2bs1k3rem2HkS4VALP2bs1k3rem2Hk2HB5Ha_st5Hl_stS2PP2bs1k3rem2HkS2bs1k3rem2HkS2PP2bs1k3rem2HkS2bs1k3rem2HkS2bs1k3cur3rem2HkS1P3BUF2bs2B11k3cur3rem2Hk4Hrem4HcurS1P3BUF2bs2B11k3cur3rem2Hk4Hrem4HcurS1P3BUF2bs2B11k3cur3rem2Hk4Hrem4HcurS2PP2bs1k3cur3rem2Hk2HB5Ha_st5Hl_stS4VALP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs4VALB1k3rem2Hk2HBS2PP2bs3PPB1k3rem2Hk2HBS4VALP2bs1k3rem2Hk2HB5Ha_st5Hl_stFS3END3BUF2bs2B31k3cur3rem2Hk4Hrem2HES2bs1k3rem2HkS2PP2bs1k3cur3rem2Hk2HB5Ha_st5Hl_stS2PP2bs1k3rem2HkS4VALP2bs1k3rem2HkS4VALP2bs4VALB1k3rem2Hk2HB5Ha_stS4VALP2bs1k3rem2HkFFFS3END3BUF2bs2B31k3cur3rem2Hk4Hrem2HES2PP2bs3PPB1k3rem2Hk2HB5Ha_stS2sp2PP4VALP2bs3PPB4VALB3AL11k3rem2Hk4Hrem3SPRS4VALP2bs4VALB1k3rem2HkS4VALP2bs1k3rem2HkS1P3BUF2bs2B14BUF01k3cur3rem2Hk4Hrem4HcurS3END3BUF2bs2B31k3cur3rem2Hk4Hrem2HES2bs1k3rem2HkS2sp2PP4VALP2bs1k3rem2Hk2HB5Ha_st5Hl_stS2sp2PP4VALP2bs1k3cur3rem2Hk2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK B1 B3 B4 D1 D2 D3 PPB VALB BUF0 AL1 SPL LO0 SCS DS1 DS2 DS3"] Lemma loop2_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_int_loops ()) "Pk,$23.Pcur,$4.Prem,$4.Premw,(2.&40.)Pv,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px15,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pjunk,(1>.(2.&8.))P,(6.$23.(24.R:.)R<.)P,(18.+1.R;.)P,(18.(10.VP,+2.)R=.)P,(18.(10.R>.R=.)VEND,)P,(6.(2.&40.)R=.(16.&40.R>.))P,(19.$1?.R7.VPP,(=.$1:.(1;.(16.&40.R10.))(13.$1:.)))P,(19.$1?.R8.VVALP,(=.$1:.(1<.R>.)(13.$1:.)))P,(25.$1?.R9.VBUF,Vbs,)P,(19.$1?.R:.(10.(12.&40.Vsp,)-10.)(=.$1:.(20.#8.R9.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1=.$1?.R;.Vlo,(10.(12.&40.Vsp,)-10.))P,(26.$1?.VAL,VCS,R<.VPP,+8.)P,(26.$1?.VAL,VCS,R=.VVALP,+4.)P,(26.$1?.VAL,VCS,R>.VBUF,(27.(28.(2.&8.)Vbs,)))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+10.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R?.)P,(14.$1?.Vm,R10.)P,(15.$1?.R11.)(21.$1?.VAL,VCS,(22.$1?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,(16.&40.(10.(29.VPP,+3.)(2:.VAL,)))R17.R16.Vs0,Vs1,(16.&40.VPP,)(16.&40.R1;.)R19.(16.&40.VVALP,)(16.&40.(10.R1;.+1.))R15.(16.&40.-64.)(16.&40.(2:.VAL,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.Vt5,Vt6,)VF,(16.&40.+995=<.)Vfc,(:.(2.&40.))R12.(;.$1?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros cur rem remw v x6 x7 x15 x28 x29 mm junk Hk Hrem Hcur HE -> HPP HVAL HBUF FR ST OPP OVAL OBUF MU WM MI; [lia|].
    al_facts.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk1 OBUF cur.
    (* [comment removed for export] *)
    get_byte bs (cur - BUF) b NB. read_at HBUF NB (cur - BUF) RD.
    zstep. clear RD. zstep. if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      eapply j2_walk with (cur := cur) (rem := rem); try eassumption; try lia. rewrite unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      replace (Z_to_bv 64 (cur + 2)) with (Z_to_bv 64 (cur + 1 + 1)) by (f_equal; lia).
      eapply (IH (cur + 1) (rem - 1)); try eassumption; try lia. f_equal; lia.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. zstep. zstep.
      shadow_chk OVAL VALP 4.
      zstep. zstep. zstep.
      eapply ret_walk with (r := 0) (p' := cur + 1); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
