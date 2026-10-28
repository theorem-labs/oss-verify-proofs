(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_mpi_cmp_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA.
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
Ltac2 gd_tbl_A_mpi_lset () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_xop_stmtA"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "lset_FR"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_lset.lset_R"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "A_WRAP_CALLOC_LS"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "A_ASAN_MEMSET_LS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"].


Definition A_WRAP_CALLOC_LS : Z := 0x69484.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_LS : Z := 0x68258.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lset_FR (d : Z) : Z := calls_FR 1 0.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L16767796506.1000001S". (* [comment removed for export] *)
Lemma lset_FR_val : forall d, lset_FR d = 3.
Proof. intros. unfold lset_FR, calls_FR, fr_charge. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition mpi_lset_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset ()) "(0.O4.O3.O2.O1.+60.Lz,$1.(2.(3.(4.(5.+2.+1?.))R1.)(6.R1.(5.+2.+1?.)))L,$7.L,$1.(8.+1.)$9.LLB,(:.$;.)LdX,$7.Lz,$1.Lr,$1.LdX',$7.(<.R3.R4.R5.R2.R1.))")
(* [comment removed for export] *).

Definition mpi_lset_stmtA_v (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
  mpi_xop_stmtA segs R HIA ENTRY 96 (fun z => -2^31 <= z < 2^31) (fun _ _ => grow_PHI 1) lset_FR
    (fun LB dX z r dX' => lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z)).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13694734361.3L18873492804.2L43424771139.3L68512857134.200000900:00C00IS1z2Hz2HpSS1z2Hz2HnS1z2Hz". (* [comment removed for export] *)
Lemma to_sign_mod16_A : forall z, -2^31 <= z < 2^31 ->
  Z.lor ((bv_signed (Z_to_bv 64 z) ≫ 30) mod 2^64) 1 mod 2^16 = (if z <? 0 then -1 else 1) mod 2^16.
Proof.
  intros z Hz. rewrite signed_lit_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec z 0) as [Hn|Hp].
  - assert (C : z / 2^30 = -2 \/ z / 2^30 = -1) by lia. destruct C as [-> | ->]; reflexivity.
  - assert (C : z / 2^30 = 0 \/ z / 2^30 = 1) by lia. destruct C as [-> | ->]; reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09c39c]).
Local Ltac zchk_new ::= constr:([0x09c22c; 0x09c234; 0x09c238; 0x09c240; 0x09c244; 0x09c248; 0x09c24c; 0x09c294; 0x09c298; 0x09c29c; 0x09c318; 0x09c31c; 0x09c320]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_LS.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_LS.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sg n P : Z) (limbs : list word) (pad : word) (own : limb_own) (z lo d : Z).
  Local Notation dX := (mkMPD X sg n P limbs pad own).
  Hypothesis HNS : own <> LStatic.
  Hypothesis ZB : -2^31 <= z < 2^31.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis DSP : own <> LNull -> P + 4 * n <= lo \/ bv_unsigned sp <= P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 96 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts hh :=
    pose proof (hcs_ok asegs R HIA hh) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hh) as SCS0;
    pose proof (arl_need_rt_free R) as NRF; pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ hh ?LBx LF ?mx, TOPx : bv_unsigned sp <= htop _ _ _ hh |- _ =>
      pose proof (hm_top asegs R HIA hh LBx LF mx HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange (hcs asegs R HIA hh) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPx HTOP; lia])
    end.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHX10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).
  Notation FRAME := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation ZSG := (if z <? 0 then -1 else 1).
  Notation POST := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                      (fun r dX' => lset_R z dX LB r dX' /\ (r = 0 -> mpd_val dX' = z)) (grow_PHI 1) (lset_FR d) lo).

  Ltac basic_facts hc LBc mm HH TOPc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0; pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02_0@C17025492443.138C35679879803.139D24559718099.141D24976250634.143D29475044183.139D52014138856.143D52827452960.141D56475227919.139D60109446735.139D6421795088.139 D66079137390.141D9136755004.139 K21652967687.143K23163039363.139K34218421467.141K36795542264.139K41937183800.143K45119377510.143K47649051183.139K60573057312.138L11498238141.14 L1455795042.1   L14945498641.137L14945498642.135L15302269400.138L21646329835.2  L22102911428.7  L22446743512.138L23100341967.117L23100341967.134L23157821630.3  L24389400072.139L29072547326.135L29074168500.138L29428324939.5  L30068999126.4  L3133433185.136 L3198704660.2   L32189170047.4  L34214986374.2  L34263059663.8  L34444000850.14 L34705680216.138L35653441506.7  L36807145629.3  L38555686690.135L39172636981.0  L3949578456.138 L4144295677.14  L41843875160.138L41933228645.2  L42605059850.133L42609101028.136L43648991903.136L45123927611.3  L46160487540.117L46732241046.2  L47652915602.3  L49493362773.2  L50702478220.2  L50790580594.6  L51454941784.138L51652323378.4  L52841365920.2  L53732153090.3  L54258572428.2  L54259486698.116L56560440097.0  L56885954266.2  L5699067096.138 L57018340393.14 L58591023192.138L59179613721.2  L59504824379.138L59580084914.135L60098763854.3  L60576273221.2  L6409744173.1   L64784619951.2  L67280348888.138L68573184663.3  N21806751459.139N22834764276.139N32741893800.139N37104593031.139N55991858255.139O15024644302.139O17025492443.138O2882393521.139 O34030650587.138O35679879803.139O57399310481.139P47649051183.139P51648157199.138P60573057312.138P64789034994.141P68577426602.139Q12370813529.117Q12370813529.136Q14424010333.138Q15643290603.139Q17203288433.135Q17207350632.118Q18194914450.138Q18365959659.139Q21879808904.139Q22285631880.140Q22287732533.137Q22288293174.139Q24258852817.139Q24561665235.140Q24974040330.142Q26056220425.119Q26207421841.118Q26207721832.119Q26207967338.116Q26295627581.138Q27585109995.139Q27907166216.139Q30415201416.139Q31271557483.139Q31654082872.118Q32655335659.139Q33918027400.139Q34077764446.138Q36425783560.139Q37620949651.135Q37625261960.116Q38248387216.139Q3830196744.139 Q38476389417.141Q38476389417.143Q39016345785.138Q39212284437.119Q39212284437.140Q39939652360.139Q41152162539.139Q42081808994.140Q43616982806.135Q43879899724.139Q43925228937.119Q44648681323.139Q4926406185.140 Q51236024939.139Q52016320488.142Q52829371424.140Q54255983967.139Q54480205009.117Q54480205009.136Q5472627854.135 Q5485126037.116 Q5485174314.117 Q5485174314.136 Q5485600919.118 Q56761401107.140Q59843171435.139Q60511567613.119Q60511567613.140Q60697995187.119Q6143569392.117 Q6143569392.136 Q62965564504.141Q63229390057.137Q6409084169.138 Q6411862452.137 Q6421795088.135 Q6421795088.139 Q66247457463.137Q66522035592.139Q8880503606.116 Q8956025278.135 Q9136755004.139 Q9538787269.116 Q9540573306.137 Q9843398792.139 00000100200V01:01;01_02P03403P03c03d04:04n05E06306J07507`07a07b08708;08<08=08P08Q08h09;09N09a09b0:K0:^0;10;C0;P0;c0;j0;k0;l0;m0<?0<R0<l0<m0<n0<o0=B0=P0=c0=d0>V0?H0?[0?\0?o0@60@70@80@?0@V0@i0@j0A10A?0AF0A_0A`0Ad0B70B;0BN0BU0Bh0C;0CE0CF0CJ0CK0C^0C_0D80D90DR0Dk0EZ0E[0E\0E]0E^0E_0E`0Ea0F=0F>0GB0H20HJ0Hb0I20IE0IR0I_0J50JH0Jg0K40KA0KN0Kg0LH0Lf0MU0Mb0Mo0N<0NI0N\0O;0OZ0Om0P:0PM0Pl0QB0Qa0Qn0R;0RK0Rj0Sf0TP0Tc0U00U=0U\0Uo0V?0VU0Vh0W50WH0WU0Wh0XF0Xm0Y:0Y;0Y<0YI0YV0Yc0Z00Z=0ZJ0Z]0Zj0[70[D0[Q0[^0\40\A0\Q0\a0]10]A0]W0^60^C0^P0^c0_00_=0_\FFS2sp1X1z2p'6limbs'2XB2HB5Ha_st5Hl_stS2sp1X1z2p'6limbs'2XB2HB5Ha_st5Hl_stFS2sp1X1z2p'6limbs'2XB2HB5Ha_st5Hl_stS2sp1X1z2p'2n'6limbs'2NR3SPR2XB2B02HB5Ha_st5Hl_stS1R3HIA2sp1X2lo2hc2p'6limbs'4TOPc2XBS1R2sp1X2lo3LOS2p'6limbs'2XBS2sp1X2p'6limbs'2XBFS2sp1X2p'2n'6limbs'2XBS1R5NEEDR2sp1X1z2lo3SLO6limbs'3DSX2XB2HB5Ha_st5Hl_stS1X2p'2n'6limbs'3DXP2XBS1X1z2p'2n'6limbs'2NR3DXP2LL2XB2HB5Ha_st5Hl_stS2sp1X2lo6limbs'3DSX2XBS1X1z2p'2n'6limbs'2NR3DXP2XB2HB5Ha_st5Hl_stS1X1z2p'2n'6limbs'2NR3DXP2XB2HB5Ha_st5Hl_stFFS1R2sp2lo3SLO3NRA3SPRS2p'FFS2sp1X2p'6limbs'2XBFS1R2lo3LOS2p'2n'3ALO2PCS2sp1X2p'6limbs'2XBS2sp1X2p'6limbs'2XBS2sp1X2p'6limbs'2XBFS1R5NEEDR2sp1X2lo3SLO2p'6limbs'3SPR2XB2B0S2sp1X2p'6limbs'2XBS2sp1X2p'6limbs'2XBS1R2lo3LOS3ALO3ACPS2lo2p'2n'2PSS2sp1X2p'6limbs'2XBS2n'2NRFFFS1R3HIA2sp2hc4TOPcS2sp1X2p'6limbs'2XBS1R3HIA2sp2lo2hc4TOPc4HTOPFFSS2sp1X2p'6limbs'2XBS2sp2n'2NR3SPRS2sp1X2p'6limbs'2XBFS1R5NEEDR2sp1X2lo3SLO2p'2n'6limbs'2NR3SPR2XB2B02PSS1R5NEEDR2sp1X2lo3SLO2p'2n'6limbs'2NR3SPR2XB2B02PSS2sp1X2p'6limbs'2XBFS2sp1X2p'6limbs'2XBS2sp2loFFS2n'2NRS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2p'6limbs'2XBFS2p'2n'S2n'6limbs'2LLS2n'2NRS2sp1X2p'2n'6limbs'2NR2XBSS2n'S2sp1X2p'6limbs'2XBS2spS2sp1X2p'6limbs'2XBS2p'2n'S2sp1X2p'6limbs'2XBS2sp1X2p'6limbs'2XBS1R2lo3LOSFS2p'FS2sp1X2p'6limbs'2XBFS2sp1X2lo6limbs'2XB3x151CFS1X2p'2n'6limbs'2XB3x151CS2sp1X2lo6limbs'2XB3x151CS1X2p'2n'6limbs'2XB3x151C1R2sp2lo3LOS2NR3ALO2PCFFFFFFFS2sp1X2lo2p'2n'6limbs'2XB2PSFS1R5NEEDR2sp1X1z2lo3LOS3SLO2p'2n'6limbs'2NR3ALO2XB2PC2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3LOS3SLO2p'2n'6limbs'3ALO2XB2PCS2sp1X2p'6limbs'4ALX82XBS2sp1X2p'6limbs'4ALX82XBS1X2p'6limbs'2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X2p'6limbs'2XB2B02HBS2sp1X2lo6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X2p'6limbs'2XB2HB5Ha_stS1X1z2p'6limbs'2XB2HB5Ha_st5Hl_stS1X1z6limbs'2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2lo3LOS3SLO6limbs'3ALO3ACP3SPR2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS2sp1X2lo6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XBS2sp1X2lo6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1X2p'2n'6limbs'2NR2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X2lo6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1R5NEEDR2sp1X1z2lo3SLO2p'2n'6limbs'2NR2XB2PS2HB5Ha_st5Hl_stS2sp1X1z2lo2p'2n'6limbs'2XB2HB5Ha_st5Hl_stS1X2p'6limbs'2XB2B0S1X6limbs'2XBS1X6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XB2HBS1X2p'2n'6limbs'2NR2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XBS2sp1X2lo6limbs'2XBS1X1z6limbs'2XB2HB5Ha_st5Hl_stS1X1z2p'2n'6limbs'2NR2XB2HB5Ha_st5Hl_stS1X6limbs'2XBFFS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS2sp1X2lo6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X6limbs'2XB2HB5Ha_stS1X6limbs'2XBS1X2p'6limbs'2XBS1X2p'6limbs'2XBS1X2p'6limbs'2XBS1X2p'6limbs'2XBS1X2p'2n'6limbs'2NR2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1X2p'2n'6limbs'2XBS1X6limbs'2XBS1X6limbs'2XBS1R5NEEDR2sp1X2lo3SLO6limbs'2XB". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR ZB LOS SLO"] Lemma tail_walk : forall (hc : HST asegs R HIA) (LBc : list blk) mm (p' n' : Z) (sw : word) (limbs' : list word) (jk : list byte)
      xra xs3 xs7 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    HM asegs R HIA hc LBc LF mm -> htop asegs R HIA hc = htop asegs R HIA h -> bv_unsigned sp <= htop asegs R HIA hc ->
    X mod 8 = 0 -> (X + 16 <= lo \/ bv_unsigned sp <= X) -> 1 <= n' <= MPI_MAX_LIMBS ->
    In (p', 4 * n') LBc -> p' mod 16 = 0 -> (X + 16 <= p' \/ p' + 4 * n' <= X) ->
    rw_cells asegs mm X (mpi_cells p' sw n' pad) -> u32arr asegs mm p' limbs' -> Z.of_nat (length limbs') = n' ->
    client_wrange L (LBc ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16 ->
    aobj asegs AL (hcs asegs R HIA hc) mm X 16 ->
    rw_cells asegs mm (bv_unsigned sp + -80) (CB 8 jk :: FRAME) -> stk asegs mm lo (bv_unsigned sp + -80) -> mem_inv asegs mm ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms' => exists x5 x6 x7 a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (w0 : word),
         ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                  F (ret_pc ra) fc None m' (seg_rom asegs)
         /\ munch [(lo, bv_unsigned sp); (X, X + 16); (p', p' + 4 * n')] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m'
         /\ rw_cells asegs m' X (mpi_cells p' (Z_to_bv 64 ZSG) n' pad)
         /\ u32arr asegs m' p' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1)))
         /\ w0 = Z_to_bv 64 (bv_swrap 32 (Z.abs z))
         /\ stk asegs m' lo (bv_unsigned sp) /\ HM asegs R HIA hc LBc LF m')
      (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 z) (Z_to_bv 64 X) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 (X + 10)) xs3 SB SHX10 (Z_to_bv 64 (Z.shiftr X 3)) xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x09c2ec) fc None mm (seg_rom asegs)).
  Proof.
    intros until xt6. intros HH HT TOPc ALX8 DSX NR HIN PAL DXP HX HPL LL CWc OX FR ST MI. basic_facts hc LBc mm HH TOPc.
    pose proof (rw_cells_bound _ _ _ _ HX) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    unfold MPI_MAX_LIMBS in NR.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CWc]; clear - LOS SLO NEEDR; lia).
    destruct (hm_apart asegs R HIA hc LBc LF mm HH) as [HF _]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & PC & _). cbn in B0, PC.
    pose proof (hm_aobj_block asegs R HIA hc LBc LF mm p' (4 * n') HH HIN) as OP.
    assert (HINF : In (p', 4 * n') (LBc ++ fdata LF)) by (apply in_app_iff; left; exact HIN).
    assert (PS : p' + 4 * n' <= lo) by (clear - PC ALO LOS; lia).
    unfold mpi_cells in HX.
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16); (p', p' + 4 * n')] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply u32arr_cells in HPL. apply (u8arr_of_rw_cells asegs) in HPL.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n')) with (Z_to_bv 64 n')
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_LS) as SPM. unfold A_ASAN_MEMSET_LS in SPM.
    callxA_sp (bv_unsigned sp + -80)
      (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := p') (v := 0) (n := n' * 4) (lo := lo) (ds := u32s limbs');
       rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | rewrite u32s_length; clear - LL; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]
             | left; clear - PS; lia                                                            (* [comment removed for export] *)
             | eapply (blk_top47_sub asegs R HIA hc LBc LF); [exact HH| exact HIN| clear; lia]     (* [comment removed for export] *)
             | eapply client_wrange_block; [exact HINF| clear; lia| clear; lia]
             | clear - NR LOS SLO NEEDR NRA TOPc SPA SPR; lia
             | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 p' _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : ?x = Z_to_bv 64 p' |- _ => subst x end.
    apply (rw_cells_of_u8arr asegs) in HPZ. rewrite repeat_length in HPZ.
    apply (rw_cells_zeros asegs m5 p' (Z.to_nat (n' * 4)) [C4 (Z_to_bv 64 0); CB (Z.to_nat (n' * 4 - 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (n' * 4 - 4)))]) in HPZ;
      [| cbn; repeat split; reflexivity | cbn [cells_size csize]; clear - NR; lia].
    apply (rw_cells_app asegs m5 p' [C4 (Z_to_bv 64 0)]) in HPZ. destruct HPZ as [HP0 HPR]. cbn [cells_size csize Nat.add] in HPR.
    replace (p' + Z.of_nat 4) with (p' + 4) in HPR by (clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OP p' 4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    match goal with H : rw_cells asegs m9 X _ |- _ => rename H into CH9 end.
    match goal with H : rw_cells asegs m9 p' [C4 ?w] |- _ => rename H into HP9; set (w0 := w) in HP9 end.
    apply (rw_cells_C2_congr asegs m9 X [C8 (Z_to_bv 64 p')] _ ZSG) in CH9; [| apply to_sign_mod16_A; exact ZB].
    apply evtA_done. deexists 15. exists w0. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact CH9|].
    split.
    { change (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) with ([w0] ++ repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))).
      apply u32arr_app. split.
      - eapply (u32arr_of_cells asegs); [eapply rw_cells_reshape; [exact HP9| cbn -[le4]; split; [apply length_le4| exact I] | cbn -[le4]; rewrite app_nil_r; reflexivity]|].
        cbn. rewrite ?app_nil_r. reflexivity.
      - cbn [length Z.of_nat Pos.of_succ_nat]. replace (Z.to_nat (n' * 4 - 4)) with (4 * Z.to_nat (n' - 1))%nat in HPR by (clear - NR; lia).
        eapply (u32arr_of_cells asegs); [exact HPR| symmetry; apply u32s_repeat0]. }
    split; [unfold w0; f_equal; apply P_mpi_cmp_int.sint_abs32; exact ZB|].
    split; assumption.
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L11681434484.4L29913573718.6L38557619554.3L39280637297.0L57933578978.9L57940023954.9L61055709130.0L7329506184.3 00000<00L00U00V01001F01G01PS1R3HIA1h2HsS1R1z2ZB3ALO3ACVS1z2ZB2HpSS1R3HIA1h1z2ZB3T164HTOP2HsS1R3HIA1h1z2SH2Hs1C2ZBSS1z2ZB2Hn". (* [comment removed for export] *)
  #[using="ZB"] Lemma uwc_z : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset ()) "Pmm,P,(=.&40.)(>.(=.&8.))Pmx,P,(=.&40.)(>.(=.&8.))PF0,$1.P,(?.$10.VR,VHIA,Vh,VLB,VLF,R2.)(11.$10.R4.(12.VR,)(13.$10.VR,VHIA,Vh,)(14.&40.(15.&40.Vz,))R2.=)")
(* [comment removed for export] *).
  Proof.
    intros mm mx F0 HH. apply uwc_stop; [clear; lia|].
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV. pose proof (hm_top16 asegs R HIA h LB LF mx HH) as T16.
    pose proof (hm_top asegs R HIA h LB LF mx HH) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (art_stk_high asegs R HIA) as SH.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
    destruct (Z_lt_le_dec z 0) as [Hn|Hp].
    - right; left.
      replace (z mod 2 ^ 64) with ((z + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; clear; lia).
      rewrite Z.mod_small by (clear - Hn ZB; lia).
      destruct (Z_lt_le_dec (arl_stklo R) (hstkhi asegs R HIA h)) as [Hs|Hs].
      + destruct (hcs_app asegs R HIA h (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R) SCS0 ltac:(clear - Hs; lia)) as [[_ C]|[_ C]]; clear - C SH Hn ZB Hs; lia.
      + clear - Hs HTOP T16 Hn ZB. lia.
    - left. rewrite Z.mod_small by (clear - Hp ZB; lia). clear - Hp ZB ALO ACV. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="HNS"] Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset ()) "Pmo,$16.Pmo',$16.Ph',(17.$10.VR,VHIA,)Pm',P,(=.&40.)(>.(=.&8.))Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Pxa1,(=.&40.)Pxa2,(=.&40.)Pxa3,(=.&40.)Pxa4,(=.&40.)Pxa5,(=.&40.)Pxa6,(=.&40.)Pxa7,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(18.$10.R?.)P,(19.$10.R10.Vlo,(14.&40.Vsp,))P,(1:.R14.R13.)P,(1;.$10.VR,(1<.VLB,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))VLF,(14.&40.Vsp,)(12.VR,)(13.$10.VR,VHIA,Vh,)(1>.(1?.$1.$1.)(20.$1.$1.VX,(21.VX,+10.))(22.(1?.$1.$1.)))Vm,R12.)P,(23.$1.(24.$10.VR,VHIA,R14.)(24.$10.VR,VHIA,Vh,))P,(23.$1.(13.$10.VR,VHIA,R15.)(13.$10.VR,VHIA,Vh,))P,(23.$1.(25.$10.VR,VHIA,R16.)(25.$10.VR,VHIA,Vh,))P,(26.$10.VR,VHIA,R17.R18.)P,Px,$1.P,(27.$10.VR,VHIA,Vh,R1.)(27.$10.VR,VHIA,R1:.R2.)P,(3.(28.$10.VR,VHIA,R19.)(21.(28.$10.VR,VHIA,Vh,)(8.+1.)))P,(3.(29.$10.VR,VHIA,R1:.)(21.(29.$10.VR,VHIA,Vh,)(9.Vd,)))P,(?.$10.VR,VHIA,R1;.VLB,VLF,R1:.)P,(2:.$10.R1;.VLB,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))(2;.$10.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$7.(2.(<.Vz,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)P,(23.$1.R2.=)(23.$1.(4:.R2.)Vz,))(8.+1.)(9.Vd,)Vlo,Vm,R1?.(2<.(2=.(2>.Vra,Vsp,Vgp,Vtp,R1;.R1:.R19.Vs0,Vs1,(15.&40.$2?.)R18.R17.R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(30.Vra,)Vfc,(31.(=.&40.))R1<.(32.$10.))R1>.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, dX, MBEDTLS_ERR_MPI_ALLOC_FAILED.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [apply mpd_out_refl; cbn [md_own]; exact HNS|].
    split; [intros b Hb; left; exact Hb|].
    cbv beta. split; [| intros E; cbv in E; discriminate E].
    unfold lset_R. split; [right; split; reflexivity|]. split; [reflexivity| intros b Hb; left; exact Hb].
  Qed.

  #[using="Type"] Lemma lset_val_abs : forall (v : Z) (k : nat), -2^31 <= v < 2^31 ->
      (if v <? 0 then -1 else 1) * limbs_val (Z_to_bv 64 (bv_swrap 32 (Z.abs v)) :: repeat (Z_to_bv 64 0) k) = v.
  Proof.
    intros v k Hv. clear - Hv. cbn [limbs_val]. rewrite limbs_val_repeat0, Z_to_bv_unsigned.
    assert (E : bv_wrap 64 (bv_swrap 32 (Z.abs v)) mod 2 ^ 32 = Z.abs v).
    { unfold bv_swrap, bv_wrap.
      change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
      destruct (Z_lt_le_dec (Z.abs v) (2 ^ 31)) as [L|L].
      - rewrite (Z.mod_small (Z.abs v + 2 ^ 31) (2 ^ 32)) by lia.
        replace (Z.abs v + 2 ^ 31 - 2 ^ 31) with (Z.abs v) by lia.
        rewrite (Z.mod_small (Z.abs v) (2 ^ 64)) by lia. apply Z.mod_small. lia.
      - replace (Z.abs v) with (2 ^ 31) by lia. reflexivity. }
    rewrite E. destruct (Z.ltb_spec v 0); lia.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L36257435357.2L57111244952.2L61449593947.200000700>00ES2n'2NRS2n'2NRS2n'2NR". (* [comment removed for export] *)
  #[using="ZB"] Lemma post_set : forall (LBr : list blk) (mo mo' : Model) (h' : HST asegs R HIA) m' (p' n' : Z) (w0 : word)
      x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31,
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> mo_frame mo mo' ->
    presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m' ->
    htop asegs R HIA h' = htop asegs R HIA h -> hstkhi asegs R HIA h' = hstkhi asegs R HIA h ->
    hflag asegs R HIA h' = hflag asegs R HIA h -> HK asegs R HIA h' mo' ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA h' x) ->
    havol asegs R HIA h' <= havol asegs R HIA h + grow_PHI 1 -> hfr asegs R HIA h' <= hfr asegs R HIA h + lset_FR d ->
    HM asegs R HIA h' LBr LF m' -> rw_cells asegs m' X (mpi_cells p' (Z_to_bv 64 ZSG) n' pad) ->
    u32arr asegs m' p' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) -> w0 = Z_to_bv 64 (bv_swrap 32 (Z.abs z)) ->
    In (p', 4 * n') LBr -> p' mod 16 = 0 ->
    1 <= n' <= MPI_MAX_LIMBS -> n' = Z.max n 1 -> X mod 8 = 0 -> 0 < X ->
    (forall b, In b LBr -> In b LB \/ b = (p', 4 * n')) -> (forall b, In b LB -> ~ In b (mpd_blk dX) -> In b LBr) ->
    (forall b, In b (mpd_blk dX) -> In b LBr -> [(p', 4 * n')] = mpd_blk dX) ->
    (In (p', 4 * n') (mpd_blk dX) \/ (fresh_apart R (mpd_keep LB dX) LF p' (4 * n') /\ ~ In (p', 4 * n') LB)) ->
    POST m mo (mkCfg (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None m' (seg_rom asegs)) mo').
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH HX HPL HW0 HIN PAL NR En ALX X0 HI1 HI2 HI3 HF.
    unfold mpi_binop_postA. deexists 14.
    dexists m', mo', h', LBr, (mkMPD X ZSG n' p' (w0 :: repeat (Z_to_bv 64 0) (Z.to_nat (n' - 1))) pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|].
    split. { split; [| cbn [md_sg]; destruct (z <? 0); [right| left]; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact HX|]. split; [exact ALX|]. split; [exact X0|]. split; [cbn [length]; rewrite repeat_length; clear - NR; lia|]. split; [clear - NR; lia|].
      split; [clear - NR; lia|]. split; [exact HIN|]. split; [exact PAL| exact HPL]. }
    split. { unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b Hb; destruct (HI1 b Hb) as [Hb'| ->]; [left; exact Hb'| right; left; reflexivity]|].
      split; [exact HI2| exact HI3]. }
    split; [cbn [mpd_blk md_own md_p md_n]; intros b [<-|[]]; destruct HF as [HF'|[HF' _]]; [left; exact HF'| right; exact HF']|].
    cbv beta. split; [| intros _; unfold mpd_val; cbn [md_sg md_limbs]; rewrite HW0; apply lset_val_abs; exact ZB].
    unfold lset_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
    split; [left; split; [reflexivity|]; split; [exact En|]; split; [reflexivity|]; split; [eexists; reflexivity| split; reflexivity]|].
    split; [reflexivity|]. intros b [<-|[]]. destruct HF as [HF'|[_ HF']]; [left; exact HF'| right; exact HF'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "03c0@D24976250634.165D3399625391.115 D3399625391.116 D34467306507.165D35881667587.115D35881667587.116D39373300857.148D50797141399.165D50797141399.166D52014138856.165D52014138856.166D59228252318.165D60098936221.166D62155808737.166D65063575786.166K21652967687.165K21652967687.166K42587433812.115K42587433812.116K44044790992.165K44044790992.166L11498238141.14 L1160155683.143 L1160155683.188 L14211003605.14 L15302269400.111L15302269400.145L1685717371.0   L19231460853.188L1954497222.2   L19947928356.143L19947928356.188L19954004375.148L21646329835.2  L22446743512.111L22446743512.145L23100341967.155L23100341967.158L24387386274.146L25214214772.111L26892418956.1  L28762391469.4  L28814040852.155L29428324939.5  L29767916836.3  L31225147636.111L3223889640.9   L3226164952.10  L3226164952.9   L3227728773.8   L3228232793.14  L33087634096.2  L34705680216.111L34705680216.145L35653441506.7  L37246946676.110L38948636245.0  L39268637205.0  L39280637297.0  L3949578456.110 L3949578456.145 L40281191306.3  L40374333670.111L40834179097.113L41321561253.7  L41843875160.111L41843875160.145L4231931142.3   L42594106808.2  L43061363337.109L44055312295.2  L46122776823.12 L46160487540.112L46160487540.157L46160572444.109L48132467214.7  L49283344500.111L49578233423.158L50790809970.7  L51038660417.9  L51041001329.10 L51041001329.9  L51043003888.14 L51043613228.8  L51454941784.111L51454941784.145L51613292135.1  L5255722929.111 L547707976.3    L5479049730.1   L55310518004.111L56010806032.10 L56013452877.11 L56013452877.12 L5613025437.11  L5617070636.15  L5699067096.111 L5699067096.145 L57026329442.0  L57344136272.143L57818804596.111L58591023192.111L58591023192.145L59308546259.3  L59308546384.3  L59308633593.3  L59314873579.2  L59504824382.145L60098763854.3  L60447862057.2  L61321319284.111L61929718192.2  L61929812241.112L61975918423.1  L61979552523.6  L62018535662.1  L62624422447.38 L62624897321.38 L62698640939.5  L63261865046.14 L63829069812.111L6404460081.3   L64194470200.2  L65358966972.3  L65361583713.1  L656136024.1    L66356042725.2  L66356286070.3  L66358289365.4  L66358289365.5  L66360349012.7  L67280348888.111L67280348888.145L67351568884.111L6935467336.1   L774765788.5    P35873984078.147P35873984078.148Q12370813529.160Q12370813529.163Q15641142849.146Q15643324129.111Q17203243724.159Q17205256176.162Q17530203490.114Q17530203490.115Q18363908161.146Q18365925601.112Q18694146040.114Q21798041355.114Q21877632546.146Q21879645826.112Q24974040330.164Q25157988860.114Q25513505925.114Q25513505925.115Q25662358575.114Q26056447029.117Q26058334103.135Q26207688439.111Q26207721832.114Q26207721832.162Q26209519061.161Q26220436438.113Q26220553932.159Q27582927425.146Q27584944865.112Q27905023394.146Q27907200258.112Q30413056290.146Q30415036802.112Q31228709292.114Q31269541057.146Q31271525473.112Q31394594844.114Q31649392511.113Q31651985788.161Q32653290817.146Q32655500769.112Q33916013346.146Q33918256002.112Q35014437530.114Q35717497884.114Q36423603362.146Q36425882626.112Q37621059886.159Q37623178258.162Q3830427394.112 Q3832375202.146 Q38476389417.165Q38476389417.166Q39212284437.114Q39212284437.162Q39939554818.112Q39941830306.146Q41152393185.112Q41154340673.146Q4143427880.114 Q42081808994.162Q43925228937.114Q43925228937.162Q44648843873.112Q44650824385.146Q45996432381.148Q49698585326.113Q49698585326.114Q51233882049.146Q51235796833.112Q52016320488.164Q52016320488.165Q5300226131.112 Q5300226131.113 Q53969758199.114Q5472542515.159 Q5483506191.162 Q5485174314.160 Q5485174314.163 Q59841124801.146Q59843137889.112Q60511567613.114Q60511567613.162Q60539943628.147Q60697995187.114Q60697995187.162Q6143569392.160 Q6143569392.163 Q61802139820.114Q62157788641.165Q62965564504.163Q62965564504.164Q6416456232.114 Q64255486968.114Q66522067074.112Q66524084258.146Q67528989526.115Q67528989526.116Q7891539809.163 Q8880780715.111 Q8884684176.159 Q9534597475.159 Q9538509144.111 Q9841349922.146 Q9843367298.111 00000P01K02[02\03I04K04Z05W06T07407T07U07V08608708h09[0:T0;b0<B0<b0=70=K0=\0=l0>;0>J0>K0>\0>b0?90?M0?\0?]0?l0@;0@L0@]0AB0AQ0AU0AV0BK0B]0Bf0C50C60C70C80C90C:0C@0CO0C^0D>0DM0DN0DO0DP0D_0Dn0E70EF0EW0EX0Eg0F60F?0F@0Fe0Ff0GG0GY0Gm0H?0HZ0Hi0I:0IQ0IR0IS0IT0IU0IV0Ie0J40J50JG0JQ0JT0Jc0Jd0Je0Jf0Jg0Jh0K70KF0KG0K]0Kl0L;0LJ0LS0L\0Le0Lj0M90MC0MI0MX0M^0N20N30N40N70N80N90N:0NF0NU0N^0Ne0Nk0Nl0No0O00O10O20O30O40OC0OR0Oa0Oe0P80PG0PV0Pn0QF0QX0Qj0R60RB0S20T70TI0T[0Tn0To0UM0Uk0VF0VY0W=0X60X70Xe0YS0Y_0Yk0Z70ZC0ZO0Z[0Zm0[?0[]0\;0\Y0]70]K0]]0]o0^;0^G0^S0^e0_70_U0`30`G0`H0`f0aD0aP0a\0b:0bX0c;0c^0cj0d60dT0e20eD0eV0eW0ei0f50fA0fS0fe0ff0gB0g^0h00hB0h]0i:0iL0i^0j20j>0jJ0jV0jb0k40kF0kR0k^0l@0lO0l^0lj0m60m70mT0mi0n>0nQ0nR0o00oN10>11C11U11a11m12912E12c13AS2sp1X5limbs2XB1A2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3LOS3SLO2X03SPR2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1R3HIA1h2ra2sp1X5limbs3TOP2XB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X5limbs3TOP2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2X03SPR2XB1A2A02HB5Ha_st5Hl_stS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2X03SPR2XB1A2A02HB5Ha_st5Hl_stS2sp1X5limbs2XB1A2HB5Ha_st5Hl_stS2sp1X5limbs2XB1A2HB5Ha_st5Hl_stFFS2sp1X5limbs2XB1A2HB5Ha_st5Hl_stFS1R5NEEDR2sp1X5limbs2lo3SLO2XB3DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp1X5limbs2lo3SLO2XB3DSX1A2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X1P5limbs2lo3SLO2XB2P03DSX2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1X5limbs2XB1A2XA2HB5Ha_st5Hl_stS1X5limbs2XB1A2XA2HB5Ha_st5Hl_stS1R2sp2lo3SLO3NRM3SPRS2sp1X1P5limbs2XB2P0S2sp1X5limbs1A2XBS1R3HIA1h2sp3TOPS2sp1X5limbs2XBS2sp1X5limbs2XBSS2sp1X5limbs1A2XBS1P2B0S2sp1X1P5limbs2lo2XB2P0S2sp1X5limbs2lo1A2XBS2sp1X5limbs2XBFS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XB1AS2sp1X5limbs2XB1AS1R5NEEDR2sp1X5limbs2lo3SLO2X03SPR2XBS2sp1X5limbs2XBS2spFS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2X03ALO3SPR2XB1A2A02ACS1R2lo3LOS3ALO3ACPS1n2NR2N1S2sp1X5limbs2XBFFFFFS1n2NRS2sp1X5limbs2XBS2sp1X5limbs2XBS1R3HIA1h2sp2lo3TOP4HTOP2h24TOP2S2sp1X5limbs2XBSSSS2sp1X5limbs2XBS2sp1X5limbs2XBS1R3HIA1hS2sp1X5limbs2XBS1R2sp1X5limbs2XBFS2sp1X5limbs2XBS2sp1X5limbs2XBS1R3HIA1hFS1R5NEEDR2sp1X5limbs2lo3SLO2X03SPR2XBFS1R2sp1n1P5limbs2lo3LOS2LL3ALO2PCS2sp1X5limbs2X02XBS2sp1X5limbs2X02XB1AS2sp1X5limbs2X02XBS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1X5limbs2XBS2sp1X5limbs2XB1AS1R5NEEDR2sp2lo3LOS3SLOFFFFFS2sp1X5limbs2XBS2sp1X5limbs2XBFS2sp1X5limbs2X02XBS1R3HIA2h2S1XS2sp1X5limbs2XBFFFFFS2sp1X5limbs2XBS2sp1X5limbs2XBSS2sp1X1n1P5limbs2XB2P0S2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS1n2K12N0S1n2K12N1S1A2A02KZS1A1HS2sp1X5limbs2XBS1R2lo3LOSS1n2NRS2sp1X5limbs2XBS1n2NRS2sp1X1n5limbs2NR2XBFFS1RFFFS2sp3SPA3SPRS2sp1X5limbs2XBS1R3HIA1hS1R3ACPS1n2N1FS1XFFFFFS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs2XBS2spS1R5NEEDR2sp2lo3SLOS2sp1X5limbs2XBS2sp1X5limbs2XBS2sp1X5limbs3ALX2X02XB1AS2sp1X5limbs3ALX2X02XB1AS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XB2HB5Ha_st5Hl_stS1R1X5limbs4IMG'2XBS2ra2sp1X5limbs2lo2XB2HB5Ha_st5Hl_stS2sp2s01X5limbs2lo2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO3ALO3ACP3SPR2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R1X5limbs5ALWF'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XB1A2HB5Ha_st5Hl_stS2sp1X5limbs2lo1A2XB2HB5Ha_st5Hl_stS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBFS1X5limbs2X02XB2HBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBFS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs3SPR2XB2HB5Ha_stS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X5limbs2XB2HB5Ha_st5Hl_stS1X5limbs2XB1A2HB5Ha_st5Hl_stS2sp1X5limbs2XB2HBS2sp1X5limbs2XB2HBS1R1X5limbs5ALWF'2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS2sp1X5limbs2lo2XBS2sp1X5limbs2lo2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3LOS3SLO2XBS1X5limbs2X02XBS1X5limbs2X02XBS1X5limbs2XBS1X5limbs2XBFS1X5limbs2XB1A2HB5Ha_st5Hl_stS1X5limbs2XB2HB5Ha_stS1X5limbs2XB2HB5Ha_stS1R1X5limbs4IMG'2XBFS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2ra2sp1X5limbs2lo3SLO2XB2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X5limbs2lo3SLO2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1X5limbs2X02XB2HBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1X5limbs2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XBS1R5NEEDR2sp1X5limbs2lo3SLO2XB". (* [comment removed for export] *)
  #[using="IMG CALLOC AMS NEEDR HND DIMG HNS ZB XW DSP LOS SLO TOP SPA TPV"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset ()) "Pmo,$16.Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(?.$10.VR,VHIA,Vh,VLB,VLF,Vm,)P,(26.$10.VR,VHIA,Vh,R?.)P,(2:.$10.Vm,VLB,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,))P,(19.$10.Vm,Vlo,(14.&40.Vsp,))P,(18.$10.Vm,)P,(33.$10.(34.VR,)(27.$10.VR,VHIA,Vh,)Vm,VX,+10.)P,(3.(21.(28.$10.VR,VHIA,Vh,)(8.+1.))$35.)P,(3.(21.(29.$10.VR,VHIA,Vh,)(9.Vd,))$36.)(37.$10.(2;.$10.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)Lr,$1.LdX',$7.(2.(<.Vz,(1=.VX,Vsg,Vn,VP,Vlimbs,Vpad,Vown,)VLB,R2.R1.)P,(23.$1.R2.=)(23.$1.(4:.R2.)Vz,))(8.+1.)(9.Vd,)Vlo,Vm,R16.)(2<.(2=.(2>.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(15.&40.VX,)(15.&40.Vz,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(15.&40.$38.)Vfc,(31.(=.&40.))Vm,(32.$10.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo MX ST MI OX BUD BUDF. unfold A_MPI_LSET. rt_facts h.
    pose proof BUDF as BUDF0. rewrite lset_FR_val in BUDF. pose proof BUD as BUD0. unfold grow_PHI in BUD.
    pose proof (HND _ _ _ _ HH) as ND.
    destruct MX as [(HXS & ALX & X0 & LL & NR & HOWN) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, ALX, X0, LL, NR, HOWN, SG.
    destruct XW as [CW DXP]. cbn [md_addr md_own md_p md_n] in CW, DXP.
    pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [mpi_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in XB.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in NR.
    assert (PB : 0 <= P /\ P + 4 * n <= alloc_ceiling
                 /\ (own = LHeap -> 0 < P /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr asegs m P limbs /\ 1 <= n)
                 /\ (own = LNull -> P = 0 /\ n = 0)).
    { destruct own; [| | exfalso; exact (HNS eq_refl)].
      - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PB as (P0 & PC & PHEAP & PNULL). clear HOWN.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    do 10 zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. shadow_chk OX (X + 10) 2.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { apply presA_nil_any. eapply (presA_tail0 asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU0| exact WM0]. }
    assert (PCH1 : own = LHeap -> u32arr asegs m1 P limbs).
    { intros E. ddestruct (PHEAP E) as (_ & _ & _ & HXL & _).
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PC ALO LOS SLO NEEDR LL; lia]. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K1 by (clear - NR; lia).
      assert (EO : own = LHeap).
      { destruct own; [| reflexivity| exfalso; exact (HNS eq_refl)]. exfalso. destruct (PNULL eq_refl) as [_ N0]. clear - N0 K1. lia. }
      ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1). pose proof (PCH1 EO) as HXL1. clear PHEAP PCH1 PNULL.
      specialize (DXP EO).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply tail_walk with (hc := h) (LBc := LB); try eassumption; try reflexivity | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS).
      all: try (exact FR).
      all: try (unfold MPI_MAX_LIMBS; clear - NR N1; lia).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "TAIL0-PRE-LEFT:" g end.
      intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & HPL9 & W09 & ST9 & HH9). subst ms'.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply aevtA_done. intros mo9 [HK9 MF9].
      assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
      { eapply presA_trans; [exact HP1|].
        eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] P (4 * n) m1 m1 m9);
          [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
        - intros b xb Hb Hr. unfold mpd_keep in Hb. cbn [md_own md_p md_n] in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          split; [exact Hb|]. intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        - eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16); (P, P + 4 * n)]);
            [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; clear; intros y Hy; tauto].
          eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) _ m1 m9); [exact HH| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|].
          apply Forall_cons; [cbn [fst snd]; replace (P + 4 * n - P) with (4 * n) by lia; eapply hcs_block; [exact HH| exact HIN]|]. apply Forall_nil. }
      eapply (post_set LB mo mo9 h); try eassumption; try reflexivity.
      all: try (intros y Hy; exact Hy).
      all: try (unfold grow_PHI, AVOL_CALL; clear; lia).
      all: try (rewrite lset_FR_val; clear; lia).
      all: try (unfold MPI_MAX_LIMBS; clear - NR N1; lia).
      all: try (clear - N1; lia).
      all: try (intros b Hb; left; exact Hb).
      all: try (intros b Hb _; exact Hb).
      all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb _; destruct Hb as [<-|[]]; reflexivity).
      all: try (left; cbn [mpd_blk md_own md_p md_n]; rewrite EO; left; reflexivity).
      all: match goal with |- ?g => idtac "SET0-LEFT:" g end.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K1 by (clear - NR; lia).
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (HNS eq_refl)]. exfalso. ddestruct (PHEAP eq_refl) as (_ & _ & _ & _ & N1). clear - N1 K1. lia. }
      destruct (PNULL EO) as [EP En]. clear PHEAP PCH1 PNULL.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := 1) (sz := 4) (lo := lo) (d := 0);
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; try eassumption; try reflexivity.
        all: try c24_lit.   (* [comment removed for export] *)
        all: try (eapply uwc_z; exact HH).
        all: clear - LOS SLO NEEDR NRM TOP SPA SPR BUD BUDF; try (unfold AMAX); try (unfold AVOL_CALL in * ); try (unfold fr_charge in * ); try lia.
        all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP1 HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
      apply (aobj_cs_mono asegs AL _ _ _ _ _ HCS2) in OX.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      clear CSOK SB64 SCS0 SCS HTOP.
      pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      + (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP.
        assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]).
        assert (MA2 : mpd_at asegs m2 LB dX).
        { eapply mpd_at_rebuild; [exact HNS| unfold mpi_cells; exact HXS| exact ALX| exact X0| exact LL| unfold MPI_MAX_LIMBS; clear - NR; lia| exact SG| intros _; split; [exact EP| exact En]|].
          intros E. rewrite EO in E. discriminate E. }
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        zstep.
        release_frame FR ST2 (bv_unsigned sp).
        zstep.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_keep mo mo9 h2); try eassumption.
        all: try (eapply mo_frame_trans; [| exact MF9]; eapply mo_frame_trans; [exact MF1| exact MF2]).
        all: try (unfold grow_PHI, AVOL_CALL in *; clear - HV2; lia).
        all: try (rewrite lset_FR_val; unfold fr_charge in HFR2; clear - HFR2; lia).
        all: match goal with |- ?g => idtac "KEEP-LEFT:" g end.
      + (* [comment removed for export] *)
        change (1 * 4) with 4 in HFRA, HAS, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in HNEW.
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP.
        assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP; lia]).
        dpose HFRA as (A0 & AC & AD & HAP).
        assert (XA : X + 16 <= A \/ A + 4 <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A 4 HFRA); [| clear; lia| clear; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (CW3 : client_wrange L (((A, 4) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
        { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
        assert (HA2 : u32arr asegs m2 A [Z_to_bv 64 0]).
        { eapply (u32arr_of_cells asegs); [exact HNEW| symmetry; apply (u32s_repeat0 1)]. }
        rewrite EP in HXS.
        pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16); (A, A + 4)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
        zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        shadow_chk OX (X + 10) 2.
        zstep. zstep. zstep. zstep. zstep.
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply tail_walk with (hc := h2) (LBc := (A, 4) :: LB) (n' := 1) (limbs' := [Z_to_bv 64 0]); try eassumption; try reflexivity
          | intros y Hy; exact Hy | ].
        all: try (exact FR).
        all: try (left; reflexivity).
        all: try (unfold MPI_MAX_LIMBS; clear; lia).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "TAIL1-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU & WM & MI9 & HX9 & HPL9 & W09 & ST9 & HH9). subst ms'.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        apply aevtA_done. intros mo9 [HK9 MF9].
        assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
        { eapply presA_trans; [exact HPX2|]. rewrite <- HS2.
          eapply (presA_drop_fresh asegs R HIA h2 (mpd_keep LB dX) LF [(X, X + 16)] A 4 m2 m9 (bv_unsigned sp)); [| apply fresh_apart_keep; exact HFRA| clear - ALO LOS SLO NEEDR; lia].
          eapply (presA_weaken asegs R ((A, 4) :: LB) (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h2) (hstkhi asegs R HIA h2) [(X, X + 16); (A, A + 4)]);
            [| intros b Hb; right; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; clear; intros y Hy; tauto].
          eapply (presA_drop_below asegs R HIA h2 ((A, 4) :: LB) LF _ lo (bv_unsigned sp) _ m2 m9); [exact HH2| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R ((A, 4) :: LB) LF _ _ _ _ m2 m9 (hcs asegs R HIA h2) CSOK);
            [| intros c0 Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia | | eapply wmono_trans; [exact WM2'| exact WM]].
          - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|].
            apply Forall_cons; [cbn [fst snd]; replace (A + 4 - A) with 4 by lia; eapply hcs_block; [exact HH2| left; reflexivity]|]. apply Forall_nil.
          - eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MU]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
        eapply (post_set ((A, 4) :: LB) mo mo9 h2); try eassumption; try reflexivity.
        all: try (eapply mo_frame_trans; [| exact MF9]; eapply mo_frame_trans; [exact MF1| exact MF2]).
        all: try (unfold grow_PHI, AVOL_CALL in *; clear - HV2; lia).
        all: try (rewrite lset_FR_val; unfold fr_charge in HFR2; clear - HFR2; lia).
        all: try (left; reflexivity).
        all: try (unfold MPI_MAX_LIMBS; clear; lia).
        all: try (rewrite En; reflexivity).
        all: try (intros b [Hb|Hb]; [right; symmetry; exact Hb| left; exact Hb]).
        all: try (intros b Hb _; right; exact Hb).
        all: try (cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b []).
        all: try (right; split; [apply fresh_apart_keep; exact HFRA| intros Hin; destruct (HAP A 4 ltac:(apply in_app_iff; left; exact Hin)); clear - H; lia]).
        all: match goal with |- ?g => idtac "SET1-LEFT:" g end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_mpi_lset_spec_v : forall (R : art_layout) (HIA : artA asegs R),
  asan_img_ok (arl_AL R) -> arl_calloc R = A_WRAP_CALLOC_LS -> arl_amemset R = A_ASAN_MEMSET_LS -> 0 <= arl_need_rt R ->
  (forall (h : HST asegs R HIA) (LB LF : list blk) (m : bv 64 -> option (bv 8)), HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  mpi_lset_stmtA_v asegs R HIA A_MPI_LSET.
Proof.
  intros R HIA IMG CAL AMS NEEDR HND DIMG. unfold mpi_lset_stmtA_v, mpi_xop_stmtA.
  intros until d. intros HH HK MX HNS ZBv XW DSP ST LOS SLO TOP SPA TPV MI RA2 OXA BUD UW XUW BUDF -> ->.
  destruct dX as [X sg n P limbs pad own].
  eapply main_walk; try eassumption. exact (proj1 OXA).
Qed.

Lemma A_mpi_lset_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_lset ()) "PR,$39.PHIA,(3:.$10.R1.)P,(3;.(34.R2.))P,(23.$1.(3<.R3.)$3=.)P,(23.$1.(3>.R4.)$3?.)P,(3.=(40.R5.))P,Ph,(17.$10.R6.R5.)PLB,(:.$;.)PLF,(:.$;.)Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.R:.R9.R4.R3.R2.R1.)(41.$1.(42.(1?.$1.$1.)$1.(43.$1.$1.)R4.))P,(2.(3.(44.(45.R7.))(46.(45.R7.)))(3.(47.(45.R7.))(48.(45.R7.))))(49.$10.R8.R7.$38.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG CAL AMS NEEDR HND DIMG. pose proof (A_mpi_lset_spec_v R HIA IMG CAL AMS NEEDR HND DIMG) as V.
  unfold mpi_lset_stmtA_v, mpi_lset_stmtA, mpi_xop_stmtA in *.
  intros until d. intros. eapply aevtS_mono; [eapply V; eassumption|].
  intros c PO. unfold mpi_binop_postA in *.
  ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & PO).
  dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', mo', h', LB', dX', r.
  ddestruct PO as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
  repeat (split; [assumption|]). exact (proj1 P16).
Qed.
