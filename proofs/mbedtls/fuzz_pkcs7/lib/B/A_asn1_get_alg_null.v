(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_platform_zeroize A_asn1_get_alg_A A_asn1_get_alg A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_asn1_get_alg_null_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_asn1_get_alg_null () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.asn1_get_alg_null_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_ASN1_GET_ALG_NULL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_SMALLOC_1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_AMEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_WRAP_MEMSET"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.asn1_get_alg_null_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis AMS : arl_amemset R = A_AMEMSET.
  Hypothesis GA : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : ALG mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 < ALG /\ ALG + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - ASN1_GET_ALG_NULL_STACK_A.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 304 - arl_need_amem R.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo ALG 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) ALG 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.   (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold ASN1_GET_ALG_NULL_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (asn1_get_alg_null_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG P END BUF lo slo).
  Local Notation W := [(PP, PP + 8); (ALG, ALG + 24)].
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1.

  Ltac rw_at_hyp :=
    match goal with
    | H : rw_cells _ ?m ?A' ?cs |- rw_cells _ ?m ?A _ =>
        first [ exact H | replace A with A' by (clear; lia); exact H ]
    end.
  Ltac bw_side :=
    first
      [ eassumption
      | lazymatch goal with
        | |- rw_cells _ _ _ _ => rw_at_hyp
        | |- PATH _ _ _ _ _ _ _ _ _ => unfold PATH;
            first [ left; split; [ reflexivity |]; split; [ reflexivity |]; split; [ reflexivity |]; split; solve [ clear; lia ]
                  | right; split; [ reflexivity |]; split; [ reflexivity |]; split; [ reflexivity |]; split; [ reflexivity |]; split; assumption ]
        | |- crange _ _ _ => solve_crange
        | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
        | |- wcover _ _ _ _ _ _ _ => solve_wcover
        | |- shadow_free _ _ _ _ _ _ _ =>
            first [ match goal with WL : wlow _ _ _ |- _ => apply (shadow_free_of_wlow _ _ _ _ _ _ _ WL); qlia end
                  | match goal with WL : wlow _ _ _, FR : fresh_apart _ _ _ _ _, HHx : HM _ _ _ _ _ _ _ |- _ =>
                      eapply (shadow_free_of_fresh' _ _ _ _ _ _ _ _ _ _ _ _ _ WL FR HHx); qlia end ]
        | |- forall b, In b _ -> In b _ =>
            let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
            first [ exact Hb | apply fdata_cons_sub; exact Hb | right; exact Hb ]
        | |- forall x, _ <= x < _ -> _ \/ in_block _ x =>
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            first [ left; clear_disj; lia
                  | right; match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; clear - Hx; lia] end
                  | right; exists (x - (x - _), 64) ]
        | |- _ \/ _ => first [ solve [clear_mods; clear_disj; lia] | pqlia ]
        | |- _ => first [ qlia | pqlia ]
        end ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03N0@D14306455775.173D14735680649.176D2459889674.173 D27388597713.173D29720839482.176D32452855249.173D3254889317.146 D33746000322.148D3386124073.173 D33956323578.148D33956323578.149D35881667587.126D35881667587.127D51255084822.126D53232575014.148D58077997354.146D61949433775.127D68409458026.173D6897397615.173 K12226132804.126K12226132804.127K44164039966.126K44164039966.127K68083879514.126K68083879514.127L11075936116.118L12219578755.2  L12222146976.2  L12745310030.0  L12758705305.0  L13948747720.1  L15756354262.7  L1685717371.0   L17097338356.118L17523603370.3  L17921795213.166L18966192929.0  L19685319514.162L19687428440.118L19980016842.7  L21866712442.2  L22066801146.3  L22286006383.164L22941438733.2  L23124392564.118L25465666776.118L28125529944.118L29025845208.118L29135309044.118L29738741675.1  L29762660275.117L31686769240.118L33801907085.2  L35287096723.127L3551623394.2   L36180999398.122L37156630869.0  L3876079316.5   L39076636629.0  L39332637397.0  L39618635427.2  L40316771656.2  L40834179097.127L41172169716.118L42250781204.117L42250781204.123L43055154860.120L43679985268.118L44166924249.3  L44168742175.3  L50616353679.164L5065130740.118 L50790731766.8  L51655746932.2  L5288099753.3   L55720577396.118L57355539152.152L58071656716.163L58790154276.6  L59308634497.15 L59393203371.1  L60692334296.118L61601561944.118L61747685364.118L62042415875.117L62505661912.118L64009471222.1  L64270350808.118L64487441312.158L64787780871.1  L65178513496.118L67758486644.118L68097772701.2  L68098527911.2  L8518322573.2   L9356559645.13  L9873114841.7   P1056307012.146 P12226132804.176P21870859916.176P22945712379.176P33789407355.176P36462068749.147P36465839390.146P40332238735.176P44164039966.176P55254318092.146P68083879514.176P8514048635.176 Q12636765557.176Q14646211407.132Q1530342990.146 Q15389352064.132Q15643324129.123Q18365925601.123Q18698356979.132Q20555445589.132Q21802252288.132Q21879645826.123Q22195309491.132Q22712450012.126Q22712450012.127Q22712450012.176Q23275034917.132Q24389563138.123Q24712021240.132Q25153781495.132Q25513505925.125Q25513505925.126Q25513505925.175Q25658182436.132Q25837565221.132Q26030354684.176Q26623612251.132Q27584944865.123Q27907200258.123Q30060557549.132Q30415036802.123Q31021924279.146Q31232886439.132Q31271525473.123Q31398809367.132Q32440606517.173Q32655500769.123Q32681824661.126Q32681824661.127Q32681824661.176Q33172436853.132Q33918256002.123Q33947335980.172Q33967969366.173Q34282861987.132Q34436830071.132Q3482560409.173 Q34964698202.176Q35027002769.132Q3521670295.132 Q35653441506.114Q35704900375.132Q36425882626.123Q3830427394.123 Q38353470298.126Q3871040767.173 Q39517585209.125Q39939554818.123Q40216283646.173Q4024466897.173 Q40271359350.146Q4069764049.173 Q41152393185.123Q41692005595.132Q42100777111.132Q42439168719.146Q42439443119.126Q42439443119.127Q42439443119.176Q43298424778.132Q44648843873.123Q46938320307.173Q47814879687.173Q48132468010.173Q49698585326.124Q49698585326.125Q49698585326.174Q50796826103.146Q51235796833.123Q52101170785.122Q53957191932.132Q55780705378.126Q56857166456.132Q59256763233.123Q59843137889.123Q59852654197.173Q59865321072.126Q59865321072.127Q59865321072.176Q60109315147.114Q60511257090.122Q61389425365.132Q61503024048.175Q6192914196.146 Q6203643061.173 Q63442744065.132Q63766058673.172Q63856323923.124Q6420632867.132 Q64242885875.132Q64333403626.123Q64683667846.126Q64683667846.127Q65285915803.127Q66522067074.123Q67026483294.147Q67038703949.146Q67449522889.132Q67563705004.132Q6897397615.173 Q8026297426.132 Q8699115497.176 Q9356560156.127 Q9633850153.173 Q9843367298.123 00000L01]01^02:03^04:04;04<04=04a05E06507C08A08B08_0:;0:<0:X0;C0<L0=80>B0>n0@80@M0@N0@O0@P0@Q0@V0@d0@e0A:0AD0AE0AF0Ab0B70BO0BP0B\0C80C90CN0Cc0D80DM0Db0Df0E;0EP0EQ0F20F90FN0FO0Fb0Fc0Fd0Fn0Fo0GJ0G_0HZ0IU0J10JF0JG0JH0Jd0K90KJ0KN0KZ0Ko0L00LP0Lf0M90M=0MR0Mg0N<0NQ0Nf0Nj0O?0P20P60PK0P`0Pa0Pb0Pc0QR0Qn0Re0S[0T]0U_0Va0WI0WJ0X20Xi0Ya0ZX0[Z0\S0\T0\j0\k0]<0]M0]_0]`0]a0^60^70^T0_O0`70`T0`i0`j0a;0a[0bY0cD0cE0cF0cm0cn0d?0dT0dm0eB0ea0f40fE0fP0fQ0fb0fc0fd0fe0ff0g;0gX0hc0i40iE0jL0k;0kN0kY0l;0l<0lQ0lf0mT0nG0nk0o@0oA0oO0ob10010A10B10C10Y11A12G13313413E13e14414S14n15I15a16<16M16^17118318418E18V18h18i18j18k19?19T19U1:D1:S1:b1:c1;<1;M1;^1;_1<01<b1>21?>1?S1@61@Y1A21A31AA1AB1B?1Bn1CG1C\S2LF2sp2PP3ALG2bs3LFB3sp12FBS1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3LFB3sp12FB3ALO3ACV3SPR3SP12HB5Ha_st5Hl_stFS2LF2sp2PP3ALG2bs3LFB3sp12FBS1R3HIA1h2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3TOP3LFB3sp12FB3ALO3ACV3SPR3SP12h15Ehtop2HB5Ha_st5Hl_stS2LF2sp2PP3ALG2bs3LFB3sp12FBFFFS2LF2sp2PP3ALG3BUF2bs3LFB3sp13x142HxS2LF2sp2PP3ALG3BUF2bs3LFB3sp13x142HxS1R3HIA1h2LF2sp2PP3ALG2bs3TOP3LFB2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2PP3ALG2bs3TOP3LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3LFB3SPR2HB5Ha_st5Hl_stFS2LF2sp2PP3ALG2bs3LFB3sp13SP1S1R2LF2ra2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3LFB3SPR2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8FS2LF2sp2PP3ALG2bs3LFB3sp12FBS2LF2sp2PP2lo2bs3SLO3DS13LFB2HB5Ha_st5Hl_stS2LF2ra2sp2PP2lo2bs3SLO3DS13LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp3BUF2lo2bs3SLO3DS43LFB2HB5Ha_st5Hl_stS2LF2ra2sp3BUF2lo2bs3SLO3DS43LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp3ALG2lo2bs3SLO3DS23LFB2HB5Ha_st5Hl_stS2LF2ra2sp3ALG2lo2bs3SLO3DS23LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp2PP3ALG2bs3LFBFFSSS3sp1S1R2lo3LOS3ALOSS2LF2sp2PP3ALG2bs3LFBS2FB2x22HxFSS2LF2sp2PP3ALG2bs3LFB3sp12FBS2LF2sp2PP3ALG2bs3LFBS1R3HIA1h2sp3TOP3sp13SP1FS2sp3sp13SP1S2LF2sp2PP3ALG2bs3LFB3sp12FBFS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2FBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBFS1R3HIA1h2LF2sp2PP3ALG2bs3LFB3sp1S2bs2EQS2LF2sp2PP3ALG2bs3LFBSS2sp2lo3SLO3sp13SP1SSS3sp14SP1MFS1R2LF2sp2PP3ALG2bs3LFB3sp1S2LF2sp2PP3ALG2bs3LFBS1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3SPH3LFB3ALO3ACV3SPRS1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3SPH3LFB3ALO3ACV3SPRS2LF2sp2PP3ALG2lo2bs3SLO3LFBS2LF2sp2PP3ALG2bs3LFBFFS2LF2sp2PP3ALG2bs3LFB3sp12FBS2LF2sp2PP3ALG2bs3LFBS1R2sp2lo3SLO3LOSS2spS2sp3SPA3SPRS2LF2sp2PP3ALG2bs3LFBFS2LF2sp2PP3ALG2bs3LFB3sp13SP12FBS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2F02F12KbS2FBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBS2bsS2LF2sp2PP3ALG2bs3LFBS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'S2spS2LF2sp2PP3ALG2bs3LFBS2LF2sp2PP3ALG2bs3LFBFFFS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP2lo2bs3SLO3DS13LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'2HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'2HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'2HB5Ha_st5Hl_stS2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2bs3LFB3sp12FB3SP12HB5Ha_st5Hl_stS2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12FB2HB5Ha_st5Hl_stS2LF2sp3ALG1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp3ALG2lo2bs3SLO3DS23LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'2HB5Ha_st5Hl_stS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP12HB5Ha_st5Hl_stFS2LF2sp2bs3LFB3sp13SP1FS2LF2sp2lo2bs3LFBS2LF2sp2lo2bs3LFBS1R2LF2bs3LFB4EGSBFFS2LF2sp2lo2bs3SLO3LFBFS2LF2sp2bs3LFB2HB5Ha_st5Hl_stS2LF2ra2sp2bs3LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp2bs3LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R3HIA1h2LF2bs3LFB3ELO5FLIMGS2LF2sp2lo2bs3SLO3LFBFS1R2LF2bs3LFB3EHIS2LF2sp2lo2bs3LFB2HB5Ha_st5Hl_stS2LF2ra2sp2lo2bs3LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp2lo2bs3LFB3sp13SP12FB2HB5Ha_st5Hl_stFFS2LF2sp2lo2bs3LFB3sp12FB2HB5Ha_st5Hl_stFS2LF2sp2lo2bs3LFBS2LF2sp2lo2bs3SLO3LFBS1R3HIA1h2LF2bs3LFB5FLIMGS2LF2sp2lo2bs3SLO3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LF2bs3LFB5ALWF'S2LF2sp2lo2bs3LFBS2LF2bs3LFBFS2LF2sp2lo2bs3LFBFFFFS2LF2sp2lo2bs3SLO3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3LFB3sp12FB3ALO3ACV3SPR3SP14SP1M3F64S1R2LF2bs3LFB3ELOS1R2LF2bs3LFB3EHIS1R2LF2sp2PP3ALG2lo2bs3PPB4ALGB3SLO3LOS3LFB3sp12FB3ALO3ACV3SPR3SP14SP1MS2LF2sp2lo2bs3SLO3LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R2LF2bs3LFB5ALWF'S2LF2bs3LFBS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPFS2LF2sp2lo2bs3SLO3LFBS2LF2sp2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALO2HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3sp12FB3ALO3SP15FRSH'S2LF2sp2lo2bs3SLO3LFB2HB5Ha_st5Hl_stS2LF2sp2lo2bs3SLO3LFBFS2LF2bs3LFB2FBS1R3HIA1h2LF2bs3LFBS2LF2bs3LFB2FBS2LF2sp2lo2bs3LFBFFS1R2LF3slo2bs4SLOS3LFBS1R2LF2sp3slo2bs4SLOS3LFB2HB5Ha_st5Hl_stS1R2LF2ra2sp3slo2bs4SLOS3LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S1R2LF3slo2bs4SLOS3LFB3sp12FB2HB5Ha_st5Hl_stFS2LF2sp2lo2bs3LFBS1R2LF2sp2lo2bs4SLO23LFB3sp13SP1S2LF2bs3LFB3sp1S1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS2LF2sp2bs3SPH3LFB2HB5Ha_stS2LF2sp2bs3SPH3LFB2HB5Ha_stS2LF2bs3LFB3sp12HB5Ha_stS1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2sp2lo2bs3LFBS2LF2sp2lo2bs3LFBS1R2LF2bs3LFB5ALWF'S2LF2ra2sp2lo2bs3SLO3LFB2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8FS2LF2sp2lo2bs3LFBS2LF2sp2lo2bs3LFBS2LF2bs3LFB3sp12HBFFFS1R2LF2lo2bs3LOS3LFBS2LF2sp2lo2bs3SLO3LFBFS2LF2sp2lo2bs3SLO3LFB3sp13SP12FB2HB5Ha_st5Hl_stS2LF2bs3LFB3sp1S2LF2bs3LFB3sp1FS2LF2sp2lo2bs3LFB3sp13SP1S2LF2sp2bs3LFB2HBS1R2LF2bs3LFB3ELOFS2LF2sp2bs3LFB2HBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3slo2bs3TOP3LFB4HTOP2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S1R2LF2ra2sp2lo2bs3SLO3LOS3LFB3ALO2HB5Ha_st5Hl_st2s02s12s22s32s42s52s62s72s8S2LF2sp2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R3HIA1h2LF2bs3LFB5FLIMGFS2LF2bs3LFB2FBFS1R3HIA1h2LF2sp3slo2bs3TOP3LFB3sp12FB4HTOP3SP12HB5Ha_st5Hl_stS1R2LF2sp2lo2bs3SLO3LOS3SPH3LFB3ALO3ACV3sp13SP1S1R2LB2LF2bs3LFB2FB5FRSH'S2LF2sp2lo2bs3SLO3LFB". (* [comment removed for export] *)
  #[using="IMG AMS GA B1 B2 B3 B4 D1 D4 D5 AL1 AL2 PPB ALGB BUF0 SLO SLO2 SLO3 RTA0 SLOS SLOL LOS SPA TOP SPH DS1 DS2 DS4 CR1 CR2 CR4 CW1 CW2 TPV LFB UARG SM1"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Patag,(0.&40.)Papad,(0.&40.)Palen,(0.&40.)Papw,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VALG,(4.$5.(9.R6.)(4.$5.(9.R5.)(4.$5.(6.R4.)(4.$5.(6.R3.)(8.$5.))))))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VALG,+18.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VALG,VP,VEND,VBUF,Vlo,Vslo,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R1:.R19.R18.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VALG,)R17.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until apw. intros HH HPP HALG HBUF ST SS MI OPP OALG OBUF. unfold A_ASN1_GET_ALG_NULL. unfold A_UAR_GOT in UARG. unfold A_SMALLOC_1 in SM1.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
    ddestruct IMG' as (EGOT & ELO & EHI & EGSB).
    (* [comment removed for export] *)
    zstep. carve_frame 96%nat ST.
    do 11 zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    align32 (bv_unsigned sp + -96) sp1.
    assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (clear - Hsp1 SPA SPR; subst sp1; lia).
    assert (SP1M : sp1 mod 32 = 0) by (clear - Hsp1 SPR; subst sp1; lia).
    clear Hsp1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
        destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
        pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
      end end.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    clear GOT GSB UGOT UFLAG AB FLIMG.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
    replace (Z_to_bv 64 340076 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96);
                [ exact HHc | exact LFB | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
                | exact LOS | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SLO3 SP1; lia
                | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SP1 TOP; lia
                | assumption | exact TPV | reflexivity ])
    end.
    clear ST1.
    lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
    clear HH.
    presA_transport HP1. clear HP1.
    lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
      destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    ddestruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 1)) with 16%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 1)) with 128%nat in FRM by reflexivity.
      replace (64 * 2 ^ 1) with 128 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; ddestruct FRSH as (F0 & F1 & _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [24; 8; 24; 40; 32]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat FD FRM3. chunk_split FRM3 1%nat RZ G2. clear G2.
      replace (FB + 24 + 8) with (FB + 32) in FD, RZ by (clear; lia). replace (FB + 32 + 24) with (FB + 56) in RZ by (clear; lia).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -80); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -80) (sp1 + 8) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell). rename SLOT0 into SLOT.
      (* [comment removed for export] *)
      assert (INF : In (FB, 128) ((FB, 128) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 128 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 88) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 128 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo ALG 24 FB 128 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 128 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      pose proof (hm_abase asegs R HIA h1 LB _ m4 ltac:(eassumption)) as AB3.
      eapply body_walk with (FB := FB) (spv := sp1) (s2v := FB) (sp1 := sp1) (sh2 := sp1) (LF' := (FB, 128) :: LF) (h1 := h1) (m0 := m).
      all: bw_side.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_asn1_get_alg_null_spec : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.+1.)$23.)P,(1>.$1?.(24.R5.)$25.)P,(1>.$1?.(26.R6.)$27.)P,Pm,P,(0.&40.)(28.(0.&8.))P,(29.R8.R1.)(2:.R2.)P,(2;.=(2<.R8.))(2=.$2.R9.R8.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM1 AMS MSI RTC NEED0.
  pose proof (A_asn1_get_alg_spec R HIA IMG MSI RTC NEED0) as GA.
  unfold asn1_get_alg_null_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
