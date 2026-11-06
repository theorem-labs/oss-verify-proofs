(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Plain.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require E_As0ui.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Spec LibIface V_World V_Img0 U_Img V_Co10c V_Paq9r V_Li4zm U_Liw9k DU_T0kc E_As0ui.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.ShapeEF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Li4zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_Liw9k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_T0kc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_WSuvw V_VEz1x.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VEz1x.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VEzrv V_Parse V_vefn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_vek4w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_vek4w V_vezwa.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH_BOM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd V_PHnsa.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH4jn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PHpon.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH0sd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH4jn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_PH3d1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_Cov8m U_Pahif U_WS6ei U_VExcu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_WS6ei.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_VEjd9 U_Parse U_ve3w7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_ve2lq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_veqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_veqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_veqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_veqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHhwf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHhwf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHhwf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe9v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe9v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PH010 U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe9v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHgal.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe2z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHe9v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require U_PHhwf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0 LayoutPU DriverKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require DrvImzd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require DrvImzd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DriverKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DrvImzd.Allo10x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.DrvImzd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require DrvIp11.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require DrvIp11.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.DrvIp11.Allof7f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.DrvIp11.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Local Open Scope Z_scope.

Section Top.
  (* [comment removed for export] *)
  Context {Clg : Ceiling}.

  Let MC0 := V_vefn7.vep_mark_common_ok.
  Let ER0 := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt.vep_error_ok.
  Let MCU := U_ve3w7.vep_mark_common_ok.
  Let ERU := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_vermr.vep_error_ok.

  (* [comment removed for export] *)
  Definition P0_handlers (st : vstate) : st <> S_MatchBuf -> V_Paq9r.handler_stmt st :=
    match st as s return (s <> S_MatchBuf -> V_Paq9r.handler_stmt s) with
    | S_Start => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PH88s.PH_Start
    | S_BOM => fun _ => V_PH_BOM.PH_BOM MC0
    | S_TestXml => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PH2vn.PH_TestXml MC0
    | S_NotXml => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHlrw.PH_NotXml MC0
    | S_NotMyTag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PH1oh.PH_NotMyTag MC0
    | S_NxtTag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PH968.PH_NxtTag MC0
    | S_StartTag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHd1p.PH_StartTag
    | S_Comment => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PH6ek.PH_Comment
    | S_CommentESI => fun _ => V_PH3d1.PH_CommentESI MC0
    | S_CDATA => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHham.PH_CDATA
    | S_end_ESITag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHayj.PH_end_ESITag
    | S_ESITag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHc39.PH_ESITag MC0
    | S_ESI_Include => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHtv2.PH_ESI_Include ER0
    | S_ESI_Remove => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHoxm.PH_ESI_Remove
    | S_ESI_Comment => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PH9xg.PH_ESI_Comment ER0
    | S_ESI_Bogon => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHbir.PH_ESI_Bogon ER0
    | S_InTag => fun _ => V_PH0sd.PH_InTag MC0 ER0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_veyvr.vep_do_comment_ok OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_vec2f.vep_do_remove_ok V_vek4w.vep_do_include_tag_ok
    | S_TagError => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH4jn.V_PHhx7.PH_TagError MC0
    | S_Attr => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHg4q.PH_Attr
    | S_SkipAttribute => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHo3d.PH_SkipAttribute ER0
    | S_AttrGetValue => fun _ => V_PHpon.PH_AttrGetValue
    | S_AttrDelim => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH0sd.V_PHgbh.PH_AttrDelim ER0
    | S_AttrValue => fun _ => V_PH4jn.PH_AttrValue ER0 V_vezwa.vep_do_include_attr_ok
    | S_Until => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHkde.PH_Until MC0
    | S_Match => fun _ => V_PHnsa.PH_Match
    | S_MatchBuf => fun NE => False_ind _ (NE eq_refl)
    end.

  Definition PU_handlers (st : vstate) : st <> S_MatchBuf -> U_Pahif.handler_stmt st :=
    match st as s return (s <> S_MatchBuf -> U_Pahif.handler_stmt s) with
    | S_Start => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PH010.U_PHrp1.PH_Start
    | S_BOM => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PH010.U_PH_BOM.PH_BOM MCU
    | S_TestXml => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHhwf.U_PHsv3.PH_TestXml MCU
    | S_NotXml => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PH010.U_PHyeb.PH_NotXml MCU
    | S_NotMyTag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PH010.U_PHxiy.PH_NotMyTag MCU
    | S_NxtTag => fun _ => U_PHhwf.PH_NxtTag MCU
    | S_StartTag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHhwf.U_PHyo4.PH_StartTag
    | S_Comment => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHwzj.PH_Comment
    | S_CommentESI => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe9v.U_PHtsh.PH_CommentESI ERU MCU
    | S_CDATA => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHj88.PH_CDATA
    | S_end_ESITag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PH010.U_PH1yj.PH_end_ESITag
    | S_ESITag => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe9v.U_PH9sb.PH_ESITag MCU
    | S_ESI_Include => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHej2.PH_ESI_Include ERU
    | S_ESI_Remove => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHnex.PH_ESI_Remove
    | S_ESI_Comment => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHow2.PH_ESI_Comment ERU
    | S_ESI_Bogon => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHjur.PH_ESI_Bogon ERU
    | S_InTag => fun _ => U_PH010.PH_InTag MCU ERU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_veqq1.U_ver8l.vep_do_comment_ok OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_veqq1.U_ve4oy.vep_do_remove_ok U_veqq1.vep_do_include_tag_ok
    | S_TagError => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe9v.U_PHxdz.PH_TagError MCU
    | S_Attr => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHy8z.PH_Attr
    | S_SkipAttribute => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHaq6.PH_SkipAttribute ERU
    | S_AttrGetValue => fun _ => U_PHgal.PH_AttrGetValue
    | S_AttrDelim => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHe2z.U_PHbhj.PH_AttrDelim ERU
    | S_AttrValue => fun _ => U_PHe9v.PH_AttrValue ERU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_veqq1.U_verfs.vep_do_include_attr_ok
    | S_Until => fun _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_PHhwf.U_PHlv2.PH_Until MCU
    | S_Match => fun _ => U_PHe2z.PH_Match
    | S_MatchBuf => fun NE => False_ind _ (NE eq_refl)
    end.

  (* [comment removed for export] *)
  Definition LIB0 : lib_call_ok E_As0ui.LL0 :=
    V_Li4zm.lib_call_ok0
      V_WSuvw.WS_Init_ok V_VEz1x.VEP_Init_ok
      (V_Parse.VEP_Parse_ok MC0 P0_handlers)
      (V_VEzrv.VEP_Finish_ok MC0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.V_verwm.vep_emit_common_ok)
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VEz1x.V_WSitf.WS_Rollback_ok.

  (* [comment removed for export] *)
  Definition LIBU : lib_call_ok (DU_T0kc.LLU IMGU_LO IMGU_HI img_okU img_okU_intro) :=
    U_Liw9k.lib_call_okU
      U_WS6ei.WS_Init_ok U_VExcu.VEP_Init_ok
      (U_Parse.VEP_Parse_ok MCU PU_handlers)
      (U_VEjd9.VEP_Finish_ok U_ve3w7.vep_mark_common_ok OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_veyab.vep_emit_common_ok OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_ve2lq.U_vermr.vep_error_ok)
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.U_WS6ei.U_WSwbl.WS_Rollback_ok.

End Top.

Lemma HlimgU : 0x10000 <= IMGU_LO /\ IMGU_HI <= 0x319f8.
Proof. unfold IMGU_LO, IMGU_HI. lia. Qed.

(* [comment removed for export] *)
Theorem strong_universal_error_free_esi_parse_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact (strong_universal_error_free_T_scfg_budgets_of_scfg _ _ _
          (@E_As0ui.ubsan_base
             (fun Clg => @AllocP0 Clg) (fun Clg => @DriverP0 Clg)
             (fun Clg => @AllocPU Clg) (fun Clg => @DriverPU Clg)
             (fun Clg => @LIB0 Clg)
             IMGU_LO IMGU_HI HlimgU img_okU img_okU_intro
             (fun Clg => @LIBU Clg))).
Qed.
