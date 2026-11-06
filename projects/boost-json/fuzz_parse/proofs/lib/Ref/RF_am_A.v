(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstatehc6region37Corelib4Init5Logicmc3and01N46Stdlib6ZArith6BinInt1Zo92leo92ltmc2eqmc2exmc2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~ra4RCTXo93add25stdpp9countablehg8bN_countable35stdpp7numbers1Nhi86eq_dec37Corelib4Init9Datatypeshk34Somehk36optionmc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hn35lr_lohc7RKGrouphc6r_basehc6r_kindhc5r_lenhc5rkindhcbround_up_pghc9s_regions25stdpp4baseig46lookup25stdpp4gmapiha4gmapihabgmap_lookup89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref7RF_am_A3HCW~~~~~~ijd6ram_fp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~io99ralloc_fp04Npos35stdpp9bitvectorbdefinitionsite7Z_to_bvitebbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jh55hceilrabrregions_wfhc4concite2bvhn39meta_slotra5rmrephc4aptrhc4area35stdpp7numbers1Zjp76eq_dechg8bZ_countablehg8eprod_countable25stdpp9decidablejt3bprod_eq_dechc7s_areasmc3iff3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskg3dmachine_state3h5LinuxProcessSemantics5Riscv7Preludekkb5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~kna5rsegshk34None79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ks73mkRks73stkks75wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lha2MSlha6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~lm77mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lqc7seg_romio9crpres_excepthk34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mge4cellhk34consmge2C8hk33nilhn32wz69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~mmd7hcanarymge2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocModel_B~~~~~~mrb9clr_links79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~nge3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nl08rw_cellsijd9ram_frameijdcram_ret_postraaRSSP_GUARDhc8upd_metao93sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_A~~~~~~nt27am_tookra6RMLOCKo93pow" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition ram_fp : ltac2:(zQ "20!h9!la>2st$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "hc0!m3!o0!o6!h9!q1!q6!qb!r0!r5!vb!hg2!hh9!hj9!hlb!hm3!hmd!hr5!hre!la!hs8!ht1!hta!hu2!hua!hv8!ih0!ii6!iie\2st$h2\2lo$3\2sp$3\1a$3@2$8@2$1@2$4^3^1@2$5^1^2@2$8@2$1@2$4$9^1@2$5^1@2$a$9+jq0@2$7$2\3rid$2@2$7$0\1r$0@2$1@3$6@1$e$0@6$h9$2$0@4$ha$2$c$b$0@4$hb$2$c$b$0^2@1$h8^6@2$d$0^1@2$1@1$f@3$6$h6@1$h4^1$h1@2$1@2$4@1$h0^1^3@2$5^3@2$a@1$h3^1@1$h7@1$h5^1").

Lemma ram_fp_alloc_fp : ltac2:(zQ "80!h9!hu2!qb!hmd!inf!isb!hre!la>2st$7>2lo$0>2sp$0>1a$0>0@4$4^4^3^2^1@5$5\1k$1@1$3@3$2$1^1$6^5^4^3^2").
Proof. intros st lo sp a. try hcb. try hsb. unfold ram_fp, ralloc_fp. tauto. Qed.
Lemma ram_fp_stack : ltac2:(zQ "60!h9!o0!inf!la!q1!q6>2st$3>2lo$0>2sp$0>1a$0>0@2$1@2$4^3^1@2$5^1^2@4$2^5^4^3^2").
Proof. intros st lo sp a. try hcb. try hsb. intros; left; assumption. Qed.
Lemma ram_fp_ctx : ltac2:(zQ "80!h9!vb!o0!inf!la!hg2!q1!q6>2st$4>2lo$0>2sp$0>1a$0>0@2$2@2$6$1^1@2$7^1@2$5$1+jq0@4$3^5^4^3^2").
Proof. intros st lo sp a. try hcb. try hsb. intros; right; left; assumption. Qed.
Lemma ram_fp_region : ltac2:(zQ "ha0!m3!o6!h9!qb!hh9!hj9!hlb!hm3!o0!hmd!hr5!inf!hre!la!hs8!ht1!hta!hu2!hua!hv8!hg2!q1!q6!ih0!ii6!iie>2st$d>2lo$2>2sp$2>1a$2>3rid$1>1r$0>0@3$3@1$7$0@6$h7$1$0@4$h8$1$5$4$0@4$h9$1$5$4$0^2@1$h3^6@2$6$0^1>0@1$9@3$3$h1@1$f^2$c>0@2$8@2$h5@1$a^3^5@2$h6^5@2$h4@1$e^3@1$h2@1$h0^3@4$b^9^8^7^6").
Proof. intros st lo sp a rid r. try hcb. try hsb. intros; right; right. exists rid, r. auto. Qed.
Lemma ram_fp_not_errno : ltac2:(zQ "d2!it8!h9!hg2!q1!ivb!jg6!o0!hmd!jl0!inf!jl9!la!q6&@2$5@1$0#k0@2$4@1$0#k0+hgrmr8&@2$2~0-q4>2st$b>2lo$1>2sp$1>1a$1>0@4$9^4^3^2^1>0@2$a?5HCEIL^5>0@2$3@1$8?5HCEIL^5@1$7@2$6@2$3~1^4@2$c^4@2$2~1+4").
Proof. intros st lo sp a. try hcb. try hsb.
  (intros [H|[H|(rid & r & Hr & _ & H)]] nd_i1 LO; ndestruct nd_i1 as (_ & WR & _)); hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; rewrite ?unsigned_lit by lia; try lia.
  destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
  pose proof (lr_lo_ge r). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RBC. lia.
Qed.
Lemma ram_fp_meta : ltac2:(zQ "e0!h9!it8!jm7!jme!hm3!o0!jn4!inf!jo1!jo9!la!hg2!q1!q6>2st$a>1m>0@1$3@1$1#k0@1$4@1$3@1$1#8>2lo$0>2sp$0>1q$9>1a$0>0@4$8?5HCEIL?4HSEC^6^5>0@2$6^7^3>0@2$5@2$c@2$2^8^4^3@2$d^3@2$b@2$2^8^4+i8@4$7^9^7^6^4").
Proof. try hcb. try hsb.
  (intros st m lo sp q a MR nd_i2 Ha; ndestruct nd_i2 as (ar & arr & k & Har & Hk & Eq)). pose proof MR as (WF & _).
  ndestruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
(* [comment removed for export] *)
Lemma ram_fp_area : ltac2:(zQ "hb0!h9!jp0!o6!jo9!hj9!jq8!hm3!it8!jm7!jme!hh9!jr2!js1!ju4!hlb!o0!qb!inf!jo1!la!jv3!hg2!q1!q6!ih0!ii6!iie>2st$h3>1m>0@1$9@1$7#k0@1$6@1$9@1$7#8>2lo$0>2sp$0>2ak$3>2ar$1>1a$0>0@4$h2?5HCEIL?4HSEC^7^6>0@3$h0@1$6$1@6$h8$3$1@4$h9$3@4$d$2$4$0$5@6$c$2$4$a$0$5$b$1@4$ha$3@4$d$2$4$0$5@6$c$2$4$a$0$5$b$1^4@1$h4^8@2$e$1^3>0@2$f@2$h6@2$8^9^5^3@2$h7^3@2$h5@2$8^9^5+hgg0@4$h1^a^8^7^4").
Proof. try hcb. try hsb.
  intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
  ndestruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
  eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma ram_fp_same : ltac2:(zQ "b0!h9!inf!la!hv8!qb!jvd!o6!m3!hh9!ii6!hj9>2st$2>3st'$2>2lo$0>2sp$0>1a$0>0@3$4@4$9$6$a$8$7@1$3^4@1$3^5@2$5@4$1^5^4^3^2@4$1^6^4^3^2").
Proof. intros st st' lo sp a. try hcb. try hsb. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

(* [comment removed for export] *)
Definition ram_ret_post : ltac2:(zQ "70!it8!jme!la!hm3!h9!kja!kn1>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2lo$4>3stF$2>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>3st'$2>2rv@1$1@1$0#k0>0$5P") := ltac2:(zQ "h71!it8!jme!r0!o0!kr6!hm3!kja!la!jg6!krf!qb!h9!kn1!lg3!lga!lh1!ll7!lld!lq1!lub!inf!jo1!lv6&>0@1$1@1$0#k0@1$5@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$c@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2lo$b\3stF$7\1m~0\3st'$7\2rv@1$1@1$0#k0\3ms'$6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$3@3$a$6^h0@7$h0@hf$d^i7^i6^i5^i4^f^e^d^i3^i2^h1^c^b^a^9^8^7^6^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^5^4^3^2^h7@1$h1^i7^h6@1$9@1$1@1$0#k0^1@1$h3$4@2$3@3$h6@3$h4^h4^h5@2$8@1$0#k0^i6^h3^1@2$3@3$f$4^h3^1@2$3@2$h2$4^1@2$3@4$e$4^1^h5@2$8@1$0#k0^i6@4$h5?5HCEIL?4HSEC^h2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_frame : ltac2:(zQ "40!it8!jme!mg6!mka>4junk@1$2@1$1@1$0#8>2s4@1$1@1$0#k0>2s3@1$1@1$0#k0>2s2@1$1@1$0#k0>2s1@1$1@1$0#k0>2s0@1$1@1$0#k0>2ra@1$1@1$0#k0@1$2$3") := ltac2:(zQ "a0!mka!ml2!it8!mla!jme!mg6!mm0!mm7!mqa!mr5\4junk@1$5@1$4@1$2#8\2s4@1$4@1$2#k0\2s3@1$4@1$2#k0\2s2@1$4@1$2#k0\2s1@1$4@1$2#k0\2s0@1$4@1$2#k0\2ra@1$4@1$2#k0@3$1$0@2$9N8^7@3$1$0@1$3@1$7@1$8?4HSEC@3$1$0@1$3^6@3$1$0@1$3^5@3$1$0@1$3^4@3$1$0@1$3^3@3$1$0@1$3^2@3$1$0@1$3^1@1$6$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_tail : ltac2:(zQ "hf0!it8!jme!kr6!ivb!jg6!hg2!jm7!q1!krf!mg6!hm3!h9!kn1!ng1!jn4!jl0!nk9!lg3!lga!ll7!lq1!lub!nob!np7!nq4!nr4!jo1!jo9!la!ns1!nsc>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>2x1@1$1@1$0#k0>3raw@1$1@1$0#k0>3s0o@1$1@1$0#k0>3s1o@1$1@1$0#k0>3s2o@1$1@1$0#k0>3s3o@1$1@1$0#k0>3s4o@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$a@1$1@1$0#8>4junk@1$9@1$1@1$0#8>2lo$b>2st$hc>1q$hb>0@4$ha?5HCEIL?4HSEC^2^5>0@2$h4$2^6>0@2$e^4^3>0@4$h6$2^8@2$5@2$4@1$0#k0^id-k0@7$h7^7^b^c^d^e^f^h0>0@4$h2$2^9^7@2$5@2$4@1$0#k0^ie-k0>0@2$7@1$f?5HCEIL^8>0@2$7^9@2$he@2$4@1$0#k0^j0+k0@3$h0$2@h7$h8^h4^j1^j0^if^h3^h2^h1^h0^f^i0^hf^he^hd^hc^hb^ha^e^d^a^9^c@3$hd^8$d^9@2$3@1$0#k0@2$6^9^8@7$h3@hf$h1^h5@2$3@1$0#k0@2$5@2$4@1$0#k0^j1-k0^j0^if^ie^id^ic^ib^ia@2$3@1$0#k0@2$6^9^8^i9^i8^i7^i6^i5^i4^i3@2$3@1$0#k0$h9^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^e@2$3@1$0#k0+ttjm8^d@1$8@1$1@1$0#k0^c@1$h5$2").
Proof. try hcb. try hsb.
  intros until q. intros MR MI MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  npose MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
  rmeta_chunk MR MSq CH.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RSSP_GUARD, ram_frame in *.
  rmeta_open (conc st q) MUq WMq.
  (* [comment removed for export] *)
  st1. st1.
  rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
  rewrite <- upd_meta_put in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta q clr_links st) mX)
      by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply ram_fp_stack. lia.
      - intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
  apply evt_done. unfold ram_ret_post. neexists 15.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_b0 : ltac2:(zQ "i20!it8!jme!ivb!kr6!jg6!hg2!q1!h9!jm7!krf!mg6!hm3!o0!kn1!oh1!jn4!jl0!nk9!lg3!lga!ll7!lq1!lub!nob!np7!nq4!ohc!nr4!jo1!jo9!la!q6!oi5!nsc>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>2x1@1$1@1$0#k0>3raw@1$1@1$0#k0>3s0o@1$1@1$0#k0>3s1o@1$1@1$0#k0>3s2o@1$1@1$0#k0>3s3o@1$1@1$0#k0>3s4o@1$1@1$0#k0>1F@2$d@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>4junk@1$a@1$1@1$0#8>2lo$7>3cnt$7>2st$he>1q$hd>0@4$hc?5HCEIL?4HSEC^2^6>0@2$h5$3^7>0@2$f^4^3>0@2$c@2$6Z^6@2$hf^6@2$i0+2+k0>0@4$h7$3^a@2$5@2$4@1$0#k0^id-k0@7$h8^9^d^e^f^h0^h1^h2>0@4$h3$3^b^9@2$5@2$4@1$0#k0^ie-k0>0@2$6@1$h0?5HCEIL^a>0@2$6^b@2$i1@2$4@1$0#k0^j0+k0@3$h1$3@h7$h9^h6^j1^j0^if^h5^h4^h3^h2^h1^i2^i1^i0^hf^he^hd^hc^h0^f^c^a^e@3$e^a^9^b@2$2@1$0#k0@2$8^a^9@7$h4@hf$h2^h7@2$2@1$0#k0@2$5@2$4@1$0#k0^j1-k0^j0^if^ie^id^ic^ib^ia@2$2@1$0#k0@2$8^a^9@2$2@1$0#k0^b^i9^i8^i7^i6^i5^i4@2$2@1$0#k0$hb@2$2@1$0#k0$ha^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h0@2$2@1$0#k0+ttjlc^f@1$9@1$1@1$0#k0^e@1$h6$3").
Proof. try hcb. try hsb.
  intros until q. intros MR MI MSq HC FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  npose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RCTX, RMLOCK in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
  { eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
      rewrite (conc_aadd st q META_SIZE) by (ndestruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
          ndestruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
      unfold META_SIZE, wz. exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
  clear MUc WMc C1.
  change (conc st q) with (conc st1 q).
  eapply evt_mono.
  { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
      [exact MR1 | assumption | exact MSq | exact FR | exact ST | hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia | lia]. }
  intros ms' RP. unfold ram_ret_post in RP |- *.
  ndestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
  neexists 15. split; [reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|exact I]].
      + intros x Hx. apply ram_fp_stack. lia.
      + intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

End HCW.

