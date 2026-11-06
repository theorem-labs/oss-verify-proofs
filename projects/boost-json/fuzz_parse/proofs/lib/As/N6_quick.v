(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst N6_tac N6_rip.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~02sh46Stdlib6ZArith6BinInt1Zk23addk23div37Corelib4Init5Logicm63and37Corelib7Numbers7BinNumso01Zk23subk22lem62eqk23mulm62or07hull_hi07hull_lok22lto04Npos35stdpp9bitvectorbdefinitionst62bv37Corelib4Init9Datatypesv83nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hh64cellv84consv86lengthv84listv83nilv86option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ho05asegshh62CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hsa8rw_cellsv84Some37Corelib5Lists7ListDefih83nth3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsij6dov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ine2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ire2b8k26of_natk26to_natm62ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jh63stkk23powhh62C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsConst~~~~~~jm56ACONST03memhh62C8t67Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~js15u8arr" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma hull_words : ltac2:(zQ "d3!je!la!m0!na!p9!pd!q3!q8!qd!r3!r8!s1!sa&@2$2@1$0@2$5@2$1^4^3+1+8&@2$8+8~0&@2$1~1+8>1d$4>1k$4>0@2$6Z^2>0@2$3@2$6+1^2@2$6^2+k0@2$3@3$7$4@1$0@1$b^4@2$8+8@2$2@1$0^4+8@2$3@3$7$4@1$0@1$a@2$1^4^3~2@2$3@2$9@3$7$4~0@2$2@1$0^4+8@3$7$4~0@2$1@2$2@1$0^4+8+1@2$3@2$6@2$8+8@2$2@1$0^4+8@1$0^4@2$3@2$6@1$0^4@1$0@2$5@2$1^4^3+1@2$c@1$0@2$5@2$1^4^3+1~2").
Proof.
  intros d k Hd Hk. unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val.
  repeat split; Z.div_mod_to_equations; nia.
Qed.

Lemma rw_cells_CB_length : ltac2:(zQ "e0!sf!v3!hh0!hl2!hla!hm1!hma!hn1!hn7!q8!p9!hrb!hs4!ig5>2mm>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$a>1k$2>2bs@1$6@1$1@1$0#8>0@4$d$b^4^3@3$4$3@2$c^2^1@1$7$3@3$9$2@2$5@1$1@1$0#8^2^3").
Proof. intros mm A k bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Section QRead.
  Variables (mm : word -> option byte) (q1 : Z) (qj : list byte).
  Hypothesis QA : ltac2:(zQ "30!hrb!jvb!qd@4$1$0?2mm@2$2+8?2q1?2qj").
  Lemma q_read : ltac2:(zQ "h70!sf!v3!qd!hma!ih1!hla!hm1!hn1!hn7!na!q8!iif!p9!imd!hrb!ir8!iv9!la!q3!sa!ivf!pd!jg8>1x$c>0@2$9@2$h2@2$2+8?2q1^1@2$h3^1@2$h1@2$2+8?2q1@1$h4@2$6@1$1@1$0#8?2qj@3$a@1$8@1$3@1$1@1$0#8@4$d$e?2mm@1$f^2N1@2$4@1$3@1$1@1$0#8@3$5@1$1@1$0#8@4$b@1$1@1$0#8@1$h6@2$h5^2@2$2+8?2q1?2qj@1$h0Z@1$7@1$1@1$0#8").
  Proof.
    intros x Hx. eapply (u8arr_read asegs mm (8 * q1) qj (x - 8 * q1)); [exact QA | | lia | f_equal; lia].
    apply nth_error_nth'. lia.
  Qed.
End QRead.

(* [comment removed for export] *)
Lemma hull_chunk : ltac2:(zQ "hc1!je!la!sf!v3!m0!na!q8!p9!hm1!q3!qd!pd!hma!hh0!hrb!hl2!hla!hn1!hn7!jh1!r3!r8!s1!hs4!jl2!ig5!ivf!jl9&@2$4@1$0@2$b@2$1^7^6+1+8>2mm>0@1$3@1$2#k0@1$h2@1$3@1$2#8>1d$7>1k$7>0@2$9Z^2>0@2$5@2$9+1^2@2$9^2+k0>0@2$9@2$1@2$1^4^3+8@2$hb+2+if>0@4$h8$e^6@1$0@1$h6^5@1$0@1$h5@2$1^5^4@2$h3@1$c@1$3@1$2#8\2qj@1$c@1$3@1$2#8@2$5@4$h9$e^8@2$a+8@2$4@1$0^7+8@3$h0$f@2$h7@2$8@1$3@1$2#8^1^1@1$h1$f@2$5@3$6$7@2$1@2$a+8~0+8@2$1@2$a+8@2$4@1$0^7+8@1$ha@2$8@1$3@1$2#8^1@2$h4@2$5@3$6$7~0@2$4@1$0^7+8@3$6$d@2$8@1$3@1$2#8^1N8@2$5@3$6$7~0@2$1@2$4@1$0^7+8+1@3$6$d@2$8@1$3@1$2#8^1Nh0").
Proof.
  intros mm d k Hd Hk Htop SV.
  ndestruct (hull_words d k Hd Hk) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3). rewrite HLO, HHI in SV.
  pose proof (sh_range_app d ltac:(unfold AAPP_HI; lia)) as SR1. rewrite ASHADOW_BASE_val in SR1.
  destruct HQ2 as [E|E]; rewrite E in SV |- *.
  - destruct (stk_carve asegs mm _ _ 8 SV ltac:(lia)) as [_ [qj QW]].
    replace (8 * (sh d / 8) + 8 - Z.of_nat 8) with (8 * (sh d / 8)) in QW by lia.
    pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| left; split; reflexivity].
  - destruct (stk_carve asegs mm _ _ 16 SV ltac:(lia)) as [_ [qj QW]].
    replace (8 * (sh d / 8 + 1) + 8 - Z.of_nat 16) with (8 * (sh d / 8)) in QW by lia.
    pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| right; split; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ACONST_layout_flag : ltac2:(zQ "d0!hl2!hla!hn1!hrb!jlf!ig5!iv9!na!sf!jq2!jqc!jr1!jr7>2mm$a>0@1$9^1@2$7@4$5$3^2+hrmhg0@3$1$0@1$b@2$c@1$8#k0+hsgvh9@1$2$0@4$5$3^2+hsgvh8@3$1$0@1$4@1$6+1@3$1$0@1$4@1$6+1@1$2$0").
Proof.
  intros mm ACx.
  change 1794304 with AGOT_RINTRIN. change 1838873 with ARINTRIN_CELL. change 1838872 with AINITED_CELL.
  split; (eapply ACONST_cell; [exact ACx|]; cbn; clear; tauto).
Qed.
