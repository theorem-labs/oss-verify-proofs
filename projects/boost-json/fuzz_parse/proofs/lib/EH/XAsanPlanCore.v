(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAxSymExec3B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC8WithSegs~~~~~~hc5mkind37Corelib4Init9Datatypesn44booln45falsen44truen44listhc3acs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~qf6kentryhc4a_ssqf6s_knowqf4s_pcqf4expr3h5LinuxProcessSemantics5Riscv5Instrhhb7ALU_ADDqf5mkAluhhb5M_MULqf4ELitqf4mkMdn43natqf5saddrhccexpr_vars_ltqf6a_basen44andbhcdsaddr_vars_ltqf8expr_eqbqf9saddr_eqb46Stdlib6ZArith6BinInt1Zhrd3eqb46Stdlib5Arith8PeanoNat3Nathtc3eqbqferanges_apart_xhrd3lebhrd3subqf5two64htc3lebhrd3ltbhrd6of_nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B~~~~~~ijd4bctxijdfranges_apart_xB37Corelib4Init5Logicipf2eqhcekentry_apart_bhcfkentry_apart_bBijd4mkbcqf5sprepqferanges_apart_pijdfranges_apart_pBhcfkentry_apart_bphch0kentry_apart_bpBn43orbhc6kimg_bqf8mk_sprep36Stdlib5Lists4Listjl06filterijd5bc_fkijd9mk_sprepBhc9kn_unfillhcakn_unfillBn43niln44conshc5kwr_bqf9kfill_cutqf8kunk_cutqf9kzero_cutijdakfill_cutBijd9kunk_cutBijdakzero_cutBhc6havoc1hc7havoc1Bhc7havoc1phc8havoc1pBjl08flat_maphc8kn_havochc9kn_havocBhc9kn_havocMqf3KWrqf4kcutijd5kcutBhc7kwr_cuthc8kwr_cutBhc7cutout1hc8cutout1Bhc8cutout1phc9cutout1pBhc9kn_cutouthcakn_cutoutB89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~ks46img_hiks46img_lon46optionn44Noneqf8sidecondhhb5aluophhb5mulopqf4lresn44Someqfbknow_lookuphrd6moduloijdcknow_lookupBhc6kreadZhc7kreadZBhc7kread8ehc8kread8eBhc9kwritablehcakwritableBhcbkwritable_xhcckwritable_xBhc7kzero_xhc8kzero_xBhc7kfill_xhc8kfill_xBhcboff_image_xhccoff_image_xBn44prodhrd3addqfabase_rangeqf3xhiqf3xloijdbbase_rangeBijd4xhiBijd4xloBhc6flat_xhc7flat_xBn44pairqf7lin_ge0ijd8lin_ge0Bhc7len_eqbhc8len_eqbBqf6ealignijd7ealignBhccpage_alignedhcdpage_alignedBqfalin_brangeqf6erangeqfalin_srangehrd3maxqf6zlit64ijdblin_brangeBijd7erangeBijdblin_srangeBhc4xlo1hc5xlo1Bhrd3minhc4xhi1hc5xhi1Bhc3xb2hc4xb2Bhc4xlo2hc5xlo2Bhc4xhi2hc5xhi2Bhcbkread_byteshcckread_bytesBhc4amaphcffind_containinghch0find_containingBhc9shadow_ofhcashadow_ofBhccshadow_factshcdshadow_factsBhcbinside_mapshccinside_mapsBks44CEILhcasafe_rangehcbsafe_rangeBhccgrant_keep_bhcdgrant_keep_bBhc9kimg_cliphcfkn_grant_filterhch0kn_grant_filterBhc9kn_rezerohcakn_rezeroBhcaamap_matchhcbamap_matchBhcacopy_factshcbcopy_factsBjl07existsbhc7img_covhc8img_covBhc6escaleqf4EVarhc4V_S1hc4V_S2hc4eaddhc6V_ARGChc5e_sp0hc6V_ENVChc6e_envp04Npos35stdpp9bitvectorbdefinitionspm12bvhhb4ffmthhb5instrhhb6awidthhhb5csrophhb7fcvt_tyhhb5msizeqf6s_regsqf6sr_getn43fsthhb5amoophhbbbranch_condhhb6fariophhb6fcmpophhb5fmaophhb9fminmaxophhb6fmvdirhhb6fsgnophc2pcqfacond_probeqfbitab_lookupks46e_auxvqf9split_litks46e_auxbn43sndqf5KWordqf2SAhrd3mul3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeqo47Segmentqf4itabks46atable" s.
Import ListNotations.
Open Scope Z_scope.

Module APC.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

Section WithSegs.
Variable segs : ltac2:(zQ "20!q2!qr9@1$0$1").
Variable IT : ltac2:(zQ "10!qs4$0").
Variable A : ltac2:(zQ "10!qsb$0").
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb : ltac2:(zQ "20!mc!oc>1a$0>1b$0$1") := ltac2:(zQ "40!p3!mc!oc!pb\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$3").

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind : ltac2:(zQ "20!oc!mc>1k$1$0") := ltac2:(zQ "40!p3!mc!pb!oc\1k$1M1\1k$1$3^1$0$0$0$0$2$2").
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool               (* [comment removed for export] *)
}.

Definition kn : ltac2:(zQ "30!q2!q9!v4>2cs$1@1$0$2") := ltac2:(zQ "30!vd!q9!hg4\2cs$1@1$2@1$0^1").
Definition pc : ltac2:(zQ "20!h9!q9>2cs$1$0") := ltac2:(zQ "30!vd!q9!hgd\2cs$1@1$2@1$0^1").



(* [comment removed for export] *)
Definition eadd : ltac2:(zQ "10!hh4>1a$0>1b$0$0") := ltac2:(zQ "30!hh4!hjf!hka\1a$0\1b$0@3$2$1^2^1").
Definition escale : ltac2:(zQ "20!hh4!h9>1c$1>1e$0$0") := ltac2:(zQ "50!h9!hl2!hlb!hh4!hm2\1c$0\1e$3@3$4$1@1$2^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt : ltac2:(zQ "30!oc!hm9!hmf>1b$1>1a$2$0") := ltac2:(zQ "40!hm9!hn7!ho6!hmf\1b$0\1a$3@2$1^2@1$2^1").

(* [comment removed for export] *)
Definition kentry_vars_lt : ltac2:(zQ "30!oc!hm9!v4>1b$1>1K$2$0") := ltac2:(zQ "a2!hn7!hh4!hof!hp6!hmf!h9!hm9!v4!oc!pb&\1n$1@2$2@2$3^4^2@2$0^4^1&\1a$4~0\1b$6\1K$7M7\1K$7$8^1\1a$4\1w$6\1v$1@2$2@2$3^5^3@2$0^5^1~1\1a$4\1n$1\1k$6@2$2@2$3^5^3@2$0^5^2\2lo$5\2hi$5$9\1e$1\1m$5@2$0^4^2\1e$1\2lo$5\2hi$5@2$0^5^3~1\2a1$4\2n1$1\2a2$4\2n2$1@2$2@2$2@2$2@2$3^6^4@2$0^6^3@2$3^6^2@2$0^6^1\1a$4\1n$1\1c$5@2$2@2$3^5^3@2$0^5^2~1").
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kentry_eqb : ltac2:(zQ "20!v4!oc>1x$0>1y$0$1") := ltac2:(zQ "c3!hh4!p3!hmf!h9!v4!hm9!hof!oc!hq6!hr1!ht5!hv7&\2a1$2\2n1$0\2a2$2\2n2$0$1&\2n'$0@2$6@2$9^4^2@2$8^3^1&\2a'$2~1\1x$4\1y$4M4\1x$4$7^2\1a$2\1w$5\1v$0M4\1y$4$7^4\2a'$2\2w'$5\2v'$0@2$6@2$6@2$9^6^3@2$b^5^2@2$8^4^1\2a0$2\1n$0$1\2a0$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\1n$0$1~0\2a0$2\1n$0\1c$3$1\2a0$2\1n$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1~2\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\1a$2\1n$0\1k$5M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a'$2\2n'$0\2k'$5@2$6@2$6@2$9^6^3@2$8^5^2@2$b^4^1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\2lo$3\2hi$3M4\1y$4$7^3\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\3lo'$3\3hi'$3@2$6@2$a^4^2@2$a^3^1\1e$0\1m$3$1\1e$0\3lo0$3\3hi0$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1e$0\1m$3M4\1y$4$7^3\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\2e'$0\2m'$3@2$6@2$8^4^2@2$a^3^1\2e0$0\2lo$3\2hi$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1e$0\2lo$3\2hi$3M4\1y$4$7^4\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\3lo0$3\3hi0$3$1\2e0$0\1m$3$1\2e'$0\3lo'$3\3hi'$3@2$6@2$6@2$8^6^3@2$a^5^2@2$a^4^1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1~2~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\2a1$2\2n1$0\2a2$2\2n2$0M4\1y$4$7^5\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\3a1'$2\3n1'$0\3a2'$2\3n2'$0@2$6@2$6@2$6@2$9^8^4@2$8^7^3@2$9^6^2@2$8^5^1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1a$2\1n$0\1c$3M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a'$2\2n'$0\2c'$3@2$6@2$6@2$9^6^3@2$8^5^2@2$a^4^1\2a0$2\2n0$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1~2").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b : ltac2:(zQ "50!hh4!v4!oc!q2!h9>5allkn@1$3$1>2ub$0>2uk$4>2un$0>1K$1$2") := ltac2:(zQ "h16!hmf!hh4!h9!oc!hve!hof!v4!pb!hlb!hm9!igf!ih6!q2!ihd!ii5!iic!ij3&\1b$1\1k$2@7$4^9^8^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1k$2@7$4^a^9^8^7^2^1^4&M0\1a$0$3^3~4\5allkn@1$c$6\2ub$1\2uk$2\2un$1\1K$6M6\1K$6$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$e^4N8@7$4^a^9^8^7^2^1@1$8@1$h0^4~3\1a$0\1l$1\2k0$9~5\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$f@2$b^1^2$d@7$4^7^6^5^4@1$8Z^2@1$8@2$b^1^2\1e$1\1m$2$7\1e$1\2lo$2\2hi$2$7\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$7\1a$0\1l$1\1c$2~5~3").

Definition kentry_apart_bB : ltac2:(zQ "50!hh4!oc!h9!v4!io4>2bc$4>2ub$0>2uk$2>2un$0>1K$3$1") := ltac2:(zQ "h16!hmf!hh4!h9!oc!ioc!hof!pb!hlb!v4!hm9!igf!ih6!ihd!io4!ii5!iic!ij3&\1b$1\1k$2@7$4^9^8^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1k$2@7$4^a^9^8^7^2^1^4&M0\1a$0$3^3~4\2bc$d\2ub$1\2uk$2\2un$1\1K$8M8\1K$8$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$e^4N8@7$4^a^9^8^7^2^1@1$7@1$h0^4~3\1a$0\1l$1\2k0$9~5\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$f@2$b^1^2$c@7$4^7^6^5^4@1$7Z^2@1$7@2$b^1^2\1e$1\1m$2$6\1e$1\2lo$2\2hi$2$6\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$6\1a$0\1l$1\1c$2~5~3").

Lemma kentry_apart_bB_eqf : ltac2:(zQ "90!hh4!v4!oc!q2!ir3!h9!ir9!isa!itc>2fk@1$3$1@3$4>2ub$0>2uk$5>2un$0>1K$1$2@1$7@1$8^1@1$6^1").
Proof. intros. bcfe. unfold kentry_apart_bB, kentry_apart_b. (repeat first [ rewrite ranges_apart_xB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp : ltac2:(zQ "60!hh4!v4!oc!q2!h9!iu4>5allkn@1$3$1>2sp$5>2ub$0>2uk$4>2un$0>1K$1$2") := ltac2:(zQ "h28!hmf!hh4!h9!oc!iuc!hof!v4!pb!hlb!hm9!igf!ih6!q2!iu4!ihd!ii5!iic!ij3&\1k$2@8$4^a^9^8^7^6^2^1^3&\1b$1~0&M0\1a$0$3^2~1&\1l$1~2&\1a$0~3&\1k$2@8$4^b^a^9^8^7^2^1^4&\1b$1~5&M0\1a$0$3^3~6\5allkn@1$c$6\2sp$d\2ub$1\2uk$2\2un$1\1K$6M6\1K$6$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$f^4N8@8$4^b^a^9^8^7^2^1@1$8@1$h1^4~4\1a$0\1l$1\2k0$9~7\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$h0@2$b^1^2$e@8$4^8^7^6^5^4@1$8Z^2@1$8@2$b^1^2\1e$1\1m$2$7\1e$1\2lo$2\2hi$2$7\1a$0\1n$1~2\2a1$0\2n1$1\2a2$0\2n2$1$7\1a$0\1l$1\1c$2~7~4").

Definition kentry_apart_bpB : ltac2:(zQ "60!hh4!oc!h9!v4!iu4!io4>2bc$5>2sp$4>2ub$0>2uk$2>2un$0>1K$3$1") := ltac2:(zQ "h28!hmf!hh4!h9!oc!ivd!hof!pb!hlb!v4!hm9!igf!ih6!iu4!ihd!io4!ii5!iic!ij3&\1k$2@8$4^a^9^8^7^6^2^1^3&\1b$1~0&M0\1a$0$3^2~1&\1l$1~2&\1a$0~3&\1k$2@8$4^b^a^9^8^7^2^1^4&\1b$1~5&M0\1a$0$3^3~6\2bc$e\2sp$c\2ub$1\2uk$2\2un$1\1K$8M8\1K$8$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$f^4N8@8$4^b^a^9^8^7^2^1@1$7@1$h1^4~4\1a$0\1l$1\2k0$9~7\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$h0@2$b^1^2$d@8$4^8^7^6^5^4@1$7Z^2@1$7@2$b^1^2\1e$1\1m$2$6\1e$1\2lo$2\2hi$2$6\1a$0\1n$1~2\2a1$0\2n1$1\2a2$0\2n2$1$6\1a$0\1l$1\1c$2~7~4").

Lemma kentry_apart_bpB_eqf : ltac2:(zQ "a0!hh4!v4!oc!q2!ir3!h9!jh0!ji2!iu4!itc>2fk@1$3$1@3$4>2sp$8>2ub$0>2uk$5>2un$0>1K$1$2@1$7@1$9^1@1$6^1").
Proof. intros. bcfe. unfold kentry_apart_bpB, kentry_apart_bp. (repeat first [ rewrite ranges_apart_pB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b : ltac2:(zQ "20!oc!v4>1K$1$0") := ltac2:(zQ "80!hh4!p3!hmf!h9!v4!hm9!oc!pb\1K$4M4\1K$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$7\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1").

(* [comment removed for export] *)
Definition kn_unfill : ltac2:(zQ "40!q2!hh4!v4!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "a0!v4!hh4!q2!jj6!h9!jh0!jjc!jk5!iu4!jm3\1k@1$2$0\2ub$1\2uk$4\2un$1=2sp$8@4$7^4^3^2^1@3$9$0\1K$0@2$3@1$6^1@6$5^6^2^5^4^3^1^5").

Definition kn_unfillB : ltac2:(zQ "50!hh4!q2!h9!v4!io4>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "b0!hh4!v4!jj6!h9!ji2!jjc!iu4!jmd!io4!jn6!jm3\2bc$8\2ub$0\2uk$3\2un$0=2sp$6@4$9^4^3^2^1@3$a$1\1K$1@2$2@1$5^1@6$4^6^2^5^4^3^1@1$7^5").

Lemma kn_unfillB_eqf : ltac2:(zQ "80!q2!hh4!v4!ir3!h9!jo3!jof!itc>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold kn_unfillB, kn_unfill. (repeat first [ rewrite bc_fk_mkbc | rewrite mk_sprepB_eqf | rewrite kentry_apart_bpB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.




(* [comment removed for export] *)
Definition kwr_b : ltac2:(zQ "20!oc!v4>1K$1$0") := ltac2:(zQ "80!hh4!p3!hmf!h9!v4!hm9!oc!pb\1K$4M4\1K$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$7\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1").
Definition havoc1 : ltac2:(zQ "40!v4!q2!hh4!h9>1k@1$1$0>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "f0!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!jj6!ir9!jq9!jr1!jrd!js8\1k@1$5$0\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@5$a^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^3^a^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3").

Definition havoc1B : ltac2:(zQ "50!hh4!v4!q2!h9!io4>2bc$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h00!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!jj6!isa!jq9!io4!jt4!ju2!juf\2bc$c\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@5$a^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$f^9^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$d^a^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3").

Lemma havoc1B_eqf : ltac2:(zQ "80!v4!q2!hh4!ir3!h9!jvd!kg6!itc>2fk@1$1$0@3$3>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold havoc1B, havoc1. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite kentry_apart_bB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p : ltac2:(zQ "50!v4!q2!hh4!h9!iu4>1k@1$1$0>2sp$4>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "h00!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!jj6!jh0!jq9!jr1!jrd!js8!iu4\1k@1$5$0\2sp$f\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@6$a^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^a^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^3^b^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^a^8^7^6^2^1^3").

Definition havoc1pB : ltac2:(zQ "60!hh4!v4!q2!h9!iu4!io4>2bc$5>2sp$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h10!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!jj6!ji2!jq9!iu4!io4!jt4!ju2!juf\2bc$d\2sp$c\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@6$a^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$h0^a^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$e^b^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$f^a^8^7^6^2^1^3").

Lemma havoc1pB_eqf : ltac2:(zQ "90!v4!q2!hh4!ir3!h9!kh0!kha!iu4!itc>2fk@1$1$0@3$3>2sp$7>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold havoc1pB, havoc1p. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite kentry_apart_bpB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc : ltac2:(zQ "40!q2!hh4!v4!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "80!v4!hh4!q2!h9!kh0!jk5!iu4!ki5\1k@1$2$0\2ub$1\2uk$3\2un$1=2sp$6@4$5^4^3^2^1@4$7$0$0@5$4^5^1^4^3^2^5").

Definition kn_havocB : ltac2:(zQ "50!hh4!q2!h9!v4!io4>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "90!hh4!v4!h9!kha!iu4!jmd!io4!jn6!ki5\2bc$6\2ub$0\2uk$2\2un$0=2sp$4@4$7^4^3^2^1@4$8$1$1@5$3^5^1^4^3^2@1$5^5").

Lemma kn_havocB_eqf : ltac2:(zQ "80!q2!hh4!v4!ir3!h9!kj1!kjc!itc>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold kn_havocB, kn_havoc. (repeat first [ rewrite bc_fk_mkbc | rewrite mk_sprepB_eqf | rewrite havoc1pB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM : ltac2:(zQ "40!q2!hh4!v4!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "40!q2!kjc!v4!itc\1k@1$0$2@1$1@1$3^1").
Lemma kn_havocM_eq : ltac2:(zQ "70!q2!hh4!v4!ir3!h9!kj1!kk8@3$3>1k@1$0$2>2ub$1>2uk$4>2un$1@1$0$2$6$5"). Proof. apply functional_extensionality; intros k. unfold kn_havocM. apply kn_havocB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_cut : ltac2:(zQ "40!hh4!q2!h9!v4>1k@1$1$3>2ub$0>2uk$2>2un$0>2kb$0>2kk$2>3len$0@1$1$3") := ltac2:(zQ "60!hh4!h9!q2!kl4!kla!v4\1k@1$2$5\2ub$0\2uk$1\2un$0\2kb$0\2kk$1\3len$0@8$4$3^7^6^5^4^3^2^1").

Definition kwr_cutB : ltac2:(zQ "50!hh4!h9!q2!v4!io4>2bc$4>2ub$0>2uk$1>2un$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "50!hh4!h9!kl4!io4!km1\2bc$3\2ub$0\2uk$1\2un$0\2kb$0\2kk$1\3len$0@8$4^7$2^6^5^4^3^2^1").

Lemma kwr_cutB_eqf : ltac2:(zQ "80!hh4!q2!h9!v4!ir3!kma!kn4!itc>2fk@1$1$3@3$4>2ub$0>2uk$2>2un$0>2kb$0>2kk$2>3len$0@1$1$3@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold kwr_cutB, kwr_cut. (repeat first [ rewrite kcutB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 : ltac2:(zQ "40!v4!q2!hh4!h9>1k@1$1$0>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "e0!v4!hh4!hmf!h9!q2!jpc!oc!hm9!jq2!ir9!kma!jr1!jrd!js8\1k@1$4$0\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$4$0@5$9^5^4^3^2^1@3$8$0^1@1$5$0M0\1K$0@1$4$0^1\1a$2\1w$7\1v$1@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$5$0\2lo$3\2hi$3@1$5$0\1e$1\1m$3@1$5$0\1e$1\2lo$3\2hi$3@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$a^9^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$5$0\1a$2\3len$1\1c$3M2\1a$2@1$4$0^3\2kb$1\2kk$3@8$b^3^a^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$c^9^8^7^6^2^1^3").

Definition cutout1B : ltac2:(zQ "50!hh4!v4!q2!h9!io4>2bc$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "f0!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!isa!kn4!io4!jt4!ju2!juf\2bc$b\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@5$9^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$a^9^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^a^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3").

Lemma cutout1B_eqf : ltac2:(zQ "80!v4!q2!hh4!ir3!h9!knf!ko9!itc>2fk@1$1$0@3$3>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold cutout1B, cutout1. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite kentry_apart_bB_eqf | rewrite kwr_cutB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p : ltac2:(zQ "50!v4!q2!hh4!h9!iu4>1k@1$1$0>2sp$4>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "f0!v4!hh4!hmf!h9!q2!jpc!oc!hm9!jq2!jh0!kma!jr1!jrd!js8!iu4\1k@1$4$0\2sp$e\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$4$0@6$9^6^5^4^3^2^1@3$8$0^1@1$5$0M0\1K$0@1$4$0^1\1a$2\1w$7\1v$1@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$d^a^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$5$0\2lo$3\2hi$3@1$5$0\1e$1\1m$3@1$5$0\1e$1\2lo$3\2hi$3@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$a^a^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$5$0\1a$2\3len$1\1c$3M2\1a$2@1$4$0^3\2kb$1\2kk$3@8$b^3^b^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$c^a^8^7^6^2^1^3").

Definition cutout1pB : ltac2:(zQ "60!hh4!v4!q2!h9!iu4!io4>2bc$5>2sp$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h00!v4!hh4!hmf!h9!jpc!q2!oc!hm9!jq2!ji2!kn4!iu4!io4!jt4!ju2!juf\2bc$c\2sp$b\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@6$9^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$f^a^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$a^a^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$d^b^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^a^8^7^6^2^1^3").

Lemma cutout1pB_eqf : ltac2:(zQ "90!v4!q2!hh4!ir3!h9!kp4!kpf!iu4!itc>2fk@1$1$0@3$3>2sp$7>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold cutout1pB, cutout1p. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite kentry_apart_bpB_eqf | rewrite kwr_cutB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout : ltac2:(zQ "40!q2!hh4!v4!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "80!v4!hh4!q2!h9!kp4!jk5!iu4!ki5\1k@1$2$0\2ub$1\2uk$3\2un$1=2sp$6@4$5^4^3^2^1@4$7$0$0@5$4^5^1^4^3^2^5").

Definition kn_cutoutB : ltac2:(zQ "50!hh4!q2!h9!v4!io4>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "90!hh4!v4!h9!kpf!iu4!jmd!io4!jn6!ki5\2bc$6\2ub$0\2uk$2\2un$0=2sp$4@4$7^4^3^2^1@4$8$1$1@5$3^5^1^4^3^2@1$5^5").

Lemma kn_cutoutB_eqf : ltac2:(zQ "80!q2!hh4!v4!ir3!h9!kqb!kr7!itc>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold kn_cutoutB, kn_cutout. (repeat first [ rewrite bc_fk_mkbc | rewrite mk_sprepB_eqf | rewrite cutout1pB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.




(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_clip : ltac2:(zQ "20!q2!v4>1k@1$0$1@1$0$1") := ltac2:(zQ "d0!hh4!pb!hmf!h9!v4!igf!hof!hm9!oc!q2!lgb!lh5!jm3\1k@1$9$4@3$c$4\1K$4M4\1K$4$8^1\1a$2\1w$7\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$7$1\2lo$3\2hi$3@2$6@2$6@2$5@1$b?1A^2@2$5^2^1@2$5^1@1$a?1A\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1^1").

(* [comment removed for export] *)
Definition kreadZ : ltac2:(zQ "60!h9!q2!hm9!lhf!hh4!v4>1k@1$1$5>1b$4>3off$0>1n$2@1$3$0") := ltac2:(zQ "h20!h9!hh4!li8!q2!hm9!lif!oc!lhf!jpc!lja!lk3!lkc!ll3!p3!v4!lla!ihd!lm8\1k@1$3$e\1b$1\3off$0\1n$4Mb\1x$b@1$7$0@8$f?4segs^4^3^2^1$d@1$8$6@1$8$5\1v$1\3scs@1$3$5\5hints@1$3$6M1\1v$1@1$7$0^3\1z$0M3\3scs@1$3$5@1$7$0^3@2$c$0@2$h1^1$h0\1s$5\1l@1$3$5@1$2$0\2n0$4@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2sx$6\2lo$4\2n0$4\1e$1@1$2$0\2sx$6\2k0$4\1i$0\2n0$4@1$2$0\3scs@1$3$5\5hints@1$3$6@1$2$0@1$2$0").

Definition kreadZB : ltac2:(zQ "50!h9!hm9!lhf!hh4!io4>2bc$4>1b$3>3off$0>1n$1@1$2$0") := ltac2:(zQ "h20!h9!hh4!li8!q2!hm9!lif!oc!lhf!jpc!lja!lk3!lkc!ll3!p3!ihd!io4!ln2!lm8\2bc$f\1b$1\3off$0\1n$4Mb\1x$b@1$7$0@8$h0?4segs^4^3^2^1$d@1$8$6@1$8$5\1v$1\3scs@1$3$5\5hints@1$3$6M1\1v$1@1$7$0^3\1z$0M3\3scs@1$3$5@1$7$0^3@2$c$0@2$h1^1$e\1s$5\1l@1$3$5@1$2$0\2n0$4@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2sx$6\2lo$4\2n0$4\1e$1@1$2$0\2sx$6\1k$4\1i$0\2n0$4@1$2$0\3scs@1$3$5\5hints@1$3$6@1$2$0@1$2$0").

Lemma kreadZB_eqf : ltac2:(zQ "a0!h9!q2!hm9!lhf!ir3!lo2!lob!hh4!v4!itc>2fk@1$1$8@3$4>1b$7>3off$0>1n$2@1$3$0@1$6@1$9^1@1$5^1").
Proof. intros. bcfe. unfold kreadZB, kreadZ. (repeat first [ rewrite know_lookupB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e : ltac2:(zQ "50!hh4!q2!lhf!h9!v4>1k@1$1$4>1b$0>3off$3@1$2$0") := ltac2:(zQ "d0!q2!hh4!lif!li8!oc!jpc!lhf!lkc!ll3!p3!h9!v4!lla\1k@1$0$b\1b$1\3off$aM7\1x$7@1$6$1@8$c?4segs^3^2^1N8$9@1$5$4@1$5$2\1v$1\3scs@1$0$2\5hints@1$0$4M0\3scs@1$0$2@1$6$1^2@2$8$1^3\1s$2\1l@1$0$2@1$3$1\3scs@1$0$2\5hints@1$0$4@1$3$1@1$3$1").

Definition kread8eB : ltac2:(zQ "40!hh4!lhf!h9!io4>2bc$3>1b$0>3off$2@1$1$0") := ltac2:(zQ "d0!hh4!q2!lif!li8!oc!jpc!lhf!lkc!ll3!p3!h9!io4!ln2\2bc$b\1b$0\3off$aM7\1x$7@1$6$0@8$c?4segs^3^2^1N8$9@1$5$4@1$5$2\1v$0\3scs@1$1$2\5hints@1$1$4M1\3scs@1$1$2@1$6$0^2@2$8$0^3\1s$2\1l@1$1$2@1$3$0\3scs@1$1$2\5hints@1$1$4@1$3$0@1$3$0").

Lemma kread8eB_eqf : ltac2:(zQ "90!hh4!q2!lhf!ir3!h9!lp5!lpf!v4!itc>2fk@1$1$7@3$3>1b$0>3off$4@1$2$0@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold kread8eB, kread8e. (repeat first [ rewrite know_lookupB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%bool then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.

Lemma kwritableB_eqf : ltac2:(zQ "90!q2!h9!v4!oc!ir3!lqa!lr6!hh4!itc>2fk@1$0$2@3$4>1k@1$0$2>1b$7>3off$1>1n$1$3@1$6@1$8^1@1$5^1").
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritableB kwritable]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.

Lemma kwritable_xB_eqf : ltac2:(zQ "90!q2!hh4!v4!oc!ir3!h9!ls3!lt1!itc>2fk@1$0$2@3$4>1k@1$0$2>1b$1>3off$5>1n$1$3@1$7@1$8^1@1$6^1").
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kwritable_xB kwritable_x]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xhiB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.

Lemma kzero_xB_eqf : ltac2:(zQ "90!q2!hh4!v4!oc!ir3!h9!lu0!lua!itc>2fk@1$0$2@3$4>1k@1$0$2>1b$1>3off$5>1n$1$3@1$7@1$8^1@1$6^1").
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. 
  revert b off n. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kzero_xB kzero_x]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xhiB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%bool then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.

Lemma kfill_xB_eqf : ltac2:(zQ "90!q2!h9!hh4!v4!oc!ir3!lv5!lvf!itc>2fk@1$0$3@3$5>1k@1$0$3>1b$2>3off$1>1n$2>1c$1$4@1$7@1$8^1@1$6^1").
Proof.
  intros fk. apply functional_extensionality; intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros n. apply functional_extensionality; intros c. 
  revert b off n c. induction k as [|K rest IH]; intros; bcfe; [reflexivity|].
  cbn [kfill_xB kfill_x]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xhiB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x : ltac2:(zQ "50!hh4!oc!q2!h9!v4>1k@1$2$4>1b$0>3off$3>1n$0$1") := ltac2:(zQ "90!lh5!hlb!hh4!q2!h9!lgb!v4!hve!ih6\1k@1$3$6\1b$2\3off$4\1n$2@7$7^4^3^2^1@1$1Z@1$0?1A@1$1@2$8@1$5?1A@1$0?1A").

Definition off_image_xB : ltac2:(zQ "40!hh4!oc!h9!io4>2bc$3>1b$0>3off$2>1n$0$1") := ltac2:(zQ "80!lh5!hlb!hh4!h9!lgb!io4!ioc!ih6\2bc$5\1b$2\3off$3\1n$2@7$6^4^3^2^1@1$1Z@1$0?1A@1$1@2$7@1$4?1A@1$0?1A").

Lemma off_image_xB_eqf : ltac2:(zQ "90!hh4!oc!q2!ir3!h9!mga!mh8!v4!itc>2fk@1$2$7@3$3>1b$0>3off$4>1n$0$1@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold off_image_xB, off_image_x. (repeat first [ rewrite ranges_apart_xB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x : ltac2:(zQ "50!hh4!oc!q2!h9!v4>1k@1$2$4>1b$0>3off$3>1n$0$1") := ltac2:(zQ "h00!h9!lhf!oc!mi7!p3!mie!hof!hh4!igf!q2!mj5!v4!ihd!mk2!mk8!iic\1k@1$9$b\1b$7\3off$0\1n$7M1\1x@1$1@2$3$0$0$2@2$a^4^3\1p@2$3$0$0M3\1p@2$3$0$0$2^1\2lo$0\2hi$0M1\1x@1$1$0$2@2$e^7^4\2nl$0M1\1x@1$1$0$2@2$d^8^5\2nh$0@2$6@2$6@2$8Z@2$5^4^7@2$8@2$5@2$5^3^7^1$c@2$fZ^2$4$4$4").

Definition flat_xB : ltac2:(zQ "40!hh4!oc!h9!io4>2bc$3>1b$0>3off$2>1n$0$1") := ltac2:(zQ "f0!h9!lhf!oc!mi7!p3!mie!hof!hh4!igf!ihd!mke!io4!mld!mm5!iic\2bc$b\1b$7\3off$0\1n$7M1\1x@1$1@2$3$0$0$2@2$a^4^3\1p@2$3$0$0M3\1p@2$3$0$0$2^1\2lo$0\2hi$0M1\1x@1$1$0$2@2$d^7^4\2nl$0M1\1x@1$1$0$2@2$c^8^5\2nh$0@2$6@2$6@2$8Z@2$5^4^7@2$8@2$5@2$5^3^7^1$9@2$eZ^2$4$4$4").

Lemma flat_xB_eqf : ltac2:(zQ "90!hh4!oc!q2!ir3!h9!mmd!mn6!v4!itc>2fk@1$2$7@3$3>1b$0>3off$4>1n$0$1@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold flat_xB, flat_x. (repeat first [ rewrite base_rangeB_eqf | rewrite xloB_eqf | rewrite xhiB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "40!q2!hh4!v4!mk2\1k@1$0$2\1e$1@2$3^2^1").
Definition elo : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "40!q2!hh4!v4!mk8\1k@1$0$2\1e$1@2$3^2^1").

(* [comment removed for export] *)
Definition len_eqb : ltac2:(zQ "40!hh4!oc!q2!v4>1k@1$2$3>1n$0>1m$0$1") := ltac2:(zQ "c2!hh4!h9!mi7!jq2!jpc!mo0!mo7!hof!q2!jj6!hq6!v4&@3$3@2$2$0$1@4$5$0$1^2Z@1$4@2$2$0$1&@3$3@2$2$0$1@4$5$0$1^1Z@1$4@2$2$0$1\1k@1$8$b\1n$0\1m$0@2$9@2$a^2^1@2$7@3$6^3~0~1@3$6^3~1~0").

Definition len_eqbB : ltac2:(zQ "30!hh4!oc!io4>2bc$2>1n$0>1m$0$1") := ltac2:(zQ "b2!hh4!h9!mi7!jq2!jpc!mo0!mp1!hof!jj6!hq6!io4&@3$3@2$2$0$1@4$5$0$1^2Z@1$4@2$2$0$1&@3$3@2$2$0$1@4$5$0$1^1Z@1$4@2$2$0$1\2bc$a\1n$0\1m$0@2$8@2$9^2^1@2$7@3$6^3~0~1@3$6^3~1~0").

Lemma len_eqbB_eqf : ltac2:(zQ "80!hh4!oc!q2!ir3!mpd!mq7!v4!itc>2fk@1$2$6@3$3>1n$0>1m$0$1@1$5@1$7^1@1$4^1").
Proof. intros. bcfe. unfold len_eqbB, len_eqb. (repeat first [ rewrite lin_ge0B_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_aligned : ltac2:(zQ "40!oc!q2!hh4!v4>1k@1$1$3>1e$2$0") := ltac2:(zQ "c3!hh4!mr2!igf!hm9!oc!h9!lja!lk3!q2!v4!ht5!lm8&\1a$0\1b$0@2$2+c@2$1^5^4&\2op$6~0&\2op$7~0\1k@1$8$9\1e$0M0\1e$0$4^1\1z$5@2$a@2$b^1+hgg0Z\1n$3@2$2+c@2$1^3^2~1~1~2~2\2sx$4\2lo$3\1n$3\2e0$0@2$2+c@2$1^6^5\2sx$4\2k0$3\1i$5\1n$3@2$2+c@2$1^6^5").

Definition page_alignedB : ltac2:(zQ "30!oc!hh4!io4>2bc$2>1e$1$0") := ltac2:(zQ "b3!hh4!mrb!igf!hm9!oc!h9!lja!lk3!io4!ht5!lm8&\1a$0\1b$0@2$2+c@2$1^5^4&\2op$6~0&\2op$7~0\2bc$8\1e$0M0\1e$0$4^1\1z$5@2$9@2$a^1+hgg0Z\1n$3@2$2+c@2$1^3^2~1~1~2~2\2sx$4\2lo$3\1n$3\2e0$0@2$2+c@2$1^6^5\2sx$4\1k$3\1i$5\1n$3@2$2+c@2$1^6^5").

Lemma page_alignedB_eqf : ltac2:(zQ "80!oc!q2!ir3!ms6!mt5!hh4!v4!itc>2fk@1$1$6@3$2>1e$5$0@1$4@1$7^1@1$3^1").
Proof. intros. bcfe. unfold page_alignedB, page_aligned. (repeat first [ rewrite ealignB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : ltac2:(zQ "20!q2!hm9@1$0$1") := ltac2:(zQ "30!hm9!jq2!jpc@3$1$0N1@3$1$0N5@3$1$0N6@3$1$0N7@3$1$0Na@3$1$0Nb@3$1$0Nc@3$1$0Nd@3$1$0Ne@3$1$0Nf@3$1$0Nh0@3$1$0Nh1@3$1$0Nhc@3$1$0Nhd@3$1$0Nhe@3$1$0Nhf@1$2$0").

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := 16.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h1hb!h9!lhf!mi7!ll3!mu5!hh4!li8!mv2!mvb!ng8!hm9!oc!lja!lk3!q2!v4!ngf&\3lo'$0\2z0$0@2$3$0@2$9^5^2&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\3lo'$0\1z$0@2$3$0^2&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^2&\1z$0~7&\2lo$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^2&\1z$0~h3&\2lo$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\1k@1$e$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$h0^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^2M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\2k0$a\1i$0\1n$a~ha").

Definition xlo1B : ltac2:(zQ "40!lhf!h9!hh4!io4>2bc$3>1e$2@1$0$1") := ltac2:(zQ "h0hb!h9!lhf!mi7!ll3!nh8!hh4!li8!ni7!nj2!ng8!hm9!oc!lja!lk3!ngf!io4&\3lo'$0\2z0$0@2$3$0@2$9^5^2&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\3lo'$0\1z$0@2$3$0^2&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^2&\1z$0~7&\2lo$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^2&\1z$0~h3&\2lo$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\2bc$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$e^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^2M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\1k$a\1i$0\1n$a~ha").

Lemma xlo1B_eqf : ltac2:(zQ "90!q2!lhf!ir3!h9!nk1!nk8!hh4!v4!itc>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof. intros. bcfe. unfold xlo1B, xlo1. (repeat first [ rewrite erangeB_eqf | rewrite lin_srangeB_eqf | rewrite lin_brangeB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h1hb!h9!lhf!mi7!ll3!mu5!hh4!li8!mv2!mvb!nl0!hm9!oc!lja!lk3!q2!v4!ngf&\2z0$0\3hi'$0@2$3$0@2$9^4^1&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\1z$0\3hi'$0@2$3$0^1&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^1&\2hi$0~7&\1z$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^1&\2hi$0~h3&\1z$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\1k@1$e$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$h0^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^1M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\2k0$a\1i$0\1n$a~ha").

Definition xhi1B : ltac2:(zQ "40!lhf!h9!hh4!io4>2bc$3>1e$2@1$0$1") := ltac2:(zQ "h0hb!h9!lhf!mi7!ll3!nh8!hh4!li8!ni7!nj2!nl0!hm9!oc!lja!lk3!ngf!io4&\2z0$0\3hi'$0@2$3$0@2$9^4^1&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\1z$0\3hi'$0@2$3$0^1&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^1&\2hi$0~7&\1z$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^1&\2hi$0~h3&\1z$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\2bc$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$e^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^1M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\1k$a\1i$0\1n$a~ha").

Lemma xhi1B_eqf : ltac2:(zQ "90!q2!lhf!ir3!h9!nl7!nle!hh4!v4!itc>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof. intros. bcfe. unfold xhi1B, xhi1. (repeat first [ rewrite erangeB_eqf | rewrite lin_srangeB_eqf | rewrite lin_brangeB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) :=
  let plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1 k e', xhi1 k e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) :=
  let plain := match xlo1B bc e, xhi1B bc e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1B bc e', xhi1B bc e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Lemma xb2B_eqf : ltac2:(zQ "a0!h9!q2!lhf!mi7!ir3!nm6!nmc!hh4!v4!itc>2fk@1$1$8@3$4>1e$7@1$2@2$3$0$0@1$6@1$9^1@1$5^1").
Proof. intros. bcfe. unfold xb2B, xb2. (repeat first [ rewrite xlo1B_eqf | rewrite xhi1B_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "90!h9!lhf!mi7!li8!ll3!q2!nm6!hh4!v4\1k@1$5$8\1e$7M1\1x@1$1@2$2$0$0@1$1$0@2$6^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$4$0^2@1$3$0").

Definition xlo2B : ltac2:(zQ "40!lhf!h9!hh4!io4>2bc$3>1e$2@1$0$1") := ltac2:(zQ "80!h9!lhf!mi7!li8!ll3!nmc!hh4!io4\2bc$7\1e$6M1\1x@1$1@2$2$0$0@1$1$0@2$5^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$4$0^2@1$3$0").

Lemma xlo2B_eqf : ltac2:(zQ "90!q2!lhf!ir3!h9!nn3!nna!hh4!v4!itc>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof. intros. bcfe. unfold xlo2B, xlo2. (repeat first [ rewrite xb2B_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 : ltac2:(zQ "50!q2!lhf!h9!hh4!v4>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "90!h9!lhf!mi7!li8!ll3!q2!nm6!hh4!v4\1k@1$5$8\1e$7M1\1x@1$1@2$2$0$0@1$1$0@2$6^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$4$0^1@1$3$0").

Definition xhi2B : ltac2:(zQ "40!lhf!h9!hh4!io4>2bc$3>1e$2@1$0$1") := ltac2:(zQ "80!h9!lhf!mi7!li8!ll3!nmc!hh4!io4\2bc$7\1e$6M1\1x@1$1@2$2$0$0@1$1$0@2$5^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$4$0^1@1$3$0").

Lemma xhi2B_eqf : ltac2:(zQ "90!q2!lhf!ir3!h9!no2!no9!hh4!v4!itc>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof. intros. bcfe. unfold xhi2B, xhi2. (repeat first [ rewrite xb2B_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : ltac2:(zQ "a0!q2!h9!hm9!lhf!ir3!np1!npf!hh4!v4!itc>2fk@1$0$8>4fuel$2@3$4>1b$7>3off$1@1$3@1$0$1@2$6@1$9^2^1@2$5^1^2").
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [kread_bytesB kread_bytes]. rewrite IH. (repeat first [ rewrite kreadZB_eqf ]). reflexivity.
Qed.
Lemma kread_bytesB_eqf : ltac2:(zQ "a0!q2!hm9!h9!lhf!ir3!np1!npf!hh4!v4!itc>2fk@1$0$8@3$4>4fuel$1>1b$7>3off$2@1$3@1$0$2@1$6@1$9^1\4fuel$1@2$5^1^2").
Proof. intros fk. apply functional_extensionality; intros fuel. apply kread_bytesB_eqf'. Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideB bc b off n (am_base m) 0 (am_len m)) ms.

Lemma find_containingB_eqf : ltac2:(zQ "b0!q2!nqe!hh4!lhf!ir3!h9!nr5!ns7!mc!v4!itc>2fk@1$0$9@3$4>2ms@1$0$1>5kinds@1$0$8>1b$2>3off$5>1n$2@1$3$1@1$7@1$a^1@1$6^1").
Proof. intros. bcfe. unfold find_containingB, find_containing. (repeat first [ rewrite xinsideB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : ltac2:(zQ "90!hh4!mi7!q2!ir3!h9!ntb!nu7!v4!itc>2fk@1$2$7@3$3>1b$0>1n$0@2$1@2$1$0$4$0@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. (repeat first [ rewrite mkSrlB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  match find_containing k ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match find_containingB bc ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Lemma shadow_factsB_eqf : ltac2:(zQ "80!q2!hh4!v4!ir3!nqe!nv4!og3!itc>2fk@1$0$2@3$3>2ms@1$0$4>1b$1>1n$1@1$0$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold shadow_factsB, shadow_facts. (repeat first [ rewrite find_containingB_eqf | rewrite shadow_ofB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : ltac2:(zQ "a0!q2!hh4!oc!ir3!h9!nqe!oh3!oi1!v4!itc>2fk@1$0$8@3$3>2ms@1$0$5>1b$1>3off$4>3len$1$2@1$7@1$9^1@1$6^1").
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros len. 
  revert b off len. induction ms as [|m rest IH]; intros; bcfe; [reflexivity|].
  cbn [inside_mapsB inside_maps]. rewrite IH. (repeat first [ rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



Definition safe_range : ltac2:(zQ "60!q2!hh4!oc!h9!nqe!v4>1k@1$0$5>2ms@1$0$4>1b$1>3off$3>3len$1$2") := ltac2:(zQ "h40!h9!mie!lhf!mi7!igf!oc!hof!p3!q2!jj6!hh4!oj0!nqe!oh3!lgb!lh5!mj5!v4!ihd!mk2\1k@1$8$h1\2ms@1$8$c\1b$a\3off$0\3len$a@2$9M2\1x@1$2$0$5@2$h3^5^1\2lh$0M2\1x@1$2@2$3$0$0$5@2$h0^6^4\1p@2$3$0$0M3\1p@2$3$0$0$5^1\2lo$0\2hi$0@2$9@2$6@2$4$b@2$1^2^6@2$4@2$1@2$1^1^6^4$h2@2$6@2$4@1$f?1A@2$1^2^6@2$4@2$1@2$1^1^6^4@1$e?1A$7$7@5$d^5^4^3^2^1").

Definition safe_rangeB : ltac2:(zQ "60!hh4!oc!q2!h9!nqe!io4>2bc$5>2ms@1$2$4>1b$0>3off$3>3len$0$1") := ltac2:(zQ "h40!h9!mie!lhf!mi7!igf!oc!hof!p3!jj6!hh4!q2!oj0!nqe!oi1!lgb!lh5!ihd!mke!io4!mld\2bc$h2\2ms@1$a$c\1b$9\3off$0\3len$9@2$8M2\1x@1$2$0$5@2$h3^5^1\2lh$0M2\1x@1$2@2$3$0$0$5@2$h1^6^4\1p@2$3$0$0M3\1p@2$3$0$0$5^1\2lo$0\2hi$0@2$8@2$6@2$4$b@2$1^2^6@2$4@2$1@2$1^1^6^4$h0@2$6@2$4@1$f?1A@2$1^2^6@2$4@2$1@2$1^1^6^4@1$e?1A$7$7@5$d^5^4^3^2^1").

Lemma safe_rangeB_eqf : ltac2:(zQ "a0!q2!hh4!oc!ir3!h9!nqe!oj8!ok5!v4!itc>2fk@1$0$8@3$3>2ms@1$0$5>1b$1>3off$4>3len$1$2@1$7@1$9^1@1$6^1").
Proof. intros. bcfe. unfold safe_rangeB, safe_range. (repeat first [ rewrite base_rangeB_eqf | rewrite xhiB_eqf | rewrite inside_mapsB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b : ltac2:(zQ "40!q2!v4!oc!nqe>1k@1$0$1>2ms@1$0$3>1K$1$2") := ltac2:(zQ "e6!hmf!hh4!h9!oc!oj8!pb!v4!q2!hm9!hof!nqe!hlb!ii5!ij3&\1b$1\1o$2@5$4^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1o$2@5$4^8^7^2^1^4&M0\1a$0$3^3~4\1k@1$7$6\2ms@1$7$a\1K$6M6\1K$6$3^1\1a$0\1w$8\1v$1M0\1a$0$3^3\1b$1\1o$2@2$9@2$c^4N8@5$4^8^7^2^1@1$b@1$d^4~3\1a$0\1l$1\2k0$8~5\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1l$1\1c$2~5~3").

Definition grant_keep_bB : ltac2:(zQ "50!oc!q2!nqe!v4!io4>2bc$4>2ms@1$1$2>1K$3$0") := ltac2:(zQ "f6!hmf!hh4!h9!oc!ok5!pb!v4!hm9!hof!q2!nqe!hlb!io4!ii5!ij3&\1b$1\1o$2@5$4^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1o$2@5$4^8^7^2^1^4&M0\1a$0$3^3~4\2bc$c\2ms@1$9$a\1K$6M6\1K$6$3^1\1a$0\1w$7\1v$1M0\1a$0$3^3\1b$1\1o$2@2$8@2$d^4N8@5$4^8^7^2^1@1$b@1$e^4~3\1a$0\1l$1\1k$7~5\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1l$1\1c$2~5~3").

Lemma grant_keep_bB_eqf : ltac2:(zQ "80!q2!v4!oc!ir3!nqe!ol3!om2!itc>2fk@1$0$1@3$3>2ms@1$0$4>1K$1$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold grant_keep_bB, grant_keep_b. (repeat first [ rewrite safe_rangeB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter : ltac2:(zQ "30!q2!v4!nqe>1k@1$0$1>2ms@1$0$2@1$0$1") := ltac2:(zQ "60!q2!v4!nqe!ol3!on2!jm3\1k@1$0$1\2ms@1$0$2@1$4@3$5$1@2$3^2^1^2").

Definition kn_grant_filterB : ltac2:(zQ "40!q2!nqe!v4!io4>2bc$3>2ms@1$0$1@1$0$2") := ltac2:(zQ "80!q2!nqe!om2!on2!v4!jmd!io4!jm3\2bc$6\2ms@1$0$1@1$3@3$7$4@2$2^2^1@1$5^2").

Lemma kn_grant_filterB_eqf : ltac2:(zQ "70!q2!v4!ir3!nqe!one!op0!itc>2fk@1$0$1@3$2>2ms@1$0$3@1$0$1@1$5@1$6^1@1$4^1").
Proof. intros. bcfe. unfold kn_grant_filterB, kn_grant_filter. (repeat first [ rewrite bc_fk_mkbc | rewrite grant_keep_bB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kn_rezero : ltac2:(zQ "40!q2!hh4!v4!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "c0!hh4!hmf!pb!h9!v4!jh0!hm9!oc!q2!jk5!iu4!jm3\1k@1$8$4\2ub$0\2uk$3\2un$0=2sp$a@4$9^4^3^2^1@3$b$4\1K$4M4\1K$4$7^1\1a$1\1w$6\1v$0@6$5^9^5^8^7^6^4\1a$1\1n$0$2\1a$1\1n$0\2k0$6@6$5^9^5^8^7^6^4\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3$2\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$2\1a$1\1n$0\1c$3@6$5^9^5^8^7^6^4\1a$1\1n$0$2^5").

Definition kn_rezeroB : ltac2:(zQ "50!hh4!q2!h9!v4!io4>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "d0!hh4!hmf!pb!h9!v4!ji2!hm9!oc!iu4!jmd!io4!jn6!jm3\2bc$a\2ub$0\2uk$3\2un$0=2sp$8@4$b^4^3^2^1@3$c$4\1K$4M4\1K$4$7^1\1a$1\1w$6\1v$0@6$5^9^5^8^7^6^4\1a$1\1n$0$2\1a$1\1n$0\1k$6@6$5^9^5^8^7^6^4\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3$2\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$2\1a$1\1n$0\1c$3@6$5^9^5^8^7^6^4\1a$1\1n$0$2@1$9^5").

Lemma kn_rezeroB_eqf : ltac2:(zQ "80!q2!hh4!v4!ir3!h9!oq4!or0!itc>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof. intros. bcfe. unfold kn_rezeroB, kn_rezero. (repeat first [ rewrite bc_fk_mkbc | rewrite mk_sprepB_eqf | rewrite kentry_apart_bpB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.




(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.

Lemma amap_matchB_eqf : ltac2:(zQ "90!hh4!oc!q2!ir3!nqe!ord!osa!v4!itc>2fk@1$2$7@3$3>1b$0>1n$0>1m$4$1@1$6@1$8^1@1$5^1").
Proof. intros. bcfe. unfold amap_matchB, amap_match. (repeat first [ rewrite len_eqbB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Lemma copy_factsB_eqf' : ltac2:(zQ "a0!h9!q2!hh4!v4!hm9!lhf!ir3!ot8!ou5!itc>2fk@1$1$3>4fuel$4@3$6>2sb$2>2sk$0>2db$2>2dk$0>1n$0@1$5@1$1$3@2$8@1$9^2^1@2$7^1^2").
Proof.
  intros fk fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
  cbn [copy_factsB copy_facts]. rewrite IH. (repeat first [ rewrite know_lookupB_eqf | rewrite kread8eB_eqf | rewrite kread_bytesB_eqf' ]). reflexivity.
Qed.
Lemma copy_factsB_eqf : ltac2:(zQ "a0!h9!q2!hm9!hh4!v4!lhf!ir3!ot8!ou5!itc>2fk@1$1$4@3$6>4fuel$2>2sb$3>2sk$0>2db$3>2dk$0>1n$0@1$5@1$1$4@1$8@1$9^1\4fuel$2@2$7^1^2").
Proof. intros fk. apply functional_extensionality; intros fuel. apply copy_factsB_eqf'. Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition img_cov : ltac2:(zQ "40!h9!oc!q2!v4>1k@1$2$3>1a$0>1b$0$1") := ltac2:(zQ "b0!hh4!p3!h9!hmf!v4!hm9!igf!hof!oc!q2!ov3\1k@1$9$4\1a$2\1b$2@3$a$4\1K$4M4\1K$4$8^1\2a0$3\1w$5\1v$0$1\2a0$3\1n$0$1\2a0$3\1n$0\2k0$5$1\2lo$2\2hi$2@2$7@2$6^2^5@2$6^4^1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2a0$3\1n$0$1\2a1$3\2n1$0\2a2$3\2n2$0$1\2a0$3\1n$0\1c$2$1\2a0$3\1n$0$1^3").

Definition img_covB : ltac2:(zQ "30!h9!oc!io4>2bc$2>1a$0>1b$0$1") := ltac2:(zQ "c0!hh4!p3!h9!hmf!v4!hm9!igf!hof!oc!jmd!io4!ov3\2bc$a\1a$2\1b$2@3$b$4\1K$4M4\1K$4$8^1\2a0$3\1w$5\1v$0$1\2a0$3\1n$0$1\2a0$3\1n$0\1k$5$1\2lo$2\2hi$2@2$7@2$6^2^5@2$6^4^1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2a0$3\1n$0$1\2a1$3\2n1$0\2a2$3\2n2$0$1\2a0$3\1n$0\1c$2$1\2a0$3\1n$0$1@1$9^3").
Lemma img_covB_eqf : ltac2:(zQ "80!h9!oc!q2!ir3!ove!pg8!v4!itc>2fk@1$2$6@3$3>1a$0>1b$0$1@1$5@1$7^1@1$4^1").
Proof. intros. bcfe. unfold img_covB, img_cov. (repeat first [ rewrite bc_fk_mkbc ]). reflexivity. Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
    (* [comment removed for export] *)
     (* [comment removed for export] *)
   (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
    (* [comment removed for export] *)
   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : ltac2:(zQ "10!hh4$0") := ltac2:(zQ "50!ph3!phc!pi3!pia!pj1@2$4@2$0+ogg0@1$1$2@2$0+h0@1$1$3").
(* [comment removed for export] *)
Definition e_envp : ltac2:(zQ "10!hh4$0") := ltac2:(zQ "60!pj1!pj8!pk1!ph3!hlb!phc@2$0$2@2$0@2$3+8@1$5$1@1$4+h0").
Definition e_auxv : ltac2:(zQ "10!hh4$0") := ltac2:(zQ "60!pj1!pk9!pl2!ph3!hlb!phc@2$0$2@2$0@2$3+8@1$5$1@1$4+8").
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe : ltac2:(zQ "30!lhf!q9!hh4>2cs$1@1$0$2") := ltac2:(zQ "hfh1!plb!pne!hh4!li8!po4!oc!lja!lhf!poc!pp5!ppf!pq8!pr3!lk3!vd!prc!ps5!ll3!pse!pt4!ptd!puc!pv6!qg0!qg9!qh6!qi0!q9!qia!qif!qjc&\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@1$3$2&\3rs1@1$1@1$0#5\3imm@1$1@1$0#c@1$3$2&\2rd@1$1@1$0#5~1&\3rs2@1$1@1$0#5\3imm@1$1@1$0#c@1$3$2&\3rs1@1$1@1$0#5~3&\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@1$3$2&\2rd@1$1@1$0#5~5&\2op$6~6&\2rd@1$1@1$0#5\3rs1@1$1@1$0#5@1$3$2&\2op$d~6&\2rl$5~6&\2aq$5~a&\1w$9~b&\3rs1@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2&\2rd@1$1@1$0#5~d&\3fmt$4~6&\3fmt$4~8\2cs$hbM7\1x@1$7$8@1$7$2@2$he?2IT@1$hc^1\1i$8M8\1i$8@1$7$2^1~0~0\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@1$3$2~2\1c$h4\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d@2$h1$2@3$h2$2$5@3$hd^4@2$h0@1$f@1$e^6^3@2$h0@1$f@1$e^6^2\2sz$c\6signed$5~2\2sz$c~4\2op$6~2\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#6@1$3$2~7~2\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#5@1$3$2~7\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4~8~2@1$3$2@1$3$2~9~9\1w$9\2aq$5\2rl$5~8~c\2op$h3~c\2op$a\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3csr@1$1@1$0#c@1$3$2\2op$a\2rd@1$1@1$0#5\4uimm@1$1@1$0#5\3csr@1$1@1$0#c@1$3$2\3fmt$4~2\3fmt$4~4\2op$h7\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2\2op$h5\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2\3fmt$4~e\2op$ha~f\2op$h8~f\2op$h6~f\3dst$b\3src$b~e\3dir$h9~h0~h0@1$3$2").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_auxb : ltac2:(zQ "30!mi7!h9!hh4@2$0$2$1") := ltac2:(zQ "20!qka!ql4@1$1$0").
Definition auxw : ltac2:(zQ "40!h9!q2!hh4!v4>1i$0>2ty$0>1v$2@1$1$3") := ltac2:(zQ "d0!h9!hh4!qm0!v4!mie!jq2!pse!qma!qn0!qn8!qnd!jpc!hlb\1i$0\2ty$0\1v$1@3$5$3@3$8@2$9@3$6$1$0$2@2$4@3$7$1$0$2@2$a+h0^3N8@1$c^2@3$5$3@3$8@2$9@3$6$1$0$2@2$4@2$4@3$7$1$0$2@2$a+h0^3+8N8^1@1$b$3").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

       (* [comment removed for export] *)
 (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End APC.
(* [comment removed for export] *)
