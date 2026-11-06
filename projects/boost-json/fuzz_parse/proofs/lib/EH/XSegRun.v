(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare
  XFPSteps XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XAxFast.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR8WithSegs~~~~~~m94wdenm94wentk13app37Corelib4Init5Logics62eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~tf3envtf6sentry89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~hj39mem_denotm94wlogk14boolk13nat01Z89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~hq3cexpr_vars_lttf4exprk14andbtf6a_basetf5saddrm9cwent_vars_lt36Stdlib5Lists4Listii87forallbtf6edenotk14true79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~il69env_agreem9awl_vars_lttf9sym_statetf6s_nextk15falsehq3akn_vars_lthq3asr_vars_lttf6s_knowtf5s_logtf6s_regs37Corelib5Lists7ListDefjg33nthtf4ELitk14None3h5LinuxProcessSemantics5Riscv5Instrjif5aluopjif5mulopk14Sometf5two64m93reg46Stdlib6ZArith6BinInt1Zjna3eqbjna3lebjna3ltbjna6modulotf6kentryk13nil37Corelib4Init3Natjs03addhq33NCShq3ccaller_savedhq38sr_freshtf3SSRtf6sr_updk14prodk14pairtf4elentf5sprepjna3addk13orbtf8expr_eqbtferanges_apart_ptf6zlit64jna3subjg33maptf8mk_sprepm99log_hullstf8sidecondhj37know_okhj38log_flathj39scs_denotm97carry_fs63ands62extf5a_offjna2leii82Injna6of_natm98hull_addtf2SEm9chull_coveredm95cold1m97cold_ok37Corelib4Init5Peanolh22lehj34flathj36estarttf2SAs62orhj35elenZm98mk_hullshj39kentry_okm95kspank13fstm96ksplitk13sndm96carry208positivetf8prune1pcm94nosptf7prunepctf5SPrepm98carry_fLm97carry2Ltfabase_rangek12ttk14unittf6pruneptf6sp_rnghj3bbr_cache_okm98prunepcFm98carry_fFtffranges_apart_pcm98cold_okcm97ksplitcm97carry2F89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XAxFast3AXF~~~~~~ml3dsym_execTXBIFtf8facts_oftf4s_pc89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B~~~~~~mr76mk_kixmr74mkbck14negbjna3powtfdknow_lookupA0lh22lttf4lresm97cw_keepii86filtertf4LHittf5LMisstf6LStucktfeknow_bytes_littfclit_of_bytestfbknow_lookupm9cknow_lookupWhq37kread8em98kread8eWhq3bkread_bytesm9ckread_bytesWhq3acopy_factsm9bcopy_factsWjna3muljg33seqjif7ALU_ADDhq36flat_xhq39kn_havocMhq3bkwritable_xtf4EVartf5mkAlutf3xhim9bconsecutivem9bfsd_targetsm9bkimg_precutm96kslotsm9bwslots_wentm9efld_sources_okii87existsbm95efoldtf6erangem95EVMAXm95evarsm94zseqjna6to_nat46Stdlib5Arith8PeanoNat3Natot73ltbm9aeval_rangehq33acshq33ACShq35FdStdhq34amapot73eqbk16lengthm95sstepm96closedm9astep_blockm99step_copym9cstep_diamondm9cstep_evalregm99step_fillm9bstep_fldseqm9bstep_fsdseqm9bstep_strlenjna2lt3h5LinuxProcessSemantics5Riscv7Preludepr95bvmaphj37regs_okil6akn_vars_ltil6asr_vars_lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~qgf7FPStateqgf6fp_csrqgf4mksthf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~qn56mstepsm93INVm99STEP_POSTs61Iqgf4getrhf2BVhf4BvWf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6XHoare~~~~~~qu66ret_okm97ret_litqgf7seg_romm96wslotshfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~rl89mem_grows3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsrq3h0word_to_le_bytesqgf3rdntf4ridxjif5instrrq3afetch_wordrq38is_ecall3h5LinuxProcessSemantics5Riscv7DecodeCsi0adecode_anytfbitab_lookuprq38store_okii89nth_error89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib3APS~~~~~~snb3updii84incltf2ebtf2evm99join_regsm96arm_oks64Truem9h0strlen_step_stmtm98seg_stepm98step_reqm96regionm97within1m97outsidem9cregions_flatm9bwent_withinm9aregions_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypetm27Segmenttf4itabtfaitab_sound89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~tr69copy_spectr69fill_spec" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SR.
Section WithSegs.
Variable segs : ltac2:(zQ "20!l9!tp7@1$0$1").
Variable IT : ltac2:(zQ "10!tq2$0").
Variable x_cpy : Z.      (* [comment removed for export] *)
Variable x_set : Z.      (* [comment removed for export] *)
Variable x_len : Z.      (* [comment removed for export] *)
Variable ro_lo ro_hi : Z. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive went : Type :=
| WSt (a : saddr) (wd : nat) (v : expr)                       (* [comment removed for export] *)
| WCopy (db : expr) (dk : Z) (sb : expr) (sk : Z) (n : Z)     (* [comment removed for export] *)
| WFill (db : expr) (dk : Z) (n : Z) (c : Z).                 (* [comment removed for export] *)

Fixpoint wden (E : env) (M : word -> option byte) (w : list went) : word -> option byte :=
  match w with
  | [] => M
  | WSt a wd v :: r => wbytes (wden E M r) (adenot E a) (word_to_le_bytes wd (edenot E v))
  | WCopy db dk sb sk n :: r =>
      let m := wden E M r in
      match rdn segs m (adenot E (SA sb sk)) (Z.to_nat n) with
      | Some bs => wbytes m (adenot E (SA db dk)) bs
      | None => m
      end
  | WFill db dk n c :: r => wbytes (wden E M r) (adenot E (SA db dk)) (repeat (Z_to_bv 8 c) (Z.to_nat n))
  end.

Fixpoint wlog (log : list sentry) : list went :=
  match log with [] => [] | SE a wd v :: r => WSt a wd v :: wlog r end.

Lemma wden_wlog : ltac2:(zQ "c1!h9!jc!l9!m0!r2!r9!s0!ta!hi4!hia!hnf!hoc&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1E$8>1M~0>3log@1$2$9>1w@1$2$5@3$7~0@3$4^4^3@3$6$5@1$b^2^1@3$a^4@3$4^4^3^1^2").
Proof.
  intros E M log w. induction log as [|[a wd v] r IH]; cbn [wlog app wden mem_denot]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition went_vars_lt : ltac2:(zQ "30!hp3!hpa!r9>1b$1>1g$2$0") := ltac2:(zQ "90!hq0!hua!hva!r9!ig1!hpa!hp3!ig8!ih1\1b$5\1g$3M3\1g$3$6^1\1a$8\2wd$5\1v$2@2$4@2$1^5@1$7^3@2$1^5^1\2db$2\2dk$0\2sb$2\2sk$0\1n$0@2$4@2$1^7^5@2$1^7^3\2db$2\2dk$0\1n$0\1c$0@2$1^6^4").
Definition wl_vars_lt : ltac2:(zQ "40!hp3!l9!hpa!r9>1b$2>1w@1$1$3$0") := ltac2:(zQ "50!r9!l9!hpa!ih9!ijb\1b$2\1w@1$1$0@3$4$0@1$3^2^1").

Lemma edenot_agree_AP : ltac2:(zQ "b0!ta!ik6!hi4!hp3!hpa!ikf!h9!hua!hva!ip6!jc>1b$4>1E$2>2E'$2>1e$8>0@3$9^4^3^2>0@3$0$3@2$7^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
Proof.
  intros b E E' e Hag H. apply (edenot_agree b); [exact Hag|].
  induction e; cbn in *; try reflexivity; try exact H;
    try (apply andb_true_iff in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
Qed.

Lemma wden_agree : ltac2:(zQ "d1!h9!jc!m0!ta!hi4!r2!hp3!l9!hpa!ikf!ip6!r9!iq3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1b$8>1E$4>2E'$4>1M~0>1w@1$7$b>0@3$a^5^4^3>0@3$3$6@2$c^6^2$9@3$3~0@3$5^6^4^3@3$5^5^4^3").
Proof.
  intros b E E' M w Hag. induction w as [|g r IH]; intros H; [reflexivity|].
  cbn [wl_vars_lt forallb] in H. apply andb_true_iff in H as [Hg Hr].
  destruct g as [[ab ak] wd v|db dk sb sk n|db dk n c]; cbn [wden went_vars_lt a_base] in *;
    rewrite (IH Hr).
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' ab Hag H1), (edenot_agree_AP b E E' v Hag H2). reflexivity.
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' db Hag H1), (edenot_agree_AP b E E' sb Hag H2). reflexivity.
  - unfold adenot. cbn [a_base a_off]. rewrite (edenot_agree_AP b E E' db Hag Hg). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive sstep : Type :=
| SBlock (stops : list Z)
| SCopy
| SFill
| SFsdSeq (n : nat)        (* [comment removed for export] *)
| SFldSeq (n : nat)        (* [comment removed for export] *)
| SStrlen (k : Z)          (* [comment removed for export] *)
| SExpect (pc : Z)
| SDiamond (joinpc : Z)    (* [comment removed for export] *)
| SEvalReg (r : nat).      (* [comment removed for export] *)

Variable BFUEL : nat.

(* [comment removed for export] *)
Definition closed : ltac2:(zQ "40!hp3!l9!ir0!r9>2ss$2>1w@1$1$3$0") := ltac2:(zQ "f0!l9!ig1!irc!hia!hp3!is5!ikf!isd!itb!iu9!iv2!iva!ir0!r9!iq3\2ss$c\1w@1$0$d@2$1@2$1@2$1@2$8@1$2^2@1$b^2@2$7@1$2^2@1$9^2@2$e@1$2^2^1M0\1x@1$0$3$4@1$a^2$6\1s$3\1l@1$0$3$5").

Definition reg : ltac2:(zQ "30!hpa!hva!ir0>2ss$2>1n$0$1") := ltac2:(zQ "60!hpa!jha!ji1!hva!iva!ir0\2ss$5\1n$0@4$1$3^1@1$4^2@1$2Z").
Definition ret_lit : ltac2:(zQ "30!m0!hq0!ir0>2ss$2@1$0$1") := ltac2:(zQ "h10!hq0!hva!ji8!hpa!hp3!ig1!m0!jl3!jlc!jm5!ir0!jmc!jn4!jp2!jp9!jq0!jq7\2ss$aM1\1x$1@1$6$0@2$c^1N1\1r$0M4\0$4@1$6$0@2$5@2$5@2$d@2$h0^1+2Z@2$f^1$b@2$eZ^1@2$9$0^1@1$2$0\1n$3@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2sx$4\2lo$3\1n$3\1e$1@1$2$0\2sx$4\1k$3\1i$0\1n$3@1$2$0").

(* [comment removed for export] *)
Definition after_call : ltac2:(zQ "50!ir0!l9!hq0!hva!jr1>2ss$0>3ret$2>2rv$3>2k'@1$1$4$0") := ltac2:(zQ "h20!ji8!l9!hpa!jra!jt2!hq0!jt9!ju0!jv0!jvc!hva!jr1!irc!iva!ih1!hia!kg2!ir0\2ss$h1\3ret$5\2rv$a\2k'@1$1$b=2nx$2@1$c^4@6$9^4@3$h0@3$8@1$d^5$7^1Na^3@1$3$f^2@2$4^1$6@1$0$e").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint hull_add (hs : list (expr * Z * Z)) (b : expr) (lo hi : Z) : list (expr * Z * Z) :=
  match hs with
  | [] => [(b, lo, hi)]
  | (b', lo', hi') :: rest =>
      if expr_eqb b b' then (b', Z.min lo lo', Z.max hi hi') :: rest
      else (b', lo', hi') :: hull_add rest b lo hi
  end.
Fixpoint log_hulls (log : list sentry) : list (expr * Z * Z) :=
  match log with
  | [] => []
  | SE a w _ :: older => hull_add (log_hulls older) (a_base a) (a_off a) (a_off a + Z.of_nat w)
  end.
(* [comment removed for export] *)
Definition kspan : ltac2:(zQ "50!m0!kgb!hva!jr1!ih1>1K$3@1$0@2$1$4$2") := ltac2:(zQ "b5!hva!ih1!kgb!hq0!ji8!jm5!kh2!jr1!hpa!m0!kh9&@2$5@2$2$1$0@4$6$1$0^2^1&\1n$0~0&\1a$1~1&@2$5@2$2$1$0@4$6$1$0^3^2&\2lo$3\2hi$3@1$4@2$2$1$0\1K$7M7\1K$7@1$9@2$2$1$0^1\1a$1\2w'$8\1v$0@2$5@2$2$1$0@4$6$1$0^3@1$a^2~2\1a$1\1n$0\1k$8~3~4\1e$0\1m$3@1$4@2$2$1$0\1e$0~4\1a$1\1n$0@1$4@2$2$1$0\2a1$1\2n1$0\2a2$1\2n2$0@1$4@2$2$1$0\1a$1\1n$0\1c$3~3~2").
(* [comment removed for export] *)
Definition cold1 : ltac2:(zQ "70!kgb!hq0!hva!hp3!l9!jr1!ki0>2fk@1$4$5>1h@2$0@2$0@2$0$2$1$1$6>2kb$2>2kk$1>2kl$2$3") := ltac2:(zQ "h50!hva!kgb!hq0!hp3!is5!hpa!ki0!jp9!ig1!jl3!jlc!ki8!l9!kif!ji1!kj5!jr1!kk0!jmc!kl1!jq0\2fk@1$c$h0\1h@2$1@2$1@2$1$0$2$2$6\2kb$0\2kk$2\2kl$0M1\1h@2$1@2$1@2$1$0$2$2$6$3^4\1p@2$1@2$1$0$2$2\2sp$6M1\1p@2$1@2$1$0$2$2$3^2\2p0@2$1$0$2\1n$2M1\2p0@2$1$0$2$3^2\1b$0\2lo$2@2$8@2$8@2$7Z^3@2$h4^3$h2M3\0$3$3@2$f^9^2M0\2kl$0$3^7\1l$2@2$d@2$7@2$b^9@1$h3^1^2@2$7@2$b^2^4^9\2n0$5$4\2op$9\1a$0\2b0$0$4\2op$9\1a$0\2b0$0$4\2op$a\1a$0\2b0$0$4\2op$a\1a$0\2b0$0$4\2sx$3\3lo0$5\2n0$5\1e$0$4\2sx$3\1k$5\1i$2\2n0$5$4@8$h1^b^5^2^1@1$e^3^9^8^7").
Fixpoint cold_ok (fk : list kentry) (hs : list (expr * Z * Z * sprep)) (kb : expr) (kk : Z) (kl : expr) : bool :=
  match hs with
  | [] => true
  | h :: rest => (cold1 fk h kb kk kl && cold_ok fk rest kb kk kl)%bool
  end.
Fixpoint ksplit (fk : list kentry) (hs : list (expr * Z * Z * sprep)) (kn : list kentry) : list kentry * list kentry :=
  match kn with
  | [] => ([], [])
  | K :: rest =>
      let '(hot, cold) := ksplit fk hs rest in
      match kspan K with
      | Some (a, kl) => if cold_ok fk hs (a_base a) (a_off a) kl then (hot, K :: cold) else (K :: hot, cold)
      | None => (K :: hot, cold)
      end
  end.
Definition mk_hulls : ltac2:(zQ "70!l9!kgb!hq0!hva!jr1!hia!ki0>2fk@1$0$4>3log@1$0$5@1$0@2$1@2$1@2$1$3$2$2$6") := ltac2:(zQ "d0!kgb!hq0!hva!ki0!kh2!l9!kla!km1!ji1!jr1!km8!hia!kn3\2fk@1$5$9\3log@1$5$b@4$7@2$0@2$0$2$1$1@2$0@2$0@2$0$2$1$1$3\1h@2$0@2$0$2$1$1M0\1h@2$0@2$0$2$1$1@2$0@2$0@2$0$2$1$1$3^1\1y@2$0$2$1\2hi$1M0\1y@2$0$2$1@2$0@2$0@2$0$2$1$1$3^2\1b$2\2lo$1@4$4@2$0@2$0$2$1$1$3@4$4@2$0$2$1$1@4$4$2$1^2^1@2$6^3^1@4$a^7^2^1@1$8@2$6^3^1@1$c^1").
(* [comment removed for export] *)
Fixpoint carry_f (fk : list kentry) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry_f fk older kn hints in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Definition carry2 (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | _ =>
      let fk := facts_of kn in
      let hs := mk_hulls fk log in
      let '(hot, cold) := ksplit fk hs kn in
      let '(kn', scs, hs') := carry_f fk log hot hints in
      (kn' ++ cold, scs, hs')
  end.

(* [comment removed for export] *)
Lemma carry_f_sound : ltac2:(zQ "h11!l9!h9!jr1!jc!hp3!knf!m0!kgb!koa!kh2!ta!hi4!hia!kp5!hnf!kq1!kqe&>0@1$3@1$1#k0@1$6@1$3@1$1#8>1E$b>7anybase~0>2M0~0>2fk@1$0$2>4base~0>3log@1$0$c>2kn@1$0$2>5hints@1$0$4>3kn'@1$0$2>3scs@1$0$5>3hs'@1$0$4>0@3$a@2$7@2$7@1$0$2@1$0$5@1$0$4@4$h0^8^6^5^4@4$9@2$7@1$0$2@1$0$5@1$0$4@4$9@1$0$2@1$0$5^3^2^1>0@4$8?4segs^c^a^9>0@2$d^d^8>0@4$8?4segs^e^a^8>0@4$f?4segs^e^f^6@4$8?4segs^h0@3$e^h0^c^b^8").
Proof.
  intros E anyb M0 fk base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hall Hlf Hkn Hscs.
  - cbn in Hc. injection Hc as <- <- <-. exact Hkn.
  - cbn [carry_f] in Hc. cbn [log_flat] in Hlf. ndestruct Hlf as (Hw8 & Hfa & Hlf').
    destruct (carry_f fk older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
    rewrite (prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)) in Hc. rewrite prunep_eq in Hc.
    destruct (prune fk a w v kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
    injection Hc as <- <- <-.
    apply scs_denot_app in Hscs as [Hs1 Hs2].
    cbn [mem_denot].
    constructor.
    + cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
      pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
      rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
      ndestruct Hfa as (?&?&?&?). lia.
    + eapply prune_sound; eauto.
Qed.

(* [comment removed for export] *)
Definition hull_covered : ltac2:(zQ "60!kgb!hq0!l9!hpa!hva!ih1>2hs@1$2@2$0@2$0$4$1$1>1a$5>1w$3P") := ltac2:(zQ "f0!hq0!kgb!hva!kh2!kr8!kre!ks3!ksb!l9!hpa!ig8!ih1!kt1!ki8!kt7\2hs@1$8@2$1@2$1$2$0$0\1a$b\1w$9@2$5$0\2lo$0@2$5$0\2hi$0@2$4@3$c@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0@1$a^4^2^1^5@2$4@2$7^2@1$6^4@2$7@2$d@1$6^4@1$e^3^1").

Lemma hull_add_old : ltac2:(zQ "a0!hq0!hva!kgb!kh2!kr8!kre!kt1!ksb!l9!ku1>2hs@1$8@2$2@2$2$1$0$0>1b$1>2lo$0>2hi$0>2b0$1>3lo0$0>3hi0$0>0@3$6@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^3^2^1^7@2$5$0\3lo1$0@2$5$0\3hi1$0@2$4@3$6@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^6^2^1@4$9^a^9^8^7@2$4@2$7^2^5@2$7^4^1").
Proof.
  induction hs as [|[[b' lo'] hi'] rest IH]; intros b lo hi b0 lo0 hi0 Hin; [destruct Hin|].
  cbn [hull_add]. destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->. destruct (expr_eqb b b0).
    + exists (Z.min lo lo0), (Z.max hi hi0). split; [left; reflexivity|]. lia.
    + exists lo0, hi0. split; [left; reflexivity|]. lia.
  - destruct (expr_eqb b b').
    + exists lo0, hi0. split; [right; exact Hin|]. lia.
    + ndestruct (IH b lo hi b0 lo0 hi0 Hin) as (lo1 & hi1 & H1 & H2 & H3).
      exists lo1, hi1. split; [right; exact H1|]. lia.
Qed.

Lemma hull_add_new : ltac2:(zQ "a0!hq0!kgb!hva!kh2!kr8!kre!ksb!l9!ku1!kt1>2hs@1$7@2$1@2$1$2$0$0>1b$2>2lo$0>2hi$0@2$5$0\3lo1$0@2$5$0\3hi1$0@2$4@3$9@2$1@2$1$2$0$0@4$3@2$1$2$0$0@4$3$2$0^5^2^1@4$8^6^5^4^3@2$4@2$6^2^4@2$6^3^1").
Proof.
  induction hs as [|[[b' lo'] hi'] rest IH]; intros b lo hi.
  - exists lo, hi. split; [left; reflexivity|]. lia.
  - cbn [hull_add]. destruct (expr_eqb b b') eqn:Heq.
    + apply expr_eqb_eq in Heq. subst b'. exists (Z.min lo lo'), (Z.max hi hi'). split; [left; reflexivity|]. lia.
    + ndestruct (IH b lo hi) as (lo1 & hi1 & H1 & H2 & H3). exists lo1, hi1. split; [right; exact H1|]. lia.
Qed.

Lemma log_hulls_cover : ltac2:(zQ "90!hia!l9!hpa!kuc!hva!ih1!kv1!kn3!kt1>3log@1$1$0>1a$5>1w$2>1v$4>0@3$8$0@3$3^3^2^1^4@3$6@1$7^5^4^3").
Proof.
  induction log as [|[a0 w0 v0] older IH]; intros a w v Hin; [destruct Hin|].
  cbn [log_hulls]. destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->.
    ndestruct (hull_add_new (log_hulls older) (a_base a) (a_off a) (a_off a + Z.of_nat w)) as (lo1 & hi1 & H1 & H2 & H3).
    exists lo1, hi1. split; [exact H1|]. lia.
  - ndestruct (IH a w v Hin) as (lo & hi & H1 & H2 & H3).
    destruct (hull_add_old (log_hulls older) (a_base a0) (a_off a0) (a_off a0 + Z.of_nat w0) _ _ _ H1) as (lo1 & hi1 & G1 & G2 & G3).
    exists lo1, hi1. split; [exact G1|]. lia.
Qed.

Lemma cold_ok_in : ltac2:(zQ "c0!kgb!hq0!hva!ki0!hp3!l9!ikf!ta!jr1!lg0!lg8!kt1>2fk@1$5$8>2hs@1$5@2$0@2$0@2$0$2$1$1$3>2kb$2>2kk$1>2kl$2>1h@2$0@2$0@2$0$2$1$1$3>0@3$7$4@5$a^6^5^4^3^2$6>0@3$b@2$0@2$0@2$0$2$1$1$3^2^6@3$7$4@5$9^8^3^6^5^4$6").
Proof.
  induction hs as [|h0 rest IH]; intros kb kk kl h Hc Hin; [destruct Hin|].
  cbn [cold_ok] in Hc. apply andb_prop in Hc as [H0 Hr].
  destruct Hin as [<-|Hin]; [exact H0 | exact (IH _ _ _ _ Hr Hin)].
Qed.

Lemma log_flat_in : ltac2:(zQ "d0!hia!l9!hpa!kr8!li6!kuc!hi4!hva!ih1!lic!kp5!kt1!kt7>1E$6>3log@1$1$0>1a$8>1w$2>1v$7>0@2$a^5^4>0@3$b$0@3$5^4^3^2^5@2$3@2$4^4N8@3$9^7^5@1$c^4").
Proof.
  induction log as [|[a0 w0 v0] older IH]; intros a w v Hlf Hin; [destruct Hin|].
  cbn [log_flat] in Hlf. ndestruct Hlf as (Hw8 & Hfa & Hlf').
  destruct Hin as [Heq|Hin]; [injection Heq as -> -> ->; auto | exact (IH _ _ _ Hlf' Hin)].
Qed.

(* [comment removed for export] *)
Lemma cold_ok_sound : ltac2:(zQ "hb0!lj4!hva!l9!h9!lje!hia!ki8!ksb!jc!hp3!hpa!m0!ikf!ta!lk3!hq0!kuc!hi4!jr1!ih1!lk8!koa!kp5!lg8!ll1!kt1!kt7>1E$h1>2M0>0@1$8@1$3#k0@1$b@1$8@1$3#8>2fk@1$2$h2>3log@1$2$5>2kb$1>2kk$f>2kl$1>1a$h3>1w$a>1v$1>0@4$h5?4segs^a^9^8>0@2$h6^b^8>0@3$d$9@5$h7^a@2$h8^a^9^8^7^6$c>0@3$h9$5@3$h0^6^5^4^a@2$e@2$7@2$6@2$0^e^7@1$ha^6@2$0^e@2$4^a^9@2$7@2$6@2$0^e@2$4^a^9@2$h4^e^8@2$0^e^7").
Proof.
  intros E M0 fk log kb kk kl a w v Hfk Hlf Hc Hin.
  ndestruct (log_hulls_cover log a w v Hin) as (lo & hi & H1 & H2 & H3).
  destruct (log_flat_in E log a w v Hlf Hin) as [Hw8 Hfa].
  assert (Hm : In (a_base a, lo, hi - lo, mk_sprep fk (a_base a) lo (ELit (hi - lo))) (mk_hulls fk log)).
  { unfold mk_hulls. apply in_map_iff. exists (a_base a, lo, hi). split; [reflexivity | exact H1]. }
  pose proof (cold_ok_in fk _ kb kk kl _ Hc Hm) as T. unfold cold1 in T.
  apply andb_prop in T as [Tn T]. apply andb_prop in Tn as [Tn0 Tn1]. apply Z.leb_le in Tn0. apply Z.ltb_lt in Tn1.
  unfold two64 in Tn1.
  destruct (expr_eqb kb (a_base a)) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst kb.
    destruct kl as [l| | | | | | |]; try discriminate.
    rewrite zlit64_eq in T. unfold elenZ. cbn [edenot]. rewrite u_lit64.
    unfold estart. cbn [a_base a_off].
    apply orb_prop in T as [T|T]; apply Z.leb_le in T; lia.
  - rewrite ranges_apart_p_eq in T.
    pose proof (ranges_apart_x_sound segs E M0 fk _ _ _ _ _ _ Hfk T) as D.
    rewrite elenZ_lit in D. rewrite Z.mod_small in D by lia.
    unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cold_kentry_ok : ltac2:(zQ "ha0!hva!ih1!lj4!m0!kgb!h9!hia!llc!ki8!ksb!jc!jm5!l9!hpa!kh2!ta!lk3!kuc!hi4!jr1!lk8!kp5!hnf!lm9!kt1!kt7>1E$h2>4base>0@1$a@1$5#k0@1$3@1$a@1$5#8>3log@1$c$6>1K$h3>2ka$1>2kl$0>0@3$f@1$3@2$4$1$0@1$h7^3@2$b@2$4$1$0@4$e$1$0^2^1>0@2$h5^7^5>0>1a$1>1w$d>1v$0>0@3$h8$6@3$h1^3^2^1^9@2$h0@2$9@2$8@2$2^c^4@1$h9^3@2$2^c^8@2$9@2$8@2$2^c^8@2$h4^c^7@2$2^c^4>0@4$7?4segs^9^8^6@4$7?4segs^a@3$h6^a^9^8^7").
Proof.
  intros E base log K ka kl Hsp. induction log as [|[a w v] older IH]; intros Hlf Hdis HK; [exact HK|].
  cbn [log_flat] in Hlf. ndestruct Hlf as (Hw8 & Hfa & Hlf').
  cbn [mem_denot].
  assert (HK' : kentry_ok segs E (mem_denot E base older) K).
  { apply IH; [exact Hlf' | | exact HK]. intros a' w' v' Hin. apply (Hdis a' w' v'). right. exact Hin. }
  eapply kentry_ok_frame with (ka := ka) (kl := kl); [exact Hfa | exact HK' | | apply (Hdis a w v); left; reflexivity].
  destruct K as [a0 w0 v0|a0 n0|a0 n0 bk|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|a0 n0 fc|a0 n0];
    cbn [kspan] in Hsp; try discriminate; injection Hsp as <- <-; auto.
  cbn [kentry_ok] in HK'. destruct HK' as (Hw0 & _). auto.
Qed.

Lemma ksplit_hot : ltac2:(zQ "90!jr1!l9!kgb!hq0!kt1!ln1!hva!ki0!ln7>2fk@1$1$0>2hs@1$1@2$2@2$2@2$2$6$3$3$7>2kn@1$1$0>1K$0>0@3$4$0^1@3$5@1$1$0@1$1$0@3$8^4^3^2@3$4$0^2^3").
Proof.
  induction kn as [|K0 rest IH]; intros K Hin; [destruct Hin|].
  cbn [ksplit] in Hin. destruct (ksplit fk hs rest) as [hot cold] eqn:Hks. cbn [fst] in IH.
  destruct (kspan K0) as [[a kl]|]; [destruct (cold_ok fk hs (a_base a) (a_off a) kl)|]; cbn [fst] in Hin.
  - right. exact (IH _ Hin).
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH _ Hin)].
  - destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH _ Hin)].
Qed.

Lemma ksplit_cold : ltac2:(zQ "h60!jr1!hva!l9!kgb!ih1!kr8!ta!kre!hq0!kt1!jm5!hp3!m0!kh2!lo0!ikf!ig8!ks3!ki0!lg8!lm9!ln7>2fk@1$2$0>2hs@1$2@2$3@2$3@2$3$1$8$8$h2>2kn@1$2$0>1K$0>0@3$9$0^1@3$e@1$2$0@1$2$0@3$h5^4^3^2@2$5@3$9$0^2^3@2$7$4\1a$4@2$7$1\2kl$1@2$5@3$6@1$c@2$3$4$1@1$h4^4@2$a@2$3$4$1@4$d$4$1^2^1@3$6$b@5$h3^7^6@1$h0^2@1$h1^2^1$f").
Proof.
  induction kn as [|K0 rest IH]; intros K Hin; [destruct Hin|].
  cbn [ksplit] in Hin. destruct (ksplit fk hs rest) as [hot cold] eqn:Hks. cbn [snd] in IH.
  destruct (kspan K0) as [[a kl]|] eqn:Hsp; [destruct (cold_ok fk hs (a_base a) (a_off a) kl) eqn:Hc|]; cbn [snd] in Hin.
  - destruct Hin as [<-|Hin].
    + split; [left; reflexivity|]. exists a, kl. auto.
    + destruct (IH _ Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
  - destruct (IH _ Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
  - destruct (IH _ Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Theorem carry2_sound : ltac2:(zQ "h11!l9!jr1!hp3!h9!knf!jc!kgb!m0!kh2!koa!ta!hi4!hia!kp5!hnf!kq1!lo6&>0@1$5@1$3#k0@1$7@1$5@1$3#8>1E$b>7anybase~0>4base~0>3log@1$0$c>2kn@1$0$1>5hints@1$0$2>3kn'@1$0$1>3scs@1$0$4>3hs'@1$0$2>0@3$a@2$6@2$6@1$0$1@1$0$4@1$0$2@3$h0^6^5^4@4$8@2$6@1$0$1@1$0$4@1$0$2@4$8@1$0$1@1$0$4^3^2^1>0@2$d^a^7>0@4$9?4segs^b^9^7>0@4$f?4segs^b^c^5@4$9?4segs^d@3$e^d^b^a^7").
Proof.
  intros E anyb base log kn hints kn' scs hs' Hc Hlf Hkn Hscs.
  destruct log as [|s older] eqn:Hlog.
  { cbn in Hc. injection Hc as <- <- <-. exact Hkn. }
  rewrite <- Hlog in *. clear s older Hlog.
  unfold carry2 in Hc.
  destruct log as [|s0 older0]; [cbn in Hc; injection Hc as <- <- <-; exact Hkn|].
  set (log := s0 :: older0) in *.
  set (fk := facts_of kn) in Hc. set (hs := mk_hulls fk log) in Hc.
  destruct (ksplit fk hs kn) as [hot cold] eqn:Hks.
  destruct (carry_f fk log hot hints) as [[kn1 scs1] hs1] eqn:Hcf.
  injection Hc as <- <- <-.
  assert (Hfk : know_ok segs E base fk) by (subst fk; apply facts_of_ok; exact Hkn).
  apply Forall_app. split.
  - eapply carry_f_sound; [exact Hcf | exact Hfk | exact Hlf | | exact Hscs].
    apply Forall_forall. intros K HK. apply (proj1 (Forall_forall _ _) Hkn).
    apply (ksplit_hot fk hs). rewrite Hks. exact HK.
  - apply Forall_forall. intros K HK.
    assert (HK2 : In K (snd (ksplit fk hs kn))) by (rewrite Hks; exact HK).
    ndestruct (ksplit_cold fk hs kn K HK2) as (Hin & a & kl & Hsp & Hcold).
    eapply cold_kentry_ok; [exact Hsp | exact Hlf | | exact (proj1 (Forall_forall _ _) Hkn K Hin)].
    intros a' w' v' Hin'. destruct a as [kb kk]. cbn [a_base a_off] in Hcold.
    eapply cold_ok_sound; [exact Hfk | exact Hlf | exact Hcold | exact Hin'].
Qed.


(* [comment removed for export] *)
Definition nosp : ltac2:(zQ "30!hp3!jr1!ih1>2wa$2>1K$1$0") := ltac2:(zQ "d6!hva!ih1!hq0!hp3!is5!hpa!ig8!ikf!kj5!jr1!lof!jl3!jlc&\2kb$0\5a_off$2@2$8^2@1$6^7&M1\1a$1$3^3~0&\2kb$0\5a_off$2@2$8^2@1$6^6&M1\1a$1$3^2~2&\1n$0~3&\1a$1~4\2wa$1\1K$9M9\1K$9$3^1\1a$1\1w$5\1v$0~1~5\1a$1\1n$0\1k$5~1\2lo$2\2hi$2M0\1x$0$3@1$6^4\1z$2M2\1z$2$3^1$7\1p$a$4\1p$a$4\1n$5$4\2op$b\1a$0\1b$0$4\2op$b\1a$0\1b$0$4\2op$c\1a$0\1b$0$4\2op$c\1a$0\1b$0$4\2sx$3\2lo$5\1n$5\1e$0$4\2sx$3\1k$5\1i$2\1n$5$4\1e$0\1m$2$7\1e$0\2lo$2\2hi$2$7\1a$1\1n$0$7\2a1$1\2n1$0\2a2$1\2n2$0$7\1a$1\1n$0\1c$2~1~5").
Lemma prune1pc_sp_irrel : ltac2:(zQ "f0!l9!hp3!kgb!jr1!ta!hq0!lp9!ki0!hpa!m0!ikf!hva!ih1!knf!lq4>5allkn@1$0$3>3sp1$7>3sp2$7>2wa$c>1w$8>2wv$b>1K$3>5hints@1$0$1>3br2@1$9@2$2$5$5>0@3$4$1@2$e^6^3$a@3$4@2$2@2$2@1$0$3@1$0$d@1$0$1@8$6^a^9^7^6^5^4^3^2@8$6^a^8^7^6^5^4^3^2").
Proof.
  intros allkn sp1 sp2 [wb wk] w wv K hints br2 H.
  destruct K as [[kb kk] w2 v|[kb kk] len|[kb kk] len bk|ilo ihi|e m|e elo ehi|[kb kk] len|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [nosp a_base] in H;
    unfold prune1pc; cbn [a_base a_off]; try reflexivity.
  - unfold prune1p; cbn [a_base a_off]. rewrite H. reflexivity.
  - rewrite H. unfold prune1p; cbn [a_base a_off]. unfold prune_zf. rewrite H. reflexivity.
  - rewrite H. unfold prune1p; cbn [a_base a_off]. rewrite H. reflexivity.
  - unfold prune1p; cbn [a_base a_off]. destruct wb as [z| | | | | | |]; try discriminate. destruct z; try discriminate. reflexivity.
  - rewrite H. unfold prune1p; cbn [a_base a_off]. unfold prune_zf. rewrite H. reflexivity.
  - rewrite H. unfold prune1p; cbn [a_base a_off]. unfold prune_zf. rewrite H. reflexivity.
Qed.
Lemma prunepc_sp_irrel : ltac2:(zQ "h00!l9!kgb!jr1!hp3!ta!hq0!hva!lqb!ki0!hpa!m0!ikf!ih1!knf!lq4!ijb>5allkn@1$0$2>3sp1$8>3sp2$8>2wa$c>1w$9>2wv$6>2kn@1$0$2>5hints@1$0$3>5cache@1$0@2$1$6@1$a@2$1$5$5>0@3$4$3@3$f$2@1$e^6^3$b@3$4@2$1@2$1@1$0$2@1$0$d@1$0$3@8$7^a^9^7^6^5^4^3^2@8$7^a^8^7^6^5^4^3^2").
Proof.
  intros allkn sp1 sp2 wa w wv kn. induction kn as [|K rest IH]; intros hints cache H; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [HK Hr]. cbn [prunepc].
  destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache2].
  rewrite (prune1pc_sp_irrel allkn sp1 sp2 wa w wv K hints br2 HK).
  destruct (prune1pc allkn sp2 wa w wv K hints br2) as [[kept scs1] hs1].
  rewrite (IH hs1 cache2 Hr). reflexivity.
Qed.
Definition SP0 : ltac2:(zQ "10!ki0$0") := ltac2:(zQ "70!kgb!hq0!ji8!jra!hva!ih1!lr5@4$6@1$2@2$0$1$1@1$2$1@1$3@2$0$5$4@1$3@2$0$5$4").
Fixpoint carry_fL (fk : list kentry) (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let (p1, hs1) := carry_fL fk older kn hints in let (kn1, scs1) := p1 in
      let sp := if forallb (nosp a) kn1 then SP0 else mk_sprep fk (a_base a) (a_off a) (elen w) in
      let (p2, hs2) := prunepc fk sp a w v kn1 hs1 [] in let (kn2, scs2) := p2 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma carry_fL_eq : ltac2:(zQ "90!l9!jr1!hp3!kgb!ta!hia!knf!kqe!lrd>2fk@1$0$1>3log@1$0$5>2kn@1$0$1>5hints@1$0$2@3$4@2$3@2$3@1$0$1@1$0$6@1$0$2@4$8^4^3^2^1@4$7^4^3^2^1").
Proof.
  intros fk log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry_fL carry_f]. rewrite IH. destruct (carry_f fk older kn hints) as [[kn1 scs1] hs1].
  destruct (forallb (nosp a) kn1) eqn:Hn.
  - rewrite (prunepc_sp_irrel fk SP0 (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] Hn).
    destruct (prunepc fk _ a w v kn1 hs1 []) as [[kn2 scs2] hs2]. reflexivity.
  - destruct (prunepc fk _ a w v kn1 hs1 []) as [[kn2 scs2] hs2]. reflexivity.
Qed.
Definition carry2L (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | _ =>
      let fk := facts_of kn in
      let hs := mk_hulls fk log in
      let '(hot, cold) := ksplit fk hs kn in
      let '(kn', scs, hs') := carry_fL fk log hot hints in
      (kn' ++ cold, scs, hs')
  end.
Lemma carry2L_eq : ltac2:(zQ "90!l9!hp3!kgb!jr1!ta!hia!knf!lo6!ls8>3log@1$0$5>2kn@1$0$3>5hints@1$0$1@3$4@2$2@2$2@1$0$3@1$0$6@1$0$1@3$8^3^2^1@3$7^3^2^1").
Proof.
  intros log kn hints. destruct log as [|e l]; [reflexivity|]. unfold carry2L, carry2. cbv zeta.
  destruct (ksplit _ _ kn) as [hot cold]. rewrite carry_fL_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint prunepcF (allkn : list kentry) (spt : unit -> sprep) (rng : option (Z * Z)) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry)
  (hints : list bool) (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      match match K with
            | KWord (SA kb kk) w' v =>
                if expr_eqb kb (a_base wa) then
                  Some (if Z.leb (kk + Z.of_nat w') (a_off wa) then [K]
                        else if Z.leb (a_off wa + Z.of_nat w) kk then [K]
                        else kword_cut kb kk w' v (a_off wa) w)
                else None
            | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => Some [K]   (* [comment removed for export] *)
            | KImg lo hi =>   (* [comment removed for export] *)
                match a_base wa with
                | ELit 0 => None
                | _ => if Z.ltb (hi - lo) two64 then
                         match rng with
                         | Some (lo1, hi1) =>
                             if (if Z.leb (hi1 + a_off wa + zlit64 (Z.of_nat w)) (0 + lo) then true
                                 else Z.leb (0 + lo + zlit64 (hi - lo)) (lo1 + a_off wa)) then Some [K] else None
                         | None => None
                         end
                       else None
                end
            | _ => None
            end with
      | Some kept => let '(r, scs2, hs2) := prunepcF allkn spt rng wa w wv rest hints cache in (kept ++ r, scs2, hs2)
      | None =>
          let '(br2, cache') :=
            match kbase K with
            | Some kb => match br_lookup cache kb with
                         | Some r => (r, cache)
                         | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                         end
            | None => (None, cache)
            end in
          let sp := if nosp wa K then SP0 else spt tt in   (* [comment removed for export] *)
          let '(kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2 in
          let '(r, scs2, hs2) := prunepcF allkn spt rng wa w wv rest hs1 cache' in
          (kept ++ r, scs1 ++ scs2, hs2)
      end
  end.
Lemma zmod_0_two64 : ltac2:(zQ "40!ta!hq0!jmc!jq7@3$0$1@2$3Z$2Z"). Proof. reflexivity. Qed.
Lemma prunepcF_eqp : ltac2:(zQ "h40!hq0!l9!kgb!m0!ta!jr1!ki0!hp3!ig8!lt2!hva!hpa!ltf!lu4!lub!ih1!knf!lv4!lvd!mgc>5allkn@1$1$5>3spt>1x$d$6>3rng@1$3@2$2$0$0>2sp$6>2wa$f>1w$b>2wv$a>2kn@1$1$5>5hints@1$1$7>5cache@1$1@2$2$a@1$3@2$2$0$0>0@3$4$6@1^9$c^7>0@3$4@1$3@2$2$0$0@1$h1^8@2$9^b@1$8^7>0@3$4@1$3@2$2$0$0^a@2$9^c@1$8^8>0@2$h2^d^4@3$4@2$2@2$2@1$1$5@1$1$h0@1$1$7@9$h3^e^d^c^a^9^8^7^6^5@7$e^e^b^a^9^8^7^6").
Proof.
  intros allkn spt rng sp wa w wv kn hints cache Hsp Hrng Hr. revert hints cache. subst rng.
  induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
  cbn [prunepcF prunep]. rewrite Hsp.
  assert (NOSP : forall br2, prune1pc allkn (if nosp wa K then SP0 else sp) wa w wv K hints br2 = prune1pc allkn sp wa w wv K hints br2).
  { intros br2. destruct (nosp wa K) eqn:HN; [|reflexivity]. apply prune1pc_sp_irrel. exact HN. }
  assert (SLOW : (let '(br2, cache') := match kbase K with
                                      | Some kb => match br_lookup cache kb with
                                                   | Some r => (r, cache)
                                                   | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                                                   end
                                      | None => (None, cache)
                                      end in
                 let sp0 := if nosp wa K then SP0 else sp in
                 let '(kept, scs1, hs1) := prune1pc allkn sp0 wa w wv K hints br2 in
                 let '(r, scs2, hs2) := prunepcF allkn spt (base_range allkn (a_base wa)) wa w wv rest hs1 cache' in
                 (kept ++ r, scs1 ++ scs2, hs2))
                = (let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
                   let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
                   (kept ++ r, scs1 ++ scs2, hs2))).
  { destruct (kbase K) as [kb|] eqn:HK.
    - destruct (br_lookup cache kb) as [r|] eqn:HL; cbv beta iota zeta; rewrite NOSP.
      + rewrite (AX2S.prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (AX2S.br_lookup_ok _ _ _ _ Hc HL)).
        destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
      + rewrite (AX2S.prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
        destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
        rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
    - cbv beta iota zeta. rewrite NOSP. rewrite (AX2S.prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
      destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity. }
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
    try exact SLOW;
    (* [comment removed for export] *)
    try (cbn [prune1p]; rewrite (IH hints cache Hc); destruct (prunep allkn sp wa w wv rest hints) as [[r scs2] hs2]; reflexivity).
  - (* [comment removed for export] *)
    destruct (expr_eqb kb (a_base wa)) eqn:HE; [|exact SLOW]. clear SLOW.
    unfold prune1p. cbv zeta. rewrite HE.
    destruct (Z.leb (kk + Z.of_nat w') (a_off wa)), (Z.leb (a_off wa + Z.of_nat w) kk); cbv beta iota zeta delta [orb];
      rewrite (IH hints cache Hc); destruct (prunep allkn sp wa w wv rest hints) as [[r scs2] hs2]; reflexivity.
  - (* [comment removed for export] *)
    destruct wa as [wb wk]. cbn [a_base a_off] in *.
    assert (T64 : two64 = 2 ^ 64) by reflexivity.
    assert (APART : forall lo1 hi1, base_range allkn wb = Some (lo1, hi1) ->
              (if Z.leb (hi1 + wk + zlit64 (Z.of_nat w)) (0 + lo) then true else Z.leb (0 + lo + zlit64 (hi - lo)) (lo1 + wk)) = true ->
              ranges_apart_p allkn sp wb wk (elen w) (ELit 0) lo (ELit (hi - lo)) = true).
    { intros lo1 hi1 HB HT. unfold ranges_apart_p, elen. rewrite Hrng, HB. cbn [base_range]. rewrite zmod_0_two64.
      destruct (Z.leb (hi1 + wk + zlit64 (Z.of_nat w)) (0 + lo)) eqn:E1.
      - cbn [orb]. reflexivity.
      - rewrite HT. cbn [orb]. reflexivity. }
    destruct wb as [z| | | | | | |]; try (destruct z); rewrite ?T64;
      try exact SLOW;
      (destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:HL; [|exact SLOW]);
      (destruct (base_range allkn _) as [[lo1 hi1]|] eqn:HB; [|exact SLOW]);
      (destruct (if Z.leb (hi1 + wk + zlit64 (Z.of_nat w)) (0 + lo) then true else Z.leb (0 + lo + zlit64 (hi - lo)) (lo1 + wk)) eqn:HT; [|exact SLOW]);
      clear SLOW; unfold prune1p; cbv zeta; cbn [a_base a_off]; rewrite HL, (APART lo1 hi1 eq_refl HT);
      rewrite (IH hints cache Hc); destruct (prunep allkn sp _ w wv rest hints) as [[r scs2] hs2]; reflexivity.
Qed.
Lemma prunepcF_eq : ltac2:(zQ "h20!l9!kgb!hva!hq0!jr1!hp3!jra!m0!ta!km8!hpa!lu4!ig8!lt2!lqb!ih1!knf!mgc>5allkn@1$0$4>1b$2>1k$3>1n$2>2wa$f>1w$a>2wv$2>2kn@1$0$4>5hints@1$0$5>0@3$8$2^8@1$c^5@3$8@2$1@2$1@1$0$4@1$0$h0@1$0$5@9$h1^a\0$b@4$9^b^a^9^8@2$d^a^9^6^5^4^3^2@1$6@2$1$2@1$7@2$1$3$3@8$e^a@4$9^a^9^8^7^6^5^4^3^2@1$6@2$1$2@1$7@2$1$3$3").
Proof.
  intros allkn b k n wa w wv kn hints ->.
  rewrite (prunepcF_eqp allkn _ _ (mk_sprep allkn (a_base wa) k n) wa w wv kn hints [] eq_refl eq_refl eq_refl ltac:(constructor)).
  rewrite (AX2S.prunepc_eq _ _ _ _ _ _ _ [] ltac:(constructor)). reflexivity.
Qed.

Fixpoint carry_fF (fk : list kentry) (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let (p1, hs1) := carry_fF fk older kn hints in let (kn1, scs1) := p1 in
      let spt := fun _ : unit => mk_sprep fk (a_base a) (a_off a) (elen w) in   (* [comment removed for export] *)
      let (p2, hs2) := prunepcF fk spt (base_range fk (a_base a)) a w v kn1 hs1 [] in let (kn2, scs2) := p2 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
Lemma carry_fF_eq : ltac2:(zQ "90!l9!jr1!hp3!kgb!ta!hia!knf!mh7!lrd>2fk@1$0$1>3log@1$0$5>2kn@1$0$1>5hints@1$0$2@3$4@2$3@2$3@1$0$1@1$0$6@1$0$2@4$7^4^3^2^1@4$8^4^3^2^1").
Proof.
  intros fk log kn hints. rewrite carry_fL_eq. induction log as [|[a w v] older IH]; [reflexivity|].
  cbn [carry_fF carry_f]. rewrite IH. destruct (carry_f fk older kn hints) as [[kn1 scs1] hs1].
  rewrite (prunepcF_eq fk (a_base a) (a_off a) (elen w) a w v kn1 hs1 eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Definition cold1c : ltac2:(zQ "80!hq0!kgb!hva!hp3!l9!m0!jr1!ki0>2fk@1$4$6>1h@2$1@2$1@2$1$2$0$0$7>2kb$2>2kk$0>2kl$2>3br2@1$5@2$1$0$0$3") := ltac2:(zQ "h60!hva!hq0!kgb!hp3!is5!hpa!ki0!jp9!ig1!jl3!jlc!ki8!l9!m0!kif!ji1!kj5!jr1!mi2!jmc!kl1!jq0\2fk@1$c$h1\1h@2$2@2$2@2$2$0$1$1$6\2kb$0\2kk$1\2kl$0\3br2@1$d@2$2$1$1M2\1h@2$2@2$2@2$2$0$1$1$6$3^5\1p@2$2@2$2$0$1$1\2sp$6M2\1p@2$2@2$2$0$1$1$3^2\2p0@2$2$0$1\1n$1M2\2p0@2$2$0$1$3^2\1b$0\2lo$1@2$8@2$8@2$7Z^3@2$h5^3$h3M3\0$3$3@2$h0^a^2M0\2kl$0$3^8\1l$1@2$e@2$7@2$b^a@1$h4^1^2@2$7@2$b^2^4^a\2n0$5$4\2op$9\1a$0\2b0$0$4\2op$9\1a$0\2b0$0$4\2op$a\1a$0\2b0$0$4\2op$a\1a$0\2b0$0$4\2sx$3\3lo0$5\2n0$5\1e$0$4\2sx$3\1k$5\1i$1\2n0$5$4@9$h2^c^5^2^1@1$f^3^7^a^9^8").
Fixpoint cold_okc (fk : list kentry) (hs : list (expr * Z * Z * sprep)) (kb : expr) (kk : Z) (kl : expr) (br2 : option (Z * Z)) : bool :=
  match hs with
  | [] => true
  | h :: rest => (cold1c fk h kb kk kl br2 && cold_okc fk rest kb kk kl br2)%bool
  end.
Lemma cold_okc_eq : ltac2:(zQ "b0!kgb!hq0!hva!l9!hp3!ta!lt2!jr1!ki0!lg8!mj4>2fk@1$3$7>2hs@1$3@2$0@2$0@2$0$2$1$1$8>2kb$2>2kk$1>2kl$2@3$5$4@6$a^5^4^3^2^1@2$6^5^3@5$9^5^4^3^2^1").
Proof.
  intros fk hs kb kk kl. induction hs as [|[[[b lo] n] sp] rest IH]; [reflexivity|].
  cbn [cold_okc cold_ok cold1c cold1]. rewrite IH, AX2S.ranges_apart_pc_eq. reflexivity.
Qed.
Fixpoint ksplitc (fk : list kentry) (hs : list (expr * Z * Z * sprep)) (kn : list kentry) (cache : list (expr * option (Z * Z)))
  : list kentry * list kentry :=
  match kn with
  | [] => ([], [])
  | K :: rest =>
      match kspan K with
      | Some (a, kl) =>
          let kb := a_base a in
          let '(br2, cache') := match br_lookup cache kb with
                                | Some r => (r, cache)
                                | None => let r := base_range fk kb in (r, (kb, r) :: cache)
                                end in
          let '(hot, cold) := ksplitc fk hs rest cache' in
          if cold_okc fk hs kb (a_off a) kl br2 then (hot, K :: cold) else (K :: hot, cold)
      | None => let '(hot, cold) := ksplitc fk hs rest cache in (K :: hot, cold)
      end
  end.
Lemma ksplitc_eq : ltac2:(zQ "b0!l9!kgb!hq0!jr1!hva!m0!ta!ki0!lvd!ln7!mjf>2fk@1$0$3>2hs@1$0@2$1@2$1@2$1$4$2$2$7>2kn@1$0$3>5cache@1$0@2$1$4@1$5@2$1$2$2>0@2$8^4^1@3$6@2$1@1$0$3@1$0$3@4$a^5^4^3^2@3$9^5^4^3").
Proof.
  intros fk hs kn. induction kn as [|K rest IH]; intros cache Hc; [reflexivity|].
  cbn [ksplitc ksplit]. destruct (kspan K) as [[a kl]|].
  - destruct (br_lookup cache (a_base a)) as [r|] eqn:HL; cbv beta iota zeta.
    + rewrite (IH cache Hc). rewrite (AX2S.br_lookup_ok _ _ _ _ Hc HL), cold_okc_eq. reflexivity.
    + rewrite (IH ((a_base a, base_range fk (a_base a)) :: cache)) by (constructor; [reflexivity | exact Hc]).
      rewrite cold_okc_eq. reflexivity.
  - rewrite (IH cache Hc). reflexivity.
Qed.

Definition carry2F (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | _ =>
      let fk := facts_of kn in
      let hs := mk_hulls fk log in
      let '(hot, cold) := ksplitc fk hs kn [] in
      let '(kn', scs, hs') := carry_fF fk log hot hints in
      (kn' ++ cold, scs, hs')
  end.
Lemma carry2F_eq : ltac2:(zQ "90!l9!hp3!kgb!jr1!ta!hia!knf!mk9!ls8>3log@1$0$5>2kn@1$0$3>5hints@1$0$1@3$4@2$2@2$2@1$0$3@1$0$6@1$0$1@3$7^3^2^1@3$8^3^2^1").
Proof.
  intros log kn hints. destruct log as [|e l]; [reflexivity|]. unfold carry2F, carry2L. cbv zeta.
  rewrite (ksplitc_eq _ _ kn [] ltac:(constructor)). destruct (ksplit _ _ kn) as [hot cold]. rewrite carry_fF_eq. reflexivity.
Qed.

Definition step_block : ltac2:(zQ "60!l9!ir0!r9!m0!kgb!hq0>5stops@1$0$5>2ss$1>1w@1$0$2@1$3@2$4$1@1$0$2") := ltac2:(zQ "hd0!l9!kgb!ir0!r9!knf!jr1!hp3!m0!iu9!ji8!jra!iv2!jm5!s0!kh2!ikf!hq0!mp4!jvc!mq5!irc!mr0!iva!ih1!hia!mve!ng8!mk9!hoc\5stops@1$0$h0\2ss$2\1w@1$0$3=3ss'$2@9$h1?4segs@1$ha@1$h3@1$8^2@1$h9@1$8^2?2ITN0?5BFUEL$f^3^2M1\1x@2$1@2$1@1$0$5@1$0$4@1$0$6@1$7@2$1$2@1$0$3@3$hb@1$b^1@1$8^1@1$a$6\1p@2$1@1$0$5@1$0$4\1l@1$0$6M1\1p@2$1@1$0$5@1$0$4@1$7@2$1$2@1$0$3^2\3kn'@1$0$5\2l0@1$0$4M0\2l0@1$0$4@1$7@2$1$2@1$0$3^1@2$c@2$1$2@1$0$3@4$e$2@1$0$3@6$h2@1$h5^5@1$h6^5@1$a$h8^2@1$h4^5@1$9$h7@3$d$3@1$hc@1$b^5^6\1s$4\2l1@1$0$4@1$9@2$1$2@1$0$3").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cw_keep : ltac2:(zQ "40!hq0!hp3!hva!jr1>2sb$2>2lo$0>2hi$0>1K$3$1") := ltac2:(zQ "h32!hva!hp3!hq0!hpa!ikf!ih1!is5!jl3!jlc!jp9!kj5!nh0!kif!jr1!ki8!lof!jq7!nh7!kt7&\2sx$1\3lo0$3\2n0$3\1e$0$4&\2sx$1\1k$3\1i$2\2n0$3$4\2sb$0\2lo$2\2hi$2\1K$dMd\1K$d$1^1\1a$5\1w$3\1v$0M5\1a$5$1^3\2kb$0\2kk$2M1\0$1$1@2$a^9^2@1$b@2$c@2$9@2$e^1@1$h2^4^8@2$9^7^1$6\1a$5\1n$0M5\1a$5$1^2\2kb$0\2kk$2M0\1n$0$1^3\2l0$2M1\0$1$1@2$a^9^3@1$b@2$c@2$9@2$e^2@2$h0^1@2$h1+2+k0^8@2$9^7^2$4\2n0$3$4\2op$7\2a0$0\1b$0$4\2op$7\2a0$0\1b$0$4\2op$8\2a0$0\1b$0$4\2op$8\2a0$0\1b$0$4~0~1\1a$5\1n$0\1k$3M5\1a$5$1^3\2kb$0\5a_off$2@2$a^9^2\3lo0$2\3hi0$2M0\2sb$0$1^6\1z$2M2\1z$2$1^1$4\1p$f$6\1p$f$6\1n$3$6\2op$7\1a$0\1b$0$6\2op$7\1a$0\1b$0$6\2op$8\1a$0\1b$0$6\2op$8\1a$0\1b$0$6\2sx$1\3lo0$3\1n$3\1e$0$6\2sx$1\1k$3\1i$2\1n$3$6\1e$0\1m$2$6\1e$0\3lo0$2\3hi0$2$6\1a$5\1n$0$6\2a1$5\2n1$0\2a2$5\2n2$0$6\1a$5\1n$0\1c$2M5\1a$5$1^3\2kb$0\2kk$2M0\1n$0$1^4\2l0$2M1\0$1$1@2$a^a^3@1$b@2$c@2$9@2$e^2@2$h0^1@2$h1+2+k0^9@2$9^8^2$4\2n0$3$4\2op$7\2a0$0\1b$0$4\2op$7\2a0$0\1b$0$4\2op$8\2a0$0\1b$0$4\2op$8\2a0$0\1b$0$4~0~1\1a$5\1n$0$6").

Lemma cw_walk : ltac2:(zQ "h10!hp3!l9!hq0!jr1!jra!nhe!ksb!hpa!ta!nie!hva!nj4!knf!njb!nk5!ki8!kt7>5allkn@1$1$3>2sb$a>2lo$2>2hi$2>2kn@1$1$3>2rk$2>1n$7>2sx$0>3acc@1$1$c>0@2$6^7^4>0@2$6@2$f^5@1$h0^4^7>0@2$9N0^5@3$8$b@9$5^c?4segs^8^b^7^6^5@1$4$0^4@9$5^c?4segs@3$e$3@3$d^b^a^9^8^b^7^6^5@1$4$0^4").
Proof.
  intros allkn sb lo hi kn. induction kn as [|K rest IH]; intros rk n sx acc Hlo Hhi Hn; [reflexivity|].
  cbn [List.filter]. destruct (cw_keep sb lo hi K) eqn:HK.
  - destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len kb2|ilo ihi|e m|e elo ehi|[kb kk] len|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
      cbn [know_lookupA0]; rewrite <- ?IH by assumption; try reflexivity.
  - destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len kb2|ilo ihi|e m|e elo ehi|[kb kk] len|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
      cbn [know_lookupA0 cw_keep] in *; rewrite <- ?IH by assumption; try reflexivity.
    + unfold rel_lit. destruct (expr_eqb sb kb); [|reflexivity]. cbn [negb orb] in HK.
      destruct (Z.leb (kk + Z.of_nat w) lo) eqn:E1.
      * apply Z.leb_le in E1. destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool eqn:C; [apply andb_prop in C as [_ C]; apply Z.leb_le in C; lia|].
        destruct ((rk + Z.of_nat n <=? kk) || (kk + Z.of_nat w <=? rk))%bool; reflexivity.
      * destruct (Z.leb hi kk) eqn:E2; [apply Z.leb_le in E2|discriminate].
        destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool eqn:C; [apply andb_prop in C as [C _]; apply Z.leb_le in C; lia|].
        destruct ((rk + Z.of_nat n <=? kk) || (kk + Z.of_nat w <=? rk))%bool; reflexivity.
    + destruct len as [l0| | | | | | |]; try discriminate. unfold rel_lit. destruct (expr_eqb sb kb); [|discriminate]. cbn [negb orb] in HK.
      destruct (Z.leb (kk + l0 mod 2 ^ 64) lo) eqn:E1.
      * apply Z.leb_le in E1. destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64))%bool eqn:C; [apply andb_prop in C as [_ C]; apply Z.leb_le in C; lia|].
        destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool eqn:D; [reflexivity|]. apply orb_false_iff in D as [_ D]. apply Z.leb_gt in D. lia.
      * destruct (Z.leb hi kk) eqn:E2; [apply Z.leb_le in E2|discriminate].
        destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64))%bool eqn:C; [apply andb_prop in C as [C _]; apply Z.leb_le in C; lia|].
        destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool eqn:D; [reflexivity|]. apply orb_false_iff in D as [D _]. apply Z.leb_gt in D. lia.
    + rewrite HK. reflexivity.
    + destruct sb as [z| | | | | | |]; try reflexivity. destruct z; [discriminate|reflexivity|reflexivity].
    + destruct len as [l0| | | | | | |]; try discriminate. unfold rel_lit. destruct (expr_eqb sb kb); [|discriminate]. cbn [negb orb] in HK.
      destruct (Z.leb (kk + l0 mod 2 ^ 64) lo) eqn:E1.
      * apply Z.leb_le in E1. destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64))%bool eqn:C; [apply andb_prop in C as [_ C]; apply Z.leb_le in C; lia|].
        destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool eqn:D; [reflexivity|]. apply orb_false_iff in D as [_ D]. apply Z.leb_gt in D. lia.
      * destruct (Z.leb hi kk) eqn:E2; [apply Z.leb_le in E2|discriminate].
        destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + l0 mod 2 ^ 64))%bool eqn:C; [apply andb_prop in C as [C _]; apply Z.leb_le in C; lia|].
        destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool eqn:D; [reflexivity|]. apply orb_false_iff in D as [D _]. apply Z.leb_gt in D. lia.
Qed.

(* [comment removed for export] *)
Definition know_lookupW : ltac2:(zQ "70!l9!jr1!hp3!hpa!hq0!hva!nj4>2kf@1$0$1>1k@1$0$1>2rb$5>2rk$4>1n$3>2sx$2$6") := ltac2:(zQ "h00!l9!hp3!nj4!hq0!knf!jra!m0!nkf!hva!jr1!hpa!nl6!nle!nm7!nhe!nn8\2kf@1$0$9\1k@1$0$9\2rb$8\2rk$3\1n$a\2sx$1M2\1x$2$2@9$e^5?4segs^6^4^3^2^1@1$5$1@1$5$4\1v$8\3scs@1$0$4\5hints@1$0$1@3$7^3^2^1\3acc@1$0$4\5hints@1$0$1M6\1x@1$6@1$0$3$2@5$d?4segs^7^6^5^4\2bs@1$0$3@3$7@3$f^4^5^1^3^2@2$b^2^1$c").
Lemma know_lookupW_eq : ltac2:(zQ "h20!hq0!hp3!jra!jr1!ksb!l9!hpa!ta!nie!hva!no7!nj4!knf!njb!np5!nk5!ki8!kt7>1k@1$5$3>2sb$9>2lo$0>2hi$0>2rk$0>1n$6>2sx$1>0@2$4^5^3>0@2$4@2$h0^4@1$h1^3^5>0@2$8N0^4@3$7$b@6$e@3$f$3@3$d^9^8^7^a^a^9^6^5^4@8$a?4segs^a^9^6^5^4@1$2$1@1$2$c").
Proof.
  intros k sb lo hi rk n sx Hlo Hhi Hn. unfold know_lookupW, know_lookup, know_lookupA.
  rewrite <- (cw_walk k sb lo hi k rk n sx [] Hlo Hhi Hn). reflexivity.
Qed.
Definition kread8eW : ltac2:(zQ "50!l9!hva!jr1!m0!hq0>2kf@1$0$2>1k@1$0$2>1b$1>3off$4@1$3$1") := ltac2:(zQ "c0!l9!hva!knf!ji8!hp3!m0!jr1!nj4!jm5!is5!hq0!np5\2kf@1$0$6\1k@1$0$6\1b$1\3off$aM7\1x$7@1$5$1@6$b^4^3^2^1N8$9\1v$1\3scs@1$0$2\5hints@1$0$4M0\3scs@1$0$2@1$5$1^2@2$8$1^3\1s$2\1l@1$0$2@1$3$1\3scs@1$0$2\5hints@1$0$4@1$3$1@1$3$1").
Definition kreadZW : ltac2:(zQ "60!l9!hq0!jr1!hpa!m0!hva>2kf@1$0$2>1k@1$0$2>1b$5>3off$1>1n$3@1$4$1") := ltac2:(zQ "h10!hq0!hva!ji8!l9!hpa!knf!hp3!m0!jl3!jlc!jr1!nj4!jm5!is5!jmc!np5!jq7\2kf@1$3$a\1k@1$3$a\1b$1\3off$0\1n$4Mb\1x$b@1$7$0@6$f^5^4^3^2^1$d\1v$1\3scs@1$3$5\5hints@1$3$6M1\1v$1@1$7$0^3\1z$0M3\3scs@1$3$5@1$7$0^3@2$c$0@2$h0^1$e\1s$5\1l@1$3$5@1$2$0\2n0$4@1$2$0\2op$8\1a$1\2b0$1@1$2$0\2op$8\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2sx$6\2lo$4\2n0$4\1e$1@1$2$0\2sx$6\2k0$4\1i$0\2n0$4@1$2$0\3scs@1$3$5\5hints@1$3$6@1$2$0@1$2$0").
Fixpoint kread_bytesW (fuel : nat) (kf k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZW kf k b off 1 with
           | Some z => match kread_bytesW f kf k b (off + 1) with Some rest => Some (z :: rest) | None => None end
           | None => None
           end
  end.
Lemma kread8eW_eq : ltac2:(zQ "c0!hq0!hva!jr1!ksb!l9!m0!ta!nq4!njb!nqf!nk5!ki8>1k@1$4$2>2sb$1>2lo$0>2hi$0>3off$0>0@2$3^3^1>0@2$3@2$b^2+8^3@3$6@1$5$1@4$9@3$a$2@3$8^6^5^4^7^7^6^3@4$7?4segs^7^6^3").
Proof. intros. unfold kread8eW, APC.kread8e. rewrite (know_lookupW_eq k sb lo hi off 8 false) by (cbn; lia). reflexivity. Qed.
Lemma kread_bytesW_eq : ltac2:(zQ "e0!hq0!l9!jr1!ksb!hpa!m0!ta!nra!hva!njb!ns9!nk5!ki8!kt7>4fuel$4>1k@1$1$2>2sb$8>2lo$0>2hi$0>3off$0>0@2$3^3^1>0@2$3@2$c^2@1$d^7^3@3$6@1$5@1$1$0@5$a^8@3$b$2@3$9^6^5^4^7^7^6^3@5$7?4segs^8^7^6^3").
Proof.
  intros fuel k sb lo hi. induction fuel as [|f IH]; intros off Hlo Hhi; [reflexivity|].
  cbn [kread_bytesW APC.kread_bytes]. unfold kreadZW, APC.kreadZ.
  rewrite (know_lookupW_eq k sb lo hi off 1 false) by (cbn; lia).
  destruct (know_lookup segs k sb off 1 false [] []) as [[z| | | | | | |] [|? ?] hs|scs hs|]; try reflexivity.
  rewrite IH by lia. destruct (APC.kread_bytes segs f k sb (off + 1)); reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint copy_factsW (fuel : nat) (kf k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      let bytewise := fun u : unit =>
        if Z.leb 1 n then
          match know_lookupW kf k sb sk 1 false with
          | LHit v [] _ => match copy_factsW f kf k sb (sk + 1) db (dk + 1) (n - 1) with Some rest => Some (KWord (SA db dk) 1 v :: rest) | None => None end
          | _ => None
          end
        else Some [] in
      if Z.leb 8 n then
        match (match kread8eW kf k sb sk with
               | Some v => Some v
               | None => match kread_bytesW 8 kf k sb sk with Some bs => Some (ELit (zbytes_le_to_Z bs)) | None => None end
               end) with
        | Some v => match copy_factsW f kf k sb (sk + 8) db (dk + 8) (n - 8) with Some rest => Some (KWord (SA db dk) 8 v :: rest) | None => None end
        | None => bytewise tt
        end
      else bytewise tt
  end.
Lemma copy_factsW_eq : ltac2:(zQ "d0!hq0!jr1!l9!hva!ksb!hpa!m0!ta!nt8!nu6!njb!nk5!ki8>4fuel$5>1k@1$2$1>2sb$3>2lo$0>2hi$0>2sk$0>2db$3>2dk$0>1n$0>0@2$4^6^4>0@2$4@2$c^5^2^6@3$7@1$6@1$2$1@8$9^b@3$b$1@3$a^9^8^7^a^a^9^6^5^4^3@8$8?4segs^b^a^9^6^5^4^3").
Proof.
  intros fuel k sb lo hi. induction fuel as [|f IH]; intros sk db dk n Hlo Hhi; [reflexivity|].
  cbn [copy_factsW APC.copy_facts]. cbv beta.
  destruct (Z.leb 8 n) eqn:H8.
  - apply Z.leb_le in H8. rewrite (kread8eW_eq k sb lo hi sk) by lia. rewrite (kread_bytesW_eq 8 k sb lo hi sk) by (cbn; lia).
    cbn [andb].
    destruct (APC.kread8e segs k sb sk) as [v|] eqn:Hv.
    + rewrite IH by lia. destruct (APC.copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)); reflexivity.
    + destruct (APC.kread_bytes segs 8 k sb sk) as [bs|] eqn:Hbs.
      * rewrite IH by lia. destruct (APC.copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)); reflexivity.
      * destruct (Z.leb 1 n) eqn:H1; [|reflexivity]. apply Z.leb_le in H1.
        rewrite (know_lookupW_eq k sb lo hi sk 1 false) by (cbn; lia).
        destruct (know_lookup segs k sb sk 1 false [] []) as [v [|? ?] hs|scs hs|]; try reflexivity.
        rewrite IH by lia. destruct (APC.copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)); reflexivity.
  - cbn [andb]. destruct (Z.leb 1 n) eqn:H1; [|reflexivity]. apply Z.leb_le in H1.
    rewrite (know_lookupW_eq k sb lo hi sk 1 false) by (cbn; lia).
    destruct (know_lookup segs k sb sk 1 false [] []) as [v [|? ?] hs|scs hs|]; try reflexivity.
    rewrite IH by lia. destruct (APC.copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kimg_precut (k : list kentry) (db : expr) (dk n : Z) : list kentry :=
  match k with
  | [] => []
  | KImg lo hi :: r =>
      match db with
      | ELit 0 =>
          (if Z.ltb lo (Z.min dk hi) then [KImg lo (Z.min dk hi)] else [])
          ++ (if Z.ltb (Z.max lo (dk + n)) hi then [KImg (Z.max lo (dk + n)) hi] else [])
          ++ kimg_precut r db dk n
      | _ => KImg lo hi :: kimg_precut r db dk n
      end
  | K :: r => K :: kimg_precut r db dk n
  end.

Definition step_copy (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_cpy) then None else
  match ret_lit ss, reg ss 12 with
  | Some ret, ELit n0 =>
      let n := n0 mod two64 in
      let dst := reg ss 10 in let src := reg ss 11 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xhi fk dst, xhi fk src with
      | Some dhi, Some shi =>
      if (Z.ltb 0 n && Z.leb n 2048 && Z.ltb (dhi + n) two64 && Z.ltb (shi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.flat_x fk sb sk (ELit n)
          && APC.kwritable_x fk k db dk (ELit n) && ranges_apart_x fk db dk (ELit n) sb sk (ELit n))%bool
      then match copy_factsW (Z.to_nat n) (List.filter (cw_keep sb sk (sk + n)) k) k sb sk db dk n with   (* [comment removed for export] *)
           | Some kc =>
               (* [comment removed for export] *)
               let kh := APC.kn_havocM (kimg_precut k db dk n) db dk (ELit n) in   (* [comment removed for export] *)
               let k' := if expr_eqb dst (reg ss 2) then kh ++ kc else kc ++ kh in
               if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WCopy db dk sb sk n :: w) else None
           | None => None
           end
      else None
      | _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition step_fill (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_set) then None else
  match ret_lit ss, reg ss 11, reg ss 12 with
  | Some ret, ELit c0, ELit n0 =>
      let n := n0 mod two64 in let c8 := (c0 mod two64) mod 256 in
      let dst := reg ss 10 in let '(db, dk) := split_lit dst in
      match xhi fk dst with
      | Some dhi =>
      if (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.ltb (dhi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.kwritable_x fk k db dk (ELit n))%bool
      then let k' := (if Z.eqb c8 0 then KZero (SA db dk) (ELit n) else KFill (SA db dk) (ELit n) c8)
                      :: APC.kn_havocM (kimg_precut k db dk n) db dk (ELit n) in
           if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WFill db dk n c8 :: w) else None
      else None
      | None => None
      end
  | _, _, _ => None
  end.


(* [comment removed for export] *)
Fixpoint fsd_targets (p : Z) (n : nat) (ss : sym_state) : option (list (expr * Z)) :=
  match n with
  | O => Some []
  | S n' =>
      match itab_lookup IT p with
      | Some (FStore FMT_D rs1 _ imm) =>
          match fsd_targets (p + 4) n' ss with
          | Some r => Some (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) :: r)
          | None => None
          end
      | _ => None
      end
  end.
Fixpoint consecutive (b : expr) (k : Z) (l : list (expr * Z)) : bool :=
  match l with [] => true | (b', k') :: r => expr_eqb b' b && Z.eqb k' k && consecutive b (k + 8) r end%bool.
Fixpoint kslots (db : expr) (dk : Z) (vs : list expr) : list kentry :=
  match vs with [] => [] | v :: r => KWord (SA db dk) 8 v :: kslots db (dk + 8) r end.
Fixpoint wslots_went (db : expr) (dk : Z) (vs : list expr) (acc : list went) : list went :=
  match vs with [] => acc | v :: r => wslots_went db (dk + 8) r (WSt (SA db dk) 8 v :: acc) end.
Definition step_fsdseq : ltac2:(zQ "60!l9!ir0!r9!hpa!m0!kgb>1n$3>2ss$1>1w@1$0$2@1$4@2$5$1@1$0$2") := ltac2:(zQ "if0!l9!kgb!ir0!r9!m0!hq0!hva!ji8!ig1!jr1!hp3!hpa!ji1!jt2!ki8!isd!mr0!nv4!kt7!jm5!s0!jra!kh2!km1!nvb!og2!hua!ogd!oh7!oi4!oj3!jvc!mq5!oja!iu9!irc!iva!ih1!hia!jmc!ok2!ok8!ol6!om4!on2!onb!jq0\1n$b\2ss$2\1w@1$0$3=1k@1$0$9@1$i2^2=2fk@1$0$9@1$i0^1=2nx$b@1$i3^4M4\1x@1$4@1$0@2$1$6$5@1$4@2$1$2@1$0$3@3$ia@1$h0^5^6^5\1l@1$0@2$1$6$5M0\1l@1$0@2$1$6$5@1$4@2$1$2@1$0$3^1@1$7@2$1$2@1$0$3\1p@2$1$6$5\4rest@1$0@2$1$6$5M1\1p@2$1$6$5@1$4@2$1$2@1$0$3^2\2db$6\2dk$5=3len$5@2$h1+8@1$h2^bM4\1x@1$4$5@1$4@2$1$2@1$0$3@2$i8^8@3$i1$h9^3@1$c^2\3dhi$5Ma\0$a@1$4@2$1$2@1$0$3@2$8@2$8@2$8@2$8@3$i9^4@2$e^3+8^5@2$ie@2$e^1^2$i7@4$hb^9^4^3@1$c^2@5$hd^9^a^4^3@1$c^2@2$ha^8^4=2vs@1$0$6@4$h7$b$6\1j$b@1$he@2$d^9^1@2$h8N0^d=2kh@1$0$9@4$hc@4$ib^b^5^4^3^5^4@1$c^3=2k'@1$0$9@3$h4$9@3$ic^6^5^2^1Ma\0$a@1$4@2$1$2@1$0$3@2$8@2$f@2$d^b^h0^1@2$f^b^2@2$h3@2$1$2@1$0$3@4$h6$2@1$0$3@6$hf@2$e@1$h0^f@2$h1+4@1$h2^h0@1$i4^f@1$h5$i6^1@2$d^b^h0@1$7$i5@4$id^7^6^3^e@1$7@2$1$2@1$0$3@1$7@2$1$2@1$0$3@1$7@2$1$2@1$0$3@1$7@2$1$2@1$0$3").

(* [comment removed for export] *)
Fixpoint fld_sources_ok (p : Z) (n : nat) (ss : sym_state) : bool :=
  match n with
  | O => true
  | S n' =>
      match itab_lookup IT p with
      | Some (FLoad FMT_D _ rs1 imm) =>
          let a := to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm) in
          kn_readable segs (facts_of (s_know ss)) (s_know ss) (a_base a) (a_off a) 8 && fld_sources_ok (p + 4) n' ss
      | _ => false
      end
  end%bool.
Definition step_fldseq : ltac2:(zQ "60!l9!ir0!r9!hpa!m0!kgb>1n$3>2ss$1>1w@1$0$2@1$4@2$5$1@1$0$2") := ltac2:(zQ "h60!l9!ir0!r9!kgb!ji8!hp3!mr0!jm5!hpa!jra!m0!kh2!jvc!iu9!irc!iva!ih1!hia!oo9!ki8!nv4!kt7\1n$8\2ss$1\1w@1$0$2M5\0$5@1$a@2$3$1@1$0$2@3$h2@1$6^2^3^2@2$7@2$3$1@1$0$2@4$b$1@1$0$2@6$c@2$h3@1$6^2@2$h4+4@1$h5^3@1$f^2@1$9$h1@1$d^2@1$e^2@1$4$h0^1@1$4@2$3$1@1$0$2").


(* [comment removed for export] *)
Fixpoint bytes_nonzero (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match know_lookup segs k b off 1 false [] [] with
            | LHit (ELit z) [] _ => negb (Z.eqb (z mod 256) 0) && bytes_nonzero fk k b (off + 1) n'
            | _ => false
            end
  end%bool.
Definition byte_zero : ltac2:(zQ "50!hp3!l9!hq0!hva!jr1>1k@1$1$4>1b$3>3off$2$0") := ltac2:(zQ "f0!hva!is5!hp3!l9!knf!hpa!hq0!jra!jl3!jlc!nj4!jr1!no7!jp2!jq7\1k@1$3$b\1b$0\3off$6Ma\1x$a$2@8$c?4segs^3^2^1N1$1@1$7$2@1$7$4\1v$0\3scs@1$3$4\5hints@1$3$2M0\1v$0$2^3\1z$6M3\3scs@1$3$4$2^3@2$d@2$e^1+hg0Z\1s$4\1l@1$3$4$1\1n$5$1\2op$8\1a$0\2b0$0$1\2op$8\1a$0\2b0$0$1\2op$9\1a$0\2b0$0$1\2op$9\1a$0\2b0$0$1\2sx$2\2lo$5\1n$5\1e$0$1\2sx$2\2k0$5\1i$6\1n$5$1\3scs@1$3$4\5hints@1$3$2$1$1").
Fixpoint words_readable (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => kn_readable segs fk k b off 1 && words_readable fk k b (off + 1) n'
  end%bool.
Definition ro_covered : ltac2:(zQ "30!hp3!l9!jr1>1k@1$1$2$0") := ltac2:(zQ "b0!hva!is5!ih1!hq0!jr1!hpa!jp9!ig1!hp3!l9!opa\1k@1$9$4@3$a$4\1K$4M4\1K$4$8^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$5$1\2lo$3\2hi$3@2$7@2$6^2?5ro_lo@2$6?5ro_hi^1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1^1").
Definition step_strlen (kz : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) x_len) then None else
  match ret_lit ss with
  | Some ret =>
      let sp := reg ss 10 in let '(sb, sk) := split_lit sp in
      match xhi fk sp, ealign k sb with
      | Some shi, al =>
          (* [comment removed for export] *)
          let hi := (sk + kz) - (sk + kz) mod 8 + 8 in
          if (Z.leb 0 kz && Z.ltb (shi + (hi - sk)) two64 && Z.leb 3 al
              && bytes_nonzero fk k sb sk (Z.to_nat kz) && byte_zero k sb (sk + kz)
              && words_readable fk k sb (sk + kz + 1) (Z.to_nat (hi - (sk + kz + 1)))
              && APC.flat_x fk sb sk (ELit (hi - sk))
              && ro_covered k)%bool
          then Some (SS ret (sr_upd (APC.sr_fresh (s_regs ss) [11; 12; 13; 14; 15; 16]%nat nx) 10 (ELit kz)) [] k (nx + 6)%nat, w)
          else None
      | None, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition EVMAX : Z := 8192.
(* [comment removed for export] *)
Fixpoint evars (e : expr) (acc : option (list nat)) : option (list nat) :=
  match acc with
  | None => None
  | Some l =>
      match e with
      | ELit _ => acc
      | EVar n => Some (if existsb (Nat.eqb n) l then l else n :: l)
      | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars b (evars a acc)
      | EExt _ _ _ a => evars a acc
      | EBlob _ _ _ _ => None
      end
  end.
(* [comment removed for export] *)
Fixpoint efold (x : nat) (k : Z) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar n => if Nat.eqb n x then ELit k else e
  | EAlu op a b => mkAlu op (efold x k a) (efold x k b)
  | EAluw op a b => mkAluw op (efold x k a) (efold x k b)
  | EMd op a b => mkMd op (efold x k a) (efold x k b)
  | EMdw op a b => mkMdw op (efold x k a) (efold x k b)
  | EExt sx lo n a => if Nat.leb n 8 then mkExt sx lo n (efold x k a) else EExt sx lo n (efold x k a)
  | EBlob _ _ _ _ => e
  end.
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Definition eval_range : ltac2:(zQ "50!l9!m0!hq0!hva!jr1>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "hb0!hq0!hpa!ji8!m0!hva!l9!hp3!kgb!jm5!jl3!jlc!oq5!jp9!kla!ig1!jra!ji1!oj3!oqd!kj5!jr1!or6!ore!os6!ijb!ki8!osd\1k@1$5$h4\1e$4M3\1x@1$3@1$5$1@1$3$0@2$h6^1@2$8@1$5$1@1$f$1\1l@1$5$1M5\1l@1$5$1@1$3$0^1@1$2$0\1x$1\2l0@1$5$1M5\2l0@1$5$1@1$3$0^1M3\1x@1$3@2$7$0$0@1$3$0@2$h2^5@1$h1^2\1p@2$7$0$0M7\1p@2$7$0$0@1$3$0^1\2lo$0\2hi$0M6\0$6@1$3$0@2$e@2$c^2^1@2$c@2$d^1^2$h5M4\1x$4@1$3$0@3$b^5^2^7\1c$0M6\0$6@1$3$0@3$h8$0\1v$0@2$h3@3$b^7^1^9@1$h0^2@2$h7^3@1$ha@2$h9@2$d^2^3+1@2$8$0^1@1$2$0\1n$1@1$2$0\2op$9\1a$4\1b$4@1$2$0\2op$9\1a$4\1b$4@1$2$0\2op$a\1a$4\1b$4@1$2$0\2op$a\1a$4\1b$4@1$2$0\2sx$6\3lo0$1\1n$1\2e0$4@1$2$0\2sx$6\2k0$1\1i$0\1n$1@1$2$0@1$2$0@1$2$0\1n$1\2l1@1$5$1@1$2$0@1$2$0").
Definition step_evalreg : ltac2:(zQ "60!l9!ir0!r9!hpa!m0!kgb>1r$3>2ss$1>1w@1$0$2@1$4@2$5$1@1$0$2") := ltac2:(zQ "h90!l9!ir0!r9!kgb!m0!ji8!hp3!hq0!iu9!ov2!jm5!ig1!hpa!jra!kh2!ji1!jvc!irc!mr0!iva!ih1!hia!kg2!ov9!jn4\1r$c\2ss$1\1w@1$0$2M6\0$6@1$4@2$3$1@1$0$2@2$b@2$9N0^3@2$9^3Ni0M4\1x@1$4$7@1$4@2$3$1@1$0$2@2$h7@1$8^2@2$h8^2^3\1c$7@2$a@2$3$1@1$0$2@4$e$1@1$0$2@6$h0@1$h2^3@3$h6@1$h3^3^4@1$f^1@1$d$h5@1$8^3@1$h1^3@1$5$h4^2@1$5@2$3$1@1$0$2@1$5@2$3$1@1$0$2").

(* [comment removed for export] *)
Definition acs_of : ltac2:(zQ "20!pg6!ir0>2ss$1$0") := ltac2:(zQ "90!hva!jra!kgb!is5!pgd!ph4!phd!ji1!ir0\2ss$8@b$4^1@1$1$6ZZZ@1$1@2$2$0$0@1$1@2$2$0$0Z@1$7Z$5$3").
Fixpoint join_regs (i : nat) (ra rb : list expr) (nx : nat) : list expr * nat :=
  match ra, rb with
  | a :: ra', b :: rb' =>
      if expr_eqb a b then let '(r, n) := join_regs (S i) ra' rb' nx in (a :: r, n)
      else let '(r, n) := join_regs (S i) ra' rb' (S nx) in (EVar nx :: r, n)
  | _, _ => ([], nx)
  end.
Definition arm_ok : ltac2:(zQ "40!hp3!hpa!hq0!ir0>6joinpc$2>2nx$1>2sa$3$0") := ltac2:(zQ "h50!hva!is5!hp3!l9!hpa!ig1!hq0!iva!hia!ikf!lof!jl3!jlc!pi5!pic!itb!iv2!irc!mr0!ir0!jp2\6joinpc$6\2nx$4\2sa$h3@2$5@2$5@2$5@2$5@2$5@2$h4@1$h2^1^3M3\1x@1$3$8$2@1$h0^1$9\1s$8\1l@1$3$8$1@2$d@1$h1^1^2@2$f^2@1$7^1@2$d@2$e$0@1$7^1Ni0M3\1x@1$3$0$2@1$7^1$1\1e$0\1l@1$3$0M0\1e$0$2^2\1z$6M6\1z$6$2^1$9\1p$a$1\1p$a$1\1n$4$1\2op$b\1a$0\1b$0$1\2op$b\1a$0\1b$0$1\2op$c\1a$0\1b$0$1\2op$c\1a$0\1b$0$1\2sx$2\2lo$4\1n$4\2e0$0$1\2sx$2\1k$4\1i$6\1n$4$1").
Definition step_diamond (joinpc : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let nx := s_next ss in
  match APC.branch_probe IT (acs_of ss) with
  | Some e =>
      match erange k e with
      | Some (lo, hi) =>
          let sa := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: k) nx) in
          let sb := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: k) nx) in
          if (XAxSymRun3.expr_vars_lt nx e && arm_ok joinpc nx sa && arm_ok joinpc nx sb)%bool then
            let '(rj, nx') := join_regs 0 (s_regs sa) (s_regs sb) nx in
            Some (SS joinpc rj [] k nx', w)
          else None
      | None => None
      end
  | None => None
  end.

Definition seg_step : ltac2:(zQ "60!l9!ir0!r9!m0!kgb!pj5>2st$5>2ss$1>1w@1$0$2@1$3@2$4$1@1$0$2") := ltac2:(zQ "h80!l9!ir0!r9!kgb!hp3!hq0!hpa!m0!pj5!ji8!jm5!nh0!kh2!mr0!pjd!pk6!pl3!plf!pme!pnd!po9!pp7!pq5!jp2\2st$8\2ss$1\1w@1$0$2M4\0$4@1$7@2$3$1@1$0$2@1$b@2$e^2^1@1$9@2$3$1@1$0$2M8\2st$8@1$7@2$3$1@1$0$2^3\5stops@1$0$5@3$f^1^3^2@2$h0^2^1@2$h3^2^1\1n$6@3$h5^1^3^2\1n$6@3$h4^1^3^2\2kz$5@3$h6^1^3^2\2pc$5M4\0$4@1$7@2$3$1@1$0$2@2$h7@1$d^3^1@2$a@2$3$1@1$0$2@4$c$1@1$0$2^3^2@1$9@2$3$1@1$0$2\2jp$5@3$h1^1^3^2\1r$6@3$h2^1^3^2").

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis IT_ok : ltac2:(zQ "10!tq9@2$0?4segs?2IT").
(* [comment removed for export] *)
Hypothesis COPY : ltac2:(zQ "20!qke!tv8>2fx$0@3$1^1?4segs?5x_cpy").
Hypothesis FILL : ltac2:(zQ "30!jmc!qke!ug5>2fx$1@4$2^1?4segs?5x_set$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow64_pos : ltac2:(zQ "20!pr3!nh7@2$0Z@2$1+2+k0").
Proof. reflexivity. Qed.

Definition INV : ltac2:(zQ "80!h9!jc!l9!m0!ptf!hi4!ir0!r9>1E$5>2ss$6>1w@1$2$7>1R@2$4@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8P") := ltac2:(zQ "e0!h9!jc!l9!m0!kr8!ptf!hi4!iu9!iva!ir0!koa!pu8!r2!r9\1E$6\2ss$9\1w@1$2$d\1R@2$5@1$0#5@1$1@1$0#k0\1M>0@1$1@1$0#k0@1$3@1$1@1$0#8@2$4@3$b^5@1$8^4^2@4$a?4segs^5@3$c^5^1^3@1$7^4").

Lemma closed_parts : ltac2:(zQ "h10!ta!hp3!ikf!kr8!irc!l9!hia!jra!iu9!iv2!iva!ir0!pv3!qg1!pjd!r9!iq3>2ss$b>1w@1$5$f>0@3$0$1@2$e^2^1$2@2$3@3$0$1@2$d@1$4^3@1$a^3$2@2$3@3$0$1@2$c@1$4^3@1$8^3$2@2$3@3$0$1@2$h0@1$4^3^2$2@3$0@1$5$6@1$9^3@1$7$6").
Proof.
  intros ss w H. unfold closed in H.
  apply andb_true_iff in H as [H Hl]. apply andb_true_iff in H as [H Hw]. apply andb_true_iff in H as [Hs Hk].
  rewrite APS.sr_vars_lt_eq in Hs. rewrite APS.kn_vars_lt_eq in Hk.
  repeat split; try assumption. destruct (s_log ss); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition STEP_POST : ltac2:(zQ "91!h9!jc!l9!m0!ir0!r9!ptf!hi4!qke&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2fx$8>2ss$4>1w@1$2$5>3ss'$4>2w'@1$2$5>1E$7>1R@2$6@1$0#5@1$1@1$0#k0>1M~0>3rom~0P") := ltac2:(zQ "h61!h9!jc!kr8!kre!ptf!hi4!irc!qke!l9!m0!mr0!ir0!ql9!qm3!r2!r9!qmb!ta!li6!ip6!qr2!qrc&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2fx$7\2ss$b\1w@1$8$f\3ss'$b\2w'@1$8$f\1E$5\1R@2$4@1$0#5@1$1@1$0#k0\1M~0\3rom~0@2$3$7\3fx'$7@2$3$5\2E'$5@2$3@2$4@1$0#5@1$1@1$0#k0\2R'@2$4@1$0#5@1$1@1$0#k0@2$2@3$h1@1$1@1$0#i0@1$c^3@1$c^c@2$2@3$h3@1$6^b^7^2@2$2@2$h2@1$6^b@1$6^9@2$2@5$h5^2^9^8^1^5@3$h4?4segs@5$d^c^6@2$h0@1$0#k0@1$a^b@3$e^7^5^a^4@5$d^3^1@2$h0@1$0#k0@1$a^9@3$e^2^5^8^4").

Lemma some_pair_inj : forall {A B} (a c : A) (b d : B), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros A B a c b d H. injection H as -> ->. split; reflexivity. Qed.
Lemma step_block_sound : ltac2:(zQ "h41!l9!h9!ir0!r9!jc!m0!kgb!ta!jm5!hp3!kh2!ikf!hq0!ptf!hi4!qke!qrc!qs2!pjd!pk6&>0@1$4@1$1#k0@1$5@1$4@1$1#8>2fx$f>5stops@1$0$c>2ss$2>1w@1$0$3>3ss'$2>2w'@1$0$3>1E$e>1R@2$d@1$1#5@1$4@1$1#k0>1M~0>3rom~0>0@3$7$9@2$h2^8^7$b>0@3$7@1$5@2$6$2@1$0$3@3$h3^a^9^8@2$8@2$6$2@1$0$3@4$a$2@1$0$3^7^6>0@5$h0^6^a^9^5^4@9$h1^d^b^a^9^8^7^6^5^4").
Proof.
  intros fx stops ss w ss' w' E R M rom Hcl H [HR HK].
  ndestruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_block in H. rewrite AXF.sym_execTXBIF_eq, carry2F_eq in H.   (* [comment removed for export] *)
  rewrite (sym_execTXBI_eq segs (s_know ss)) in H by reflexivity. rewrite carry2L_eq in H.   (* [comment removed for export] *)
  destruct ss as [p sr log k nx rsv]. cbn [s_pc s_regs s_log s_know s_next] in *. subst log.
  set (ss1 := sym_execTX segs IT 0%nat BFUEL true stops (SSR p sr [] k nx rsv)) in H.
  destruct (carry2 (s_log ss1) (s_know ss1) []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection H as <- <-.
  assert (Hx : sym_execTX segs IT 0%nat BFUEL true stops (SS p sr [] k nx) = ss1).
  { subst ss1. unfold sym_execTX. reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL stops p sr k nx E (wden E M w) rom R IT_ok HR HK Fsr Fkn) as X.
  cbn zeta in X. rewrite Hx in X. ndestruct X as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  nexists fx, E', R'. split; [reflexivity|]. split; [exact Hag|]. split; [exact Hle|].
  assert (Hw : wden E' M w = wden E M w) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  split.
  - split; cbn [s_regs s_know]; [exact HR'|].
    rewrite wden_wlog, Hw. eapply (carry2_sound _ (fun _ => None)); [exact Hc | exact Hlf | exact HK' | constructor].
  - cbn [s_pc]. rewrite wden_wlog, Hw. exact Hms.
Qed.

(* [comment removed for export] *)
Lemma reg_sound1 : ltac2:(zQ "e0!h9!jc!qse!ta!ptf!ik6!hi4!iva!ir0!pu8!qt2!jn4!qta!qtf>1E$6>2ss$8>1R@2$4@1$0#5@1$1@1$0#k0>0@3$9^3@1$7^2^1@3$3@1$1@1$0#k0@2$a^2@3$c@1$0#5+1Kv$2@2$d@1$0#5+1@2$5^4@2$b^3N1").
Proof. intros E ss R HR. exact (HR 1%bv). Qed.
Lemma reg_sound10 : ltac2:(zQ "e0!h9!jc!qse!ta!ptf!ik6!hi4!iva!ir0!pu8!qt2!jn4!qta!qtf>1E$6>2ss$8>1R@2$4@1$0#5@1$1@1$0#k0>0@3$9^3@1$7^2^1@3$3@1$1@1$0#k0@2$a^2@3$c@1$0#5+aKv$2@2$d@1$0#5+a@2$5^4@2$b^3Na").
Proof. intros E ss R HR. exact (HR 10%bv). Qed.
Lemma reg_sound11 : ltac2:(zQ "e0!h9!jc!qse!ta!ptf!ik6!hi4!iva!ir0!pu8!qt2!jn4!qta!qtf>1E$6>2ss$8>1R@2$4@1$0#5@1$1@1$0#k0>0@3$9^3@1$7^2^1@3$3@1$1@1$0#k0@2$a^2@3$c@1$0#5+bKv$2@2$d@1$0#5+b@2$5^4@2$b^3Nb").
Proof. intros E ss R HR. exact (HR 11%bv). Qed.
Lemma reg_sound12 : ltac2:(zQ "e0!h9!jc!qse!ta!ptf!ik6!hi4!iva!ir0!pu8!qt2!jn4!qta!qtf>1E$6>2ss$8>1R@2$4@1$0#5@1$1@1$0#k0>0@3$9^3@1$7^2^1@3$3@1$1@1$0#k0@2$a^2@3$c@1$0#5+cKv$2@2$d@1$0#5+c@2$5^4@2$b^3Nc").
Proof. intros E ss R HR. exact (HR 12%bv). Qed.

Lemma ret_lit_sound : ltac2:(zQ "h60!h9!kr8!hq0!ta!qmb!jc!jm5!m0!qse!ptf!hi4!iva!ir0!jmc!pu8!ri2!qt2!ric!ksb!pr3!qta!qtf>1E$a>2ss$c>1R@2$9@1$0#5@1$5@1$0#k0>1r$2>0@3$e^4@1$b^3^2>0@3$3@1$7$2@1$h1^4@2$6$2^2@2$1@3$3@1$5@1$0#k0@2$h0^4@3$h4@1$0#5+1Kv$8@2$h5@1$0#5+1@2$4@1$0#k0^3@2$1@1$f@2$4@1$0#k0^3@2$1@2$h2Z^3@2$h3^3$d").
Proof.
  intros E ss R r HR H. unfold ret_lit in H.
  destruct (reg ss 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound1 E ss R HR) as R1. rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_of_Z by (unfold two64 in Hlt; lia). exact He.
Qed.

Lemma nth_sr_vars_lt : ltac2:(zQ "b0!hp3!hpa!ikf!ta!hva!l9!nie!jha!hua!itb!ji1>1b$1>2sr@1$5$4>1r$1>0@3$3$0@2$9^3^2$2>0@2$6^2Ni0@3$3$0@2$8^5@4$7$4^3^4@1$aZ$2").
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APC.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma kimg_precut_ok : ltac2:(zQ "a0!h9!hq0!koa!jc!l9!m0!hi4!hva!jr1!om4>1E$6>1M>0@1$3@1$0#k0@1$5@1$3@1$0#8>1k@1$4$8>2db$7>2dk$1>1n$1>0@4$2?4segs^6^5^4@4$2?4segs^7^6@4$9^5^4^3^2").
Proof.
  intros E M k db dk n H. induction k as [|K r IH]; [constructor|].
  apply Forall_cons_iff in H as [HK Hr]. specialize (IH Hr). cbn [kimg_precut].
  assert (PIECE : forall lo hi lo' hi', kentry_ok segs E M (KImg lo hi) -> lo <= lo' -> hi' <= hi ->
                   kentry_ok segs E M (KImg lo' hi')).
  { intros lo hi lo' hi' X Hlo Hhi. cbn [kentry_ok] in *. ndestruct X as (X0 & X1 & X2).
    split; [lia|]. split; [lia|]. intros i Hi. apply X2. lia. }
  destruct K as [| | |lo hi| | | | | |]; try (constructor; assumption).
  destruct db as [z| | | | | | |]; [destruct z|..]; try (constructor; assumption).
  apply Forall_app. split; [|apply Forall_app; split; [|exact IH]].
  - destruct (Z.ltb lo (Z.min dk hi)) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
  - destruct (Z.ltb (Z.max lo (dk + n)) hi) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
Qed.

Lemma step_copy_sound : ltac2:(zQ "h40!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!kh2!ikf!ptf!hi4!qke!rj6!qrc!qs2!pjd!pl3>2fx$e>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$d>1R@2$c@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h2^7^6$b>0@3$7@1$5@2$6$1@1$0$2@2$h3^8^7@2$8@2$6$1@1$0$2@4$a$1@1$0$2^6^5>0@5$h0^5^9^8^4^3@9$h1^b^a^9^8^7^6^5^4@1$f?4segs").
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  ndestruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_copy in H. rewrite ?APC.kn_havocM_eq in H.
  destruct (Z.eqb (s_pc ss) x_cpy) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd. destruct (split_lit (reg ss 11)) as [sb sk] eqn:Hss.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (reg ss 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  rewrite copy_factsW_eq in H by apply Z.le_refl.   (* [comment removed for export] *)
  destruct (APC.copy_facts segs (Z.to_nat (n0 mod two64)) (s_know ss) sb sk db dk (n0 mod two64)) as [kc|] eqn:Hcf; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hap. rename X0 into Hwr. rename X1 into Hfs. rename X2 into Hfd. rename X3 into Hshi'. rename X4 into Hdhi'. rename X5 into Hn2048.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn2048. apply Z.ltb_lt in Hdhi'. apply Z.ltb_lt in Hshi'.
  set (n := (n0 mod two64)%Z) in *. set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi', Hshi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold two64 in Hn64; lia).
  ndestruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  ndestruct (APSX.w_flat_x_sound segs E m fk sb sk (ELit n) HKf Hfs) as (Slo & Shi & _).
  ndestruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  pose proof (ranges_apart_x_sound segs E m fk db dk (ELit n) sb sk (ELit n) HKf Hap) as Hapart.
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi, Shi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  ndestruct (APSX.copy_facts_sound segs E m k sb db (Z.to_nat n) sk dk n kc HK Hcf ltac:(lia) ltac:(lia) Slo Shi Dlo Dhi)
    as (bs & Hlbs & Hrd & Hkc).
  (* [comment removed for export] *)
  ndestruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in R11.
  change (bv_unsigned (edenot E db) + dk)%Z with D in R10. change (bv_unsigned (edenot E sb) + sk)%Z with S in R11.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD. pose proof (xhi_sound segs E m fk (reg ss 11) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in XS.
  change (bv_unsigned (edenot E db) + dk)%Z with D in XD. change (bv_unsigned (edenot E sb) + sk)%Z with S in XS.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64. rewrite u64_of_Z in XS by exact HS64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A3 : rdn segs m (Z_to_bv 64 S) (length bs) = Some bs) by (rewrite Hlbs; exact Hrd).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (length bs) = true) by (rewrite Hlbs; apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 D) + n <= bv_unsigned (Z_to_bv 64 S) \/ bv_unsigned (Z_to_bv 64 S) + n <= bv_unsigned (Z_to_bv 64 D))
    by (rewrite (u64_of_Z D HD64), (u64_of_Z S HS64); exact Hapart).
  assert (A6 : bv_unsigned (Z_to_bv 64 S) + n < 2 ^ 64) by (rewrite (u64_of_Z S HS64); clear - XS Hshi'; lia).
  assert (A7 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  ndestruct (COPY fx m (Z_to_bv 64 D) (Z_to_bv 64 S) n bs R (Z_to_bv 64 ret) A1 Hlbs A3 A4 A5 A6 A7 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  (* [comment removed for export] *)
  set (nx := s_next ss) in *.
  nexists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [reflexivity|]. split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fsrc : APC.expr_vars_lt nx (reg ss 11) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb. pose proof (APSX.split_lit_vars _ _ _ _ Hss Fsrc) as Fsb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  assert (ES : adenot (APSX.ext_call E nx regs') (SA sb sk) = Z_to_bv 64 S).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ sb Hag Fsb). reflexivity. }
  assert (MEM : wden (APSX.ext_call E nx regs') M (WCopy db dk sb sk n :: w) = wbytes m (Z_to_bv 64 D) bs).
  { cbn [wden]. rewrite Hw, ES, ED. fold S in Hrd. rewrite Hrd. reflexivity. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      lazymatch goal with |- know_ok _ ?EE ?MM _ =>
        assert (KC : know_ok segs EE MM kc);
        [ apply Hkc; rewrite <- Hlbs; apply rdn_wbytes_hit; rewrite u64_of_Z by lia; rewrite Hlbs; lia
        | assert (KH : know_ok segs EE MM (APC.kn_havoc (kimg_precut (s_know ss) db dk n) db dk (ELit n)));
          [ eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows];
            intros x Hx; rewrite Hlen in Hx; apply wbytes_out; rewrite ?Hlbs, ?u64_of_Z by lia; lia
          | destruct (expr_eqb _ _); apply Forall_app; split; assumption ] ]
      end.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.

Lemma step_fill_sound : ltac2:(zQ "h40!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!kh2!ikf!ptf!hi4!qke!rj6!qrc!qs2!pjd!pnd>2fx$e>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$d>1R@2$c@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h2^7^6$b>0@3$7@1$5@2$6$1@1$0$2@2$h3^8^7@2$8@2$6$1@1$0$2@4$a$1@1$0$2^6^5>0@5$h0^5^9^8^4^3@9$h1^b^a^9^8^7^6^5^4@1$f?4segs").
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  ndestruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_fill in H. rewrite ?APC.kn_havocM_eq in H.
  destruct (Z.eqb (s_pc ss) x_set) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 11) as [c0| | | | | | |] eqn:H11; try discriminate.
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hwr. rename X0 into Hfd. rename X1 into Hdhi'. rename X2 into Hn40.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hdhi'.
  set (n := (n0 mod two64)%Z) in *. set (c8 := ((c0 mod two64) mod 256)%Z) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  ndestruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  ndestruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.
  (* [comment removed for export] *)
  ndestruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12. rewrite H11 in R11. cbn [edenot] in R11.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. change (bv_unsigned (edenot E db) + dk)%Z with D in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }
  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A2 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (Z.to_nat n) = true) by (apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 c0) < two64) by (unfold two64; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 c0)) as X; exact (proj2 X)).
  ndestruct (FILL fx m (Z_to_bv 64 D) (Z_to_bv 64 c0) n R (Z_to_bv 64 ret) A1 A2 A4 A5 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  assert (Hc8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c0)) = Z_to_bv 8 c8).
  { subst c8. rewrite APSX.Z_to_bv8_mod. f_equal; try (rewrite Z_to_bv_unsigned; reflexivity). }
  rewrite Hc8 in Hms.
  set (nx := s_next ss) in *.
  nexists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [reflexivity|]. split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  set (M' := wbytes m (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat n))).
  assert (MEM : wden (APSX.ext_call E nx regs') M (WFill db dk n c8 :: w) = M').
  { cbn [wden]. rewrite Hw, ED. reflexivity. }
  assert (FILLED : forall i, 0 <= i < n -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c8)).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. apply APSX.wbytes_fill_at; [rewrite (u64_of_Z D HD64); clear - A2 XD Hdhi'; lia | exact Hi]. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      * destruct (Z.eqb c8 0) eqn:Hz; cbn [kentry_ok]; unfold flat, elenZ; cbn [a_base a_off edenot]; rewrite (u64_of_Z n) by lia;
          change (estart E (SA db dk)) with D.
        -- apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. rewrite (FILLED i Hi), Hz. reflexivity.
        -- split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. exact (FILLED i Hi).
      * eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows].
        intros x Hx. rewrite Hlen in Hx. subst M'. apply wbytes_out; rewrite ?repeat_length, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx Hc HD64 Dhi; lia.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.


Fixpoint wslots (m : word -> option byte) (a : Z) (vs : list word) : word -> option byte :=
  match vs with [] => m | v :: r => wslots (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (a + 8) r end.

Lemma wden_wslots_went : ltac2:(zQ "h01!h9!jc!hva!l9!m0!r2!ta!km1!hq0!lje!ik6!hi4!lj4!r9!rk1!onb&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1E$b>1M~0>2db$2>2dk$8>2vs@1$3$2>3acc@1$3$d@3$6~0@3$5^6^5@4$f^4^3^2^1@3$e@3$5^6^5^1@2$c^6@2$9^4^3@4$7$2@1$1@1$0#k0@1$a^6^2").
Proof.
  intros E M db dk vs. revert dk. induction vs as [|v r IH]; intros dk acc; cbn [wslots_went wslots map]; [reflexivity|].
  rewrite IH. cbn [wden]. rewrite APSX.adenot_SA.
  replace (estart E (SA db (dk + 8))) with (estart E (SA db dk) + 8)%Z by (unfold estart; cbn [a_base a_off]; lia).
  reflexivity.
Qed.

Lemma wslots_out : ltac2:(zQ "h00!h9!jc!ksb!pic!m0!ki8!nv4!kt7!rka!l9!ta!lk3!hq0!rk1!pr3!nh7>2vs@1$9@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a$c>1x@1$1@1$0#k0>0@2$2Z^2>0@2$2@2$5^3@2$6+8@1$7@2$3@1$1@1$0#k0^5@2$f+2+k0>0@2$b@2$e@2$8@1$0#k0^3^4@2$2@2$5^4@2$6+8@1$7@2$3@1$1@1$0#k0^6@2$8@1$0#k0^3@3$a@1$4@1$1@1$0#8@4$d^6^5^7^4@1^6^4").
Proof.
  induction vs as [|v r IH]; intros m a x Ha Hnw Hx; cbn [wslots length] in *; [reflexivity|].
  rewrite IH by lia. apply wbytes_out; rewrite length_N_to_le_bytes, (u64_of_Z a) by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma wslots_grows : ltac2:(zQ "70!h9!jc!l9!m0!hq0!rk1!rp6>2vs@1$2@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a$4@2$6^2@3$5^2^1^3").
Proof.
  induction vs as [|v r IH]; intros m a; cbn [wslots]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.

Lemma wslots_slot : ltac2:(zQ "h40!h9!jc!l9!pic!m0!ki8!ksb!nv4!kt7!qmb!jm5!hpa!ta!nie!jha!hq0!rta!ruf!rk1!nh7>2vs@1$2@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a$f>1i$b>0@2$6Z^2>0@2$6@2$5^3@2$7+8@1$8@2$3@1$1@1$0#k0^5@2$h3+2+k0>0@2$d^3@2$3@1$1@1$0#k0^6@3$c@1$4@1$2@1$1@1$0#8@4$h1?4segs@3$h2^6^5^7@2$9@1$0#k0@2$5^5@2$7+8@1$8^4N8@2$a@1$2@1$1@1$0#8@2$h0N8@4$e@1$1@1$0#k0^4^7@2$9@1$0#k0Z").
Proof.
  induction vs as [|v r IH]; intros m a i Ha Hnw Hi; cbn [wslots length nth] in *; [lia|].
  destruct i as [|i].
  - rewrite Z.mul_0_r, Z.add_0_r.
    rewrite <- (rdn_wbytes_hit8 segs m (Z_to_bv 64 a) v) by (rewrite u64_of_Z by lia; lia).
    apply rdn_ext; [rewrite u64_of_Z by lia; cbn; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
    apply wslots_out; cbn in Hx; lia.
  - replace (a + 8 * Z.of_nat (S i))%Z with ((a + 8) + 8 * Z.of_nat i)%Z by lia. apply IH; lia.
Qed.


Lemma ridx_bv5 : ltac2:(zQ "60!h9!jc!ta!rv6!kt7!qmb>1r@1$1@1$0#5@3$2@1$1@1$0#5@2$5@1$0#5@1$4@1$3^1^1").
Proof.
  intros r. unfold ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range _ r); lia). apply Z_to_bv_bv_unsigned.
Qed.
Lemma ridx_of_nat : ltac2:(zQ "70!hpa!ta!nie!h9!rv6!kt7!qmb>1i$0>0@2$2^1Ni0@3$1$0@1$4@2$6@1$3#5@1$5^2^2").
Proof.
  intros i Hi. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma itab_fact : ltac2:(zQ "h20!rvd!h9!ta!hq0!jc!jm5!m0!kgb!kr8!hp3!is5!kh2!kre!sg6!sh4!sk6!sl4!qmb>1p$3>1i$0>0@3$2@1$6$0@2$h0?2IT^2@2$5$0^1@2$c@1$4@1$1#i0\1w@1$4@1$1#i0@2$8@3$2@1$6@1$4@1$1#i0@2$d?4segs@2$h1@1$1#k0^4@2$5@1$4@1$1#i0^1@2$8@3$2$9@1$e^1$a@3$2@1$6@2$7$0$3@1$f^1@2$5@2$7$0$3@4$b$0$3^3+4").
Proof.
  intros p i Hl. pose proof (IT_ok _ _ Hl) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection Hen as ->.
  exists w. split; [reflexivity|]. split; [exact Hec | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma fsd_run : ltac2:(zQ "i80!hq0!h9!hva!kgb!jc!l9!ta!nv4!kt7!hpa!m0!ki8!qmb!jm5!qm3!rj6!hp3!ln1!pic!lo0!ikf!kr8!kre!sm2!ptf!lje!hi4!iva!ir0!lj4!pu8!qr2!qke!ol6!rk1!sme!ksb!pr3!nh7!osd>2fx$i0>1n$9>1p$0>2ss$hc>2tl@1$5@2$3$2$0>1E$ha>1R@2$h8@1$1#5@1$4@1$1#k0>1m>0@1$4@1$1#k0@1$a@1$4@1$1#8>1D$0>0@3$6@1$a@1$5@2$3$2$0@3$i1^7^8^6@2$d@1$5@2$3$2$0^5>0@3$he^5@1$hb^7^4>0>1j$9>2bk@2$3$2$0>0@3$6@1$a@2$3$2$0@3$i3@2$3$2$0^9^2@2$d@2$3$2$0^1@3$6$0@2$hd^9@2$h9@3$h1$2$0^2@3$h3$2$0^2@2$b^6@2$7+8@1$8^3>0@2$i4Z^4>0@2$i5@2$b^5@2$7+8@1$8^c@2$i6+2+k0>0@3$6$h0@4$h7?4segs^7@2$c@1$1#k0^6@1$i7@2$7+8@1$8^d$h4@2$h6@1$5@1$4@1$1#k0\4vals@1$5@1$4@1$1#k0@2$h5@3$6$9@2$h2@1$4@1$1#k0^1^f@3$hf?4segs@5$e^h0^a@2$c@1$1#k0^e^9@1$f?4segs@5$e^h0^a@2$c@1$1#k0@2$b^e@2$7+4@1$8^f@3$i2^9^8^1@1$f?4segs").
Proof.
  intros fx n. induction n as [|n IH]; intros p ss tl E R m D Htl HR Hest HD0 HDn Hst.
  - exists []. split; [reflexivity|]. cbn [wslots]. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fsd_targets] in Htl.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection Htl as <-.
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    pose proof (Hest 0%nat _ eq_refl) as E0. cbn [fst snd] in E0. rewrite Z.mul_0_r, Z.add_0_r in E0.
    set (v := reg_get (@fp_regs fx) rs2).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = Z_to_bv 64 D).
    { rewrite (HR rs1). rewrite <- E0.
      destruct (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) as [b0 k0] eqn:Hsp.
      cbn [fst snd]. unfold estart. cbn [a_base a_off].
      pose proof (APSX.w_split_lit_denot E _ b0 k0 Hsp) as X. rewrite <- X. rewrite mkAlu_denot. cbn [edenot].
      rewrite alu_add. unfold v_addi, v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_r. reflexivity. }
    assert (Hst8 : store_ok segs m (Z_to_bv 64 D) 8%nat = true).
    { eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 D) (Z.to_nat (8 * Z.of_nat (S n))) 8%nat); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia. }
    pose proof (fp_step_fsd fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rs1 rs2 imm (Z_to_bv 64 D) Hf Hec Hd Ha Hst8) as STEP.
    ndestruct (IH (p + 4) ss r E R (wbytes m (Z_to_bv 64 D) (word_to_le_bytes 8 v)) (D + 8) Hr HR) as (vals & Hlen & Hms).
    + intros j bk Hj. replace (D + 8 + 8 * Z.of_nat j)%Z with (D + 8 * Z.of_nat (S j))%Z by lia. apply Hest. cbn. exact Hj.
    + lia. + lia.
    + eapply store_ok_mono; [apply wbytes_grows|].
      eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 (D + 8)) (Z.to_nat (8 * Z.of_nat (S n))) (Z.to_nat (8 * Z.of_nat n))); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia.
    + exists (v :: vals). split; [cbn; lia|].
      eapply mst_step; [reflexivity | exact STEP |].
      replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
      2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
          change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
      replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia.
      cbn [wslots]. exact Hms.
Qed.

Lemma consecutive_nth : ltac2:(zQ "h20!hq0!hva!kgb!ta!jm5!hp3!ln1!l9!hpa!m0!lo0!ikf!kr8!ok8!sme!ki8!nv4!kt7>1l@1$7@2$2$1$0>1b$1>1k$0>1j$8>2bk@2$2$1$0>0@3$3$5@3$d^4^3^5$b>0@3$3@1$9@2$2$1$0@3$e@2$2$1$0^6^3@2$4@2$2$1$0^2@2$c@3$3$1@3$6$1$0^3^6@3$3$0@3$a$1$0^3@2$f^5@2$h0+8@1$h1^4").
Proof.
  induction l as [|[b' k'] r IH]; intros b k j bk H Hj; [destruct j; discriminate|].
  cbn [consecutive] in H. apply andb_true_iff in H as [H Hr]. apply andb_true_iff in H as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. subst b' k'.
  destruct j as [|j]; cbn [nth_error] in Hj.
  - injection Hj as <-. cbn [fst snd]. split; [reflexivity | lia].
  - destruct (IH b (k + 8)%Z j bk Hr Hj) as [A B]. split; [exact A | lia].
Qed.

Lemma fsd_targets_length : ltac2:(zQ "b0!hq0!kgb!hva!l9!hpa!ta!jm5!pic!m0!ir0!ol6>1p$0>1n$4>2ss$9>2tl@1$3@2$1$2$0>0@3$5@1$8@1$3@2$1$2$0@3$a^4^3^2@2$6@1$3@2$1$2$0^1@3$5$4@2$7@2$1$2$0^2^4").
Proof.
  intros p n. revert p. induction n as [|n IH]; intros p ss tl H; cbn [fsd_targets] in H.
  - injection H as <-. reflexivity.
  - destruct (itab_lookup IT p) as [i|]; [|discriminate]. destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

Lemma step_fsdseq_sound : ltac2:(zQ "h50!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!hpa!kh2!ikf!ptf!hi4!qke!rj6!qrc!qs2!pjd!pp7>2fx$f>1n$a>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$e>1R@2$d@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h3^7^6$c>0@3$7@1$5@2$6$1@1$0$2@3$h4^9^8^7@2$8@2$6$1@1$0$2@4$b$1@1$0$2^6^5>0@5$h1^5^9^8^4^3@9$h2^c^a^9^8^7^6^5^4@1$h0?4segs").
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  ndestruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  cbv beta zeta delta [step_fsdseq] in H. rewrite ?APC.kn_havocM_eq in H.
  destruct (fsd_targets (s_pc ss) n ss) as [[|[db dk] rest]|] eqn:Htl; try discriminate.
  destruct (xhi (facts_of (s_know ss)) (mkAlu ALU_ADD db (ELit dk))) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  apply some_pair_inj in H as [<- <-].
  apply andb_true_iff in Hc as [Hc Fdb]. apply andb_true_iff in Hc as [Hc Hwr]. apply andb_true_iff in Hc as [Hc Hfd]. apply andb_true_iff in Hc as [Hcons Hdhi'].
  apply Z.ltb_lt in Hdhi'. unfold two64 in Hdhi'. apply andb_true_iff in Hkv as [Hkv Hkvh].
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *. set (nx := s_next ss) in *.
  set (len := (8 * Z.of_nat n)%Z) in *.
  pose proof (fsd_targets_length _ _ _ _ Htl) as Hn. cbn [length] in Hn.
  assert (Hnpos : (1 <= n)%nat) by lia.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen64 : 0 < len < 2 ^ 64).
  { subst len. split; [lia|]. (* [comment removed for export] *)
    pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as X. pose proof (u64_range (edenot E (mkAlu ALU_ADD db (ELit dk)))). lia. }
  assert (Hlen : elenZ E (ELit len) = len) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  ndestruct (APSX.w_flat_x_sound segs E m fk db dk (ELit len) HKf Hfd) as (Dlo & Dhi & _).
  ndestruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit len) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit len))) with (elenZ E (ELit len)) in Dhi. rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.
  pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as XD.
  rewrite mkAlu_denot in XD. cbn [edenot] in XD. rewrite alu_add in XD. unfold v_add in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hlen64; lia).
  assert (XD' : D <= dhi).
  { unfold D, estart in *. cbn [a_base a_off] in *.
    replace (Z_to_bv 64 (bv_unsigned (edenot E db) + bv_unsigned (Z_to_bv 64 dk)))
      with (Z_to_bv 64 (bv_unsigned (edenot E db) + dk)) in XD.
    2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite u64_of_Z in XD by exact HD64. exact XD. }
  (* [comment removed for export] *)
  assert (EST : forall j bk, nth_error ((db, dk) :: rest) j = Some bk -> estart E (SA (fst bk) (snd bk)) = D + 8 * Z.of_nat j).
  { intros [|j] bk Hj.
    - cbn in Hj. injection Hj as <-. cbn [fst snd]. lia.
    - cbn [nth_error] in Hj. destruct (consecutive_nth _ _ _ _ _ Hcons Hj) as [A B].
      destruct bk as [b' k']. cbn [fst snd] in *. subst b' k'. unfold D, estart. cbn [a_base a_off]. lia. }
  destruct (fsd_run fx n (s_pc ss) ss _ E R m D Htl HR EST ltac:(lia) ltac:(clear - XD' Hdhi' HD64; lia)
              ltac:(apply Wst; subst len; rewrite Z2Nat.id by lia; lia)) as (vals & Hvl & Hms).
  (* [comment removed for export] *)
  set (E' := APS.ext_list E nx vals).
  pose proof (APS.ext_list_agree E nx vals) as Hag. fold E' in Hag.
  nexists fx, E', R. split; [reflexivity|]. split; [exact Hag|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (ED : estart E' (SA db dk) = D).
  { unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E E' db Hag Fdb). reflexivity. }
  assert (VALS : map (edenot E') (map (fun j => EVar (nx + j)%nat) (seq 0 n)) = vals).
  { rewrite map_map. rewrite <- (map_id vals). rewrite <- Hvl.
    transitivity (map (fun j => nth j vals (Z_to_bv 64 0)) (seq 0 (length vals))).
    - apply map_ext_in. intros j Hj. apply in_seq in Hj. cbn [edenot]. unfold E'. apply APS.ext_list_at. lia.
    - rewrite map_id. clear. induction vals as [|v r IH]; [reflexivity|].
      cbn [length]. rewrite <- cons_seq. cbn [map nth]. f_equal.
      rewrite <- seq_shift, map_map. cbn [nth]. exact IH. }
  assert (MEM : wden E' M (wslots_went db dk (map (fun j => EVar (nx + j)%nat) (seq 0 n)) w) = wslots m D vals).
  { rewrite wden_wslots_went, Hw, ED, VALS. reflexivity. }
  split.
  - split.
    + cbn [s_regs]. eapply APS.regs_ok_agree'; [exact Hag | exact Fsr0 | exact HR].
    + cbn [s_know]. rewrite MEM. apply Forall_app. split.
      * assert (SL : forall vs dk0 i0, (i0 + length vs = n)%nat -> estart E' (SA db dk0) = D + 8 * Z.of_nat i0 ->
                     (forall j, (j < length vs)%nat -> edenot E' (nth j vs (ELit 0)) = nth (i0 + j) vals (Z_to_bv 64 0)) ->
                     know_ok segs E' (wslots m D vals) (kslots db dk0 vs)).
        { induction vs as [|v r IH]; intros dk0 i0 Hl He Hv; cbn [kslots]; [constructor|].
          cbn [length] in Hl. constructor.
          - cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite He; clear - HD64 Hl XD' Hdhi'; lia|].
            rewrite APSX.adenot_SA, He. pose proof (Hv 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0, Nat.add_0_r.
            apply wslots_slot; [lia | rewrite Hvl; clear - HD64 XD' Hdhi'; lia | rewrite Hvl; lia].
          - apply (IH (dk0 + 8) (S i0)); [lia | unfold estart in *; cbn [a_base a_off] in *; lia |].
            intros j Hj. replace (S i0 + j)%nat with (i0 + S j)%nat by lia. apply (Hv (S j)). cbn [length]. lia. }
        apply (SL _ dk 0%nat).
        -- rewrite length_map, length_seq. reflexivity.
        -- rewrite ED. lia.
        -- intros j Hj. cbn [Nat.add]. rewrite <- VALS.
           change (Z_to_bv 64 0) with (edenot E' (ELit 0)). rewrite map_nth. reflexivity.
      * eapply APS.know_ok_agree'; [exact Hag | exact Hkvh |].
        eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wslots_grows].
        intros x Hx. rewrite Hlen in Hx. apply wslots_out; rewrite ?Hvl; clear - Hx HD64 XD' Hdhi'; subst len; lia.
  - cbn [s_pc]. rewrite MEM. exact Hms.
Qed.

(* [comment removed for export] *)
Lemma fld_run : ltac2:(zQ "hd0!h9!jc!ta!qke!l9!jr1!ql9!qm3!rj6!qmb!hp3!hpa!m0!ikf!kr8!kre!hq0!ptf!hi4!iu9!iva!ir0!koa!pu8!qr2!oo9!ki8!nv4!kt7>1n$b>2fx$3>1p$h0>2ss$h5>1E$h2>1R@2$h1@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$c@1$1@1$0#8>5allkn@1$4$5>0@3$2$a@3$h9^6^8^5$d>0@3$h7^5@1$h4^6^4>0@4$h6?4segs^6^4^3>0@3$2@1$4$5^4@1$h3^8@2$f$3\3fx'$3@2$e@3$2@1$1@1$0#i0@1$6^1@1$6^c@3$h8?4segs@5$7^c^8@2$9@1$0#k0^b^7@1$8?4segs@5$7^1^8@2$9@1$0#k0@2$ha^b@2$hb+4@1$hc^d^7@1$8?4segs").
Proof.
  induction n as [|n IH]; intros fx p ss E R m allkn H HR HK Hak.
  - exists fx. split; [reflexivity|]. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fld_sources_ok] in H.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    apply andb_true_iff in H as [Hrd Hrest].
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    subst allkn.
    destruct (kn_readable_sound segs E m (facts_of (s_know ss)) m (s_know ss) _ _ 8 (facts_of_ok segs E m _ HK) HK
                ltac:(lia) ltac:(lia) Hrd) as (Hfl & bs & Hbs & Hlbs).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = adenot E (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm))).
    { rewrite (HR rs1). rewrite to_saddr_denot. reflexivity. }
    pose proof (fp_step_fld fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rd rs1 imm _ bs Hf Hec Hd Ha Hbs) as STEP.
    ndestruct (IH (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                 (p + 4) ss E R m (s_know ss) Hrest HR HK eq_refl) as (fx' & Hfc & Hms).
    exists fx'. split; [exact Hfc|]. eapply mst_step; [reflexivity | exact STEP |].
    replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
    2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
        change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
    replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia. exact Hms.
Qed.

Lemma step_fldseq_sound : ltac2:(zQ "h50!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!hpa!kh2!ikf!ptf!hi4!qke!rj6!qrc!qs2!pjd!po9>2fx$f>1n$a>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$e>1R@2$d@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h3^7^6$c>0@3$7@1$5@2$6$1@1$0$2@3$h4^9^8^7@2$8@2$6$1@1$0$2@4$b$1@1$0$2^6^5>0@5$h1^5^9^8^4^3@9$h2^c^a^9^8^7^6^5^4@1$h0?4segs").
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK]. unfold step_fldseq in H.
  destruct (fld_sources_ok (s_pc ss) n ss) eqn:Hs; [|discriminate]. apply some_pair_inj in H as [<- <-].
  ndestruct (fld_run n fx (s_pc ss) ss E R (wden E M w) (s_know ss) Hs HR HK eq_refl) as (fx' & Hfc & Hms).
  nexists fx', E, R. split; [exact Hfc|]. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|].
  split; [split; [exact HR | exact HK]|]. cbn [s_pc]. exact Hms.
Qed.

(* [comment removed for export] *)
Definition strlen_step_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h50!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!kh2!ikf!hq0!ptf!hi4!qke!rj6!qrc!qs2!pjd!pq5>2fx$f>2kz$c>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$e>1R@2$d@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h3^7^6$b>0@3$7@1$5@2$6$1@1$0$2@3$h4^9^8^7@2$8@2$6$1@1$0$2@4$a$1@1$0$2^6^5>0@5$h1^5^9^8^4^3@9$h2^c^a^9^8^7^6^5^4@1$h0?4segs").

(* [comment removed for export] *)
Lemma efold_denot : ltac2:(zQ "b0!h9!ik6!hpa!ta!hq0!hi4!hva!src!oq5!qmb!jc>1E$5>1x$2>1k$4>1e$6@3$3@1$a@1$0#k0@2$1^4@3$8^3^2^1@2$1@3$7^4^3@2$9@1$0#k0^2^1").
Proof.
  intros E x k e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    cbn [efold edenot]; try reflexivity.
  - unfold APS.upd. cbn [ev]. destruct (Nat.eqb n x); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - destruct (Nat.leb n 8) eqn:Hn.
    + apply Nat.leb_le in Hn. rewrite mkExt_denot by exact Hn. rewrite IHa. reflexivity.
    + cbn [edenot]. rewrite IHa. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evars_mono : ltac2:(zQ "a0!hpa!l9!m0!jm5!ta!kr8!kre!hva!ore!ss3>1e$7>3acc@1$2@1$1$0>1l@1$1$0>0@3$4@1$2@1$1$0@2$8^3^2@2$3@1$1$0^1@2$6@1$1$0\2l0@1$1$0@2$5@3$4@1$2@1$1$0^4@2$3@1$1$0^1@3$9$0^1^3").
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l H;
    destruct acc as [l0|]; cbn [evars] in H; try discriminate;
    try (destruct (IHb _ _ H) as (l1 & H1 & S1); destruct (IHa _ _ H1) as (l2 & H2 & S2); injection H2 as <-;
         exists l0; split; [reflexivity | eapply incl_tran; [exact S2 | exact S1]]).
  - injection H as <-. exists l0. split; [reflexivity | apply incl_refl].
  - injection H as <-. exists l0. split; [reflexivity|]. intros m Hm. destruct (existsb (Nat.eqb n) l0); [exact Hm | right; exact Hm].
  - exact (IHa _ _ H).
Qed.

Lemma evars_agree : ltac2:(zQ "e0!hpa!l9!ta!h9!jc!m0!ssb!ik6!hi4!st0!jm5!hva!ore!kt1>1e$b>3acc@1$5@1$1$0>1l@1$1$0>1E$8>2E'$8>0@3$2@1$5@1$1$0@2$c^5^4@2$a@1$1$0^3>0>1n$0>0@3$d$0^1^5@3$2@1$4@1$3#k0@2$9^5^2@2$9^4^2>0@3$2>0$0@1$1@1$4@1$3#8@1$6^4@1$6^3@3$2@1$4@1$3#k0@2$7^5^8@2$7^4^8").
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l E E' H Hv Hb;
    destruct acc as [l0|]; cbn [evars edenot] in *; try discriminate; try reflexivity;
    try (destruct (evars_mono b _ _ H) as (l1 & H1 & S1);
         rewrite (IHa _ _ E E' H1), (IHb _ _ E E' H); [reflexivity | exact Hv | exact Hb | intros m Hm; apply Hv; apply S1; exact Hm | exact Hb]).
  - injection H as <-. apply Hv. destruct (existsb (Nat.eqb n) l0) eqn:Hx.
    + apply existsb_exists in Hx as (m & Hm & He). apply Nat.eqb_eq in He. subst m. exact Hm.
    + left. reflexivity.
  - first [rewrite (IHa _ _ E E' H Hv Hb); reflexivity | rewrite Hb; reflexivity].
Qed.

Lemma zseq_In : ltac2:(zQ "90!hq0!hpa!kr8!os6!kt1!ki8!ksb!pr3!kt7>2lo$0>1n$1>1v$0>0@2$2@2$6^3^1@2$7^1@2$5^3@1$8^2@3$4$0^2@2$3^4^3").
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo v Hv; [lia|]. cbn [zseq].
  destruct (Z.eq_dec v lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

Lemma eval_range_sound : ltac2:(zQ "e0!h9!hq0!jc!m0!ta!jm5!l9!ik6!hi4!hva!jr1!koa!ov9!qmb>1E$8>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>1k@1$6$a>1e$9>1c$1>0@4$b?4segs^5^4^3>0@3$4@1$3$1@2$c^4^3@2$5$1^2@3$4@1$2@1$0#k0@2$7^7^4@2$d@1$0#k0^3").
Proof.
  intros E M k e c HK H. unfold eval_range in H.
  destruct (evars e (Some [])) as [[|x [|]]|] eqn:Hev; try discriminate.
  destruct (erange k (EVar x)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (Z.leb lo hi && Z.leb (hi - lo) EVMAX)%bool eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  destruct (efold x lo e) as [c0| | | | | | |] eqn:Hf; try discriminate.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hall; [|discriminate] end.
  injection H as <-.
  pose proof (erange_sound segs E M k (EVar x) lo hi HK Her) as Hx. cbn [edenot] in Hx.
  set (v := bv_unsigned (ev E x)) in *.
  assert (Hin : In v (zseq lo (Z.to_nat (hi - lo + 1)))).
  { apply zseq_In. rewrite Z2Nat.id by lia. clear - Hx Hb1. lia. }
  rewrite forallb_forall in Hall. specialize (Hall v Hin).
  apply expr_eqb_eq in Hall.
  transitivity (edenot (APS.upd E x (Z_to_bv 64 v)) e).
  - eapply evars_agree; [exact Hev | | reflexivity]. intros n Hn. destruct Hn as [<-|[]].
    unfold APS.upd. cbn [ev]. rewrite Nat.eqb_refl. subst v. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite <- efold_denot, Hall. reflexivity.
Qed.

Lemma step_evalreg_sound : ltac2:(zQ "h50!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!hpa!kh2!ikf!ptf!hi4!qke!rj6!qrc!qs2!pjd!pme>2fx$f>1r$a>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$e>1R@2$d@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h3^7^6$c>0@3$7@1$5@2$6$1@1$0$2@3$h4^9^8^7@2$8@2$6$1@1$0$2@4$b$1@1$0$2^6^5>0@5$h1^5^9^8^4^3@9$h2^c^a^9^8^7^6^5^4@1$h0?4segs").
Proof.
  intros fx r ss w ss' w' E R M Hcl H [HR HK]. unfold step_evalreg in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool eqn:Hr; [|discriminate].
  apply andb_true_iff in Hr as [Hr0 Hr32]. apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32.
  destruct (eval_range (s_know ss) (reg ss r)) as [c|] eqn:Hev; [|discriminate]. injection H as <- <-.
  nexists fx, E, R. split; [reflexivity|]. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|]. split.
  - split; [|cbn [s_know]; exact HK]. cbn [s_regs].
    pose proof (eval_range_sound E _ (s_know ss) (reg ss r) c HK Hev) as Hc.
    intros r'. unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr'0.
    + specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
    + rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') r) eqn:Hi.
      * apply Nat.eqb_eq in Hi. specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR.
        rewrite HR. unfold reg in Hc. rewrite <- Hi in Hc. rewrite Hc. reflexivity.
      * specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
  - cbn [s_pc]. apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma join_regs_sound : ltac2:(zQ "h70!hva!hpa!pic!ta!l9!hp3!kr8!jha!ji1!nie!h9!hi4!jc!ikf!jt2!hua!ik6!kh2!kgb!kre!li6!ip6!st5>2ra@1$4$0>2rb@1$4$0>1i$1>2nx$1>2rj@1$4$0>3nx'$1>1E$b>1G>0$1@1$c@1$a#k0>4side$5>0@3$3@2$h2@1$4$0$1@4$h6^7^9^8^6@4$h1@1$4$0$1^5^4>0@3$3$1@2$2$0^9@2$2$0^a>0>1j$1>0@2$9^1@2$2$0^c@3$3@1$c@1$a#k0@1^6@2$e^b^2@2$h0^7@4$7$0^2M5\4side$5@1$4$0^5^d^c@1$8Z>0>1j$1>0@2$9^1@2$2$0^d@2$6@3$3$5@2$f^b@4$7$0^2^e@1$8Z$d@3$3$5@2$f^b@4$7$0^2^d@1$8Z$d@2$h3$b\2E'$b@2$6@3$h5^b^8^1@2$6@2$h4^b^9@2$6@3$3$1@2$2$0^a@2$2$0^e>1j$1>0@2$9^1@2$2$0^f@3$3@1$c@1$a#k0@1^9@2$e^e^2@2$h0^3@4$7$0^2^c@1$8Z").
Proof.
  induction ra as [|a ra IH]; intros rb i nx rj nx' E G side H Hlen HG Hv.
  - cbn [join_regs] in H. injection H as <- <-. exists E. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [reflexivity|].
    intros j Hj. cbn in Hj. lia.
  - destruct rb as [|b rb]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen. cbn [join_regs] in H.
    assert (HG' : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E (nth j (if side then ra else rb) (ELit 0))).
    { intros j Hj. replace (S i + j)%nat with (i + S j)%nat by lia. rewrite (HG (S j)) by (cbn; lia). destruct side; reflexivity. }
    assert (Hv' : forall j, (j < length ra)%nat -> APC.expr_vars_lt nx (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt nx (nth j rb (ELit 0)) = true).
    { intros j Hj. exact (Hv (S j) ltac:(cbn; lia)). }
    destruct (Hv 0%nat ltac:(cbn; lia)) as [Hva Hvb]. cbn [nth] in Hva, Hvb.
    pose proof (HG 0%nat ltac:(cbn; lia)) as HG0. rewrite Nat.add_0_r in HG0. cbn [nth] in HG0.
    destruct (expr_eqb a b) eqn:Hab.
    + destruct (join_regs (S i) ra rb nx) as [r n] eqn:Hr. injection H as <- <-.
      ndestruct (IH rb (S i) nx r n E G side Hr Hlen HG' Hv') as (E' & Hag & Hle & Hlr & HR).
      exists E'. split; [exact Hag|]. split; [exact Hle|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. rewrite HG0. apply expr_eqb_eq in Hab. subst b.
        destruct side; (eapply edenot_agree_AP; [exact Hag | first [exact Hva | exact Hvb]]).
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
    + destruct (join_regs (S i) ra rb (S nx)) as [r n] eqn:Hr. injection H as <- <-.
      set (E1 := APS.upd E nx (G i)).
      assert (Hag1 : env_agree nx E E1).
      { split; [|reflexivity]. intros m Hm. unfold E1, APS.upd. cbn [ev]. destruct (Nat.eqb m nx) eqn:He; [apply Nat.eqb_eq in He; lia | reflexivity]. }
      assert (HG1 : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E1 (nth j (if side then ra else rb) (ELit 0))).
      { intros j Hj. rewrite (HG' j Hj). destruct (Hv' j Hj) as [X Y].
        destruct side; (eapply edenot_agree_AP; [exact Hag1 | first [exact X | exact Y]]). }
      assert (Hv1 : forall j, (j < length ra)%nat -> APC.expr_vars_lt (S nx) (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt (S nx) (nth j rb (ELit 0)) = true).
      { intros j Hj. destruct (Hv' j Hj) as [X Y]. split; (eapply APS.expr_vars_lt_mono; [eassumption | lia]). }
      ndestruct (IH rb (S i) (S nx) r n E1 G side Hr Hlen HG1 Hv1) as (E' & Hag & Hle & Hlr & HR).
      exists E'. split.
      { eapply APS.env_agree_trans; [exact Hag1 | eapply APS.env_agree_le; [exact Hag | lia]]. }
      split; [lia|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. cbn [edenot]. destruct Hag as [Hagv _]. rewrite <- (Hagv nx) by lia. unfold E1, APS.upd. cbn [ev]. rewrite Nat.eqb_refl. reflexivity.
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
Qed.

Lemma arm_ok_parts : ltac2:(zQ "h40!ta!kr8!hpa!hva!iva!hp3!ikf!hq0!ji1!hia!pic!l9!jra!jha!itb!iv2!irc!mr0!ir0!su1>6joinpc$7>2nx$2>2sa$h2>0@3$0$5@3$h3^3^2^1$6@2$1@3$0$7@1$h1^2^4@2$1@3$0@1$b$9@1$f^2@1$c$9@2$1@3$0$2@1$h0^2^3@2$1@3$0$5@2$e^3@1$4^2$6@2$1@3$0$2@2$a$3@1$4^2Ni0@3$0$3@4$d$3N0@1$4^2@1$8Z@1$8Z").
Proof.
  intros joinpc nx sa H. unfold arm_ok in H.
  apply andb_true_iff in H as [H Hr0]. apply andb_true_iff in H as [H Hlen]. apply andb_true_iff in H as [H Hvars].
  apply andb_true_iff in H as [H Hnx]. apply andb_true_iff in H as [Hpc Hlog].
  apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hnx. apply Nat.eqb_eq in Hlen.
  destruct (s_log sa); [|discriminate].
  split; [exact Hpc|]. split; [reflexivity|]. split; [exact Hnx|]. split; [exact Hvars|]. split; [exact Hlen|].
  destruct (s_regs sa) as [|[z| | | | | | |] t]; try discriminate. destruct z; try discriminate. reflexivity.
Qed.

Lemma step_diamond_sound : ltac2:(zQ "h50!l9!ir0!r9!h9!jc!m0!kgb!ta!jm5!hp3!kh2!ikf!hq0!ptf!hi4!qke!rj6!qrc!qs2!pjd!plf>2fx$f>2jp$c>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$e>1R@2$d@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@3$7$9@2$h3^7^6$b>0@3$7@1$5@2$6$1@1$0$2@3$h4^9^8^7@2$8@2$6$1@1$0$2@4$a$1@1$0$2^6^5>0@5$h1^5^9^8^4^3@9$h2^c^a^9^8^7^6^5^4@1$h0?4segs").
Proof.
  intros fx jp ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  ndestruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_diamond in H.
  destruct (APC.branch_probe IT (acs_of ss)) as [e|] eqn:Hbp; [|discriminate].
  destruct (erange (s_know ss) e) as [[lo hi]|] eqn:Her; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hok; [|discriminate] end.
  apply andb_true_iff in Hok as [Hok Hokb]. apply andb_true_iff in Hok as [Hve Hoka].
  set (sa := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: s_know ss) (s_next ss))) in *.
  set (sb := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: s_know ss) (s_next ss))) in *.
  destruct (join_regs 0 (s_regs sa) (s_regs sb) (s_next ss)) as [rj nx'] eqn:Hjoin. injection H as <- <-.
  destruct (arm_ok_parts _ _ _ Hoka) as (PCa & LOGa & NXa & Va & La & Z0a).
  destruct (arm_ok_parts _ _ _ Hokb) as (PCb & LOGb & NXb & Vb & Lb & Z0b).
  set (m := wden E M w) in *.
  pose proof (erange_sound segs E m (s_know ss) e lo hi HK Her) as Hrange.
  (* [comment removed for export] *)
  assert (ARM : exists (side : bool) (sx : sym_state), (sx = (if side then sa else sb))
            /\ know_ok segs E m ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss)).
  { destruct (Z_le_gt_dec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exists true, sa. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK].
    - exists false, sb. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK]. }
  ndestruct ARM as (side & sx & Hsx & HKx).
  assert (Fknx : XAxSymRun3.kn_vars_lt (s_next ss) ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) = true).
  { destruct side; cbn [XAxSymRun3.kn_vars_lt XAxSymRun3.kentry_vars_lt]; rewrite Hve, Fkn; reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL [jp] (s_pc ss) (s_regs ss) _ (s_next ss) E m (seg_rom segs) R IT_ok HR HKx Fsr Fknx) as X.
  cbn zeta in X.
  replace (sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) (s_next ss)))
    with sx in X by (subst sx; destruct side; reflexivity).
  ndestruct X as (E1 & R1 & Hag1 & Hle1 & HR1 & Hlf1 & HK1 & Hms1 & _).
  assert (PCx : s_pc sx = jp) by (subst sx; destruct side; assumption).
  assert (LOGx : s_log sx = []) by (subst sx; destruct side; assumption).
  assert (NXx : s_next sx = s_next ss) by (subst sx; destruct side; assumption).
  rewrite LOGx in Hms1. cbn [mem_denot] in Hms1. rewrite PCx in Hms1.
  (* [comment removed for export] *)
  set (G := fun n : nat => getr R1 (Z_to_bv 5 (Z.of_nat n))).
  assert (HG : forall j, (j < length (s_regs sa))%nat -> G (0 + j)%nat = edenot E1 (nth j (if side then s_regs sa else s_regs sb) (ELit 0))).
  { intros j Hj. unfold G. cbn [Nat.add]. rewrite (HR1 (Z_to_bv 5 (Z.of_nat j))). unfold sr_get.
    rewrite La in Hj.
    destruct (Nat.eq_dec j 0) as [->|Hj0].
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat 0)) 0) with true by reflexivity. cbn [edenot].
      replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat j)) 0) with false.
      2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
          rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
      rewrite ridx_of_nat by lia. subst sx. destruct side; reflexivity. }
  assert (Hv : forall j, (j < length (s_regs sa))%nat -> APC.expr_vars_lt (s_next ss) (nth j (s_regs sa) (ELit 0)) = true
                                                  /\ APC.expr_vars_lt (s_next ss) (nth j (s_regs sb) (ELit 0)) = true).
  { intros j Hj. rewrite La in Hj. split; (apply nth_sr_vars_lt; [assumption | lia]). }
  assert (Hlen : length (s_regs sb) = length (s_regs sa)) by (rewrite La, Lb; reflexivity).
  ndestruct (join_regs_sound (s_regs sa) (s_regs sb) 0 (s_next ss) rj nx' E1 G side Hjoin Hlen HG Hv) as (E' & Hag' & Hle' & Hlr & HRj).
  nexists fx, E', R1. split; [reflexivity|].
  split; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag']|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fw]).
  split.
  - split; cbn [s_regs s_know].
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      * unfold bv_eqb in Hr0. apply Z.eqb_eq in Hr0. replace r with (Z_to_bv 5 (Z.of_nat 0)) by (apply bv_eq; rewrite Hr0; reflexivity).
        pose proof (HG 0%nat ltac:(rewrite La; lia)) as X. unfold G in X. cbn [Nat.add] in X. rewrite X.
        replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
      * assert (Hr : (ridx r < 32)%nat) by (unfold ridx; pose proof (bv_unsigned_in_range _ r); change (bv_modulus 5) with 32%Z in *; lia).
        pose proof (HRj (ridx r) ltac:(rewrite La; exact Hr)) as X. unfold G in X. cbn [Nat.add] in X. rewrite ridx_bv5 in X. exact (X).
    + rewrite Hw. eapply APS.know_ok_agree'; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fkn0 | exact HK].
  - cbn [s_pc]. rewrite Hw. exact Hms1.
Qed.

(* [comment removed for export] *)
Definition step_req : ltac2:(zQ "10!pj5>2st$0P") := ltac2:(zQ "60!sua!hq0!hpa!pj5!l9!sv1\2st$3M3\2st$3P^1\5stops@1$4$1$0$0$0\1n$2$0\1n$2$0\1k$1$5\2pc$1$0\6joinpc$1$0\1r$2$0").

Lemma seg_step_sound : ltac2:(zQ "h30!l9!ir0!r9!h9!jc!m0!kgb!jm5!kh2!ta!ptf!hi4!qke!rj6!qrc!qs2!tg5!pj5!th0>2fx$c>2st$h1>2ss$1>1w@1$0$2>3ss'$1>2w'@1$0$2>1E$b>1R@2$a@1$3#5@1$4@1$3#k0>1M>0@1$4@1$3#k0@1$5@1$4@1$3#8>0@1$h2^8>0@3$9@1$5@2$6$1@1$0$2@3$h0^9^8^7@2$7@2$6$1@1$0$2@4$8$1@1$0$2^6^5>0@5$e^5^9^8^4^3@9$f^c^a^9^8^7^6^5^4@1$d?4segs").
Proof.
  intros fx st ss w ss' w' E R M Hreq H HI. unfold seg_step in H.
  destruct (closed ss w) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  destruct st as [stops| | |n|n|kz|p|jp|r].
  - eapply step_block_sound; eassumption.
  - eapply step_copy_sound; eassumption.
  - eapply step_fill_sound; eassumption.
  - eapply step_fsdseq_sound; eassumption.
  - eapply step_fldseq_sound; eassumption.
  - eapply Hreq; eassumption.
  - destruct (Z.eqb (s_pc ss) p); [|discriminate]. injection H as <- <-.
    nexists fx, E, R. split; [reflexivity|]. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [exact HI | apply mst_refl].
  - eapply step_diamond_sound; eassumption.
  - eapply step_evalreg_sound; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition region : ltac2:(zQ "00T") := ltac2:(zQ "30!kgb!hq0!hva@2$0@2$0$2$1$1").
Definition within1 (b : expr) (k len : Z) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in (expr_eqb b rb && Z.ltb 0 len && Z.leb rlo k && Z.leb (k + len) (rlo + rlen))%bool.
Definition went_within : ltac2:(zQ "40!hp3!l9!thb!r9>1F@1$1$2>1g$3$0") := ltac2:(zQ "d0!hq0!hva!thb!ih1!r9!ti4!opa!ig1!hp3!jp9!l9!hpa!kt7\1F@1$a$2\1g$4M4\1g$4$8^1\1a$3\2wd$b\1v$1M3\1a$3$8^3\1b$1\1k$0@3$6$2@3$5^2^1@1$c^4^7\2db$1\2dk$0\2sb$1\2sk$0\1n$0@2$7@2$9Z^1@3$6$2@3$5^5^4^1^7\2db$1\2dk$0\1n$0\1c$0@2$7@2$9Z^2@3$6$2@3$5^4^3^2^6").
Definition regions_flat (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Definition outside (E : env) (F : list region) (a : word) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + rlen <= bv_unsigned a) F.

Lemma within1_sound : ltac2:(zQ "h20!hq0!h9!lje!hva!lj4!rka!kh2!lk3!ki8!ksb!pr3!hp3!kgb!ikf!ta!hi4!ti4!jc>1E$f>1b$3>1k$0>3len$0>2rb$3>3rlo$0>4rlen$0>1a@1$h1@1$1#k0>0@3$e$b@4$h0^7^6^5@4$6@2$c$3$0$0@4$6$3$0^4^3^2$d>0@2$7@2$a@2$5@1$1#k0^2@2$4^9@2$2^5^4@2$9@2$8@2$4^9@2$2^5^4^3@2$5@1$1#k0^2@2$7@2$a@2$5@1$1#k0^3@2$4^a@2$2^9^8@2$9@2$8@2$4^a@2$2^9^8^7@2$5@1$1#k0^3").
Proof.
  intros E b k len rb rlo rlen a H Ha. unfold within1 in H.
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1]. apply andb_true_iff in H as [Hb H0].
  apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
  unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma wden_frame : ltac2:(zQ "f0!h9!jc!l9!m0!ta!r9!hp3!ikf!hi4!tie!thb!tj8!r2!tk7!ijb>1E$8>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>1w@1$2$5>1F@1$2$a>1a@1$1@1$0#k0>0@3$4$6@3$e$5@1$d^2^3$7>0@2$b^6^3>0@3$9^7^4^3@3$4@1$3@1$1@1$0#8@4$c^8^7^6^4@1^7^4").
Proof.
  intros E M w F a Hw HF Ha. induction w as [|g r IH]; [reflexivity|].
  cbn [forallb] in Hw. apply andb_true_iff in Hw as [Hg Hr]. specialize (IH Hr).
  assert (REG : forall b k len, existsb (within1 b k len) F = true -> 0 <= len ->
            0 <= estart E (SA b k) /\ estart E (SA b k) + len <= 2 ^ 64 /\ 0 < len
            /\ (bv_unsigned a < estart E (SA b k) \/ estart E (SA b k) + len <= bv_unsigned a)).
  { intros b k len Hex Hlen. apply existsb_exists in Hex as ([[rb rlo] rlen] & Hin & Hw1).
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hfl. pose proof (proj1 (Forall_forall _ _) Ha _ Hin) as Hout.
    cbn beta iota in Hfl, Hout.
    pose proof (within1_sound E b k len rb rlo rlen a Hw1 Hout) as X.
    unfold within1 in Hw1. apply andb_true_iff in Hw1 as [Hw1 H2]. apply andb_true_iff in Hw1 as [Hw1 H1]. apply andb_true_iff in Hw1 as [Hb H0].
    apply expr_eqb_eq in Hb. apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
    unfold estart in *. cbn [a_base a_off] in *. lia. }
  destruct g as [[b k] wd v|db dk sb sk n|db dk n c]; cbn [wden went_within] in *.
  - ndestruct (REG b k (Z.of_nat wd) Hg ltac:(lia)) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite length_N_to_le_bytes, APSX.adenot_SA, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    ndestruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    destruct (rdn segs (wden E M r) (adenot E (SA sb sk)) (Z.to_nat n)) as [bs|] eqn:Hrd; [|exact IH].
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlbs.
    rewrite wbytes_out; [exact IH | |]; rewrite Hlbs, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    ndestruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite repeat_length, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record post_spec : Type := PS {
  ps_pc : Z;
  ps_regs : list (nat * expr);                 (* [comment removed for export] *)
  ps_regions : list region;                    (* [comment removed for export] *)
  ps_cells : list kentry                       (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition region_flat_chk (kn : list kentry) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in
  match rb with
  | ELit 0 => (Z.leb 0 rlo && Z.ltb 0 rlen && Z.ltb (rlo + rlen) two64)%bool
  | _ => (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool
  end.

Lemma region_flat_chk_sound : forall E M kn r,
  know_ok segs E M kn -> region_flat_chk kn r = true ->
  let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64.
Proof.
  intros E M kn [[rb rlo] rlen] HK H. unfold region_flat_chk in H.
  assert (GEN : (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool = true ->
                0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64).
  { intros G. apply andb_true_iff in G as [G0 G]. apply Z.ltb_lt in G0.
    apply existsb_exists in G as (K & Hin & HKc).
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [| | | | | |[b lo] [len| | | | | | |]| | |]; try discriminate.
    apply andb_true_iff in HKc as [HKc H0]. apply andb_true_iff in HKc as [HKc Hlt].
    apply andb_true_iff in HKc as [HKc H2]. apply andb_true_iff in HKc as [Hb H1].
    apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0. subst b.
    cbn [kentry_ok] in HKK. destruct HKK as [Hfl _]. unfold flat, elenZ in Hfl. cbn [edenot] in Hfl.
    rewrite u64_of_Z in Hfl by (unfold two64 in Hlt; lia). unfold two64 in Hlt.
    unfold estart in *. cbn [a_base a_off] in *. pose proof (bv_unsigned_in_range _ (edenot E rb)). lia. }
  destruct rb as [z| | | | | | |]; try (apply GEN; exact H).
  destruct z; try (apply GEN; exact H).
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

(* [comment removed for export] *)
Definition regions_ok (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Lemma regions_ok_flat : ltac2:(zQ "50!l9!hi4!thb!tj8!tl5>1E$1>1F@1$0$2>0@2$4^2^1@2$3^3^2").
Proof.
  intros E F H. unfold regions_ok, regions_flat in *. eapply Forall_impl; [|exact H].
  intros [[rb rlo] rlen] X. lia.
Qed.

End WithSegs.
End SR.
(* [comment removed for export] *)
