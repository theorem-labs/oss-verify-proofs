(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require AsCert0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~03lin37Corelib4Init9Datatypesk64prod37Corelib7Numbers7BinNumsm54Npos35stdpp9bitvectorbdefinitionso52bvk64list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsMainVM~~~~~~qe3siv03envk64boolk63nilm51Z79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~hg54ldeno57Z_to_bvk64consk63fstk64pairk63snd46Stdlib6ZArith6BinInt1Zhn83ltbhn83sub37Corelib4Init5Logichpe3andhn82lehn83powhn82lt04exprk63apphn83addhg54tdenhpe2eqqe4lcatqe6lconst06kentry08lin_test06lsub_ehn83lebk66optionk64Nonek64Some0blin_nowrapR06lin_of05saddrqe7lin_ofx06a_base05a_offqe6le_link64andb0ashares_var36Stdlib5Lists4Listio67existsbk63nat3h5LinuxProcessSemantics5Riscv5Instriqa5aluopiqa5mulopk64trueqe7lin_hask63orbk65falseqe6insideqe7lin_ofak64negbqe9kdisj_preqe6kdisj1qe5kdisjqecdisjoint_decqeadrop_emptyqe6lt_lin79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~jlb4vmopqe7sym_subqe6siv_ofjlb5mkind79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~jrdcis_lazy_kindjrdcis_none_kindjrd2uEhg56estarthpe2oro5bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Statekk5dmaps_subtractqe7siv_denqe8sivs_den37Corelib5Lists7ListDefkp96Forallqe6siv_wfqe8sym_sub1jrd5vm_ivqe8sym_stepjrd7vm_stepqeasym_replayjrd9vm_replayqe8is_arithio66filterhg57know_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeli77Segmentqe8kn_arith3h5LinuxProcessSemanticsfLinuxProcessSem2Fsln22Fskk55Modelkk59m_vm_lazykk58m_vmmapskk5bvm_noaccess3h5LinuxProcessSemantics5Riscv7Preludelt45bvmapjlb7a_vmopsjlb3acsjlb6atablejlb2knjrd5cs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~mie4bctxmie9lin_testBmieclin_nowrapRBqe8lin_ofxBqe7le_linBqe7insideBqe8lin_ofaBqe7kdisj1Bmie5bc_fkqe6kdisjBqeddisjoint_decBqebdrop_emptyBqe7lt_linBqe8sym_subBqe7siv_ofBqebsym_replayBmie4mkbcqe9sym_sub1Bqe9sym_stepBqeacs_ledgers" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition siv : ltac2:(zQ "00T") := ltac2:(zQ "20!k1!le@2$1$0$0").

Definition siv_den : ltac2:(zQ "60!ne!q2!q7!le!u9!uf>1E$5>1s$4@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "h22!ne!q2!le!k1!v4!vb!hg1!hkc!hl4!hle!hm5!q7!hmb!hn2!u9!uf!hp0!hp7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0\1E$f\1s$e=2lo$6@2$7^2@3$a$3$3^1=2hi$6@2$7^3@3$d$3$3^2M4\0$4@1$b~0@2$h0^2^1@3$9~0@4$c@1$1@1$0#k0@1$1@1$0#k0@2$8@1$0#k0^2@2$8@1$0#k0@2$h1^1^2~1~1").
Fixpoint sivs_den (E : env) (l : list siv) : list (word * word) :=
  match l with [] => [] | s :: r => siv_den E s ++ sivs_den E r end.

(* [comment removed for export] *)
Definition siv_wf : ltac2:(zQ "20!u9!uf>1E$1>1s$0P") := ltac2:(zQ "b0!k1!hkc!hm5!hn2!hr2!hr9!hrf!u9!uf!hs6!hp7\1E$8\1s$7@2$4@2$5Z@2$1^2@3$2$0$0^1@2$4@2$5@2$1^2@3$3$0$0^1@2$6+2+k0@2$9@2$a@2$1^2@3$3$0$0^1@2$1^2@3$2$0$0^1@2$6+2+k0").

Definition lconst : ltac2:(zQ "20!hg1!k1>1c$0$1") := ltac2:(zQ "60!hg1!le!hsc!q7!vb!hmb\1c$0@4$5$0@1$3@2$1$0$2^1@1$4@2$1$0$2").
Definition lcat : ltac2:(zQ "10!k1>1x$0>1y$0$0") := ltac2:(zQ "a0!hg1!le!hsc!q7!hm5!hn2!k1!ht2!hmb!ht8\1x$6\1y$6@4$8$0@1$3@2$1$0$2@2$9@3$4$0@1$3@2$1$0$2^2@3$4$0@1$3@2$1$0$2^1@3$7@2$1$0$2@3$5$0@1$3@2$1$0$2^2@3$5$0@1$3@2$1$0$2^1").

Lemma tden_app : ltac2:(zQ "90!hg1!le!hsc!htf!q7!ht2!hu7!uf!ht8>1E$7>1a@1$4@2$1$0$2>1b@1$4@2$1$0$2@3$6$0@2$3^3@3$5@2$1$0$2^2^1@2$8@2$3^3^2@2$3^3^1").
Proof. intros E a b. induction a as [|[k e] a IH]; cbn [tden app]; [lia|]. rewrite IH. lia. Qed.
Lemma lcat_den : ltac2:(zQ "70!hkc!k1!hu7!hg1!hud!uf!ht8>1E$5>1x$1>1y$1@3$2$3@2$0^3@2$4^2^1@2$6@2$0^3^2@2$0^3^1").
Proof. intros E [c1 t1] [c2 t2]. unfold lcat, lden. cbn [fst snd]. rewrite tden_app. lia. Qed.
Lemma lconst_den : ltac2:(zQ "50!hg1!hu7!hv4!uf!hkc>1E$3>1c$0@3$1$0@2$4^2@1$2^1^1").
Proof. intros E c. unfold lconst, lden. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition le_lin : ltac2:(zQ "40!k1!v4!q7!hvd>2kn@1$2$3>1x$0>1y$0$1") := ltac2:(zQ "c0!hg1!q7!le!hsc!hm5!hn2!k1!hvd!ig5!igf!ih7!hp7\2kn@1$1$7\1x$6\1y$6@4$8^3@2$b@3$4$0@1$1@2$2$0$3^1@3$4$0@1$1@2$2$0$3^2@2$9@3$5$0@1$1@2$2$0$3^1@3$5$0@1$1@2$2$0$3^2\2lo$0\0$0@2$aZ^2").
Definition lt_lin : ltac2:(zQ "40!k1!v4!q7!hvd>2kn@1$2$3>1x$0>1y$0$1") := ltac2:(zQ "c0!hg1!q7!le!hsc!hm5!hn2!k1!hvd!ig5!igf!hp0!hp7\2kn@1$1$7\1x$6\1y$6@4$8^3@2$b@3$4$0@1$1@2$2$0$3^1@3$4$0@1$1@2$2$0$3^2@2$9@3$5$0@1$1@2$2$0$3^1@3$5$0@1$1@2$2$0$3^2\2lo$0\0$0@2$aZ^2").

(* [comment removed for export] *)
Definition lin_ofx : ltac2:(zQ "50!q7!ihe!hsc!hvd!k1>2kn@1$0$3>1e$2@1$1$4") := ltac2:(zQ "a0!k1!v4!ii7!iie!q7!ihe!hsc!hvd!ij5!ik2\2kn@1$4$7\1e$6M1\0$1@1$5$0@2$8^2^1@2$3$0@1$9^1@1$2$0").
(* [comment removed for export] *)
Definition lin_ofa : ltac2:(zQ "50!q7!ihe!hvd!k1!ika>2kn@1$0$2>1a$4@1$1$3") := ltac2:(zQ "c0!k1!ihe!ii7!iie!q7!hud!hv4!il1!ilb!im3!hvd!ika\2kn@1$4$a\1a$bM1\1x@1$1$0@1$1$0@2$7^2@1$8^1\1l$0@2$3$0@2$5^1@1$6@1$9^2@1$2$0").

Definition inside : ltac2:(zQ "50!k1!v4!q7!u9!hvd>2kn@1$2$4>1x$3>3flo$0>3fhi$0$1") := ltac2:(zQ "80!k1!ima!in3!hm5!q7!hn2!u9!hvd\2kn@1$4$7\1x$6\3flo$0\3fhi$0@2$2@3$1^4^2@3$3$0$0^3@3$1^4@3$5$0$0^3^1").

(* [comment removed for export] *)
Definition lin_has : ltac2:(zQ "30!v4!hsc!k1>1l$2>1e$1$0") := ltac2:(zQ "d8!hsc!hg1!le!hn2!q7!ina!ip9!iq4!v4!ise!it7!iu0!k1&\1t@2$2$1$0@2$5^5@3$3$1$0^1&@3$6@2$2$1$0~0@3$3$1@1$4@2$2$1$0^5&\1b$0~1&\1a$0~2&\2op$9~3&\2op$a~3&\1t@2$2$1$0@2$5^6@3$3$1$0^1&@3$6@2$2$1$0~6@3$3$1@1$4@2$2$1$0^6\1l$c\1e$0M0\1e$0$8^1\1z$1$b\1n$7@3$6@2$2$1$0\1t@2$2$1$0@2$5^3@3$3$1$0^1@3$3$1@1$4@2$2$1$0^3~4~4~5~5\2sx$8\2lo$7\1n$7\2e0$0~7\2sx$8\1k$7\1i$1\1n$7~7").
Definition kdisj_pre : ltac2:(zQ "30!u9!hsc!v4>1x$0>1r$0>2b1$1>2b2$1$2") := ltac2:(zQ "70!k1!hm5!iu7!in3!u9!hsc!iv1\1x$4\1r$4\2b1$5\2b2$5@2$6@2$3@2$2@3$1$0$0^4^2@2$2@3$1$0$0^3^1@2$3@2$2@3$1$0$0^4^1@2$2@3$1$0$0^3^2").

(* [comment removed for export] *)
Definition kdisj1 : ltac2:(zQ "40!u9!hvd!v4!q7>2kn@1$3$1>1x$0>1r$0>1K$1$2") := ltac2:(zQ "h40!iv7!hsc!k1!v4!ihe!ika!hg1!ivf!hvd!in3!iq4!hud!jg8!il1!u9!ilb!q7!jh2!iv1!jh9\2kn@1$h0$8\1x$e\1r$e\1K$8M8\1K$8$3^1\1a$5\1w$a\1v$1$0\1a$5\1n$1$0\1a$5\1n$1\1k$a$0\2lo$6\2hi$6$0\1e$1\1m$6$0\1e$1\2lo$6\2hi$6$0\1a$5\1n$1$0\2a1$5\2n1$1\2a2$5\2n2$1M3\0$3$3@1$h1@4$h3^7^6@1$f^4@1$f^2$0M4\1x@1$4$2$3@2$c^8^4\2f1$2M4\1x@1$4$2$3@2$d^9^4\2m1$2M4\1x@1$4$2$3@2$c^a^4\2f2$2M4\1x@1$4$2$3@2$d^b^4\2m2$2=2g1$2@2$b^4^3=2g2$2@2$b^3^2@2$h2@2$9@4$7^e^d^6^2@4$7^e^c^4^1@2$9@4$7^e^d^4^1@4$7^e^c^6^2$0$0$0$0\1a$5\1n$1\1c$6$0\1a$5\1n$1$0").
Definition kdisj : ltac2:(zQ "40!u9!v4!q7!hvd>2kn@1$2$3>1x$0>1r$0$1") := ltac2:(zQ "50!u9!hvd!q7!ji5!ip9\2kn@1$2$1\1x$0\1r$0@3$4$1@3$3^3^2^1^3").

Definition disjoint_dec : ltac2:(zQ "40!u9!v4!q7!hvd>2kn@1$2$3>1x$0>1r$0$1") := ltac2:(zQ "90!k1!hm5!iv1!hn2!ima!u9!q7!jie!hvd\2kn@1$6$8\1x$5\1r$5@2$2@2$2@3$4^3@3$3$0$0^2@3$1$0$0^1@3$4^3@3$3$0$0^1@3$1$0$0^2@3$7^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint drop_empty (kn : list kentry) (l : list siv) : list siv :=
  match l with
  | [] => []
  | s :: r => if le_lin kn (snd s) (fst s) then drop_empty kn r else s :: drop_empty kn r
  end.

Definition sym_sub1 : ltac2:(zQ "40!u9!q7!ihe!hvd>2kn@1$1$3>1r$0>1x$0@1$2@1$1$0") := ltac2:(zQ "h10!k1!ihe!u9!v4!q7!iie!ii7!ima!hle!le!hm5!vb!hmb!hn2!jj6!jk5!hvd\2kn@1$4$h0\1r$2\1x$2M3\0$3@1$1@1$4$2@3$e^3^1^2@2$5@1$4$2@3$8$2^1@1$b$2=1a$0@3$a$0$0^1=1b$0@3$d$0$0^2=2lo$0@3$a$0$0^4=2hi$0@3$d$0$0^5M1\1x@1$1$0@1$1@1$4$2M3\0$3@1$1$0@3$7^7^2^3@2$5$0^2M3\0$3@1$1$0@3$7^7^3^2@2$5$0^3@1$6$0\2mn$0M1\1x@1$1$0@1$1@1$4$2M3\0$3@1$1$0@3$7^8^5^2@2$5$0^2M3\0$3@1$1$0@3$7^8^2^5@2$5$0^5@1$6$0\2mx$0@2$5@1$4$2@2$f^9@3$8@2$9$0$0@4$c$0$0^6^2@3$8@2$9$0$0@4$c$0$0^1^5@1$b@2$9$0$0@1$6@1$4$2@1$6@1$4$2").

Fixpoint sym_sub (kn : list kentry) (l : list siv) (r : siv) : option (list siv) :=
  match l with
  | [] => Some []
  | x :: l' => match sym_sub1 kn r x, sym_sub kn l' r with
               | Some p, Some q => Some (p ++ q)
               | _, _ => None
               end
  end.

(* [comment removed for export] *)
Definition siv_of : ltac2:(zQ "50!hsc!q7!ihe!u9!hvd>2kn@1$1$4>1a$0>1n$0@1$2$3") := ltac2:(zQ "h40!k1!ihe!u9!ii7!v4!le!hn2!il1!hsc!iie!in3!hm5!q7!hmb!hud!hv4!ima!jl2!hvd!hrf\2kn@1$c$h2\1a$8\1n$8M1\1x@1$1$0@1$1$2@2$7^3^2\2la$0M1\1x@1$1$0@1$1$2@2$7^4^2\2ln$0=1r@2$5$0$0@4$d$0$0^2@2$e^2^1M4\0$4@1$1$2@2$a@3$h1^6@3$b$0$0^1@3$6$0$0^1@3$h0^6@3$6$0$0^1@1$f@2$h3+2+k0@2$9@2$5$0$0^1@1$3$2@1$3$2@1$3$2").

Definition sym_step : ltac2:(zQ "60!q7!u9!le!ihe!jp9!hvd>2kn@1$0$5>2op$4>2NL@2$2@1$0$1@1$0$1@1$3@2$2@1$0$1@1$0$1") := ltac2:(zQ "h12!u9!q7!ihe!le!v4!ii7!hsc!jq1!iie!hle!hmb!jqb!jp9!jr4!kg1!kh1!hvd&\1x@1$2$0@1$2@2$3@1$1$0@1$1$0&\1x@1$2@1$1$0@1$2@2$3@1$1$0@1$1$0\2kn@1$1$h0\2op$c\2NL@2$3@1$1$0@1$1$0M3\2NL@2$3@1$1$0@1$1$0@1$2@2$3@1$1$0@1$1$0^1\1N@1$1$0\1L@1$1$0Mc\2op$c@1$2@2$3@1$1$0@1$1$0^4\1k$d\1a$6\1n$6M2~0@3$b^8^2^1\1r$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0M4\0$4@1$1$0@1$f^4@3$9$0^1^6^6M4\0$4@1$1$0@1$e^4@3$9$0^1^5^5@1$5@2$3@1$1$0@1$1$0\2nr$4\2pn$4\1a$6\1n$6M2~0@3$b^9^2^1\1r$0M2~1@3$7^a^7^1\2N'@1$1$0M2~1@3$7^b^7^2\2L'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0M4\2pn$4@1$1$0^6@3$9$0^3^2^2M4\2nr$4@1$1$0^7@3$9$0^3^1^1@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0\1a$6\1n$6M2~0@3$b^7^2^1\1r$0M2~1@3$7^8^5^1\2N'@1$1$0M2~1@3$7^9^5^2\2L'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0^2^1@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0\1a$6\1n$6M2~0@3$b^7^2^1\1r$0M2~1@3$7^8^5^1\2N'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0^1^5@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0").

Fixpoint sym_replay (kn : list kentry) (ops : list vmop) : option (list siv * list siv) :=
  match ops with
  | [] => Some ([], [])
  | op :: r => match sym_replay kn r with Some NL => sym_step kn op NL | None => None end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Variable segs : ltac2:(zQ "20!q7!llc@1$0$1").
  Variable E : ltac2:(zQ "10!uf$0").
  Variable M : ltac2:(zQ "30!ne!q2!ihe>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable kn : ltac2:(zQ "20!q7!hvd@1$0$1").
  Hypothesis KN : ltac2:(zQ "10!lhc@4$0?4segs?1E?1M?2kn").

  Lemma le_lin_sound : ltac2:(zQ "70!k1!hkc!v4!iu0!hu7!ima!hr9>1x$0>1y$0>0@3$4$2@3$5?2kn^2^1$3@2$6@2$1?1E^3@2$1?1E^2").
  Proof.
    intros [cx tx] [cy ty] H. unfold le_lin in H. cbn [fst snd] in H.
    apply (lin_test_sound segs E M kn) in H as (lo & hi & Ht & Hb); [|exact KN].
    apply Z.leb_le in Ht. rewrite lsub_e_sound in Hb. unfold lden. cbn [fst snd]. lia.
  Qed.
  Lemma lt_lin_sound : ltac2:(zQ "70!k1!hkc!v4!iu0!hu7!jl2!hs6>1x$0>1y$0>0@3$4$2@3$5?2kn^2^1$3@2$6@2$1?1E^3@2$1?1E^2").
  Proof.
    intros [cx tx] [cy ty] H. unfold lt_lin in H. cbn [fst snd] in H.
    apply (lin_test_sound segs E M kn) in H as (lo & hi & Ht & Hb); [|exact KN].
    apply Z.ltb_lt in Ht. rewrite lsub_e_sound in Hb. unfold lden. cbn [fst snd]. lia.
  Qed.

  Lemma lin_ofx_sound : ltac2:(zQ "90!k1!hu7!iie!ihe!hg1!il1!ki1!hsc!hkc>1e$7>1l$0>0@3$1@1$3$0@2$5?2kn^2@2$2$0^1@3$1$4@2$6?1E^3@2$8?1E^2").
  Proof.
    intros e l H. unfold lin_ofx in H. destruct (lin_nowrapR kn e) eqn:Hw; [|discriminate]. injection H as <-.
    unfold uE. rewrite (lin_nowrapR_sound segs E M kn e KN Hw). unfold lden. reflexivity.
  Qed.
  Lemma lin_ofa_sound : ltac2:(zQ "90!k1!hu7!iie!ihe!hg1!jg8!ika!ki7!hkc>1a$6>1l$0>0@3$1@1$3$0@2$5?2kn^2@2$2$0^1@3$1$4@2$7?1E^3@2$8?1E^2").
  Proof.
    intros [b k] l H. unfold lin_ofa in H. cbn [a_base a_off] in H.
    destruct (lin_ofx kn b) as [lb|] eqn:Hb; [|discriminate]. injection H as <-.
    rewrite lcat_den, lconst_den. unfold estart. cbn [a_base a_off]. rewrite <- (lin_ofx_sound b lb Hb). reflexivity.
  Qed.

  Lemma inside_sound : ltac2:(zQ "b0!k1!hkc!hr9!v4!hm5!hn2!iu0!hr2!hu7!ivf!u9>1x$a>1f$0>1g$0>0@3$8$3@4$9?2kn^3^2^1$6@2$7@2$2@2$1?1E^3@2$1?1E@3$4$0$0^4@2$2@2$1?1E@3$5$0$0^4@2$1?1E^2").
  Proof.
    intros x f g H. unfold inside in H. apply andb_prop in H as [H1 H2].
    split; [exact (le_lin_sound _ _ H1) | exact (le_lin_sound _ _ H2)].
  Qed.

  Lemma kdisj_sound : ltac2:(zQ "b0!k1!hkc!hm5!hn2!u9!hr9!v4!iu0!hu7!kj1!jie>1x$4>1r$4>0@3$8$6@3$a?2kn^2^1$7@2$9@2$5@2$1?1E@3$3$0$0^3@2$1?1E@3$2$0$0^2@2$5@2$1?1E@3$3$0$0^2@2$1?1E@3$2$0$0^3").
  Proof.
    intros x r H. unfold kdisj in H. apply existsb_exists in H as [K [HK H]].
    pose proof (proj1 (Forall_forall _ _) KN K HK) as KD.
    destruct K; try discriminate H. cbn [kdisj1] in H. cbn [kentry_ok] in KD.
    destruct (negb (kdisj_pre x r (a_base a1) (a_base a2))); [discriminate|].
    destruct (lin_ofa kn a1) as [f1|] eqn:F1; [|discriminate].
    destruct (lin_ofx kn n1) as [m1|] eqn:M1; [|discriminate].
    destruct (lin_ofa kn a2) as [f2|] eqn:F2; [|discriminate].
    destruct (lin_ofx kn n2) as [m2|] eqn:M2; [|discriminate].
    pose proof (lin_ofa_sound a1 f1 F1) as E1. pose proof (lin_ofa_sound a2 f2 F2) as E2.
    pose proof (lin_ofx_sound n1 m1 M1) as N1. pose proof (lin_ofx_sound n2 m2 M2) as N2.
    unfold elenZ in KD. fold (uE E n1) in KD. fold (uE E n2) in KD. rewrite E1, E2, N1, N2 in KD.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [Hx Hr];
      apply inside_sound in Hx as [Hx1 Hx2]; apply inside_sound in Hr as [Hr1 Hr2];
      rewrite lcat_den in Hx2, Hr2; lia.
  Qed.

  Lemma disjoint_dec_sound : ltac2:(zQ "b0!k1!hkc!hm5!hn2!u9!hr9!v4!iu0!hu7!kj1!jj6>1x$4>1r$4>0@3$8$6@3$a?2kn^2^1$7@2$9@2$5@2$1?1E@3$3$0$0^3@2$1?1E@3$2$0$0^2@2$5@2$1?1E@3$3$0$0^2@2$1?1E@3$2$0$0^3").
  Proof.
    intros x r H. unfold disjoint_dec in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - left. exact (le_lin_sound _ _ H).
    - right. exact (le_lin_sound _ _ H).
    - exact (kdisj_sound x r H).
  Qed.

  (* [comment removed for export] *)
  Lemma u_of_Z : ltac2:(zQ "90!ne!hg1!hr2!hu7!hr9!hs6!hrf!hl4!kj7>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
  Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. exact Hz. Qed.

  Lemma maps_subtract_app : ltac2:(zQ "82!ne!q2!le!q7!kn3!ht2!hg1!hu7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>2l1~1>2l2~1>2lo$6>2hi$6@3$7~1@3$4@3$5~0^4^3^2^1@3$5~0@3$4^4^2^1@3$4^3^2^1").
  Proof. intros l1 l2 lo hi. induction l1 as [|[a s] l1 IH]; cbn [maps_subtract app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

  Lemma siv_den_empty : ltac2:(zQ "c1!k1!ne!q2!le!hkc!hm5!q7!vb!hn2!hu7!ko4!hr9&@2$3@1$2@1$1#k0@1$2@1$1#k0>1s@2$3$0$0>0@2$b@2$4?1E@3$8$0$0^1@2$4?1E@3$5$0$0^1@3$9@1$6~0@2$a?1E^2@1$7~0").
  Proof. intros s H. unfold siv_den. destruct (lden E (fst s) <? lden E (snd s)) eqn:C; [apply Z.ltb_lt in C; lia | reflexivity]. Qed.
  Lemma siv_den_full : ltac2:(zQ "h01!k1!ne!q2!hkc!le!hm5!hn2!hl4!hle!q7!vb!hmb!hu7!ko4!hs6!hp7&@2$4@1$2@1$1#k0@1$2@1$1#k0>1s@2$4$0$0>0@2$e@2$3?1E@3$5$0$0^1@2$3?1E@3$6$0$0^1@3$c@1$9~0@2$d?1E^2@3$8~0@4$b@1$2@1$1#k0@1$2@1$1#k0@2$7@1$1#k0@2$3?1E@3$5$0$0^2@2$7@1$1#k0@2$f@2$3?1E@3$6$0$0^2@2$3?1E@3$5$0$0^2@1$a~0").
  Proof. intros s H. unfold siv_den. destruct (lden E (fst s) <? lden E (snd s)) eqn:C; [reflexivity | apply Z.ltb_ge in C; lia]. Qed.

  Lemma drop_empty_den : ltac2:(zQ "80!q7!ne!koe!q2!le!hu7!jk5!u9>1l@1$0$7@3$5@1$0@2$4@1$3@1$1#k0@1$3@1$1#k0@2$2?1E@2$6?2kn^1@2$2?1E^1").
  Proof.
    induction l as [|s l IH]; [reflexivity|]. cbn [drop_empty].
    destruct (le_lin kn (snd s) (fst s)) eqn:C; cbn [sivs_den]; rewrite IH; [|reflexivity].
    rewrite (siv_den_empty s (le_lin_sound _ _ C)). reflexivity.
  Qed.
  Lemma drop_empty_wf : ltac2:(zQ "50!u9!kr0!kra!q7!jk5>1l@1$3$0>0@3$1$0@1$2?1E^1@3$1$0@1$2?1E@2$4?2kn^2").
  Proof.
    induction l as [|s l IH]; intros H; [constructor|]. cbn [drop_empty]. apply Forall_cons_iff in H as [H1 H2].
    destruct (le_lin kn (snd s) (fst s)); [exact (IH H2) | constructor; [exact H1 | exact (IH H2)]].
  Qed.

  Lemma sym_sub1_sound : ltac2:(zQ "h40!k1!u9!q7!hkc!hm5!le!hn2!hu7!ne!kra!q2!iie!ihe!hr2!kr0!kn3!ko4!koe!ks3!hr9>1r@2$5$0$0>1x$1>1p@1$2$1>0@2$9?1E^2>0@2$h3@2$3?1E@3$4$0$0^4@2$3?1E@3$6$0$0^4>0@3$7@1$c@1$2$1@3$h2?2kn^5^4@2$b@1$2$1^3@2$d@3$7@1$2@2$5@1$a@1$8#k0@1$a@1$8#k0@3$f@2$h0?1E^5@2$3?1E@3$4$0$0^6@2$3?1E@3$6$0$0^6@2$h1?1E^4@3$e$1@1$9?1E^4").
  Proof.
    intros r x p WF Hr H. unfold sym_sub1 in H.
    ndestruct WF as (W1 & W2 & W3).
    destruct (disjoint_dec kn x r) eqn:D.
    - injection H as <-. split; [|constructor; [split; [assumption|split; assumption] | constructor]].
      cbn [sivs_den]. rewrite app_nil_r.
      destruct (Z.lt_ge_cases (lden E (fst x)) (lden E (snd x))) as [NE|EM].
      + rewrite (siv_den_full x NE). cbn [maps_subtract]. rewrite app_nil_r. unfold iv_subtract.
        rewrite !u_of_Z by lia.
        pose proof (disjoint_dec_sound x r D) as DD.
        destruct DD as [DD|DD].
        * destruct (lden E (fst x) <? lden E (fst r)) eqn:C1; [|apply Z.ltb_ge in C1; lia].
          destruct (lden E (snd r) <? lden E (fst x) + (lden E (snd x) - lden E (fst x))) eqn:C2; [apply Z.ltb_lt in C2; lia|].
          cbn [app]. rewrite Z.min_l by lia. reflexivity.
        * destruct (lden E (fst x) <? lden E (fst r)) eqn:C1; [apply Z.ltb_lt in C1; lia|].
          destruct (lden E (snd r) <? lden E (fst x) + (lden E (snd x) - lden E (fst x))) eqn:C2; [|apply Z.ltb_ge in C2; lia].
          cbn [app]. rewrite Z.max_l by lia. do 2 f_equal. f_equal. lia.
      + rewrite (siv_den_empty x EM). reflexivity.
    - cbn [fst snd] in H.
      set (a := fst x) in *. set (b := snd x) in *. set (lo := fst r) in *. set (hi := snd r) in *.
      destruct (if le_lin kn lo b then Some lo else if le_lin kn b lo then Some b else None) as [mn|] eqn:MN; [|discriminate].
      destruct (if le_lin kn a hi then Some hi else if le_lin kn hi a then Some a else None) as [mx|] eqn:MX; [|discriminate].
      assert (HP : drop_empty kn [(a, mn); (mx, b)] = p) by congruence. clear H. rewrite <- HP.
      assert (HMN : lden E mn = Z.min (lden E b) (lden E lo) /\ lden E mn <= lden E b).
      { destruct (le_lin kn lo b) eqn:C1.
        - injection MN as <-. pose proof (le_lin_sound _ _ C1). rewrite Z.min_r by lia. lia.
        - destruct (le_lin kn b lo) eqn:C2; [|discriminate]. injection MN as <-. pose proof (le_lin_sound _ _ C2). rewrite Z.min_l by lia. lia. }
      assert (HMX : lden E mx = Z.max (lden E a) (lden E hi) /\ lden E a <= lden E mx).
      { destruct (le_lin kn a hi) eqn:C1.
        - injection MX as <-. pose proof (le_lin_sound _ _ C1). rewrite Z.max_r by lia. lia.
        - destruct (le_lin kn hi a) eqn:C2; [|discriminate]. injection MX as <-. pose proof (le_lin_sound _ _ C2). rewrite Z.max_l by lia. lia. }
      destruct HMN as [HMN HMN2]. destruct HMX as [HMX HMX2].
      split.
      2: { apply drop_empty_wf. constructor; [unfold siv_wf; cbn [fst snd]; lia|]. constructor; [unfold siv_wf; cbn [fst snd]; lia|]. constructor. }
      rewrite drop_empty_den. cbn [sivs_den]. rewrite app_nil_r.
      destruct (Z.lt_ge_cases (lden E a) (lden E b)) as [NE|EM].
      + rewrite (siv_den_full x NE). cbn [maps_subtract]. rewrite app_nil_r. unfold iv_subtract.
        fold a. fold b. rewrite !u_of_Z by lia.
        replace (lden E a + (lden E b - lden E a)) with (lden E b) by lia.
        f_equal.
        * unfold siv_den. cbn [fst snd]. rewrite HMN.
          destruct (lden E a <? lden E lo) eqn:C1.
          -- apply Z.ltb_lt in C1. destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C2; [|apply Z.ltb_ge in C2; lia].
             do 2 f_equal. f_equal. lia.
          -- apply Z.ltb_ge in C1. destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
        * unfold siv_den. cbn [fst snd]. rewrite HMX.
          destruct (lden E hi <? lden E b) eqn:C1.
          -- apply Z.ltb_lt in C1. destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [|apply Z.ltb_ge in C2; lia]. reflexivity.
          -- apply Z.ltb_ge in C1. destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
      + rewrite (siv_den_empty x EM). cbn [maps_subtract].
        unfold siv_den. cbn [fst snd]. rewrite HMN, HMX.
        destruct (lden E a <? Z.min (lden E b) (lden E lo)) eqn:C1; [apply Z.ltb_lt in C1; lia|].
        destruct (Z.max (lden E a) (lden E hi) <? lden E b) eqn:C2; [apply Z.ltb_lt in C2; lia|]. reflexivity.
  Qed.

  Lemma sym_sub_sound : ltac2:(zQ "h30!k1!u9!q7!hkc!hm5!le!hn2!hu7!kr0!ne!kra!koe!q2!iie!ihe!hr2!kn3!jq1!hr9>1l@1$2$1>1r@2$5$0$0>1p@1$2$1>0@3$8$1@1$a?1E^3>0@2$h2@2$3?1E@3$4$0$0^3@2$3?1E@3$6$0$0^3>0@3$7@1$e@1$2$1@3$h1?2kn^5^4@2$d@1$2$1^3@2$f@3$7@1$2@2$5@1$c@1$9#k0@1$c@1$9#k0@3$h0@2$b?1E^6@2$3?1E@3$4$0$0^5@2$3?1E@3$6$0$0^5@2$b?1E^4@3$8$1@1$a?1E^4").
  Proof.
    intros l r. induction l as [|x l IH]; intros p WF Hr H; cbn [sym_sub] in H.
    - injection H as <-. split; [reflexivity | constructor].
    - destruct (sym_sub1 kn r x) as [p1|] eqn:H1; [|discriminate].
      destruct (sym_sub kn l r) as [p2|] eqn:H2; [|discriminate]. injection H as <-.
      apply Forall_cons_iff in WF as [WFx WFl].
      destruct (sym_sub1_sound r x p1 WFx Hr H1) as [A1 B1].
      destruct (IH p2 WFl Hr eq_refl) as [A2 B2].
      cbn [sivs_den]. rewrite maps_subtract_app, A1, A2. split; [|apply Forall_app; split; assumption].
      clear. induction p1 as [|s p1 IH]; cbn [sivs_den app]; [reflexivity|]. rewrite <- IH, app_assoc. reflexivity.
  Qed.

  Lemma siv_of_sound : ltac2:(zQ "h81!ne!q2!hr2!hu7!ki1!k1!le!u9!hg1!hsc!hkc!iie!hle!hm5!q7!vb!ihe!hn2!ko4!jqb!kra!kse!ht8!hs6&@2$6@1$1@1$0#k0@1$1@1$0#k0>1a$9>1n$9>1r$7>0@3$3@1$h0$7@3$h3?2kn^3^2@2$b$7^1@2$2@3$3$8@2$a?1E@3$d$5$5^2@2$4?1E^4@2$2@3$3$8@2$a?1E@3$h1$5$5^2@2$h6@2$4?1E^4@2$4?1E^3@2$2@2$h7Z@2$4?1E^3@2$2@2$h4?1E^2@3$3@1$e~0@2$h2?1E^2@3$c~0@3$h5?1E^4^3@1$f~0").
  Proof.
    intros a n r H. unfold siv_of in H.
    destruct (lin_ofx kn a) as [la|] eqn:La; [|discriminate]. destruct (lin_ofx kn n) as [ln|] eqn:Ln; [|discriminate].
    cbn [fst snd] in H.
    destruct (lt_lin kn la (lcat la ln) && le_lin kn (lcat la ln) (lconst (2 ^ 64))) eqn:C; [|discriminate].
    injection H as <-. apply andb_prop in C as [C1 C2]. cbn [fst snd].
    apply lt_lin_sound in C1. apply le_lin_sound in C2. rewrite lconst_den in C2. rewrite lcat_den in *.
    pose proof (lin_ofx_sound a la La) as Ea. pose proof (lin_ofx_sound n ln Ln) as En.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E n)) as Rn. unfold uE in Ea, En |- *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold siv_wf; cbn [fst snd]; rewrite lcat_den; lia|].
    unfold siv_den. cbn [fst snd]. rewrite lcat_den.
    destruct (lden E la <? lden E la + lden E ln) eqn:C; [|apply Z.ltb_ge in C; lia].
    unfold vm_iv. rewrite <- Ea.
    replace (bv_unsigned (edenot E a) + lden E ln - bv_unsigned (edenot E a)) with (bv_unsigned (edenot E n)) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  Lemma sym_step_sound : ltac2:(zQ "h02!q7!u9!ne!q2!le!kr0!kra!koe!hmb!hr2!hu7!iie!ihe!kt7!jp9!ku2&@2$4@1$3@1$2#k0@1$3@1$2#k0&@1$0~0>2op$e>1N@1$0$1>1L@1$0$1>2N'@1$0$1>2L'@1$0$1>0@3$5$1@1$6?1E^4>0@3$5$1@1$6?1E^4>0@3$a@1$c@2$4@1$0$1@1$0$1@3$d?2kn^7@4$8@1$0$1@1$0$1^6^5@2$b@2$4@1$0$1@1$0$1@4$8@1$0$1@1$0$1^4^3@2$9@3$a@2$4~1~1@4$f?1E^8@2$7?1E^7@2$7?1E^6@4$8~1~1@2$7?1E^5@2$7?1E^4@2$9@3$5$1@1$6?1E^5@3$5$1@1$6?1E^4").
  Proof.
    intros op N L N' L' WN WL H. destruct op as [k a n|nr pn a n|a n|a n]; cbn [sym_step] in H.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate]. injection H as <- <-.
      ndestruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      unfold vm_step. split; [|split; [destruct (is_none_kind k) | destruct (is_lazy_kind k)]; try constructor; assumption].
      destruct (is_none_kind k), (is_lazy_kind k); cbn [sivs_den]; rewrite ?R5; reflexivity.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate]. destruct (sym_sub kn L r) as [L1|] eqn:S2; [|discriminate].
      injection H as <- <-. ndestruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1]. destruct (sym_sub_sound L r L1 WL ltac:(lia) S2) as [A2 B2].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1, A2.
      split; [|split; [destruct pn | destruct nr]; try constructor; assumption].
      destruct pn, nr; cbn [sivs_den]; rewrite ?R5; reflexivity.
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate]. destruct (sym_sub kn L r) as [L1|] eqn:S2; [|discriminate].
      injection H as <- <-. ndestruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1]. destruct (sym_sub_sound L r L1 WL ltac:(lia) S2) as [A2 B2].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1, A2. split; [reflexivity | split; assumption].
    - destruct (siv_of kn a n) as [r|] eqn:R; [|discriminate].
      destruct (sym_sub kn N r) as [N1|] eqn:S1; [|discriminate].
      injection H as <- <-. ndestruct (siv_of_sound a n r R) as (R1 & R2 & R3 & R4 & R5).
      destruct (sym_sub_sound N r N1 WN ltac:(lia) S1) as [A1 B1].
      unfold vm_step, vm_lo, vm_hi. fold (uE E a). fold (uE E n). rewrite <- R2, <- R1, A1. split; [reflexivity | split; assumption].
  Qed.

  Theorem sym_replay_sound : ltac2:(zQ "h02!q7!u9!ne!q2!le!hmb!hr2!hu7!kr0!kra!koe!iie!ihe!kud!jp9!kva&@2$4@1$3@1$2#k0@1$3@1$2#k0&@1$0~0>3ops@1$0$e>1N@1$0$1>1L@1$0$1>0@3$7@1$c@2$4@1$0$1@1$0$1@2$d?2kn^3@2$b@2$4@1$0$1@1$0$1@4$5@1$0$1@1$0$1^2^1@2$6@3$7@2$4~1~1@2$f?1E^4@4$5~1~1@2$a?1E^3@2$a?1E^2@2$6@3$8$1@1$9?1E^3@3$8$1@1$9?1E^2").
  Proof.
    induction ops as [|op ops IH]; intros N L H; cbn [sym_replay] in H.
    - injection H as <- <-. split; [reflexivity | split; constructor].
    - destruct (sym_replay kn ops) as [[N0 L0]|] eqn:H0; [|discriminate].
      ndestruct (IH N0 L0 eq_refl) as (A & WN & WL).
      cbn [vm_replay]. rewrite A. exact (sym_step_sound op N0 L0 N L WN WL H).
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_arith : ltac2:(zQ "20!v4!hvd>1K$1$0") := ltac2:(zQ "80!hsc!ika!iv7!hg1!iu0!hvd!iq4!v4\1K$5M5\1K$5$7^1\1a$1\1w$6\1v$0$2\1a$1\1n$0$2\1a$1\1n$0\1k$6$2\2lo$3\2hi$3$2\1e$0\1m$3$4\1e$0\2lo$3\2hi$3$4\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$4\1a$1\1n$0\1c$3$2\1a$1\1n$0$2").
Definition kn_arith : ltac2:(zQ "20!q7!hvd>1k@1$0$1@1$0$1") := ltac2:(zQ "40!hvd!q7!lg7!lh2\1k@1$1$0@3$3$0$2^1").

Lemma kn_arith_ok : ltac2:(zQ "90!q7!ne!lhc!q2!ihe!llc!lm7!uf!hvd>4segs@1$0$5>1E$7>1M>0@1$3@1$1#k0@1$4@1$3@1$1#8>1k@1$0$8>0@4$2^4^3^2^1@4$2^5^4^3@1$6^2").
Proof. intros segs E M k H. unfold kn_arith. apply incl_Forall with (l1 := k); [apply incl_filter | exact H]. Qed.

Lemma cs_ok_vm_closed : ltac2:(zQ "he3!q7!ne!u9!q2!le!ihe!hr2!hu7!uf!kr0!kra!koe!iie!v4!hmb!hg1!lpd!llc!lq3!lqc!lr9!ls5!lva!lm7!kud!mg3!mge!mh5!mhf!mi5&>0@1$3@1$1#k0@1$5@1$3@1$1#8&@2$4@1$3@1$1#k0@1$3@1$1#k0&@1$0~1>4SEGS@1$0$h1>1A$hb>5LIMIT$f>4SINV>0$8>0~0P>4argH>0$8>0@1$3@1$1#k0$d>3FS0$h0>1E$8>2cs$ha>1R@2$h6@1$1#5@1$3@1$1#k0>4FULL~0>5model$h2>1N@1$0$2>1L@1$0$2>0@b$hd^d^c^b^a^9^8^7^6^5^4^3>0@3$7@1$5@2$4@1$0$2@1$0$2@2$h8@1$h7@1$hc^7@1$h9^7@2$c@2$4@1$0$2@1$0$2@4$e@1$0$2@1$0$2^3^2@2$6@3$7~2@1$h5@1$h4^5@2$b^9^4@2$6@3$7~2@1$h3^5@2$b^9^3@2$6@3$9$2@1$a^9^4@3$9$2@1$a^9^3").
Proof.
  intros SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR.
  pose proof (kn_arith_ok _ _ _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as KN.
  destruct (sym_replay_sound SEGS E _ _ KN (a_vmops cs) N L HR) as (HV & WN & WL).
  destruct (co_vmx _ _ _ _ _ _ _ _ _ _ _ HC) as [H1 H2]. rewrite HV in H1, H2. cbn [fst snd] in H1, H2.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3B.
Import AX2B.

Definition le_linB : ltac2:(zQ "30!k1!v4!mn1>2bc$2>1x$0>1y$0$1") := ltac2:(zQ "c0!hg1!q7!le!hsc!hm5!hn2!k1!igf!mn1!mn9!ih7!hp7\2bc$8\1x$6\1y$6@4$9^3@2$b@3$4$0@1$1@2$2$0$3^1@3$4$0@1$1@2$2$0$3^2@2$7@3$5$0@1$1@2$2$0$3^1@3$5$0@1$1@2$2$0$3^2\2lo$0\0$0@2$aZ^2").
Definition lt_linB : ltac2:(zQ "30!k1!v4!mn1>2bc$2>1x$0>1y$0$1") := ltac2:(zQ "c0!hg1!q7!le!hsc!hm5!hn2!k1!igf!mn1!mn9!hp0!hp7\2bc$8\1x$6\1y$6@4$9^3@2$b@3$4$0@1$1@2$2$0$3^1@3$4$0@1$1@2$2$0$3^2@2$7@3$5$0@1$1@2$2$0$3^1@3$5$0@1$1@2$2$0$3^2\2lo$0\0$0@2$aZ^2").
Definition lin_ofxB : ltac2:(zQ "40!ihe!hsc!k1!mn1>2bc$3>1e$1@1$0$2") := ltac2:(zQ "90!k1!v4!ii7!iie!ihe!hsc!ik2!mn1!mo6\2bc$7\1e$5M1\0$1@1$4$0@2$8^2^1@2$3$0@1$6^1@1$2$0").
Definition lin_ofaB : ltac2:(zQ "40!ihe!k1!ika!mn1>2bc$3>1a$2@1$0$1") := ltac2:(zQ "b0!k1!ihe!ii7!iie!hud!hv4!mp6!ilb!im3!ika!mn1\2bc$a\1a$9M1\1x@1$1$0@1$1$0@2$6^2@1$7^1\1l$0@2$3$0@2$4^1@1$5@1$8^2@1$2$0").
Definition insideB : ltac2:(zQ "40!k1!v4!u9!mn1>2bc$3>1x$2>3flo$0>3fhi$0$1") := ltac2:(zQ "70!k1!mq1!in3!hm5!hn2!u9!mn1\2bc$6\1x$5\3flo$0\3fhi$0@2$2@3$1^4^2@3$3$0$0^3@3$1^4@3$4$0$0^3^1").
Definition kdisj1B : ltac2:(zQ "40!u9!v4!hvd!mn1>2bc$3>1x$0>1r$0>1K$2$1") := ltac2:(zQ "h40!iv7!hsc!k1!v4!ihe!ika!hg1!mqb!hvd!in3!iq4!hud!mr5!mp6!u9!ilb!jh2!iv1!jh9!mn1\2bc$h3\1x$e\1r$e\1K$8M8\1K$8$3^1\1a$5\1w$a\1v$1$0\1a$5\1n$1$0\1a$5\1n$1\1k$a$0\2lo$6\2hi$6$0\1e$1\1m$6$0\1e$1\2lo$6\2hi$6$0\1a$5\1n$1$0\2a1$5\2n1$1\2a2$5\2n2$1M3\0$3$3@1$h0@4$h2^7^6@1$f^4@1$f^2$0M4\1x@1$4$2$3@2$c^8^4\2f1$2M4\1x@1$4$2$3@2$d^9^4\2m1$2M4\1x@1$4$2$3@2$c^a^4\2f2$2M4\1x@1$4$2$3@2$d^b^4\2m2$2=2g1$2@2$b^4^3=2g2$2@2$b^3^2@2$h1@2$9@4$7^e^d^6^2@4$7^e^c^4^1@2$9@4$7^e^d^4^1@4$7^e^c^6^2$0$0$0$0\1a$5\1n$1\1c$6$0\1a$5\1n$1$0").
Definition kdisjB : ltac2:(zQ "30!u9!v4!mn1>2bc$2>1x$0>1r$0$1") := ltac2:(zQ "60!u9!ms0!hvd!msa!mn1!ip9\2bc$4\1x$0\1r$0@3$5$2@3$1^3^2^1@1$3^3").
Definition disjoint_decB : ltac2:(zQ "30!u9!v4!mn1>2bc$2>1x$0>1r$0$1") := ltac2:(zQ "80!k1!hm5!iv1!hn2!mq1!u9!mt3!mn1\2bc$7\1x$5\1r$5@2$2@2$2@3$4^3@3$3$0$0^2@3$1$0$0^1@3$4^3@3$3$0$0^1@3$1$0$0^2@3$6^3^2^1").
Fixpoint drop_emptyB (bc : bctx) (l : list siv) : list siv :=
  match l with
  | [] => []
  | s :: r => if le_linB bc (snd s) (fst s) then drop_emptyB bc r else s :: drop_emptyB bc r
  end.
Definition sym_sub1B : ltac2:(zQ "40!u9!q7!ihe!mn1>2bc$3>1r$0>1x$0@1$2@1$1$0") := ltac2:(zQ "h10!k1!ihe!u9!v4!q7!iie!ii7!mq1!hle!le!hm5!vb!hmb!hn2!mtc!muc!mn1\2bc$h0\1r$2\1x$2M3\0$3@1$1@1$4$2@3$e^3^1^2@2$5@1$4$2@3$8$2^1@1$b$2=1a$0@3$a$0$0^1=1b$0@3$d$0$0^2=2lo$0@3$a$0$0^4=2hi$0@3$d$0$0^5M1\1x@1$1$0@1$1@1$4$2M3\0$3@1$1$0@3$7^7^2^3@2$5$0^2M3\0$3@1$1$0@3$7^7^3^2@2$5$0^3@1$6$0\2mn$0M1\1x@1$1$0@1$1@1$4$2M3\0$3@1$1$0@3$7^8^5^2@2$5$0^2M3\0$3@1$1$0@3$7^8^2^5@2$5$0^5@1$6$0\2mx$0@2$5@1$4$2@2$f^9@3$8@2$9$0$0@4$c$0$0^6^2@3$8@2$9$0$0@4$c$0$0^1^5@1$b@2$9$0$0@1$6@1$4$2@1$6@1$4$2").
Fixpoint sym_subB (bc : bctx) (l : list siv) (r : siv) : option (list siv) :=
  match l with
  | [] => Some []
  | x :: l' => match sym_sub1B bc r x, sym_subB bc l' r with
               | Some p, Some q => Some (p ++ q)
               | _, _ => None
               end
  end.
Definition siv_ofB : ltac2:(zQ "40!hsc!ihe!u9!mn1>2bc$3>1a$0>1n$0@1$1$2") := ltac2:(zQ "h30!k1!ihe!u9!ii7!v4!le!hn2!mp6!hsc!iie!in3!hm5!hmb!hud!hv4!mq1!mva!mn1!hrf\2bc$h1\1a$8\1n$8M1\1x@1$1$0@1$1$2@2$7^3^2\2la$0M1\1x@1$1$0@1$1$2@2$7^4^2\2ln$0=1r@2$5$0$0@4$c$0$0^2@2$d^2^1M4\0$4@1$1$2@2$a@3$h0^6@3$b$0$0^1@3$6$0$0^1@3$f^6@3$6$0$0^1@1$e@2$h2+2+k0@2$9@2$5$0$0^1@1$3$2@1$3$2@1$3$2").
Definition sym_stepB : ltac2:(zQ "60!q7!u9!le!ihe!jp9!mn1>2bc$5>2op$4>2NL@2$2@1$0$1@1$0$1@1$3@2$2@1$0$1@1$0$1") := ltac2:(zQ "h12!u9!q7!ihe!le!v4!ii7!hsc!ng4!iie!hle!hmb!ngf!jp9!jr4!kg1!kh1!mn1&\1x@1$2$0@1$2@2$3@1$1$0@1$1$0&\1x@1$2@1$1$0@1$2@2$3@1$1$0@1$1$0\2bc$h0\2op$c\2NL@2$3@1$1$0@1$1$0M3\2NL@2$3@1$1$0@1$1$0@1$2@2$3@1$1$0@1$1$0^1\1N@1$1$0\1L@1$1$0Mc\2op$c@1$2@2$3@1$1$0@1$1$0^4\1k$d\1a$6\1n$6M2~0@3$b^8^2^1\1r$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0M4\0$4@1$1$0@1$f^4@3$9$0^1^6^6M4\0$4@1$1$0@1$e^4@3$9$0^1^5^5@1$5@2$3@1$1$0@1$1$0\2nr$4\2pn$4\1a$6\1n$6M2~0@3$b^9^2^1\1r$0M2~1@3$7^a^7^1\2N'@1$1$0M2~1@3$7^b^7^2\2L'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0M4\2pn$4@1$1$0^6@3$9$0^3^2^2M4\2nr$4@1$1$0^7@3$9$0^3^1^1@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0\1a$6\1n$6M2~0@3$b^7^2^1\1r$0M2~1@3$7^8^5^1\2N'@1$1$0M2~1@3$7^9^5^2\2L'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0^2^1@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0\1a$6\1n$6M2~0@3$b^7^2^1\1r$0M2~1@3$7^8^5^1\2N'@1$1$0@2$8@2$3@1$1$0@1$1$0@4$a@1$1$0@1$1$0^1^5@1$5@2$3@1$1$0@1$1$0@1$5@2$3@1$1$0@1$1$0").
Fixpoint sym_replayB (bc : bctx) (ops : list vmop) : option (list siv * list siv) :=
  match ops with
  | [] => Some ([], [])
  | op :: r => match sym_replayB bc r with Some NL => sym_stepB bc op NL | None => None end
  end.
(* [comment removed for export] *)
Definition cs_ledgers : ltac2:(zQ "50!q7!u9!ihe!le!mge>2cs$4@1$2@2$3@1$0$1@1$0$1") := ltac2:(zQ "60!lm7!nh9!mg3!mge!mhf!ni7\2cs$3@2$1@1$5@1$0@1$4^1@1$2^1").

Section BEq.
  Variable fk : ltac2:(zQ "20!q7!hvd@1$0$1").
  #[local] Notation bc := (mkbc fk).
  Lemma le_linB_eqf : ltac2:(zQ "60!k1!v4!hu7!ima!mq1!ni7>1x$0>1y$0@3$2$1@3$4@1$5?2fk^2^1@3$3?2fk^2^1").
  Proof. intros. unfold le_linB, le_lin. rewrite lin_testB_eqf. reflexivity. Qed.
  Lemma lt_linB_eqf : ltac2:(zQ "60!k1!v4!hu7!jl2!mva!ni7>1x$0>1y$0@3$2$1@3$4@1$5?2fk^2^1@3$3?2fk^2^1").
  Proof. intros. unfold lt_linB, lt_lin. rewrite lin_testB_eqf. reflexivity. Qed.
  Lemma lin_ofxB_eqf : ltac2:(zQ "70!ihe!hu7!il1!mp6!hsc!k1!ni7>1e$4@3$1@1$0$5@2$3@1$6?2fk^1@2$2?2fk^1").
  Proof. intros. unfold lin_ofxB, lin_ofx. rewrite lin_nowrapRB_eqf. reflexivity. Qed.
  Lemma lin_ofaB_eqf : ltac2:(zQ "70!ihe!hu7!jg8!mr5!k1!ika!ni7>1a$5@3$1@1$0$4@2$3@1$6?2fk^1@2$2?2fk^1").
  Proof. intros. unfold lin_ofaB, lin_ofa. rewrite lin_ofxB_eqf. reflexivity. Qed.
  Lemma insideB_eqf : ltac2:(zQ "70!k1!v4!hu7!ivf!mqb!u9!ni7>1x$5>1f$0>1g$0@3$2$1@4$4@1$6?2fk^3^2^1@4$3?2fk^3^2^1").
  Proof. intros. unfold insideB, inside. rewrite !le_linB_eqf. reflexivity. Qed.
  Lemma kdisj1B_eqf : ltac2:(zQ "70!u9!v4!hu7!ji5!ms0!hvd!ni7>1x$0>1r$0>1K$5@3$2$1@4$4@1$6?2fk^3^2^1@4$3?2fk^3^2^1").
  Proof. intros x r K. destruct K; try reflexivity. cbn [kdisj1B kdisj1]. destruct (negb _); [reflexivity|]. rewrite !lin_ofaB_eqf, !lin_ofxB_eqf.
         repeat (destruct (lin_ofa fk _) || destruct (lin_ofx fk _)); try reflexivity. rewrite !insideB_eqf. reflexivity. Qed.
  Lemma kdisjB_eqf : ltac2:(zQ "60!u9!v4!hu7!jie!mt3!ni7>1x$0>1r$0@3$2$1@3$4@1$5?2fk^2^1@3$3?2fk^2^1").
  Proof.
    intros. unfold kdisjB, kdisj. rewrite bc_fk_mkbc.
    assert (H : forall l, existsb (kdisj1B bc x r) l = existsb (kdisj1 fk x r) l).
    { induction l as [|K l IH]; [reflexivity|]. cbn [existsb]. rewrite kdisj1B_eqf, IH. reflexivity. }
    apply H.
  Qed.
  Lemma disjoint_decB_eqf : ltac2:(zQ "60!u9!v4!hu7!jj6!mtc!ni7>1x$0>1r$0@3$2$1@3$4@1$5?2fk^2^1@3$3?2fk^2^1").
  Proof. intros. unfold disjoint_decB, disjoint_dec. rewrite !le_linB_eqf, kdisjB_eqf. reflexivity. Qed.
  Lemma drop_emptyB_eqf : ltac2:(zQ "60!q7!u9!hu7!jk5!muc!ni7>1l@1$0$1@3$2@1$0$1@2$4@1$5?2fk^1@2$3?2fk^1").
  Proof. induction l as [|s l IH]; [reflexivity|]. cbn [drop_emptyB drop_empty]. rewrite le_linB_eqf, IH. reflexivity. Qed.
  Lemma sym_sub1B_eqf : ltac2:(zQ "70!u9!q7!ihe!hu7!ks3!nif!ni7>1r$0>1x$0@3$3@1$2@1$1$0@3$5@1$6?2fk^2^1@3$4?2fk^2^1").
  Proof.
    intros. unfold sym_sub1B, sym_sub1. rewrite disjoint_decB_eqf, !le_linB_eqf.
    destruct (disjoint_dec fk x r); [reflexivity|].
    destruct (le_lin fk (fst r) (snd x)), (le_lin fk (snd x) (fst r)), (le_lin fk (fst x) (snd r)), (le_lin fk (snd r) (fst x));
      rewrite ?drop_emptyB_eqf; reflexivity.
  Qed.
  Lemma sym_subB_eqf : ltac2:(zQ "70!u9!q7!ihe!hu7!jq1!ng4!ni7>1l@1$1$0>1r$0@3$3@1$2@1$1$0@3$5@1$6?2fk^2^1@3$4?2fk^2^1").
  Proof. induction l as [|x l IH]; intros r; [reflexivity|]. cbn [sym_subB sym_sub]. rewrite sym_sub1B_eqf, IH. reflexivity. Qed.
  Lemma siv_ofB_eqf : ltac2:(zQ "70!hsc!ihe!hu7!u9!jqb!ngf!ni7>1a$0>1n$0@3$2@1$1$3@3$5@1$6?2fk^2^1@3$4?2fk^2^1").
  Proof.
    intros. unfold siv_ofB, siv_of. rewrite !lin_ofxB_eqf.
    destruct (lin_ofx fk a), (lin_ofx fk n); try reflexivity. rewrite lt_linB_eqf, le_linB_eqf. reflexivity.
  Qed.
  Lemma sym_stepB_eqf : ltac2:(zQ "90!q7!u9!le!ihe!hu7!kt7!njb!jp9!ni7>2op$7>2NL@2$2@1$0$1@1$0$1@3$4@1$3@2$2@1$0$1@1$0$1@3$6@1$8?2fk^2^1@3$5?2fk^2^1").
  Proof. intros op [N L]. destruct op; cbn [sym_stepB sym_step]; rewrite siv_ofB_eqf, ?sym_subB_eqf; try reflexivity;
         destruct (siv_of fk _ _); rewrite ?sym_subB_eqf; reflexivity. Qed.
  Lemma sym_replayB_eqf : ltac2:(zQ "90!q7!u9!ihe!le!hu7!kud!nh9!jp9!ni7>3ops@1$0$7@3$4@1$2@2$3@1$0$1@1$0$1@2$6@1$8?2fk^1@2$5?2fk^1").
  Proof. induction ops as [|op ops IH]; [reflexivity|]. cbn [sym_replayB sym_replay]. rewrite IH. destruct (sym_replay fk ops); [apply sym_stepB_eqf | reflexivity]. Qed.
End BEq.

Theorem cs_ledgers_sound : ltac2:(zQ "hb3!q7!ne!u9!q2!le!ihe!hr2!hu7!uf!kr0!kra!koe!iie!v4!hmb!hg1!lpd!llc!lq3!lqc!lr9!ls5!lva!nk7!mge!mh5!mi5&>0@1$3@1$1#k0@1$5@1$3@1$1#8&@2$4@1$3@1$1#k0@1$3@1$1#k0&@1$0~1>4SEGS@1$0$h1>1A$h9>5LIMIT$f>4SINV>0$8>0~0P>4argH>0$8>0@1$3@1$1#k0$d>3FS0$h0>1E$8>2cs$h8>1R@2$h6@1$1#5@1$3@1$1#k0>4FULL~0>5model$h2>1N@1$0$2>1L@1$0$2>0@b$ha^d^c^b^a^9^8^7^6^5^4^3>0@3$7@1$5@2$4@1$0$2@1$0$2@1$h7^7@2$c@2$4@1$0$2@1$0$2@4$e@1$0$2@1$0$2^3^2@2$6@3$7~2@1$h5@1$h4^5@2$b^9^4@2$6@3$7~2@1$h3^5@2$b^9^3@2$6@3$9$2@1$a^9^4@3$9$2@1$a^9^3").
Proof.
  intros SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR. unfold cs_ledgers in HR. rewrite sym_replayB_eqf in HR.
  exact (cs_ok_vm_closed SEGS A LIMIT SINV argH FS0 E cs R FULL model N L HC HR).
Qed.
