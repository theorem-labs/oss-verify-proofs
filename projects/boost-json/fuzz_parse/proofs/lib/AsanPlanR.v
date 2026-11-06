(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith PArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~05saddr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsanPlanR3APR8WithSegs3MAP~~~~~~k84emap02SA06a_base05a_off06kentry04exprk84amap37Corelib7Numbers7BinNumss41Z37Corelib4Init9Datatypesu13nat06KAlign05KBlob05KDisj05KFill04KImg06KRange04KUnk05KWord03KWr05KZero06sentry02SEu14list89OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsanPlanR3APR8WithSegs~~~~~~hl63ren05ptreeu14produ14units48positiveu13fstu13nilu13snd06PTLeaf36Stdlib5Lists4Listhu0afold_right79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanPlanCore3APC~~~~~~ig1bexpr_vars_tig1dkentry_vars_tig14vkeyhl63RENhl66mk_sighl65psorthl67pt_keys46Stdlib5Arith8PeanoNat3Natip14predu14boolu16optionhl65r_sig06pt_getip13ltb37Corelib4Init3Natitc3subhl63r_Mitc3add37Corelib5Lists7ListDefjg33nthhl66r_isigu14andbjg33map08sidecondhl63bwdu14Noneu14pairhl64emaphl64kmap05s_logig1akn_vars_ltig1asr_vars_lthl63fwd06s_regsu14Someu16lengthu14truehl66kn_eqbhl6blog_vars_lthl66mk_renhl64smaphl66sr_eqb03SSR08facts_of06s_know06s_next04s_pc09sym_state79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~kh64bctxkh66carryKkh63kixkh66mk_kixkh64mkbckh6csym_execTXBIip13eqbip13lebhu07forallb05carry0asym_execTX37Corelib4Init5Logicks02eqhl69run_coreRhl6drun_coreR_refig13acsig14hullig14a_ssig18fresh_okig16hs_nilig15mk_ssig1dstore_in_winsig17with_ss3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelka7Segment04itabig16atable" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module APR.
Import AX2. Import AX2B. Import APC.

Section WithSegs.
Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hkf!lnf@1$0$1").
Variable IT : ltac2:(zQ "10!loa$0").
Variable A : ltac2:(zQ "10!lp0$0").
Variable nx0 : nat.

(* [comment removed for export] *)
Section MAP.
Variable f : ltac2:(zQ "10!v9>0$0$0").
Fixpoint emap (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EVar n => EVar (f n)
  | EAlu o a b => EAlu o (emap a) (emap b)
  | EAluw o a b => EAluw o (emap a) (emap b)
  | EMd o a b => EMd o (emap a) (emap b)
  | EMdw o a b => EMdw o (emap a) (emap b)
  | EExt s l n a => EExt s l n (emap a)
  | EBlob s k i n => EBlob s k i n
  end.
Definition amap : ltac2:(zQ "10!k1>1a$0$0") := ltac2:(zQ "50!p5!pc!q0!q8!k1\1a$4@2$1@1$0@1$2^1@1$3^1").
Definition kmap : ltac2:(zQ "10!qf>1K$0$0") := ltac2:(zQ "h10!p5!r7!rd!k1!td!qf!v9!vf!hg7!hge!hh5!hhc!hi2!hia!hj0!hj7!hjc\1K$5M5\1K$5$5^1\1a$3\1w$6\1v$1@3$e@1$2^3^2@1$0^1\1a$3\1n$1@2$h0@1$2^2@1$0^1\1a$3\1n$1\1k$6@3$8@1$2^3@1$0^2^1\2lo$4\2hi$4@2$b^2^1\1e$1\1m$4@2$7@1$0^2^1\1e$1\2lo$4\2hi$4@3$c@1$0^3^2^1\1a$3\1n$1@2$f@1$2^2@1$0^1\2a1$3\2n1$1\2a2$3\2n2$1@4$9@1$2^4@1$0^3@1$2^2@1$0^1\1a$3\1n$1\1c$4@3$a@1$2^3@1$0^2^1\1a$3\1n$1@2$d@1$2^2@1$0^1").
Definition smap : ltac2:(zQ "10!hk3>1s$0$0") := ltac2:(zQ "70!hk3!v9!rd!p5!hkb!r7!k1\1s$0M0\1s$0$0^1\1a$6\1w$1\1v$5@3$4@1$2^3^2@1$3^1").
End MAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint pt_keys (t : ptree unit) (p : positive -> positive) (acc : list positive) : list positive :=
  match t with
  | PTLeaf => acc
  | PTNode l o r =>
      let acc := pt_keys r (fun k => p (xI k)) acc in
      let acc := match o with Some _ => p xH :: acc | None => acc end in
      pt_keys l (fun k => p (xO k)) acc
  end.
Fixpoint pins (k : positive) (l : list positive) : list positive :=
  match l with [] => [k] | m :: r => if Pos.ltb k m then k :: l else m :: pins k r end.
Fixpoint psort (l : list positive) (acc : list positive) : list positive :=
  match l with [] => acc | k :: r => psort r (pins k acc) end.

(* [comment removed for export] *)
Record ren := REN { r_sig : ptree nat; r_isig : list nat; r_M : nat }.

Fixpoint mk_sig (keys : list positive) (k0 : positive) (i : nat) (sig : ptree nat) (isig : list nat) : ptree nat * list nat * nat :=
  match keys with
  | [] => (sig, rev isig, i)
  | k :: rest => if Pos.leb k k0 then mk_sig rest k0 i sig isig
                 else mk_sig rest k0 (S i) (pt_set k i sig) (Nat.pred (Pos.to_nat k) :: isig)
  end.
Definition mk_ren : ltac2:(zQ "40!hkf!hpf!r7!qf>2sr@1$0$2>1k@1$0$3$1") := ltac2:(zQ "h51!v9!hkf!hq6!hqd!hr4!hrb!hs6!hsc!ht2!ht8!r7!qf!hv3!ik4!il3!im4!imc!in3!ind!io6!iqc&@3$6@2$3@1$2$0@1$1$0$0^1\2sr@1$1$a\1k@1$1$b=1t@1$2$4@5$c@1$2$4$a$d@5$c@1$2$4$b$e@1$9$4^1^2=4keys@1$1$5@2$h2@3$h3^1\1p$5^1@1$7$5@1$7$5=3res@2$3@2$3@1$2$0@1$1$0$0@5$h1^1@1$f@1$h4?3nx0?3nx0@1$9$0@1$7$0@3$h0@3$6@1$2$0@1$1$0~0@3$8@1$2$0@1$1$0~0@3$8@2$3@1$2$0@1$1$0$0^1").

(* [comment removed for export] *)
Definition fwd : ltac2:(zQ "20!v9!hpf>1r$1>1n$0$0") := ltac2:(zQ "80!v9!ir4!irb!im4!is4!hpf!isd!it5\1r$5\1n$0M1\0$1$0@2$7^1?3nx0^1M2\1x@1$2$0$0@3$6$0@1$4^2@1$3^1\1i$0^1^1").
Definition bwd : ltac2:(zQ "20!v9!hpf>1r$1>2nx$0>1i$0$0") := ltac2:(zQ "90!v9!ir4!iue!iv5!it5!ivc!jha!ji1!hpf\1r$8\2nx$0\1i$0M1\0$1$0@2$4^1?3nx0^1M1\0$1$0@2$4^1@1$3^3@4$6$0@2$2^1?3nx0@1$7^3N0@2$5^2@2$2^1@1$3^3").

(* [comment removed for export] *)
Fixpoint sr_eqb (a b : list expr) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => expr_eqb x y && sr_eqb a' b' | _, _ => false end.
Fixpoint kn_eqb (a b : list kentry) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => kentry_eqb x y && kn_eqb a' b' | _, _ => false end.
Fixpoint log_vars_lt (b : nat) (l : list sentry) : bool :=
  match l with [] => true | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r end.

(* [comment removed for export] *)
Definition run_coreR : ltac2:(zQ "80!hkf!v9!hqd!td!r7!qf!irb!hk3>1K$1>4fuel$1>5stops@1$0$3>1p$3>2sr@1$0$4>1k@1$0$5>2nx$1@1$6@2$2@2$2@2$2@2$2$3@1$0$4@1$0$7@1$0$5$1") := ltac2:(zQ "j55!hkf!hqd!qf!r7!v9!td!hk3!jib!ir4!jj2!jj9!irb!jk3!jka!jl1!jl8!jm0!jm8!hsc!ivc!jmf!jnd!job!ji1!jp2!jpa!jq1!jqa!iue!jr1!jrb!jsa!iv5!hpf!jt4!jtc!ju6!jub!jv5!jvd!kg5!k1!kgb!kl9!km1!kmb!kn2!knc!ko4!kp4!kpb!it5!kq2&@2$1@2$1@2$1$5@1$0$3@1$0$6@1$0$2&@2$1~0$4&@1$b~1&\0$8~2&@1$d~1\1K$4\4fuel$4\5stops@1$0$5\1p$5\2sr@1$0$3\1k@1$0$2\2nx$4=1r$i1@2$hf^3^2=1M$4@1$i0^1=3srR@1$0$3@4$9$3$3@1$f@1$h6^2^5=3knR@1$0$2@4$9$2$2@1$h0@1$h6^3^5M8~3@2$7@2$7@2$7@2$7@2$7@2$7@2$i3@4$9$3$3@1$f@2$c^4^5^2^7@2$hd@4$9$2$2@1$h0@2$c^4^5^1^6@3$j4$4\1u$4@2$j3^1^6@1$h7^4@2$j2?3nx0^3@2$j1^3@2$h3?3nx0@2$ha$4@1$h7^4@2$h5^3^2@2$h4^3^1=2bc$ib@1$if@1$i5^1=2kx$id@1$ie^2=3ss'$ia@9$j0?4segs^2^1?2IT^d^c$hb^b@6$i4^a^4@1$h2$6^3^5@1$d$i9M1\1x@2$1@2$1@1$0$2@1$0$a@1$0$8~2@4$ic^3@1$h1^1@1$i6^1@1$h2$8\2p0@2$1@1$0$2@1$0$a\1l@1$0$8M1\2p0@2$1@1$0$2@1$0$a~2^2\3kn'@1$0$2\2l0@1$0$aM0\2l0@1$0$a~2^1=3nx'$4@1$i7^5M8~3@2$7@2$7@2$h5^1@1$h8^6@2$he^1@1$h1^6@2$h4^1^3@2$h9~1@4$e~0$4@4$e@2$1@2$1$5@1$0$3@1$0$6@1$0$2@4$e@2$1$5@1$0$3@1$0$6@4$e$5@1$0$3@1$i8^6@4$9$3$3@1$f@2$c^c^d@1$h8^6@4$9$6$6@1$i2@2$c^c^d@1$h1^6@4$9$2$2@1$h0@2$c^c^d^3@2$h3^d@2$hc^1^b~4\1s$a\2l1@1$0$a~4~4").

(* [comment removed for export] *)
Definition run_coreR_ref : ltac2:(zQ "80!hkf!v9!hqd!td!r7!qf!irb!hk3>1K$1>4fuel$1>5stops@1$0$3>1p$3>2sr@1$0$4>1k@1$0$5>2nx$1@1$6@2$2@2$2@2$2@2$2$3@1$0$4@1$0$7@1$0$5$1") := ltac2:(zQ "j05!hkf!hqd!qf!r7!v9!td!hk3!jib!ir4!jj2!jj9!irb!jk3!jka!jl1!jl8!jm0!jm8!hsc!ivc!jmf!jnd!job!ji1!jp2!jpa!jq1!jqa!iue!jr1!jrb!jsa!iv5!hpf!jt4!jtc!ju6!kqd!jv5!jvd!kg5!k1!kr4!kgb!kp4!kpb!it5!kq2&@2$1@2$1@2$1$5@1$0$3@1$0$6@1$0$2&@2$1~0$4&@1$b~1&\0$8~2&@1$d~1\1K$4\4fuel$4\5stops@1$0$5\1p$5\2sr@1$0$3\1k@1$0$2\2nx$4=1r$i1@2$hf^3^2=1M$4@1$i0^1=3srR@1$0$3@4$9$3$3@1$f@1$h6^2^5=3knR@1$0$2@4$9$2$2@1$h0@1$h6^3^5M8~3@2$7@2$7@2$7@2$7@2$7@2$7@2$i3@4$9$3$3@1$f@2$c^4^5^2^7@2$hd@4$9$2$2@1$h0@2$c^4^5^1^6@3$if$4\1u$4@2$ie^1^6@1$h7^4@2$id?3nx0^3@2$ic^3@2$h3?3nx0@2$ha$4@1$h7^4@2$h5^3^2@2$h4^3^1=3ss'$ib@7$ia?4segs?2IT^b^a$hb^9@6$i4^8^2@1$h2$6^1^3@1$d$i9M1\1x@2$1@2$1@1$0$2@1$0$a@1$0$8~2@3$i5@1$h1^1@1$i6^1@1$h2$8\2p0@2$1@1$0$2@1$0$a\1l@1$0$8M1\2p0@2$1@1$0$2@1$0$a~2^2\3kn'@1$0$2\2l0@1$0$aM0\2l0@1$0$a~2^1=3nx'$4@1$i7^5M8~3@2$7@2$7@2$h5^1@1$h8^6@2$he^1@1$h1^6@2$h4^1^3@2$h9~1@4$e~0$4@4$e@2$1@2$1$5@1$0$3@1$0$6@1$0$2@4$e@2$1$5@1$0$3@1$0$6@4$e$5@1$0$3@1$i8^6@4$9$3$3@1$f@2$c^a^b@1$h8^6@4$9$6$6@1$i2@2$c^a^b@1$h1^6@4$9$2$2@1$h0@2$c^a^b^3@2$h3^b@2$hc^1^9~4\1s$a\2l1@1$0$a~4~4").
Lemma run_coreR_eq : ltac2:(zQ "b0!hkf!v9!hqd!td!r7!qf!irb!kt4!kta!ku7!hk3>1K$1>4fuel$1>5stops@1$0$3>1p$3>2sr@1$0$4>1k@1$0$5>2nx$1@3$7@1$6@2$2@2$2@2$2@2$2$3@1$0$4@1$0$a@1$0$5$1@7$8^7^6^5^4^3^2^1@7$9^7^6^5^4^3^2^1").
Proof.
  intros. unfold run_coreR, run_coreR_ref.
  match goal with |- (if ?c then _ else _) = _ => destruct c; [|reflexivity] end. cbv zeta.
  rewrite (sym_execTXBI_eq segs (List.map (kmap (fwd (mk_ren sr k))) k)) by reflexivity.
  set (ss' := sym_execTX segs IT K fuel true stops _).
  replace (mkbc (facts_of (List.map (kmap (fwd (mk_ren sr k))) k))) with (mkbc (facts_of (s_know ss'))) by (unfold ss'; rewrite sym_execTX_know; reflexivity).
  rewrite carryK_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition run_block_fzR : ltac2:(zQ "60!hkf!v9!kv8!kvf!irb!td>2hs@1$0$3>2ws@1$0$3>1K$1>4fuel$1>5stops@1$0$5>2cs$2@1$4$2") := ltac2:(zQ "hb2!hqd!hkf!kv8!td!r7!irb!hk3!ir4!v9!qf!jka!kvf!jpa!jqa!lg7!lgf!lhb!li5!lie!ljf!kta!jv5!jvd!kg5!jp2!kgb!kq2&@2$0@2$0@2$0$3@1$1$4@1$1$6@1$1$9&@2$0~0$8\2hs@1$1$b\2ws@1$1$b\1K$8\4fuel$8\5stops@1$1$3\2cs$2M7\0$7@1$5$2@2$f?3nx0^1=2ss$h9@1$e^1M5\1x@1$5~1@1$5$2@7$h4^5^4^3@1$h7^1@1$h8^1@1$h5^1@1$h6^1\1p~1M0\1p~1@1$5$2^1\2p0~0\3nx'$8M0\2p0~0@1$5$2^2\2p1@2$0@2$0$3@1$1$4@1$1$6\3kn'@1$1$9M0\2p1@2$0@2$0$3@1$1$4@1$1$6@1$5$2^2\2p2@2$0$3@1$1$4\4log'@1$1$6M0\2p2@2$0$3@1$1$4@1$5$2^2\2p'$3\3sr'@1$1$4M7\0$7@1$5$2M7\0$7$7@1$h0^h0$d@3$ha$6@1$h2^f^3@2$c$2@2$h3^b@4$h1^2^1^5^7@1$a$2@1$a$2@1$a$2").

(* [comment removed for export] *)
Fixpoint run_fitemsR (hs ws : list hull) (seed : ptree unit) (n0 : nat) (K fuel : nat) (more : list Z) (items : list fitem) (cs : acs) : option acs :=
  match items with
  | [] => Some cs
  | it :: rest =>
      if Nat.leb n0 (nxt cs) then
        match (match it with
               | FRun gc stops => match run_block_fzR hs ws K fuel (stops ++ more) cs with Some cs' => Some (if gc then cs_gc_seed nx0 seed cs' else cs') | None => None end
               | FFill i => if fill_in_wins hs ws cs then summary_fill A nx0 cs (if i then x_imemset A else x_memset A) (if i then 256 else two64) else None
               end) with
        | Some cs' => run_fitemsR hs ws seed n0 K fuel more rest cs'
        | None => None
        end
      else None
  end.

End WithSegs.
End APR.
