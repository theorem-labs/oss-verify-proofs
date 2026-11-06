(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec
  XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~i94expri95saddr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~nd5substi92SAi95a_off04bool37Corelib7Numbers7BinNumstb1Z3h5LinuxProcessSemantics5Riscv5Instrv85aluopv85mulopnd6esubsti94EAlui95EAluwi95EBlobi94EExti94ELiti93EMdi94EMdwi94EVari96a_basei95two6446Stdlib6ZArith6BinInt1Zhnf3addhnf6moduloi96kentrynd6asubsti96KAligni95KBlobi95KDisji95KFilli94KImgi96KRangei94KUnki95KWordi93KWri95KZeroi93env06optiontb4Nposnd6sg_geti93Envi92ebi96edenoti92ev35stdpp9bitvectorbdefinitionsijf2bv37Corelib4Init5Logicim22eqnd2Es89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~io16estarti96adenotio15elenZio14flatim23iffio19kentry_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejg57Segmentnd6ksubst04trueio17know_ok36Stdlib5Lists4Listjlf2Inim23andim22ex06length37Corelib5Lists7ListDefjod3nthio17regs_ok37Corelib4Init5Peanojr62lt3h5LinuxProcessSemantics5Riscv7Preludejt05bvmap04andbhnf3lebhnf3ltb05falsend7zlit_oki98expr_eqbtb8positive03orbhnf3eqbnd9sub_rangend9tautology89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~kleakentry_eqb46Stdlib5Arith8PeanoNat3Natkr33lebhnf6of_nathnf2lehnf2lthnf3subjr62lejod6repeat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslg2h0word_to_le_bytesijf7Z_to_bvnd8entails1jlf7existsbjlf7forallb04None04Somendball_presentndabind_cellsndaunify_regsjod3seqkr33eqbndcregs_presentndarematch_ok" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module MATCH.

(* [comment removed for export] *)
Definition subst : ltac2:(zQ "00S") := ltac2:(zQ "40!h8!he!i3!me@1$0@2$2$1$3").
Fixpoint sg_get (sg : subst) (n : nat) : option expr :=
  match sg with [] => None | (m, e) :: r => if Nat.eqb m n then Some e else sg_get r n end.

Fixpoint esubst (sg : subst) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar n => match sg_get sg n with Some e' => e' | None => e end
  | EAlu op a b => mkAlu op (esubst sg a) (esubst sg b)      (* [comment removed for export] *)
  | EAluw op a b => EAluw op (esubst sg a) (esubst sg b)
  | EMd op a b => EMd op (esubst sg a) (esubst sg b)
  | EMdw op a b => EMdw op (esubst sg a) (esubst sg b)
  | EExt sx lo n a => EExt sx lo n (esubst sg a)
  | EBlob _ _ _ _ => e
  end.
(* [comment removed for export] *)
Definition asubst : ltac2:(zQ "20!n5!s0>2sg$1>1a$0$0") := ltac2:(zQ "h70!me!s8!sd!he!t5!v4!hhc!hi4!n5!hic!s0!hj5!hjc!hk4!hkc!hl3!hla!hm0!hm7!hme!hn7!hp7!hpe\2sg$a\1a$8M0\1x$0$8@2$9^2@1$h3^1\1z$5@2$1@1$fZ@2$h5@2$h6^1$h4@1$2^2\1n$3@2$1@1$h2^1@1$2^2\2op$6\2a0$0\2b0$0@2$1@3$b^3^2^1@1$2^4\2op$6\2a0$0\2b0$0@2$1@3$c^3^2^1@1$2^4\2op$7\2a0$0\2b0$0@2$1@3$h0^3^2^1@1$2^4\2op$7\2a0$0\2b0$0@2$1@3$h1^3^2^1@1$2^4\2sx$4\2lo$3\1n$3\1e$0@2$1@4$e^4^3^2^1@1$2^5\2sx$4\1k$3\1i$5\1n$3@2$1@4$d^4^3^2^1@1$2^5").
Definition ksubst : ltac2:(zQ "20!hq8!s0>2sg$1>1K$0$0") := ltac2:(zQ "h20!hic!me!hr1!n5!v4!hq8!he!s0!hra!hs3!hsb!ht3!htb!hu2!hub!hv2!hva!ig0\2sg$7\1K$5M5\1K$5$5^1\1a$3\1w$6\1v$1@3$f@2$2^5^3^2@2$0^5^1\1a$3\1n$1@2$h1@2$2^4^2@2$0^4^1\1a$3\1n$1\1k$6@3$9@2$2^5^3@2$0^5^2^1\2lo$4\2hi$4@2$c^2^1\1e$1\1m$4@2$8@2$0^4^2^1\1e$1\2lo$4\2hi$4@3$d@2$0^5^3^2^1\1a$3\1n$1@2$h0@2$2^4^2@2$0^4^1\2a1$3\2n1$1\2a2$3\2n2$1@4$a@2$2^6^4@2$0^6^3@2$2^6^2@2$0^6^1\1a$3\1n$1\1c$4@3$b@2$2^5^3@2$0^5^2^1\1a$3\1n$1@2$e@2$2^4^2@2$0^4^1").

(* [comment removed for export] *)
Definition Es : ltac2:(zQ "20!ig8!s0>1E$0>2sg$1$0") := ltac2:(zQ "c0!ige!me!he!ih6!ihd!s0!ii6!iic!ij1!ig8!ija!ilc\1E$9\2sg$5@2$6\1n$2M0\1x@1$0$1@1$b@1$3#k0@2$4^2^1\1e$1@2$8^4^1@2$a^3^1@1$7^2").

Lemma edenot_esubst : ltac2:(zQ "90!ij1!in6!ih6!inc!hic!s0!ig8!me!ilc>1E$6>2sg$5>1e$7@3$1@1$8@1$2#k0@2$0^3@2$4^2^1@2$0@2$3^3^2^1").
Proof.
  intros E sg e. induction e; cbn [esubst edenot]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity).
  - cbn [Es ev]. destruct (sg_get sg n); reflexivity.
  - rewrite mkAlu_denot. rewrite IHe1, IHe2. reflexivity.
Qed.
Lemma estart_asubst : ltac2:(zQ "80!isd!in6!v4!inc!hr1!s0!ig8!n5>1E$6>2sg$5>1a$7@3$1$2@2$0^3@2$4^2^1@2$0@2$3^3^2^1").
Proof.
  intros E sg [b o]. unfold estart, asubst. cbn [a_base a_off].
  rewrite <- (edenot_esubst E sg b). destruct (esubst sg b) as [z| | | | | | |]; cbn [a_base a_off edenot]; try reflexivity.
  all: change (bv_unsigned (Z_to_bv 64 0)) with 0; rewrite Z_to_bv_unsigned; unfold two64, bv_wrap; change (bv_modulus 64) with (2 ^ 64); lia.
Qed.
Lemma adenot_asubst : ltac2:(zQ "90!it7!in6!ih6!inc!hr1!s0!ig8!n5!ilc>1E$6>2sg$5>1a$7@3$1@1$8@1$2#k0@2$0^3@2$4^2^1@2$0@2$3^3^2^1").
Proof.
  intros E sg a. pose proof (estart_asubst E sg a) as H. unfold estart in H. unfold adenot, v_addi.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite H. reflexivity.
Qed.
Lemma elenZ_esubst : ltac2:(zQ "80!iu0!in6!v4!inc!hic!s0!ig8!me>1E$6>2sg$5>1n$7@3$1$2@2$0^3@2$4^2^1@2$0@2$3^3^2^1").
Proof. intros. unfold elenZ. rewrite edenot_esubst. reflexivity. Qed.
Lemma flat_asubst : ltac2:(zQ "80!iu9!iv1!v4!inc!hr1!s0!ig8!n5>1E$6>2sg$5>1a$7>1n$2@2$1@3$0^4@2$4^3^2^1@3$0@2$3^4^3^2^1").
Proof. intros. unfold flat. rewrite estart_asubst. tauto. Qed.

Lemma kentry_ok_ksubst : ltac2:(zQ "b0!ih6!iv8!ilc!h8!ige!jja!inc!jk5!s0!ig8!hq8>4segs@1$3$5>1E$9>1M>0@1$2@1$0#k0@1$4@1$2@1$0#8>2sg$8>1K$a>0@4$1^5^4^3@2$7^2^1@4$1^6@2$6^5^3^4^2").
Proof.
  intros segs E M sg K H.
  destruct K; cbn [ksubst kentry_ok] in *;
    rewrite ?adenot_asubst, ?estart_asubst, ?elenZ_esubst, ?edenot_esubst in H;
    try (rewrite flat_asubst in H); exact H.
Qed.

Lemma know_ok_match : ltac2:(zQ "h20!hq8!t5!h8!jke!in6!ih6!iv8!jl4!jn2!ilc!ige!jn8!jnf!jja!inc!jk5!s0!ig8>4segs@1$2$d>1E$h1>1M>0@1$9@1$5#k0@1$a@1$9@1$5#8>2sg$h0>1T@1$2$0>1X@1$2$0>3ent>0$0>0$0$1>0>2K'$0>1K$0>0@3$4$1@2^3^2^1$3>0@4$6^a^9^8^3@4$6^b^a^9^3>0@4$7^8^7^6^3>0>1K$0>0@3$8$0^1^6@2$c$0\2K'$0@2$b@3$8$0^1^7@3$4$1@2^6^1@2$f^9^3$3@4$7^a@2$e^9^7^8^6").
Proof.
  intros segs E M sg T X ent Hent HX Hin. apply Forall_forall. intros K HK.
  apply kentry_ok_ksubst. ndestruct (Hin K HK) as (K' & HK' & He).
  eapply Hent; [exact He|]. apply (proj1 (Forall_forall _ _) HX). exact HK'.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_match : ltac2:(zQ "h00!me!jo5!h8!he!in6!jq4!ih6!hl3!jqb!jsa!jv6!inc!hic!s0!ig8!ilc>1E$e>2sg$d>3srT@1$2$0>3srX@1$2$0>1R@2$a@1$6#5@1$f@1$6#k0>0@3$8^5^2^1>0@3$4$3@2$1$0^4@2$1$0^3>0>1i$3>0@2$9^1@2$1$0^6@3$4$0@2$c^8@4$5$0^2^7@1$7Z@4$5$0^2^6@1$7Z@3$8@2$b^8^7^6^4").
Proof.
  intros E sg srT srX R HR Hlen H r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  pose proof (ridx_range r) as Hr.
  destruct (Nat.lt_ge_cases (ridx r) (length srT)) as [Hlt|Hge].
  - rewrite <- (H _ Hlt). apply edenot_esubst.
  - rewrite (nth_overflow srT) by lia. rewrite (nth_overflow srX) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint unify (pv : list nat) (fuel : nat) (t x : expr) (sg : subst) : option subst :=
  match fuel with O => None | S f =>
  match t with
  | EVar n => if existsb (Nat.eqb n) pv
              then match sg_get sg n with
                   | Some e => if expr_eqb e x then Some sg else None
                   | None => Some ((n, x) :: sg)
                   end
              else (if expr_eqb t x then Some sg else None)
  | _ => if expr_eqb (esubst sg t) x then Some sg else None   (* [comment removed for export] *)
  end end.

Fixpoint unify_regs (pv : list nat) (srT srX : list expr) (sg : subst) : option subst :=
  match srT, srX with
  | [], [] => Some sg
  | t :: rT, x :: rX => match unify pv 2 t x sg with Some sg' => unify_regs pv rT rX sg' | None => None end
  | _, _ => None
  end.

(* [comment removed for export] *)
Fixpoint find_word (X : list kentry) (a : saddr) (w : nat) : option expr :=
  match X with
  | [] => None
  | KWord a' w' v :: r => if (saddr_eqb a' a && Nat.eqb w' w)%bool then Some v else find_word r a w
  | _ :: r => find_word r a w
  end.

(* [comment removed for export] *)
Fixpoint bind_cells (pv : list nat) (T X : list kentry) (sg : subst) : option subst :=
  match T with
  | [] => Some sg
  | KWord a w t :: r =>
      match find_word X (asubst sg a) w with
      | Some x => match unify pv 2 t x sg with Some sg' => bind_cells pv r X sg' | None => bind_cells pv r X sg end
      | None => bind_cells pv r X sg      (* [comment removed for export] *)
      end
  | _ :: r => bind_cells pv r X sg
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit_ok : ltac2:(zQ "20!t5!v4>1m$1$0") := ltac2:(zQ "50!jvf!v4!hn7!kg5!kgc\1m$1@2$0@2$3Z^1@2$4^1$2").
Definition sub_range : ltac2:(zQ "40!n5!t5!v4!me>1a$0>1n$2>2a'$0>2n'$3$1") := ltac2:(zQ "h00!me!kh3!he!jvf!sd!t5!v4!hhc!hi4!hme!n5!hp7!kg5!kha!ki4!kgc\1a$a\1n$6\2a'$a\2n'$0@2$3@2$e@1$9^4@1$9^2M0\2n'$0$5^1\1m$6@2$3@2$3@2$3@1$d^1@2$c@1$4^3@1$4^5@2$c@2$b@1$4^5^4@2$b@1$4^3^1@2$fZ^4\2n0$2$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2sx$5\2lo$2\2n0$2\1e$0$1\2sx$5\1k$2\1i$6\2n0$2$1").
Lemma elenZ_lit : ltac2:(zQ "80!in6!v4!t5!jke!kha!hl3!ig8!iu0>1E$6>1m$1>0@3$0$2@1$4^1$3@3$0$1@2$7^3@1$5^2^2").
Proof.
  intros E m H. unfold zlit_ok in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold elenZ. rewrite edenot_lit. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition tautology : ltac2:(zQ "20!t5!hq8>1K$1$0") := ltac2:(zQ "h21!me!kh3!he!v4!t5!hhc!hi4!n5!jvf!kif!kha!kg5!hq8!hp7!kja!kjf!kgc!hpe&\2sx$4\2lo$2\1n$2\1e$0$1\1K$cMc\1K$c$4^1\1a$7\1w$2\1v$0$1\1a$7\1n$0$1\1a$7\1n$0\1k$2$1\2lo$3\2hi$3$1\1e$0\1m$3M0\1e$0$4^2\1z$3@2$8@2$8@1$a^1@2$h0Z^2@2$f@2$h1^1^2Z\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2sx$4\2lo$2\1n$2\2e0$0$1\2sx$4\1k$2\1i$3\1n$2$1\1e$0\2lo$3\2hi$3M0\1e$0$4^3\1z$3@2$8@2$8@1$a^1@2$b^3^1@2$b^1^2\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2sx$4\3lo0$2\1n$2\2e0$0$1\2sx$4\1k$2\1i$3\1n$2$1\1a$7\1n$0$1\2a1$7\2n1$0\2a2$7\2n2$0M7\2a1$7$4^4\6a_base$0\2oa$3M0\6a_base$0$4^2\1z$3M3\1z$3$4^1M0\2n1$0$4^6\2na$3M7\2a2$7$4^6\7a_base0$0\2ob$3M0\7a_base0$0$4^2\2z0$3M3\2z0$3$4^1M0\2n2$0$4^8\2nb$3@2$8@2$8@1$a^5@1$a^1@2$e@2$b@2$d^7^5^3@2$b@2$d^3^1^7\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1~0\2sx$4\1k$2\1i$3\1n$2$1\1p$9$1\1p$9$1\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1~0\2sx$4\1k$2\1i$3\1n$2$1\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1~0\2sx$4\1k$2\1i$3\1n$2$1\1p$9$1\1p$9$1\1n$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1~0\2sx$4\1k$2\1i$3\1n$2$1\1a$7\1n$0\1c$3$1\1a$7\1n$0$1").
Definition entails1 : ltac2:(zQ "20!hq8!t5>2K'$0>1K$0$1") := ltac2:(zQ "h22!me!kh3!v4!n5!he!t5!hq8!hhc!hi4!jvf!kk6!kja!kha!kif!kl2!kq5!kse!kt5&\2a1$3\2n1$0\2a2$3\2n2$0$1&\2sx$5\2lo$4\1n$4\1e$0$1\2K'$6\1K$6@2$b@2$b@2$f^2^1@1$e^1M6\1K$6$5^1\1a$3\1w$4\1v$0M0\1v$0$5^1\1z$2M2\1z$2$5^1M6\2K'$6$5^6\2a0$3\2w0$4\2v0$0$1\2a'$3\2n'$0@2$9@2$h0^5N8@4$a^6@1$h1^5^2^1\2a0$3\1n$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2a0$3\1n$0$1~0\2a0$3\1n$0\1c$2$1\2a0$3\1n$0$1\1p$d$1\1p$d$1\1n$4$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1~1\2sx$5\1k$4\1i$2\1n$4$1\1a$3\1n$0$1\1a$3\1n$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\1a$3\2n0$0M0\2n0$0$5^1\1n$2M6\2K'$6$5^5\2a0$3\1w$4\1v$0$1\2a0$3\2n1$0$1\2a0$3\2n1$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2a'$3\2n'$0@2$9@1$c^3@4$a^5^3^2^1~0\2a0$3\2n1$0\1c$2$1\2a0$3\2n1$0$1\1n$4$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1~1\2sx$5\1k$4\1i$2\1n$4$1\2a1$3\2n0$0\2a2$3\2n3$0M0\2n0$0$5^3\2n1$2M0\2n3$0$5^2\2n2$2M6\2K'$6$5^8\1a$3\1w$4\1v$0$1\1a$3\1n$0$1\1a$3\1n$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\1a$3\1n$0$1\2b1$3\2m1$0\2b2$3\2m2$0@2$9@2$9@1$c^6@1$c^5@2$b@2$9@4$a^a^6^4^3@4$a^8^5^2^1@2$9@4$a^a^6^2^1@4$a^8^5^4^3\1a$3\1n$0\1c$2$1\1a$3\1n$0$1\1n$4$1\2op$7\1a$0\1b$0$1\2op$7\1a$0\1b$0$1\2op$8\1a$0\1b$0$1\2op$8\1a$0\1b$0$1~1\2sx$5\1k$4\1i$2\1n$4$1\1n$4$1\2op$7\1a$0\1b$0$1\2op$7\1a$0\1b$0$1\2op$8\1a$0\1b$0$1\2op$8\1a$0\1b$0$1~1\2sx$5\1k$4\1i$2\1n$4$1\1a$3\1n$0\1c$2$1\1a$3\1n$0$1").

Lemma tautology_sound : ltac2:(zQ "c0!ih6!ilc!t5!h8!ige!jke!in6!jja!kl2!ig8!hq8!iv8>4segs@1$3$7>1E$9>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>1K$a>0@3$6$2@1$8^1$5@4$b^5^4^3^2").
Proof.
  intros segs E M K H. destruct K as [a w v|a n|a n k|lo hi|e m0|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; try discriminate; cbn [tautology] in H.
  - destruct e as [z| | | | | | |]; try discriminate.
    apply andb_true_iff in H as [H Hm]. apply andb_true_iff in H as [Hz Hp]. apply Z.ltb_lt in Hp. apply Z.eqb_eq in Hm.
    cbn [kentry_ok]. pose proof (elenZ_lit E z Hz) as X. unfold elenZ in X. rewrite X. split; [exact Hp | exact Hm].
  - destruct e as [z| | | | | | |]; try discriminate.
    apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [Hz H1]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [kentry_ok]. pose proof (elenZ_lit E z Hz) as X. unfold elenZ in X. rewrite X. lia.
  - destruct a1 as [[za| | | | | | |] oa]; try discriminate. destruct za; try discriminate.
    destruct n1 as [na| | | | | | |]; try discriminate.
    destruct a2 as [[zb| | | | | | |] ob]; try discriminate. destruct zb; try discriminate.
    destruct n2 as [nb| | | | | | |]; try discriminate.
    apply andb_true_iff in H as [H Hd]. apply andb_true_iff in H as [Ha Hb].
    cbn [kentry_ok]. rewrite (elenZ_lit E na Ha), (elenZ_lit E nb Hb). unfold estart. cbn [a_base a_off].
    rewrite edenot_lit. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    apply orb_true_iff in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.


Lemma sub_range_sound : ltac2:(zQ "h10!sd!v4!jn8!in6!hp7!n5!isd!ktf!t5!jke!jnf!kk6!ig8!me!iu0!ku5!kub>1E$c>1a$5>1n$1>2a'$5>2n'$d>0@3$3$8@4$b^4^3^2^1$9@2$a$1\1m$1@2$2@3$3$1@2$e^7^3^1@2$2@3$3$1@2$6^7^6@2$4@2$6^7^4@2$h0@1$0^6@1$0^4@2$2@2$7@1$0^4@1$0^6@2$2@2$7@2$4@1$0^6^5@2$4@1$0^4^1@2$fZ^5").
Proof.
  intros E a n a' n' H. unfold sub_range in H. apply andb_true_iff in H as [Hb H].
  destruct n' as [m| | | | | | |]; try discriminate.
  apply andb_true_iff in H as [H Hn]. apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [Hz H1].
  apply Z.ltb_lt in Hn. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists m. split; [apply elenZ_lit; exact Hz|]. apply expr_eqb_eq in Hb.
  unfold estart. rewrite Hb. lia.
Qed.

Lemma flat_sub : ltac2:(zQ "b0!sd!v4!hp7!n5!isd!iu9!ktf!in6!ig8!ku5!kub>1E$8>1a$3>1n$1>2a'$3>1m$1>0@3$5^5^2^1>0@3$7$1@2$4^6^5@2$2@2$4^6^3@2$a@1$0^5@1$0^3>0@2$6@1$0^4@1$0^6>0@2$6@2$2@1$0^7^6@2$2@1$0^5^4>0@2$9Z^7@3$5^a^9^8").
Proof. (intros E a n a' m nd_i1 He H1 H2 Hn; ndestruct nd_i1 as (F1 & F2 & F3 & F4)). unfold flat. lia. Qed.

Lemma wtlb_zero : ltac2:(zQ "c0!ih6!ilc!h8!he!in6!kv2!kv8!lj9!hl3!ij1!ig8!lke>1E$a>1w$3>0@2$5^1N8@3$4@1$2@1$1@1$0#8@2$7^2@2$9^3@1$8Z@3$6@1$1@1$0#8@2$b@1$0#8Z^2").
Proof.
  intros E w Hw. rewrite edenot_lit.
  do 9 (destruct w as [|w]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma entails1_sound : ltac2:(zQ "c0!ih6!hq8!iv8!ilc!t5!h8!ige!jke!in6!jja!ll9!ig8>4segs@1$5$9>1E$b>1M>0@1$3@1$0#k0@1$6@1$3@1$0#8>2K'$1>1K$1>0@3$8$4@2$a^2^1$7>0@4$2^6^5^4^3@4$2^7^6^5^3").
Proof.
  intros segs E M K' K H HK'. unfold entails1 in H. apply orb_true_iff in H as [H|H].
  { apply orb_true_iff in H as [H|H]; [|apply tautology_sound; exact H]. apply APS.kentry_eqb_eq in H. subst K'. exact HK'. }
  destruct K as [a w v|a n|a n k|lo hi|e m0|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; try discriminate.
  - (* [comment removed for export] *)
    destruct v as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
    destruct K' as [| a' n'| | | | | | | |]; try discriminate.
    apply andb_true_iff in H as [Hw H]. apply Nat.leb_le in Hw.
    destruct (sub_range_sound E _ _ _ _ H) as (m & Hm & He & H1 & H2 & Hn).
    cbn [kentry_ok] in HK'. destruct HK' as [Hf Hz]. rewrite Hm in Hf, Hz.
    assert (Fa : flat E a (Z.of_nat w)) by (eapply flat_sub; eauto).
    cbn [kentry_ok]. split; [exact Hw|]. split; [exact Fa|].
    rewrite (wtlb_zero E w Hw).
    apply rdn_pointwise.
    + apply repeat_length.
    + rewrite (flat_u _ _ _ Fa). ndestruct Fa as (F1 & F2 & F3 & F4). lia.
    + intros j Hj. rewrite (flat_u _ _ _ Fa). rewrite nth_repeat.
      replace (estart E a + Z.of_nat j) with (estart E a' + (a_off a - a_off a' + Z.of_nat j)) by lia.
      apply Hz. lia.
  - (* [comment removed for export] *)
    destruct n as [nz| | | | | | |]; try discriminate.
    destruct K' as [| | | | | | a' n'| | |]; try discriminate.
    apply andb_true_iff in H as [Hz H].
    destruct (sub_range_sound E _ _ _ _ H) as (m & Hm & He & H1 & H2 & Hn).
    cbn [kentry_ok] in HK'. destruct HK' as [Hf Hs]. rewrite Hm in Hf, Hs.
    cbn [kentry_ok]. rewrite (elenZ_lit E nz Hz).
    split; [eapply flat_sub; eauto|].
    intros d k Hd Hdk. replace (estart E a + d) with (estart E a' + (a_off a - a_off a' + d)) by lia.
    apply Hs; lia.
  - (* [comment removed for export] *)
    destruct n1 as [z1| | | | | | |]; try discriminate. destruct n2 as [z2| | | | | | |]; try discriminate.
    destruct K' as [| | | | | | | b1 m1 b2 m2| |]; try discriminate.
    apply andb_true_iff in H as [Hz H]. apply andb_true_iff in Hz as [Hz1 Hz2].
    cbn [kentry_ok] in HK'. cbn [kentry_ok]. rewrite (elenZ_lit E z1 Hz1), (elenZ_lit E z2 Hz2).
    apply orb_true_iff in H as [H|H]; apply andb_true_iff in H as [Ha Hb];
      destruct (sub_range_sound E _ _ _ _ Ha) as (ma & Hma & Hea & Ha1 & Ha2 & Hna);
      destruct (sub_range_sound E _ _ _ _ Hb) as (mb & Hmb & Heb & Hb1 & Hb2 & Hnb);
      rewrite ?Hma, ?Hmb in HK'; lia.
Qed.

(* [comment removed for export] *)
Definition all_present : ltac2:(zQ "40!h8!hq8!t5!s0>1T@1$0$1>1X@1$0$1>2sg$3$2") := ltac2:(zQ "70!hq8!h8!ll9!jk5!s0!lm4!lmf\1T@1$1$0\1X@1$1$0\2sg$4@3$6$0\1K$0=2K1$0@2$3^2^1@3$5$0\2K'$0@2$2^1^2^4^3").   (* [comment removed for export] *)

Definition rematch_from : ltac2:(zQ "60!h8!s0!me!hq8!he!ige>3sg0$1>2pv@1$0$4>3srT@1$0$2>1T@1$0$3>3srX@1$0$2>1X@1$0$3@1$5$1") := ltac2:(zQ "c0!s0!ige!h8!lna!t5!me!hq8!lo0!he!lo6!lp4!lq1\3sg0$0\2pv@1$2$8\3srT@1$2$5\1T@1$2$6\3srX@1$2$5\1X@1$2$6M1\1x@1$1$0@1$1$0@4$b^5^4^2^6\3sg1$0M1\1x@1$1$0@1$1$0@4$a^6^4^2^1\3sg2$0M4\0$4@1$1$0@3$9^5^3^1@2$7$0^1@1$3$0@1$3$0@1$3$0").

(* [comment removed for export] *)
Definition regs_present : ltac2:(zQ "40!h8!me!t5!s0>3srT@1$0$1>3srX@1$0$1>2sg$3$2") := ltac2:(zQ "d0!me!jo5!h8!he!jq4!hl3!jvf!lqe!hic!s0!ki4!lr5!lmf\3srT@1$2$0\3srX@1$2$0\2sg$9@2$6@2$b@2$1$0^3@2$1$0^2@3$c$3\1i$3@2$a@2$8^2@4$4$0^1^4@1$5Z@4$4$0^1^3@1$5Z@2$7N0@2$1$0^3").

Definition rematch_ok : ltac2:(zQ "50!h8!me!hq8!t5!s0>3srT@1$0$1>1T@1$0$2>3srX@1$0$1>1X@1$0$2>2sg$4$3") := ltac2:(zQ "70!h8!me!hq8!jvf!lo6!lrc!s0\3srT@1$0$1\1T@1$0$2\3srX@1$0$1\1X@1$0$2\2sg$6@2$3@3$5^5^3^1@3$4^4^2^1").

Lemma all_present_sound : ltac2:(zQ "c0!hq8!t5!h8!jke!in6!jn2!jn8!jnf!lo6!ll9!jk5!s0>1T@1$2$0>1X@1$2$0>2sg$b>0@3$4$1@3$8^3^2^1$3>1K$0>0@3$5$0^1^5@2$7$0\2K'$0@2$6@3$5$0^1^6@3$4$1@2$9^1@2$a^5^3$3").
Proof.
  intros T X sg H K HK. unfold all_present in H. rewrite forallb_forall in H.
  specialize (H K HK). apply existsb_exists in H as (K' & Hin & Heq). exists K'. split; assumption.
Qed.

Lemma regs_present_sound : ltac2:(zQ "e0!me!jo5!in6!h8!he!jq4!hl3!t5!jke!jn8!jsa!hic!lrc!s0>3srT@1$3$0>3srX@1$3$0>2sg$d>0@3$2$7@3$c^3^2^1$8@2$9@3$2$4@2$1$0^4@2$1$0^3>1i$4>0@2$a^1@2$1$0^5@3$2$0@2$b^4@4$5$0^2^6@1$6Z@4$5$0^2^5@1$6Z").
Proof.
  intros srT srX sg H. unfold regs_present in H. apply andb_true_iff in H as [Hl H].
  apply Nat.eqb_eq in Hl. split; [exact Hl|]. intros i Hi.
  rewrite forallb_forall in H. specialize (H i). apply expr_eqb_eq. apply H. apply in_seq. lia.
Qed.

Theorem rematch_sound : ltac2:(zQ "h20!h8!ih6!ilc!inc!me!hq8!jl4!jqb!t5!ige!jke!jn8!in6!jja!jv6!lsb!s0!ig8>4segs@1$0$d>1E$h1>1M>0@1$2@1$1#k0@1$9@1$2@1$1#8>1R@2$e@1$1#5@1$2@1$1#k0>3srT@1$0$4>3srX@1$0$4>1T@1$0$5>1X@1$0$5>2sg$h0>0@3$c$8@5$f^5^3^4^2^1$a>0@3$7^9^5^7>0@4$6^b^a^9^4@2$b@3$7@2$3^b^4^8^9@4$6^c@2$3^b^4^a^6").
Proof.
  intros segs E M R srT srX T X sg H HR HK. unfold rematch_ok in H. apply andb_true_iff in H as [Hr Hk].
  destruct (regs_present_sound _ _ _ Hr) as [Hlen Hnth].
  split.
  - eapply regs_ok_match; eauto.
  - eapply know_ok_match; [apply entails1_sound | exact HK | apply all_present_sound; exact Hk].
Qed.

(* [comment removed for export] *)
Lemma Es_bound : ltac2:(zQ "d0!me!in6!lo0!he!ige!ih6!inc!ihd!s0!ij1!ig8!ija!ilc>1E$a>2sg$8>1n$3>1e$0>0@3$1@1$4$0@2$7^3^2@2$2$0^1@3$1@1$c@1$5#k0@2$b@2$6^5^4^3@2$9^5^2").
Proof. intros E sg n e H. cbn [Es ev]. rewrite H. reflexivity. Qed.
Lemma Es_free : ltac2:(zQ "c0!in6!ija!me!lna!he!ige!ih6!inc!ihd!s0!ig8!ilc>1E$a>2sg$9>1n$4>0@3$0@1$5$2@2$8^2^1@1$3$2@3$0@1$b@1$6#k0@2$1@2$7^4^3^2@2$1^4^2").
Proof. intros E sg n H. cbn [Es ev]. rewrite H. reflexivity. Qed.

End MATCH.
(* [comment removed for export] *)
