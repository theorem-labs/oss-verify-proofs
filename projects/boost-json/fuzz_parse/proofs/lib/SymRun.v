(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SymExec2 SymExec2Sound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk13nat37Corelib5Lists7ListDefm63nthhf7Z_to_bvk14bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~p45saddrp46a_base79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun4FPX1~~~~~~u4cexpr_vars_ltp46kentry01Zu4dsaddr_vars_ltp44exprk14andbk14truep43env37Corelib4Init5Logichm82eqp42ebp42evhm83and37Corelib4Init5Peanohp32ltp46edenotu49env_agreep46adenot79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~hsb7regs_ok3h5LinuxProcessSemantics5Riscv7Preludeihb5bvmapu4asr_vars_lthsb4flathm83iffhsb7know_okk16option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeina7Segmentu4akn_vars_ltp43Envu47vals_evk13appk16lengthk13nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iuc4mkstp42SSp46sentryhsb5st_okp48sidecondp47scriptsp49sym_statek14prodk14pairp45s_loghm82ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~jo36mstepsp44s_pcp46s_regsp48sym_exechsb8log_flathsb9mem_denothsb9scs_denotp45carryiuc4getrp46sr_gethm81Ihm83notiuc6regupdp44ridxp46sr_updhf2BVhf4BvWfhfbbv_unsigned46Stdlib6ZArith6BinInt1Zkm02le3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskne8store_okkm03addkm06of_natkm03subp43KWrp42SAhsb9kentry_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun4FPX2~~~~~~kv16stk_okkm03opphp32lek14Somekneh0word_to_le_bytesiuc3rdnp45KWordkm03powp46KRangep46KAlignkm02ltkm06modulok14Nonep44KImgp45KZerok15falsep47ext_valkm03mul" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition vals_ev : ltac2:(zQ "40!h9!jc!l9!m0>4vals@1$2@1$1@1$0#k0>0$3@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!l9!m0!nd!o3\4vals@1$2@1$1@1$0#k0\1n$3@4$4@1$1@1$0#k0^1^2@2$5@1$0#k0Z").

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt : ltac2:(zQ "30!od!m0!t3>1b$1>1a$2$0") := ltac2:(zQ "40!m0!tb!t3!hi2\1b$0\1a$2@2$3^2@1$1^1").

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt : ltac2:(zQ "30!od!m0!hj1>1b$1>1K$2$0") := ltac2:(zQ "a0!hja!t3!hjd!hkd!hi2!hl4!m0!hj1!od!hlb\1b$6\1K$7M7\1K$7$8^1\1a$1\1w$6\1v$3@2$5@2$2^5^3@2$4^5^1\1a$1\1n$3@2$5@2$2^4^2@2$4^4^1\1a$1\1n$3\1k$6@2$5@2$2^5^3@2$4^5^2\2lo$0\2hi$0$9\1e$3\1m$0@2$4^4^2\1e$3\2lo$0\2hi$0@2$4^5^3\1a$1\1n$0@2$2^4^2\2a1$1\2n1$0\2a2$1\2n2$0@2$5@2$2^6^4@2$2^6^2").

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Definition env_agree : ltac2:(zQ "20!hm2!m0>1b$1>1E$0>2E'$0P") := ltac2:(zQ "a0!m0!hnc!h9!ho2!hm2!ho7!jc!l9!hoc!hq7\1b$0\1E$4\2E'$4@2$8>1n$0>0@2$9^1^4@3$1@1$6@1$2#k0@2$5^4^2@2$5^3^2@3$1>0$0@1$7@1$6@1$2#8@1$3^2@1$3^1").

Lemma edenot_agree : ltac2:(zQ "b0!hnc!hqd!hm2!od!m0!hlb!h9!hkd!hr6!hi2!jc>1b$4>1E$2>2E'$2>1e$7>0@3$8^4^3^2>0@3$0$3@2$9^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
Proof.
  intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Nat.ltb_lt in H. apply Hv. exact H.
  - rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : ltac2:(zQ "b0!hnc!hs2!hm2!od!m0!hlb!h9!t3!hr6!hjd!jc>1b$4>1E$2>2E'$2>1a$7>0@3$8^4^3^2>0@3$0$3@2$9^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : ltac2:(zQ "d0!h9!hm2!ih0!od!l9!m0!hlb!hnc!ik1!hkd!hr6!ika!jc>1b$5>1E$1>2E'$1>2sr@1$4$9>4regs@2$8@1$0#5@1$c@1$0#k0>0@3$a^5^4^3>0@3$7$3@2$b^6^3$6>0@3$2^6^4^3@3$2^6^5^4").
Proof.
  intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
  { clear HR r. induction sr as [|e t IH]; intros i.
    - destruct i; reflexivity.
    - cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
      destruct i; [exact He | apply IH; exact Ht]. }
  apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

Lemma flat_agree : ltac2:(zQ "b0!hm2!il7!od!m0!hlb!hnc!ilf!hja!t3!hr6!hjd>1b$3>1E$0>2E'$0>1a$8>1n$7>0@3$9^5^4^3>0@3$5$2@2$a^6^3$4@2$6@3$1^6^4^3@3$1^5^4^3").
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma know_ok_agree : ltac2:(zQ "e0!l9!h9!hm2!im6!jc!od!m0!in1!hlb!hnc!iqf!hj1!hr6!ira>4segs@1$0$a>1b$6>1E$2>2E'$2>4base>0@1$4@1$1#k0@1$7@1$4@1$1#8>2kn@1$0$b>0@3$c^5^4^3>0@3$9$5@2$d^6^2$8>0@4$3^8^6^4^3@4$3^9^6^5^4").
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | unfold flat, estart in *; rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold estart in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK2); exact Hk1 ].
    + apply andb_prop in HK as [H1 H2].
      rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
      ndestruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
      apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      ndestruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + exact Hk1.
Qed.

(* [comment removed for export] *)
Lemma vals_app_agree : ltac2:(zQ "90!h9!jc!l9!is7!isd!it7!itd!m0!hr6>4vals@1$2@1$1@1$0#k0>5extra@1$2@1$1@1$0#k0>3ebs>0$7@1$2@1$1@1$0#8@3$8@2$6@1$1@1$0#k0^3@2$3@1$4^3^1@2$3@1$4@3$5@1$1@1$0#k0^3^2^1").
Proof.
  intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
  rewrite app_nth1 by exact Hn. reflexivity.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!l9!iqf@1$0$1").

(* [comment removed for export] *)
Lemma st_ok_entry : ltac2:(zQ "h21!h9!jc!l9!in1!m0!iu6!hja!ik1!ji7!jif!hm2!hkd!hj1!jj4!im6!ih0!jjd!o3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1E$a>4base~0>3rom~0>2pc$6>2sr@1$2$b>2kn@1$2$c>2nx$4>4regs@2$7@1$0#5@1$1@1$0#k0>0@3$f^8^4^1>0@4$e?4segs^9^8^4@7$h0?2fx?4segs^a^9^8@5$9^7^6@1$5$d^5^4@5$8?2fx^3@2$h1@1$0#k0^7^9^8").
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : ltac2:(zQ "i21!h9!l9!jc!jk6!jl1!jlb!jm7!ik1!m0!iu6!in1!jme!hoc!hja!ji7!jn5!ih0!o3!hlb!hnc!jnd!jrc!jif!hm2!hkd!hj1!js6!jsd!jj4!jt6!im6!ju1!jud!jva&>0@1$2@1$0#k0@1$a@1$2@1$0#8>4fuel$8>5stops@1$1$d>3scr$4>2pc$d>2sr@1$1$h8>2kn@1$1$h9>2nx$8>3ss'$5>3scs@1$1$3>4scr'$4>1E$h7>4base~0>3rom~0>4regs@2$7@1$0#5@1$2@1$0#k0>0@3$h3@2$6@2$6$5@1$1$3$4@7$hd?4segs^e$h2^d^c@5$h6^b^a@1$9$hc^9^8@1$9$3@4$b@2$6$5@1$1$3$4@4$b$5@1$1$3^7^6^5>0@3$h0^5^b^2>0@4$he?4segs^6^5^b>0@4$i1?4segs^6^7^9@2$h4@2$7@1$0#5@1$2@1$0#k0\1R@2$7@1$0#5@1$2@1$0#k0@2$c@3$h0^9@1$hb^c^1@2$c@2$hf^9@1$f^c@3$h5?4segs@5$e?2fx^6@2$h1@1$0#k0^h0^8^7@5$e?2fx^1@2$h1@1$0#k0@1$ha^c@3$i0^9^8@1$f^c^7").
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
Theorem carry_after : ltac2:(zQ "h10!l9!hj1!od!jk6!jm7!jme!h9!im6!jc!in1!hnc!kg7!hm2!jj4!ju1!jud!jva>1E$c>4base>0@1$8@1$6#k0@1$9@1$8@1$6#8>3log@1$0$d>2kn@1$0$1>5hints@1$0$2>3kn'@1$0$1>3scs@1$0$3>3hs'@1$0$2>0@3$a@2$4@2$4@1$0$1@1$0$3@1$0$2@3$b^6^5^4@4$5@2$4@1$0$1@1$0$3@1$0$2@4$5@1$0$1@1$0$3^3^2^1>0@2$e^9^7>0@4$7?4segs^a^9^7>0@4$h0?4segs^a^b^5@4$7?4segs^c@3$f^c^b^a^7").
Proof. intros. eapply carry_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma reg_val : ltac2:(zQ "b0!h9!jc!l9!hnc!ik1!kgf!hqd!hm2!hkd!kh7!ih0>1E$7>2sr@1$2$8>1R@2$4@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@3$a^4^3^2@3$3@1$1@1$0#k0@2$5^3^2@2$6^5@2$9^4^2").
Proof. intros E sr R r HR. apply HR. Qed.

(* [comment removed for export] *)
Lemma regs_ok_set : ltac2:(zQ "h00!h9!jc!hnc!hkd!ih0!l9!ki0!ki5!ik1!kic!hqd!hm2!kj6!kjd!kk6!kkb>1E$b>2sr@1$5$3>1R@2$8@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>1e$3>0@3$4^6^5^4>0@1$7@3$2@1$1@1$0#5^4@3$e@1$0#5ZKv$6@2$f@1$0#5Z>0@3$2@1$1@1$0#k0@2$a^8^3^4@3$4^9@3$d^8@1$c^6^4@3$9^7^6^5").
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_ok : ltac2:(zQ "60!h9!jc!l9!in1!hja!iqf>4segs@1$2$5>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>1K$4P") := ltac2:(zQ "h00!h9!jc!kl2!kn8!od!l9!m0!in1!hlb!hnc!hja!iqf!kr5!ks1!ks8!kt2\4segs@1$5$b\3mem>0@1$1@1$0#k0@1$7@1$1@1$0#8\2sp@1$1@1$0#k0\1K$a>1a@1$1@1$0#k0>1n$6>0@2$3@2$f@2$2@1$0#k0^4^3@2$2@1$0#k0^2>0@2$3@2$d@2$2@1$0#k0^3@1$e^2@2$2@1$0#k0^5@3$9$4@4$c^8^7^4^3$8").

(* [comment removed for export] *)

Lemma kwr_of_stk_ok : ltac2:(zQ "h20!h9!jc!kn8!l9!in1!hoc!hnc!hja!iqf!kt9!ktf!hqd!hm2!hkd!ku4!lif!lj9!kl2>4segs@1$3$8>1E$c>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1e$d>2sp@1$1@1$0#k0>1K$7>0@3$6@1$1@1$0#k0@2$b^5^3^2>0@4$f^7^5^3^2>0@2$5@2$2Z^3@2$2^3@2$h1@1$0#k0^4@4$e^9^8^7@2$9@2$a^6@1$h0^4^4").
Proof.
  intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He.
  pose proof (u64_range sp). split; [lia|].
  intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kword_intro : ltac2:(zQ "h80!h9!jc!ks1!l9!hnc!kl2!in1!lk0!hqd!hkd!kn8!lk6!m0!hja!iqf!lkd!lm2!lm9!ktf!hm2!ku4!ks8!ln1!o3>4segs@1$3$e>1E$h3>3mem>0@1$1@1$0#k0@1$6@1$1@1$0#8>1e$9>1a@1$1@1$0#k0>3off$d>1w$c>1v$9>1x@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$8^8^6^5>0@3$4@1$1@1$0#k0@2$8^9^3^2>0@2$7N1^5>0@2$7^6N8>0@2$aZ@2$2@2$5@1$0#k0^9^8>0@2$a@2$2@2$2@2$5@1$0#k0^a^9@1$h5^8@2$h6+2+k0>0@3$4@1$6@1$3@1$1@1$0#8@4$h0^f^d@2$h7@1$0#k0@2$2@2$5@1$0#k0^b^a^9@2$b@1$3@1$1@1$0#8@2$f^9^7@4$h4^h0^f^e@3$h1@2$h2^d^b^a^9").
Proof.
  intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
  cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

Lemma krange_intro : ltac2:(zQ "e0!h9!hja!hqd!kn8!jc!kl2!l9!in1!hoc!iqf!ln8!hm2!hkd!ku4>4segs@1$6$9>1E$b>3mem>0@1$4@1$0#k0@1$7@1$4@1$0#8>1e$c>2lo$1>2hi$1>0@2$8@2$3^2@2$5@1$0#k0@2$2^5^3@2$3@2$5@1$0#k0@2$2^5^3^1@4$d^7^6^5@3$a^4^3^2").
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : ltac2:(zQ "f0!h9!hja!jc!l9!in1!hnc!iqf!lo1!hqd!hm2!hkd!ku4!loa!lp0!kl2>4segs@1$3$6>1E$9>3mem>0@1$2@1$0#k0@1$4@1$2@1$0#8>1e$a>1m$1>0@2$cZ^1>0@3$5$1@2$d@2$e@1$0#k0@2$8^5^3^2Z@4$b^7^6^5@2$7^4^3").
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kimg_intro : ltac2:(zQ "h00!h9!jc!hja!kn8!in1!lpa!l9!hoc!hnc!iqf!lq1!hm2!ku4!loa!ln1!o3>4segs@1$6$9>1E$b>3mem>1x@1$1@1$0#k0@1$4@1$1@1$0#8>2lo$2>2hi$2>0@2$3Z^2>0@2$3^2@2$e+2+k0>0>1i$2>0@2$7@2$3^5^1@2$d^1^4@3$8@1$4@1$1@1$0#8@1^7@2$f@1$0#k0^2@1$5@1$1@1$0#8@4$c^8^7^6@2$a^5^4").
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kzero_intro : ltac2:(zQ "h50!h9!jc!ks1!hja!kl2!hnc!kn8!in1!hqd!hkd!loa!o3!lk6!l9!hoc!iqf!lq8!ktf!hm2!ku4!ln1>4segs@1$d$f>1E$h2>3mem>1x@1$1@1$0#k0@1$7@1$1@1$0#8>1e$9>1a@1$1@1$0#k0>3off$3>1n$9>3len$3>0@3$5@1$1@1$0#k0@2$8^7^5^4>0@3$5$3@2$4@1$0#k0@2$8^8^3^2>0@2$6Z@2$2@2$4@1$0#k0^6^5>0@2$aZ^4>0@2$6@2$2@2$2@2$4@1$0#k0^8^7^5@2$h4+2+k0>0>1i$3>0@2$e@2$6Z^1@2$a^1^7@3$5@1$7@1$1@1$0#8@1^d@2$b@1$0#k0@2$2@2$2@2$4@1$0#k0^b^a^2@2$c@1$1@1$0#8@2$b@1$0#8Z@4$h3^e^d^c@2$h0@2$h1^b^9^8").
Proof.
  intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ext_val_zx_id : ltac2:(zQ "b0!h9!jc!lr0!m0!hnc!lr8!loa!ls2!ks8!ln1!kl2>1n$3>1v@1$1@1$0#k0>0@2$6@2$a@1$0#k0^1@2$9+2@2$7+8@1$8^2@3$4@1$1@1$0#k0@4$5$2N0^3^2^2").
Proof.
  intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ext_val_sx_id : ltac2:(zQ "d0!h9!jc!m0!hlb!hnc!lk0!lr8!loa!ls2!ks8!ln1!kt2!kl2>1n$2>1v@1$1@1$0#k0>0@2$5N1^2>0@2$7@2$c@1$0#k0^2@2$a+2@2$b@2$8+8@1$9^3+1@3$4@1$1@1$0#k0@4$6$3N0^4^3^3").
Proof.
  intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
  { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
  rewrite <- Hp. rewrite Z.div_mul by lia.
  rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
    with (bv_unsigned v) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
