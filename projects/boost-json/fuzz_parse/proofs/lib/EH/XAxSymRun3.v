(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3 XAxSymExec3Sound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool03nat89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~i35saddri36a_base89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun35FPX_1~~~~~~n9cexpr_vars_lti36kentryi34expr04andbn9dsaddr_vars_lt37Corelib7Numbers7BinNumsv41Z04truei33env37Corelib4Init5Logichhd2eqv44Nposi32ebi32ev35stdpp9bitvectorbdefinitionshk82bv04listhhd3and37Corelib4Init5Peanohn82lti36edenotn99env_agreei36adenot89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~hr07regs_ok3h5LinuxProcessSemantics5Riscv7Preludeig75bvmapn9asr_vars_lthr04flathhd3iffhr07know_ok06option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeim57Segmentn9akn_vars_lt04None03nili33SSRi36sentryhr05st_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~it54mksthk87Z_to_bvhr06eagreei35s_loghhd2exi36s_nexti34s_pchr09mem_denothn82lei34itabi3aitab_soundi36s_knowi36s_regsi3asym_execTXi39sym_statehr08log_flat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~jqd6msteps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2S.
Section FPX_1. Context {fx : FPState}.


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

Definition saddr_vars_lt : ltac2:(zQ "30!h8!he!m8>1b$1>1a$2$0") := ltac2:(zQ "40!he!n0!m8!rf\1b$0\1a$2@2$3^2@1$1^1").

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt : ltac2:(zQ "30!h8!he!se>1b$1>1K$2$0") := ltac2:(zQ "a2!t7!rf!te!m8!u4!hgd!he!se!h8!hh1&\1n$0@2$2@2$4^4^2@2$1^4^1&\1a$3~0\1b$6\1K$7M7\1K$7$8^1\1a$3\1w$6\1v$0@2$2@2$4^5^3@2$1^5^1~1\1a$3\1n$0\1k$6@2$2@2$4^5^3@2$1^5^2\2lo$5\2hi$5$9\1e$0\1m$5@2$1^4^2\1e$0\2lo$5\2hi$5@2$1^5^3~1\2a1$3\2n1$0\2a2$3\2n2$0@2$2@2$2@2$2@2$4^6^4@2$1^6^3@2$4^6^2@2$1^6^1\1a$3\1n$0\1c$5@2$2@2$4^5^3@2$1^5^2~1").

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Definition env_agree : ltac2:(zQ "20!hh7!he>1b$1>1E$0>2E'$0P") := ltac2:(zQ "a0!he!hj1!hj7!hje!hh7!hk3!hm5!hmb!hn1!hoc\1b$0\1E$4\2E'$4@2$8>1n$0>0@2$9^1^4@3$1@1$6@1$2#k0@2$5^4^2@2$5^3^2@3$1>0$0@1$7@1$6@1$2#8@1$3^2@1$3^1").

Lemma edenot_agree : ltac2:(zQ "b0!hj1!hp2!hh7!h8!he!hh1!hj7!t7!hpb!rf!hm5>1b$4>1E$2>2E'$2>1e$7>0@3$8^4^3^2>0@3$0$3@2$9^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
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

Lemma adenot_agree : ltac2:(zQ "b0!hj1!hq7!hh7!h8!he!hh1!hj7!m8!hpb!u4!hm5>1b$4>1E$2>2E'$2>1a$7>0@3$8^4^3^2>0@3$0$3@2$9^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : ltac2:(zQ "d0!hj7!hh7!hvc!h8!hmb!he!hh1!hj1!iid!t7!hpb!ij6!hm5>1b$5>1E$1>2E'$1>2sr@1$4$9>4regs@2$8@1$0#5@1$c@1$0#k0>0@3$a^5^4^3>0@3$7$3@2$b^6^3$6>0@3$2^6^4^3@3$2^6^5^4").
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

Lemma flat_agree : ltac2:(zQ "b0!hh7!ik3!h8!he!hh1!hj1!ikb!hgd!m8!hpb!u4>1b$3>1E$0>2E'$0>1a$8>1n$7>0@3$9^5^4^3>0@3$5$2@2$a^6^3$4@2$6@3$1^6^4^3@3$1^5^4^3").
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma know_ok_agree : ltac2:(zQ "e0!hmb!hj7!hh7!il2!hm5!h8!he!ild!hh1!hj1!ipa!se!hpb!iq5>4segs@1$0$a>1b$6>1E$2>2E'$2>4base>0@1$4@1$1#k0@1$7@1$4@1$1#8>2kn@1$0$b>0@3$c^5^4^3>0@3$9$5@2$d^6^2$8>0@4$3^8^6^4^3@4$3^9^6^5^4").
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
              | apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
                unfold estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
              | | ].
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
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable segs : ltac2:(zQ "20!hmb!ipa@1$0$1").

(* [comment removed for export] *)
Lemma st_ok_entry : ltac2:(zQ "h41!hj7!hm5!hmb!ild!ir2!he!ir8!hgd!iid!ird!hh7!t7!se!m8!is3!il2!hvc!isc!jh4!jhc&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1E$a>4base~0>3rom~0>2pc$7>2sr@1$2$b>2kn@1$2$c>2nx$5>4regs@2$8@1$0#5@1$1@1$0#k0>0@3$h0^8^4^1>0@4$f?4segs^9^8^4@7$h1?2fx?4segs^a^9^8@6$9^7^6@1$6$e^5^4@1$4$d@5$h2?2fx^3@2$h3@1$0#k0^7^9^8").
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

(* [comment removed for export] *)
Lemma eagree_env_agree : ltac2:(zQ "50!hh7!he!ikb!ji7!hpb>1b$1>1E$0>2E'$0@2$2@3$3^3^2^1@3$4^3^2^1").
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

(* [comment removed for export] *)
Lemma st_okX_entry : ltac2:(zQ "ha1!hj7!hm5!h8!hmb!ild!hh1!hj1!hh7!ir2!he!ir8!hgd!iid!ird!t7!se!m8!is3!ji7!il2!hvc!isc!iq5!ij6!jh4!jhc&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1E$7>4base~0>3rom~0>2pc$b>2sr@1$3$e>2kn@1$3$f>2nx$9>4regs@2$c@1$0#5@1$1@1$0#k0>0@3$h4^8^4^1>0@4$h3?4segs^9^8^4>0@3$6$2@2$h7^4^6$5>0@3$6$2@2$h6^5^6$5>2E'$7>0@3$h2^7^d^1@7$h5?2fx?4segs^2^d^c@6$d^b^a@1$a$h1^9^8@1$8$h0@5$h8?2fx^7@2$h9@1$0#k0^b^d^c").
Proof.
  intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
  apply st_ok_entry.
  - eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
  - eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

(* [comment removed for export] *)
Theorem runTX_sound : ltac2:(zQ "i91!hj7!hm5!hn1!hh7!hmb!he!hh1!iid!jj1!jh4!jhc!h8!ild!hj1!jj9!hgd!jjf!jk8!il2!jkf!hvc!hpb!ir2!ir8!jlc!ird!t7!jm2!jm9!se!jn6!jnf!m8!is3!jo8!jp5!jq1!isc!iq5!ij6!jua&>0@1$1@1$0#k0@1$c@1$1@1$0#8>1t$hb>1K$5>4fuel$5>5stops@1$4$f>2pc$f>2sr@1$4$ha>2kn@1$4$hd>2nx$5>1E$3>4base~0>3rom~0>4regs@2$7@1$0#5@1$1@1$0#k0>0@2$hc?4segs^c>0@3$h4^5^8^2>0@4$h2?4segs^6^5^8>0@3$d$b@2$i7^8^a$6>0@3$d$b@2$i6^9^a$6=3ss'$i3@7$i2?4segs^h1^h0^f$6^e@6$h9^d^c@1$h7$i1^b^a@1$h6$i0@2$e$3\2E'$3@2$e@2$7@1$0#5@1$1@1$0#k0\1R@2$7@1$0#5@1$1@1$0#k0@2$2@3$h5^d^c^2@2$2@2$h8^d@1$h0^3@2$2@3$h4^2@1$hf^3^1@2$2@2$i4^2@1$8^3@2$2@4$h2?4segs^2^b@1$he^3@2$2@3$i8?4segs@5$9?2fx^9@2$a@1$0#k0^h0^b^a@5$9?2fx^1@2$a@1$0#k0@1$h1^3@3$h3^2^b@1$8^3^a>3E''$3>0@3$h5@1$h0^4^3^1@7$i5?2fx?4segs^2^d^c^5@5$9?2fx^3@2$a@1$0#k0@1$h1^5@3$h3^4^d@1$8^5^c").
Proof.
  intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
  destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
              (st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
  exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End Run.

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

End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
