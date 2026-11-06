(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool05false04list37Corelib4Init5Logicib2eqib3iff37Corelib7Numbers7BinNumska1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AG_Free6~~~~~~m73inb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~qb3ivlqb7outside04trueib3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hg33memka4Npos35stdpp9bitvectorbdefinitionshkf2bv06optionhkfbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsho95wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hs95asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~igd3mrdm74chimigd7mem_invqb5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~im88agree_onigd8bytes_at06lengthib3and46Stdlib6ZArith6BinInt1Zisc3addisc2leisc2ltisc6of_natigd5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jga8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jl14celljl1acells_sizeqb3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jq95u8arrjq96u32arrisc3mulhg38poisonedhg32sh03nat" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint inb (W : list ivl) (a : Z) : bool :=
  match W with
  | [] => false
  | (lo, hi) :: W' => ((lo <=? a) && (a <? hi)) || inb W' a
  end.

Lemma inb_false_outside : ltac2:(zQ "90!h8!he!i5!jf!k4!m3!q5!u7!ud>1W@1$2$7>1a$5@2$4@3$3$0@2$6^2^1$1@2$8^2^1").
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn; [tauto|].
  rewrite Bool.orb_false_iff, Bool.andb_false_iff, Z.leb_gt, Z.ltb_ge, IH. split.
  - intros [[H|H] H2]; (split; [lia| exact H2]).
  - intros [H1 H2]. split; [| exact H2]. lia.
Qed.
Lemma inb_true_not_outside : ltac2:(zQ "a0!h8!i5!v7!jf!k4!vd!m3!q5!u7!ud>1W@1$1$8>1a$6@2$4@3$3$0@2$7^2^1$2@1$5@2$9^2^1").
Proof.
  intros W a. rewrite <- inb_false_outside. destruct (inb W a); split; congruence || (intros H; exfalso; apply H; reflexivity) || auto.
Qed.

Definition chim : ltac2:(zQ "30!hk1!i5!u7>1W@1$1$2>1m$0>2m2$0$0") := ltac2:(zQ "90!hk8!h8!hk1!hmc!i5!hn2!q5!u7!hna\1W@1$4$7\1m$2\2m2$2\1x@1$3@1$0#k0M1\0$1@1$5@1$3@1$0#8@2$6^4@2$8@1$0#k0^1@1^3^1@1^2^1").

(* [comment removed for export] *)
Lemma wview_pt : ltac2:(zQ "61!hk8!hmc!hn2!jf!hs0!ig4&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>2ma~0>2mb~0>1x@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#8@1^3^1@1^2^1@3$3@1$2@1$1@1$0#8@3$4$5^4^2@3$4$5^3^2").
Proof. intros ma mb x E. unfold wview. rewrite E. reflexivity. Qed.
Lemma mrd_pt : ltac2:(zQ "61!hk8!hmc!hn2!jf!ig4!ik7&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>2ma~0>2mb~0>1x@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#8@1^3^1@1^2^1@3$3@1$2@1$1@1$0#8@3$5$4^4^2@3$5$4^3^2").
Proof. intros ma mb x E. unfold mrd. rewrite E. reflexivity. Qed.

Section Chim.
  Variables (W : list ivl) (m m2 : mem).

  Lemma chim_in : ltac2:(zQ "90!hk8!jf!hmc!h8!hn2!v7!ike!q5!hna>1x@1$2@1$0#k0>0@3$1$3@2$7?1W@2$8@1$0#k0^1$5@3$1@1$4@1$2@1$0#8@4$6?1W?1m?2m2^2@1?1m^2").
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.
  Lemma chim_out : ltac2:(zQ "90!hk8!jf!hmc!h8!he!hn2!ike!q5!hna>1x@1$2@1$0#k0>0@3$1$3@2$7?1W@2$8@1$0#k0^1$4@3$1@1$5@1$2@1$0#8@4$6?1W?1m?2m2^2@1?2m2^2").
  Proof. intros x E. unfold chim. rewrite E. reflexivity. Qed.

  Lemma chim_mem_inv : ltac2:(zQ "30!ig4!il5!ike>0@2$1$0?1m>0@2$1$0?2m2@2$1$0@3$2?1W?1m?2m2").
  Proof. intros M1 M2 a b E. unfold chim in E. destruct (inb W (bv_unsigned a)); [exact (M1 a b E)| exact (M2 a b E)]. Qed.

  (* [comment removed for export] *)
  Lemma chim_wmono_in : ltac2:(zQ "30!ig4!im0!ike>0@3$1$0?1m?2m2@3$1$0?1m@3$2?1W?1m?2m2").
  Proof.
    intros WM x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)). exact Hx.
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)). exact (WM x Hx).
  Qed.
  Lemma chim_wmono_out : ltac2:(zQ "60!ig4!im0!hk8!hmc!hn2!ike>2m3>0@1$3@1$2#k0@1$4@1$3@1$2#8>0@3$1$0?1m^1>0@3$1$0?2m2^2@3$1$0@3$5?1W?1m?2m2^3").
  Proof.
    intros m3 W1 W2 x Hx. destruct (inb W (bv_unsigned x)) eqn:E.
    - rewrite (wview_pt (chim W m m2) m x (chim_in x E)) in Hx. exact (W1 x Hx).
    - rewrite (wview_pt (chim W m m2) m2 x (chim_out x E)) in Hx. exact (W2 x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma chim_agree_out : ltac2:(zQ "30!ike!iq6!ud@3$1@1$2?1W?2m2@3$0?1W?1m?2m2").
  Proof. intros a Ha Hr. apply chim_out. rewrite wa_unsigned by exact Hr. apply inb_false_outside. exact Ha. Qed.
  (* [comment removed for export] *)
End Chim.

(* [comment removed for export] *)
Section PtEq.
  Context {HCEIL : HeapCeil}.
  Variables (P : Z -> Prop) (m m' : mem).
  Hypothesis AG : ltac2:(zQ "10!iq6@3$0?1P?1m?2m'").

  Lemma bytes_at_pteq : ltac2:(zQ "c0!hk8!m3!ig4!ir2!hmc!ire!i5!is6!iu4!iub!iv1!iv7>1A$1>2bs@1$6@1$4@1$0#8>0@4$3$2?1m^2^1>0>1a$1>0@2$7@2$9^4^1@2$a^1@2$8^4@1$b@2$5@1$4@1$0#8^3@1?1P^2@4$3$2?2m'^4^3").
  Proof.
    (intros A bs nd_i1 HP; ndestruct nd_i1 as (H0 & H1 & H)). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (mrd_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma wr_at_pteq : ltac2:(zQ "70!m3!ig4!jg1!is6!iu4!iub!iv1>1A$0>1n$0>0@4$2$1?1m^2^1>0>1a$0>0@2$3@2$5^4^1@2$6^1@2$4^4^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    (intros A n nd_i2 HP; ndestruct nd_i2 as (H0 & H1 & H)). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (wview_pt m' m); [apply H; exact Hi|]. apply AG; [apply HP; lia| lia].
  Qed.
  Lemma rw_cells_pteq : ltac2:(zQ "b0!m3!ig4!jk5!i5!is6!jod!jp5!iu4!iub!iv1!iv7>1A$0>2cs@1$3$5>0@4$2$1?1m^2^1>0>1a$0>0@2$4@2$8^4^1@2$9^1@2$7^4@1$a@1$6^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    intros A cs [[Hwf Hb] Hw] HP. split; [split; [exact Hwf|]|].
    - apply bytes_at_pteq; [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact HP.
    - apply wr_at_pteq; [exact Hw| exact HP].
  Qed.
  Lemma stk_pteq : ltac2:(zQ "60!m3!ig4!jq3!is6!iub!iv1>2lo$0>2hi$0>0@4$2$1?1m^2^1>0>1a$0>0@2$3@2$4^4^1@2$5^1^3@1?1P^2@4$2$1?2m'^4^3").
  Proof.
    (intros lo hi nd_i3 HP; ndestruct nd_i3 as (H0 & H1 & H)). split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hw [b Hb]].
    assert (E : m' (wa a) = m (wa a)) by (apply AG; [apply HP; exact Ha| lia]).
    split; [rewrite (wview_pt m' m _ E); exact Hw| exists b; rewrite (mrd_pt m' m _ E); exact Hb].
  Qed.
  Lemma u8arr_pteq : ltac2:(zQ "c0!hk8!m3!ig4!ju3!hmc!ire!i5!is6!iu4!iub!iv1!iv7>1A$1>2bs@1$6@1$4@1$0#8>0@4$3$2?1m^2^1>0>1a$1>0@2$7@2$9^4^1@2$a^1@2$8^4@1$b@2$5@1$4@1$0#8^3@1?1P^2@4$3$2?2m'^4^3").
  Proof. intros A bs [Hb Hw] HP. split; [apply bytes_at_pteq; [exact Hb| exact HP]| apply wr_at_pteq; [exact Hw| exact HP]]. Qed.
  Lemma u32arr_pteq : ltac2:(zQ "d0!hk8!m3!ig4!juc!hmc!ire!i5!is6!iu4!iub!iv1!jv6!iv7>1A$1>2ws@1$6@1$4@1$0#k0>0@4$3$2?1m^2^1>0>1a$1>0@2$7@2$9^4^1@2$a^1@2$8^4@2$b+4@1$c@2$5@1$4@1$0#k0^3@1?1P^2@4$3$2?2m'^4^3").
  Proof.
    intros A ws [Hb Hw] HP. split; [| apply wr_at_pteq; [exact Hw| exact HP]].
    apply bytes_at_pteq; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HP. lia.
  Qed.
  Lemma poisoned_pteq : ltac2:(zQ "90!m3!jvd!kg9!kgf!is6!iu4!iub!iv1!iv7>1A$0>1k$3>1v$0>0@4$1?1m^3^2^1>0>1a$0>0@2$4@2$6@1$2^5^1@2$7^1@2$5@1$2^5@1$8^4@1?1P^2@4$1?2m'^5^4^3").
  Proof.
    (intros A k v nd_i4 HP; ndestruct nd_i4 as (H0 & H8 & U8)). split; [exact H0|]. split; [exact H8|]. apply u8arr_pteq; [exact U8|].
    unfold poison_bytes. rewrite repeat_length. exact HP.
  Qed.
End PtEq.
(* [comment removed for export] *)
