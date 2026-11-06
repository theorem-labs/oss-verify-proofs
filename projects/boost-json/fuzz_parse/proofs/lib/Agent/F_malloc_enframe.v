(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3lorhc6shiftr37Corelib4Init9Datatypesk34boolhc3ltb37Corelib4Init5Logicm82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~o15smear79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~t38fold_offhc3addhc4landhc3subhc2lek34listhc6to_natk33nat37Corelib5Lists7ListDefhka3maphka3seqhc6of_natk34negbk33orbhc3lebo18fold_fn1o14zseq36Stdlib5Lists4Listhpd7forallbk34trueo17fold_fnm83andhc2lthc3mul04Npos35stdpp9bitvectorbdefinitionshu32bvk34consk33nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~ih32b8ih32wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~im13le1hu37Z_to_bvt34aptrt36mstate01Nt37cellvalk33fstk33sndt39cell_readt34conct3aget_shadowt34metat3cget_meta_rect38upd_meta" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition smear : ltac2:(zQ "10!h9>1s$0$0") := ltac2:(zQ "30!h9!j4!ja\1s$0=2m1$0@2$1^1@2$2^1+1=2m2$0@2$1^1@2$2^1+2@2$1^1@2$2^1+4").

Lemma fold_off_eq : ltac2:(zQ "90!h9!lb!m2!nc!sb!hh1!hhc!hi2!hi9>3off$0>5slack$0@3$3$0@2$5^2^1M1\0$1$0@2$2^1^2=1x$0@2$7^2@1$4^1M1\0$1$0@2$2^2^1@2$8^1@2$6^2+1^1^2").
Proof. intros off slack. reflexivity. Qed.

Lemma smear_nonneg : ltac2:(zQ "30!hif!h9!sb>1s$1>0@2$0Z^1@2$0Z@1$2^2").
Proof. intros s.
  intros. unfold smear.
  repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
    repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
  all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

Lemma land_le_l : ltac2:(zQ "30!hif!h9!hi2>1a$1>1b$1>0@2$0Z^2>0@2$0Z^2@2$0@2$2^4^3^4").
Proof. intros a b.
  intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

(* [comment removed for export] *)
Definition zseq : ltac2:(zQ "20!h9!hj4>1a$0>1n$0@1$1$0") := ltac2:(zQ "60!h9!hjb!hk4!hm1!hm8!hmf\1a$0\1n$0@4$3$2$0$5@2$4@1$1^2@1$1^1").

(* [comment removed for export] *)
Definition fold_fn1 : ltac2:(zQ "20!h9!lb>1s$0>3off$0$1") := ltac2:(zQ "90!h9!hn8!hnf!sb!hhc!hi2!ho5!m2!hi9\1s$0\3off$0=1x$0@2$5^1@1$3^2@2$2@1$1@2$7^3^1@2$6@2$8^1@2$4^3+1^3").
Definition fold_fn : ltac2:(zQ "20!lb!h9>1s$1$0") := ltac2:(zQ "40!h9!hob!hp6!hr0\1s$0@3$3$0@1$1^1@2$2Z+hg0").

Lemma fold_check_true : ltac2:(zQ "70!lb!hrb!nc!h9!hs2!hp6!hr0@3$2$0@3$6$3$4@2$5Z+o0$1").
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_zseq : ltac2:(zQ "a0!h9!lb!hrb!nc!hif!hsc!hp6!hr0!hhc!ht2>1f>0$0$1>1a$0>1n$0>1x$0>0@3$3$1@3$7$0^4@2$6^3^2$2>0@2$4Z^4>0@2$5@2$4^5^3@2$9^3@2$8^5^4@3$3$1@1^7^4$2").
Proof. intros f a n x.
  intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma fold_assert_ok : ltac2:(zQ "80!hif!h9!sb!hi2!ht2!hsc!hhc!hi9>3off$1>5slack$1>0@2$5@2$0Z^2@2$4^2+hg0>0@2$0Z^2>0@2$4^3@2$3^4@1$2^3@2$0@2$7@2$3^5@1$2^4@2$6^4+1^4").
Proof. intros off slack.
  intros Ho Hs Hlt.
  pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  destruct (Z.lt_ge_cases slack 128).
  - pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
    pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
    apply orb_prop in H2. destruct H2 as [H2|H2].
    + apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
    + apply Z.leb_le in H2. exact H2.
  - lia.
Qed.

Lemma fold_off_le_slack : ltac2:(zQ "50!hif!hsc!h9!hh1!ht2>3off$2>5slack$2>0@2$1@2$0Z^2@2$4^2+hg0>0@2$0Z^2@2$1@2$0Z@2$3^4^3@2$0@2$3^4^3^3").
Proof. intros off slack.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma land_126 : ltac2:(zQ "50!h9!hi2!nc!ht7!ja>1y$0@3$2$0@2$1^1+ne@2$3+2@2$1@2$4^1+1+jf").
Proof. intros y.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|].
  - rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

Lemma mword_sc : ltac2:(zQ "90!h9!hif!ht7!hsc!hhc!ht2!nc!hi2!ja>8last_idx$0>8freeable$0>2sc$0>6maplen$0>0@2$3@2$1Z^4@2$5^4+i0>0@2$3@2$1Z^4@2$5^4+2>0@2$3@2$1Z^4@2$5^4+k0>0@2$1Z^4@3$6$0@2$7@2$8@2$4@2$4@2$4^8@2$2+i0^7@2$2+k0^6@2$2+hgg0^5+5+ne@2$2+2^6").
Proof. intros last_idx freeable sc maplen.
  intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
  replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.

Lemma le1_wz : ltac2:(zQ "d0!htd!ig0!ig6!hj4!igd!hsc!nc!h9!il5!ilb!ipb!hif!ht2>1v$7>0@2$5@2$bZ^1@2$c^1+hg0@3$6@1$3@1$1@1$0#8@1$a@1$9^2@3$2@1$1@1$0#8@1$8^2@1$4@1$1@1$0#8").
Proof. intros v. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

Lemma le1_neg32 : ltac2:(zQ "90!htd!ig0!ig6!hj4!igd!nc!il5!ipb!iq2@3$5@1$3@1$1@1$0#8@1$7@2$8@1$0#k0-i0@3$2@1$1@1$0#8@1$6+u0@1$4@1$1@1$0#8").
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FASTMODEL.
Context {O : Type}.
Variable pans : ltac2:(zQ "20!h9!iqd>0?1O>0$1>0$0>0$0$0").
Hypothesis Hpans : ltac2:(zQ "50!h9!hsc!iqd!hif!ht2>1o?1O>1p$2>1c$0>1h$0@2$1@2$3Z@4?4pans^4^3^2^1@2$4@4?4pans^4^3^2^1+hg0").
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)
Definition rdv : ltac2:(zQ "30!h9!iqd!ir4>1o?1O>2st$2>1q$1$0") := ltac2:(zQ "a0!h9!ird!is0!isa!it0!iqd!it6!iu2!iu9!ir4\1o?1O\2st$9\1q$5M2\1x$2$0@2$6@2$8^2@3$3$1$0^1@3$4$1$0^1\1v$0^1\1h$0@4?4pans^4^2@2$7^3^2^1").

Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
  unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
  unfold MallocCtrl.prun. cbn [eruns psel].
  pose proof (Hpans o q (conc st q) h).
  replace (peek_answer_ok (pans o q (conc st q) h)) with true.
  2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  reflexivity.
Qed.

Lemma rd16_oracle {R} o st q (k : Z -> M R) :
  prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

Lemma get_meta_rec_upd_same : ltac2:(zQ "60!iv6!ivd!nc!iqd!ir4!jgc>2st$4>1g$3>1f>0$0$0@3$2$0@2$1@3$5^2^1^3^2@1^1@2$1^3^2").
Proof. intros st g f. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
End FASTMODEL.
(* [comment removed for export] *)
