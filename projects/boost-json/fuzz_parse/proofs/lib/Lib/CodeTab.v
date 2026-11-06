(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Exec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Z3h5LinuxProcessSemantics5Riscv5Instrjb5instr3h5LinuxProcessSemantics5Riscv7Preludem74tree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib7CodeTab~~~~~~p48ct_entryhe8positive46Stdlib6ZArith6BinInt1Zu86to_pos04list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehgf7Segmenthe4Npos35stdpp9bitvectorbdefinitionshl62bv37Corelib4Init5Logichn92eq04Some06optionhn93and04bool05false04pairhn92ex3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshs1afetch_wordhs18is_ecall3h5LinuxProcessSemantics5Riscv7DecodeCih2adecode_anyhl67Z_to_bvp44ctab04truem74tgetp47ct_factp46ct_keyu83ltbm74tsetm76TEmptyp48ct_soundp46ct_addp48ct_buildhs1dmachine_statem75bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~is63evths19MachineOkhs1emachine_result3h5LinuxProcessSemantics5Riscv3Semji74Coreji74execp46ct_forp47ctf_tab79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jmc2MSjmcbinterp_eff0jmcblift_result" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ct_entry : ltac2:(zQ "00S") := ltac2:(zQ "30!h8!j7!lf@2$0$2$1").              (* [comment removed for export] *)
Definition ctab : ltac2:(zQ "00S") := ltac2:(zQ "20!od!t2@1$0$1").                    (* [comment removed for export] *)

Definition ct_key : ltac2:(zQ "20!j7!td>2pc$0$1") := ltac2:(zQ "20!j7!hg0\2pc$0@1$1^1").

(* [comment removed for export] *)
Definition ct_fact : ltac2:(zQ "40!j7!hg9!hk4!lf>4segs@1$1$2>2pc$0>1i$3>2sz$0P") := ltac2:(zQ "h30!hkf!j7!lf!hn3!hod!hp3!hp9!h8!hq1!hq8!hqe!hg9!hr5!hrb!hk4!hv8!ig6!ij8!ik6\4segs@1$b$e\2pc$1\1i$2\2sz$1@2$d@1$3@1$0#i0\1w@1$3@1$0#i0@2$8@3$4@1$6@1$3@1$0#i0@2$f^5@2$h2@1$0#k0^4@2$5@1$3@1$0#i0^1@2$8@3$4$9@1$h0^1$a@3$4@1$6@2$7$2$1@1$h1^1@2$5@2$7$2$1@4$c$2$1^3^2").

Definition ct_sound : ltac2:(zQ "30!hg9!hk4!il1>4segs@1$0$1>1t$2P") := ltac2:(zQ "h10!j7!lf!hod!t2!hp3!hq8!hg9!hp9!hr5!h8!il8!hk4!ile!im5!imf!il1!in8\4segs@1$6$b\1t$f>2pc$0>1i$1>2sz$0>0@3$2$5@2$h0Z^3$a>0@3$2@1$7$3@3$c$3@1$e^4^5@2$4@2$9$1$0@4$8$1$0^3^2@4$d^7^5^4^3").

Lemma ct_key_inj : ltac2:(zQ "70!hod!j7!hq8!il8!imf!in8!td>1a$1>1b$1>0@3$0$2@2$5Z^2$3>0@3$0$2@2$5Z^2$3>0@3$0$6@1$4^4@1$4^3@3$0$1^5^4").
Proof. unfold ct_key. intros a b Ha Hb E. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hb. apply Z2Pos.inj; assumption. Qed.

Definition ct_add : ltac2:(zQ "40!il1!hg9!j7!hk4>4segs@1$1$3>2pc$2>1t$0$0") := ltac2:(zQ "h20!j7!lf!il1!h8!hq8!hp9!hkf!hn3!hg9!hr5!hk4!hv8!ig6!ij8!ine!imf!in8!ik6\4segs@1$8$a\2pc$0\1t$2M5\1x@1$5@1$7@1$6#i0$2@2$b^3@2$h1@1$6#k0^2\1w@1$7@1$6#i0M4\0$4$2@1$c^1^2M5\1x@1$5@2$3$1$0$2@1$d^1\1p@2$3$1$0M3\1p@2$3$1$0$2^1\1i$1\2sz$0M4\0$4$2@2$h0Z^6@4$e@2$3$1$0@1$f^6@4$9$1$0^2^1^5^5^2^1").

Fixpoint ct_build (segs : list Segment) (pcs : list Z) (t : ctab) : ctab :=
  match pcs with
  | nil => t
  | pc :: pcs' => ct_build segs pcs' (ct_add segs pc t)
  end.

Lemma ct_sound_empty : ltac2:(zQ "50!hg9!hk4!io5!t2!ioe>4segs@1$0$1@2$4^1@1$2$3").
Proof. intros segs pc i sz _ H. destruct (ct_key pc); discriminate H. Qed.

Lemma ct_add_sound : ltac2:(zQ "60!ioe!hg9!j7!hk4!ip9!il1>4segs@1$1$3>2pc$2>1t$5>0@2$0^3^1@2$0^4@3$4^4^3^2").
Proof.
  intros segs pc t Ht. unfold ct_add.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|exact Ht].
  destruct (is_ecall w) eqn:He; [exact Ht|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Ht].
  destruct (Z.ltb 0 pc) eqn:Hp; [|exact Ht].
  intros pc' i' sz' Hp' Hg.
  destruct (Pos.eq_dec (ct_key pc) (ct_key pc')) as [E|NE].
  - rewrite <- E in Hg. rewrite tget_tset_same in Hg. injection Hg as <- <-.
    rewrite <- (ct_key_inj pc pc' Hp Hp' E). exists w. repeat split; assumption.
  - rewrite tget_tset_other in Hg by exact NE. exact (Ht _ _ _ Hp' Hg).
Qed.

Lemma ct_build_sound : ltac2:(zQ "60!hg9!ioe!j7!hk4!iq2!il1>4segs@1$0$3>3pcs@1$0$2>1t$5>0@2$1^3^1@2$1^4@3$4^4^3^2").
Proof. intros segs pcs. induction pcs as [|pc pcs IH]; intros t Ht; cbn; [exact Ht|]. apply IH. apply ct_add_sound. exact Ht. Qed.

(* [comment removed for export] *)
Class ct_for (segs : list Segment) := { ctf_tab : ctab ; ctf_ok : ct_sound segs ctf_tab }.

Lemma ct_sound_of_eq : ltac2:(zQ "90!hg9!il1!hod!j7!hk4!io5!iq2!t2!ioe>4segs@1$0$4>3pcs@1$0$3>1t$1>0@3$2$1^1@3$6^3^2@1$5$7@2$8^4^2").
Proof. intros segs pcs t ->. apply ct_build_sound. apply ct_sound_empty. Qed.

(* [comment removed for export] *)
Lemma evt_step_ct : ltac2:(zQ "he1!hkf!hn3!hp9!j7!iqd!hod!lf!ik6!ire!t2!jg1!hp3!hq8!hg9!hr5!h8!il8!hk4!jg8!jh5!ile!jk9!jl1!jl9!imf!jm2!jq9!jqf!jre!in8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h1>1C@1$h7^1>1Q>0$4P>1R@2$8@1$0#5@1$1@1$0#k0>1F@2$8@1$0#5@1$1@1$0#k0>2pc$3>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1i$6>2sz$3>3ms1$4>0@3$5$c@2$hdZ^8$h0>0@3$5@1$2$9@3$h4$9@1$h8^9@2$h9^e^d@2$b@2$f$6$3@4$e$6$3^4^3>0@3$5@1$h3$4@2$hc^6@3$hb^f@3$h6@2$7@1$0#k0^4^5@5$h5^c^b@2$7@1$0#k0^a^9^8^7@2$h2$4^3>0@3$a^h0^e^4@3$a^h1^f@7$ha^e^d@2$7@1$0#k0^c^b^a^9^8").
Proof.
  intros segs C Q R F pc fc rv m ro i sz ms1 Hp Hg Hx Hq.
  destruct (@ctf_ok segs C pc i sz Hp Hg) as (w & Hf & He & Hd).
  eapply evt_step; [|exact Hq]. split; [reflexivity|].
  rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

(* [comment removed for export] *)
Ltac ct_lookup segs pc k :=
  let C := constr:(_ : ct_for segs) in
  let r := eval lazy in (tget (ct_key pc) (@ctf_tab segs C)) in
  lazymatch r with
  | Some (?i, ?sz) => k C i sz
  end.
