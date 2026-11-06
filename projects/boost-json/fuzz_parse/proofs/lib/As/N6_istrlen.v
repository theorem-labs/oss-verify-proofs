(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk46option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm5dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeqc5bvmapi27Z_to_bvk44None37Corelib4Init5Logicub2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hg45asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hk83mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hob2MShob6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ht87seg_rom46Stdlib6ZArith6BinInt1Zii23addk46lengthk41Sk43appk44consk43nat37Corelib4Init3Natim13addii22leii26of_nati2bbv_unsignedub3andii23powk44Someub2exub3not36Stdlib5Lists4Listir79nth_errorii22ltii26to_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaN6_istrlen~~~~~~iu7cistrlen_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jj73evtii23subiu7distrlen_entryk44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jp88bytes_atir72In" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition istrlen_entry := 0x0a23cc%Z.

Definition istrlen_post : ltac2:(zQ "60!hc!jf!lc!h9!pc!t2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3len$3>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0$4P") := ltac2:(zQ "f0!hc!jf!ta!pc!u4!lc!vf!h9!t2!hjf!ho4!hs8!hse!ih7!ija\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a3@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\3len$7\1m>0@1$1@1$0#k0@1$5@1$1@1$0#8\3ms'$3@3$6$3^1@7$b@hf$a^i1^i0^hf^he^hd^hc^hb^ha^h9@2$2@1$0#k0^3@2$2@1$0#k0@2$e^3+1@2$2@1$0#k0Z^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5@1$c^i1^4@1$4@1$1@1$0#k0^2@1$d$9").

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis STR : ltac2:(zQ "80!hc!jf!ike!il4!hjf!jt2!ta!ioa@4$5$4?1m@2$7@1$0#k0?2a0@3$2@1$1@1$0#8?3str@3$3@1$1@1$0#8@2$6@1$0#8Z?5slack").
  Hypothesis NONUL : ltac2:(zQ "50!hc!ir1!jte!ta!jf@1$1@3$2@1$4@1$0#8@2$3@1$0#8Z?3str").

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (istrlen_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc len m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma full_length : ltac2:(zQ "a0!hc!jf!ik1!ika!ike!il4!ilb!vf!in3!ta@3$7$6@2$2@1$1@1$0#8@3$4@1$1@1$0#8?3str@3$5@1$1@1$0#8@2$9@1$0#8Z?5slack@2$8@2$2@1$1@1$0#8?3str@1$3@2$2@1$1@1$0#8?5slack").
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : ltac2:(zQ "90!hc!ija!ik1!ina!io0!jf!ioa!ip8!ipe@2$7@2$3Z@2$6@1$0#k0?2a0@2$3@2$1@2$1@2$1@2$6@1$0#k0?2a0@1$4@2$2@1$5@1$0#8?3str+1@1$4@2$2@1$5@1$0#8?5slack@2$8+2+k0").
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : ltac2:(zQ "h30!hc!jf!ip8!vf!h9!iq5!ike!il4!ik1!lc!iqc!ir1!isa!ina!it7!io0!itd!ta!ioa>1i$4>0@2$2@2$dZ^1@2$e^1@1$f@2$8@1$1@1$0#8?3str@2$a@1$1@1$0#8\1b@1$1@1$0#8@2$2@3$3@1$9@1$1@1$0#8@3$c@1$1@1$0#8@3$6@1$1@1$0#8?3str@3$7@1$1@1$0#8@2$h1@1$0#8Z?5slack@1$h0^3@2$5@1$1@1$0#8^1@1$b@3$3$4@2$h2@1$0#8^1Z").
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : ltac2:(zQ "c0!hc!jf!ta!iq5!ike!il4!ik1!lc!vf!isa!io0!itd@3$8@1$7@1$1@1$0#8@3$9@1$1@1$0#8@3$4@1$1@1$0#8?3str@3$5@1$1@1$0#8@2$2@1$0#8Z?5slack@1$b@1$a@2$6@1$1@1$0#8?3str@2$3@1$1@1$0#8@2$2@1$0#8Z").
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma istrlen_loop : ltac2:(zQ "h30!hc!jf!ik1!io0!ilb!hjf!ina!ta!u4!ip8!vf!h9!ji7!jn2!ho4!hs8!ih7!jn9!itd>1k$4>1i$b>3x12@1$1@1$0#k0>0@3$a$4@1$h2@2$h1@1$3@2$2@1$1@1$0#8?3str^2^3>0@2$9@2$6Z^3@2$6^3@1$3@2$2@1$1@1$0#8?3str@3$d$5@i0$c?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F?2fc@1$3@2$2@1$1@1$0#8?3str?1m@7$f@hf$e?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0@2$7@1$0#k0^4^3?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$7@1$0#k0+qijt0?2fc@1$8@1$1@1$0#k0?1m@1$h0$5").
  Proof.
    induction k as [|k IH]; intros i x12 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. do 2 zstep.
      replace (len + 1 + -1)%Z with len by lia. apply evt_done. reflexivity.
    - ndestruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read asegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      apply (IH (i + 1)%Z); lia.
  Qed.

  Lemma istrlen_body : ltac2:(zQ "d0!hc!jf!hjf!u4!ik1!jo0!ji7!jn2!ho4!hs8!ih7!io0!ta>3x11@1$1@1$0#k0>3x12@1$1@1$0#k0@3$7$2@i0$6?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F?2fc@1$b@2$4@1$1@1$0#8?3str?1m@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0^2^1?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$c@1$0#k0$5?2fc@1$3@1$1@1$0#k0?1m@1$a$2").
  Proof.
    intros x11 x12. unfold istrlen_entry. zstep.
    apply (istrlen_loop (Z.to_nat len) 0); lia.
  Qed.
End Proofs.

Lemma istrlen_spec : ltac2:(zQ "h60!hc!jf!hjf!ta!jp1!u4!ike!il4!ik1!lc!ir1!t2!jo0!ji7!jn2!ho4!hs8!jt2!ih7!jte!io0!ioa>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$b@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>3str@1$4@1$1@1$0#8>5slack@1$4@1$1@1$0#8>0@4$h1$2^3@2$h5@1$0#k0^hb@3$6@1$1@1$0#8^2@3$7@1$1@1$0#8@2$3@1$0#8Z^1>0@1$a@3$h3@1$1@1$0#8@2$3@1$0#8Z^3@3$e$2@i0$d^i6^i5^i4^i3^i2^i1^i0^hf^he^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6@1$h4@2$8@1$1@1$0#8^4^5@7$h0@hf$f^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7@2$3@1$0#k0$c^6@1$5@1$1@1$0#k0^5@1$h2$2").
Proof. intros. eapply istrlen_body; eassumption. Qed.
