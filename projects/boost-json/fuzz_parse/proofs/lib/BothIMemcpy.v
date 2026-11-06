(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SumsLib Sums_code.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv04cons03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9Sums_code~~~~~~mb7W_a21fcmb7W_a2200mb7W_a2204mb7W_a2208mb7W_a220cmb7W_a2210mb7W_a2214mb7W_a2218mb7W_a221c37Corelib4Init5Logichg11Ije2BVje4BvWfhg12eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~hic3at_69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hmb4getr3h5LinuxProcessSemantics5Riscv7Preludehqe5bvmaphg13andhe1Zhmb4mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib~~~~~~hv04memk46Stdlib6ZArith6BinInt1Zij23sub03nathg12ex69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemcpy~~~~~~ilccimemcpy_clob69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~iqa6mstepshicaregs_agreehic6ret_ok36Stdlib5Lists4Listjg52Inij22leij22ltij26of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~jj46wbytesje7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3libbBothIMemcpy4FPX2~~~~~~jo2h2asan_imemcpy_entryilcdimemcpy_wordshv07code_at69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~jv8floaded_segments06optionhv04cpyH3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekl57Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition imemcpy_words : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#i0") := ltac2:(zQ "d0!j7!lb!m0!m6!q7!r1!rb!s5!sf!t9!u3!ud!v7@3$2@1$1@1$0#i0$4@3$2@1$1@1$0#i0$5@3$2@1$1@1$0#i0$6@3$2@1$1@1$0#i0$7@3$2@1$1@1$0#i0$8@3$2@1$1@1$0#i0$9@3$2@1$1@1$0#i0$a@3$2@1$1@1$0#i0$b@3$2@1$1@1$0#i0$c@1$3@1$1@1$0#i0").

(* [comment removed for export] *)
Definition imemcpy_clob : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#5") := ltac2:(zQ "70!j7!lb!m0!hh5!hha!hhf!m6@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@3$2@1$1@1$0#5@3$4@1$0#5+eKv$3@2$5@1$0#5+e@1$6@1$1@1$0#5").
End FPX1.

Section IMEMCPY.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!h8!koa@1$0$1").
  Variable base : word.
  Variable mem0 : ltac2:(zQ "30!j7!lb!kk5>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables dst src : word.
  Variable n : Z.
  Variable bs : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#8").
  Variable rom : ltac2:(zQ "30!j7!lb!kk5>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis HCODE : ltac2:(zQ "20!jtc!jud@4$1?4segs?4baseZ$0").
  Hypothesis HOK : ltac2:(zQ "10!kkd@6$0?4segs?4mem0?3dst?3src?1n?2bs").

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemcpy_clob).
  Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma imemcpy_loop : ltac2:(zQ "h80!j7!lb!hi6!hh5!hm4!hq6!hha!hhf!ht4!htd!hu4!hu8!iia!ika!il1!il6!ipa!iu3!iud!ivb!jh8!jhe!ji4!jia>1i$e>4regs@2$8@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>1k$a>0@1$h3^2>0@3$2@1$1@1$0#k0@2$5^4@3$6@1$0#5+1Kv$3@2$7@1$0#5+1^3>0@3$2@1$1@1$0#k0@2$5^5@3$6@1$0#5+bKv$3@2$7@1$0#5+b@2$4?3src^3>0@3$2@1$1@1$0#k0@2$5^6@3$6@1$0#5+dKv$3@2$7@1$0#5+d@2$4?3dst^4>0@3$2@1$1@1$0#k0@2$5^7@3$6@1$0#5+cKv$3@2$7@1$0#5+c@2$4?3dst?1n>0@2$9@2$h5Z^6@2$h6^6?1n>0@3$2$a@1$h7^a@2$d@2$d?1n+1^7@2$f@2$8@1$0#5@1$1@1$0#k0\5regs'@2$8@1$0#5@1$1@1$0#k0@2$9@3$h1?4segs@5$b?2fx^b@2$4?4base+c@4$c?4mem0?3dst?2bs^9?3rom@5$b?2fx^1^a@4$c?4mem0?3dst?2bs?1n?3rom@3$h2\1r@1$1@1$0#5@3$h4@1$1@1$0#5^1$h0^b^1").
  Proof.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      eexists. split.
      + mlbu C12 D_a2208 k.                       (* [comment removed for export] *)
        msb C16 D_a220c k.                        (* [comment removed for export] *)
        an C20 D_a2210.                           (* [comment removed for export] *)
        an C24 D_a2214.                           (* [comment removed for export] *)
        ab_ft C28 D_a2218 ltac:(condz).           (* [comment removed for export] *)
        aret C32 D_a221c ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemcpy_clob. solve_regs_agree.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C12 D_a2208 k.
          msb C16 D_a220c k.
          an C20 D_a2210.
          an C24 D_a2214.
          ab_tk C28 D_a2218 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. (intros r1 nd_i1; ndestruct nd_i1 as (R1 & R11 & R13 & R12 & AG)).
        ndestruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Theorem imemcpy_run : ltac2:(zQ "h30!j7!lb!hh5!hi6!hq6!hha!hhf!ht4!hu8!htd!il6!ipa!jme!iu3!hm4!iud!ivb!jh8!jn8>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@1$h0^1>0@3$3@1$1@1$0#k0@2$4^3@3$5@1$0#5+1Kv$2@2$6@1$0#5+1^2>0@3$3@1$1@1$0#k0@2$4^4@3$5@1$0#5+aKv$2@2$6@1$0#5+a?3dst>0@3$3@1$1@1$0#k0@2$4^5@3$5@1$0#5+bKv$2@2$6@1$0#5+b?3src>0@3$3@1$1@1$0#k0@2$4^6@3$5@1$0#5+cKv$2@2$6@1$0#5+c@2$h2@1$0#k0?1n@2$a@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$9@3$d?4segs@5$8?2fx^8@2$e?4baseZ?4mem0?3rom@5$8?2fx^1^7@3$c?4mem0?3dst?2bs?3rom@3$f\1r@1$1@1$0#5@3$h1@1$1@1$0#5^1$b^8^1").
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    - (* [comment removed for export] *)
      eexists. split.
      + ab_tk C0 D_a21fc ltac:(condz).            (* [comment removed for export] *)
        aret C32 D_a221c ret.
        rewrite Hz. apply mst_refl.
      + apply regs_agree_refl.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C0 D_a21fc ltac:(condz).          (* [comment removed for export] *)
          av C4 D_a2200 (at_ dst n) ltac:(apply v_add_at; lia).  (* [comment removed for export] *)
          an C8 D_a2204.                          (* [comment removed for export] *)
          apply mst_refl.
        * post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. (intros r1 nd_i2; ndestruct nd_i2 as (R1 & R11 & R13 & R12 & AG)).
        ndestruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition asan_imemcpy_entry : word := 0x0a219c.

Lemma asan_imemcpy_code : ltac2:(zQ "40!js5!jtc!jud!kj2@4$2$3$0Z$1").
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : ltac2:(zQ "h81!j7!lb!hh5!hi6!hq6!hha!hhf!ht4!kk5!hu8!kj2!h8!htd!il6!hu4!js5!ipa!jme!iu3!iud!ivb!kkd!jh8!jn8&>0@1$1@1$0#k0@1$8@1$1@1$0#8>4mem0~0>3dst@1$1@1$0#k0>3src@1$1@1$0#k0>1n$e>2bs@1$b@1$1@1$0#8>3rom~0>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@6$h5$a^8^7^6^5^4>0@1$h4^2>0@3$3@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$2@2$6@1$0#5+1^3>0@3$3@1$1@1$0#k0@2$4^5@3$5@1$0#5+aKv$2@2$6@1$0#5+a^a>0@3$3@1$1@1$0#k0@2$4^6@3$5@1$0#5+bKv$2@2$6@1$0#5+b^a>0@3$3@1$1@1$0#k0@2$4^7@3$5@1$0#5+cKv$2@2$6@1$0#5+c@2$h7@1$0#k0^a@2$d@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$c@3$h2$a@5$9?2fx^9$f^f^a@5$9?2fx^1^8@3$h1^f^e^b^a@3$h3\1r@1$1@1$0#5@3$h6@1$1@1$0#5^1$h0^9^1").
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 asan_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.
End FPX2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
