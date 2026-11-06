(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim Frame RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefMemcpyBase RefMemchr Ub_code_e3ae8_e4bfc Ub_code_ee154_ee8c8 Ub_code_eee7c_eeec0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~qd6wbytes46Stdlib6ZArith6BinInt1Zv03subhf7Z_to_bvhfbbv_unsignedk16lengthk13nat37Corelib4Init5Logichj52eqhj52or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStrnlen3SNL~~~~~~hl54mem1v02lev02lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9RefMemchr~~~~~~hqa5mchrH01Zk14prodk14consk13nilk14pair69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~igf9frame_modk14listk14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~im23rdn69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~iq4floaded_segmentshj51Ihf2BVhf4BvWfim24getr3h5LinuxProcessSemantics5Riscv7Preludejg65bvmaphj53andim24mksthj52ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~jka6msteps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~jod6ret_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~jsf8keeps_csv03addk14boolk14truem28store_okv06of_nat" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SNL.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable mem : ltac2:(zQ "30!h9!jc!l9>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables s sp : word.
  Variable buf : ltac2:(zQ "30!il4!h9!jc@1$0@1$2@1$1#8").
  Variables K n : Z.
  Variable rom : ltac2:(zQ "30!h9!jc!l9>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis HOK : ltac2:(zQ "10!hu8@5$0?3mem?1s?3buf?1K?1n").
  Hypothesis HsK : ltac2:(zQ "40!h9!kha!hq5!hh8@2$2Z@2$1@2$3@1$0#k0?1s?1K").
  Hypothesis Hstk : ltac2:(zQ "90!h9!ki0!ki7!hk9!kie!ita!hg8!hge!hh8@3$3$1@4$4$5?3mem@2$7@1$0#k0@2$6@2$8@1$0#k0?2sp+i0Ni0$2").
  Hypothesis Hspr : ltac2:(zQ "40!h9!hq0!hg8!hh8@2$1+hkgo8@2$2@2$3@1$0#k0?2sp+i0").
  Hypothesis Hdisj : ltac2:(zQ "90!h9!hh8!hq0!hi6!hkf!kha!kj9!hg8!jc@2$4@2$2@2$5@2$1@1$0#k0?1s@1$6@2$3@1$8@1$0#8?3buf@2$7@2$1@1$0#k0?2sp+i0@2$2@2$1@1$0#k0?2sp@2$1@1$0#k0?1s").

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Definition mem1 : ltac2:(zQ "30!h9!jc!l9>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "70!h9!p9!u7!hg8!hge!jc!hh8\2ra@1$5@1$0#k0\2s0@1$5@1$0#k0\2s1@1$5@1$0#k0@3$2@3$2@3$2?3mem@2$4@1$0#k0@2$3@2$6@1$0#k0?2sp+8@2$1N8^3@2$4@1$0#k0@2$3@2$6@1$0#k0?2sp+h0@2$1N8^2@2$4@1$0#k0@2$3@2$6@1$0#k0?2sp+h8@2$1N8^1").

  Lemma lenW8 : ltac2:(zQ "60!h9!jc!hi6!hif!hk9!p9>1v@1$1@1$0#k0@3$4$3@2$2@1$1@1$0#8@2$5N8^1N8").
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  Lemma mem1_out : ltac2:(zQ "a0!h9!jc!hh8!l9!hk9!hkf!hp8!hq0!hq5!hg8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>1a@1$1@1$0#k0>0@2$5@2$8@2$2@1$0#k0^1@2$9@2$2@1$0#k0?2sp+h8@2$7@2$2@1$0#k0?2sp@2$2@1$0#k0^1@3$4@1$3@1$1@1$0#8@4$6^5^4^3^2@1?3mem^2").
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
    rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma HOK1 : ltac2:(zQ "40!h9!jc!hu8!hp8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0@5$2@3$3^3^2^1?1s?3buf?1K?1n").
  Proof.
    intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
    - rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
    - intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
  Qed.

  Lemma frame1 : ltac2:(zQ "c0!h9!jc!hv1!hv4!hvb!ig2!ig8!ik7!hp8!hg8!hge!hh8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0@3$7?3mem@3$8^3^2^1@3$4@2$3@1$1@1$0#k0$2@4$6@1$1@1$0#k0$2@2$a@1$0#k0@2$9@2$b@1$0#k0?2sp+i0+i0@1$5@2$3@1$1@1$0#k0$2").
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
    - intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
    - unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
      eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_ra : ltac2:(zQ "d0!h9!jc!il4!ilb!l9!hk9!p9!ipd!hp8!ita!hg8!hge!hh8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0@3$5@1$4@1$2@1$1@1$0#8@4$7$9@3$8^3^2^1@2$b@1$0#k0@2$a@2$c@1$0#k0?2sp+8N8@2$3@1$2@1$1@1$0#8@2$6N8^3").
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s0 : ltac2:(zQ "d0!h9!jc!il4!ilb!l9!hk9!p9!ipd!hp8!ita!hg8!hge!hh8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0@3$5@1$4@1$2@1$1@1$0#8@4$7$9@3$8^3^2^1@2$b@1$0#k0@2$a@2$c@1$0#k0?2sp+h0N8@2$3@1$2@1$1@1$0#8@2$6N8^2").
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s1 : ltac2:(zQ "d0!h9!jc!il4!ilb!l9!hk9!p9!ipd!hp8!ita!hg8!hge!hh8>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0@3$5@1$4@1$2@1$1@1$0#8@4$7$9@3$8^3^2^1@2$b@1$0#k0@2$a@2$c@1$0#k0?2sp+h8N8@2$3@1$2@1$1@1$0#8@2$6N8^1").
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

  (* [comment removed for export] *)
  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  Lemma strnlen_run : ltac2:(zQ "h11!h9!jc!iud!iv2!iv7!ive!hk9!jic!jj5!jjc!hge!jk4!jo3!js5!kge!hp8!ita&@3$3@1$0#5+aKv$2@2$4@1$0#5+a>4regs@2$7@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@1$d^1>0@3$6@1$1@1$0#k0@2$5^3@3$3@1$0#5+1Kv$2@2$4@1$0#5+1^2>0@3$6@1$1@1$0#k0@2$5^4@3$3@1$0#5+2Kv$2@2$4@1$0#5+2?2sp>0@3$6@1$1@1$0#k0@2$5^5~0?1s>0@3$6@1$1@1$0#k0@2$5^6@3$3@1$0#5+bKv$2@2$4@1$0#5+b@2$a@1$0#k0?1n@2$b@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$8@3$c$h0@5$9?2fx^8Kd@3$3@1$0#k0+uuuncKv$2@2$4@1$0#k0+uuunc@1$1@1$0#k0?3mem?3rom@5$9?2fx^1^7@3$f^7@2$5^8@3$3@1$0#5+8Kv$2@2$4@1$0#5+8@2$5^8@3$3@1$0#5+9Kv$2@2$4@1$0#5+9?3rom@2$8@2$e^8^1@3$6@1$1@1$0#k0@2$5^1~0@2$a@1$0#k0?1K").
  Proof.
    intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    pose proof (KL _ _ _ _ _ HOK) as HKL.
    destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
    set (s0 := getr regs 8). set (s1 := getr regs 9).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xee154 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 1 = (0xeeea0 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
                       /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
                       /\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
    { eexists. split.
      - stepiv F_eee7c D_eee7c (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_eee80 D_eee80 (Z_to_bv 64 (usp - 8)).                 (* [comment removed for export] *)
        msd F_eee84 D_eee84 (Z_to_bv 64 (usp - 16)).                (* [comment removed for export] *)
        msd F_eee88 D_eee88 (Z_to_bv 64 (usp - 24)).                (* [comment removed for export] *)
        stepn F_eee8c D_eee8c.                                       (* [comment removed for export] *)
        stepn F_eee90 D_eee90.                                       (* [comment removed for export] *)
        stepn F_eee94 D_eee94.                                       (* [comment removed for export] *)
        stepn F_eee98 D_eee98.                                       (* [comment removed for export] *)
        stepn F_eee9c D_eee9c.                                       (* [comment removed for export] *)
        rwH. fold s0 s1. unfold mem1. apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
        intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
                 | gres; reflexivity ] |]).
        destruct Hx. }
    cbv beta. (intros r1 nd_i1; ndestruct nd_i1 as (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK)).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0xeeea0 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
    { ndestruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0xeeea0 : word) (HOK1 ret s0 s1)
                  ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
      exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
    cbv beta. intros r2 (A10 & KC).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
    assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).
    (* [comment removed for export] *)
    eexists. split.
    - stepb_ft F_eeea0 D_eeea0 ltac:(rwH; apply c_eq_neq; unorm; lia).  (* [comment removed for export] *)
      stepiv F_eeea4 D_eeea4 (Z_to_bv 64 K)
        ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).          (* [comment removed for export] *)
      stepn F_eeea8 D_eeea8.                                         (* [comment removed for export] *)
      mld8 F_eeeac D_eeeac ret (rd_ra ret s0 s1).                    (* [comment removed for export] *)
      mld8 F_eeeb0 D_eeeb0 s0 (rd_s0 ret s0 s1).                     (* [comment removed for export] *)
      mld8 F_eeeb4 D_eeeb4 s1 (rd_s1 ret s0 s1).                     (* [comment removed for export] *)
      stepiv F_eeeb8 D_eeeb8 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                     (* [comment removed for export] *)
      stepret F_eeebc D_eeebc ret ltac:(reflexivity).
      apply mst_refl.
    - split.
      + intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
                  | rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
        destruct Hx.
      + gres. reflexivity.
  Qed.
End SNL.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Theorem ref_strnlen : ltac2:(zQ "i42!h9!jc!hh8!iud!hk9!iv2!iv7!hv1!ive!l9!hg8!hge!jj5!jic!hq0!hv4!jk4!jjc!ita!kha!ki0!hvb!hi6!il4!ig2!ig8!ki7!hkf!kie!jo3!ik7!js5!kge!hu8!hq5!kj9&>0@1$1@1$0#k0@1$9@1$1@1$0#8&@3$5@1$0#5+aKv$3@2$6@1$0#5+a>3mem~0>1s@1$1@1$0#k0>2sp@1$1@1$0#k0>3buf@1$h7@1$1@1$0#8>1K$7>1n$7>3rom~0>4regs@2$d@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@5$i1^9^8^6^5^4>0@2$i2Z@2$h3@2$2@1$0#k0^9^6>0@3$4$h4@4$hc$h2^b@2$b@1$0#k0@2$a@2$2@1$0#k0^9+i0Ni0$ha>0@2$e+hkgo8@2$a@2$2@1$0#k0^a+i0>0@2$hb@2$e@2$h3@2$2@1$0#k0^c@1$i3@2$h6@1$1@1$0#8^a@2$a@2$2@1$0#k0^b+i0@2$e@2$2@1$0#k0^b@2$2@1$0#k0^c>0@1$hf^6>0@3$4@1$1@1$0#k0@2$8^8@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^7>0@3$4@1$1@1$0#k0@2$8^9@3$5@1$0#5+2Kv$3@2$6@1$0#5+2^e>0@3$4@1$1@1$0#k0@2$8^a~1^h0>0@3$4@1$1@1$0#k0@2$8^b@3$5@1$0#5+bKv$3@2$6@1$0#5+b@2$b@1$0#k0^d@2$h0@2$d@1$0#5@1$1@1$0#k0\5regs'@2$d@1$0#5@1$1@1$0#k0@2$h0~0\4mem'~0@2$c@3$hd$h2@5$h1?2fx^eKd@3$5@1$0#k0+uuuncKv$3@2$6@1$0#k0+uuunc@1$1@1$0#k0^h5^f@5$h1?2fx^2^d^1^f@2$c@2$i0^e^2@2$c@3$4@1$1@1$0#k0@2$8^2~1@2$b@1$0#k0^h1@3$he^h5^1@3$h5@2$f@1$1@1$0#k0$7@4$h9@1$1@1$0#k0$7@2$b@1$0#k0@2$a@2$2@1$0#k0^h3+i0+i0@1$h8@2$f@1$1@1$0#k0$7").
Proof.
  intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
  ndestruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
    as (r & RUN & KC & A10).
  exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
  split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
End FPX1.
