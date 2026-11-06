(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export Decode.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionhf7Z_to_bv37Corelib4Init5Logicmc2eq3h5LinuxProcessSemantics5Riscv7Preludeo55bvmapk14Somek14boolk14listk14truemc1I01Z3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypet67Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh5afetch_wordhh58is_ecallhh5dmachine_state3h5LinuxProcessSemantics5Riscv3Semhn77reg_get79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~hq43evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hu62MShu65MSsvchf2BVhf4BvWfk14prodk13nilk13nat3h5LinuxProcessSemanticsfLinuxProcessSem3Runil1capply_unmapsil1capply_writesil1bapply_zeros3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiqc7MemCopyiqc9mkEffectUo59bvmap_set79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~ive4nrethf6bv_add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jkb3mkRk14consk14pairhh5cwrite_to_mem4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Uaccessjqch0delivered_writeshfbbv_unsignedk14andb46Stdlib6ZArith6BinInt1Zkga3addkga3lebkga3ltbkga2lekga3powmc3andkga2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kl02wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib7SysStep~~~~~~kp08in_rangek14None79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ku14cellk16lengthku12CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lj48rw_cells37Corelib4Init3Natlnb3sub37Corelib4Init5Peanolp42le37Corelib5Lists7ListDeflqe5skipnhh58store_okkl07mem_invku1acells_sizekl05wr_atkga6of_natku1bcells_byteskl08bytes_atlj48ro_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~mid8errno_ofkga3subhf8bv_swrapkga3oppiqc9errno_retjkb3stk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma evt_ecall : ltac2:(zQ "h61!h9!jc!l9!m2!o0!qb!r3!ra!s1!s8!sf!t3!hgb!hkc!hla!hm6!hp9!htf!ii3!ii9!ij2!ij7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$8$c>1Q>0$fP>1R@2$5@1$0#5@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2pc$b>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1w@1$1@1$0#i0>0@3$4@1$2@1$1@1$0#i0@2$d^a@2$3@1$0#k0^6@2$6@1$1@1$0#i0^1>0@3$4$7@1$e^2$9>0@1^b@8$h3^a^9@2$3@1$0#k0^8@2$h0^a@3$h4@1$0#5+h1Kv$a@2$h5@1$0#5+h1^7^6^5^4@3$h1^d^c@7$h2^b^a@2$3@1$0#k0^9^8^7^6^5").
Proof.
  intros segs Q R F pc fc rv m ro w Hf He HQ.
  eapply evt_step; [|apply evt_done; exact HQ].
  split; [reflexivity|]. rewrite (step_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac step_ecall :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evt_ecall segs Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nret_MSsvc : ltac2:(zQ "h83!h9!jc!s1!ije!l9!ik5!qb!ikb!sf!o0!hm6!ind!iod!ipd!ita!iu5!iv2!jja!ii3!ii9!ij2!ij7!m2!jk2&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>1R@2$6@1$0#5@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2x8@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$4@1$1@1$0#k0>1m~0>2ro~0>1r@1$1@1$0#k0>2ws@1$2@2$3@1$1@1$0#k0@1$2@1$1@1$0#8>2zs~2>2us~2@3$9$a@2$h1@8$h3^c^b^a^9^8^7^6^5@6$f^4^3^2^1@1$5$e@1$5@2$3@1$1@1$0#k0$7@7$h2@5$h0@1$0#5@1$1@1$0#k0@3$h4@1$0#5+aKv$8@2$h5@1$0#5+a^4^c^b@3$h7@1$0#k0^a@2$h6@1$0#k0+4^8^7@2$c@2$d@2$b^6^1^2^3^5").
Proof. reflexivity. Qed.

Lemma mkR_set_a0 : ltac2:(zQ "90!h9!jc!jo7!sf!o0!qb!iv2!ij2!ij7>2x1@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>3x10@1$1@1$0#k0>3x11@1$1@1$0#k0>3x12@1$1@1$0#k0>3x13@1$1@1$0#k0>3x14@1$1@1$0#k0>3x15@1$1@1$0#k0>3x16@1$1@1$0#k0>3x17@1$1@1$0#k0>3x18@1$1@1$0#k0>3x19@1$1@1$0#k0>3x20@1$1@1$0#k0>3x21@1$1@1$0#k0>3x22@1$1@1$0#k0>3x23@1$1@1$0#k0>3x24@1$1@1$0#k0>3x25@1$1@1$0#k0>3x26@1$1@1$0#k0>3x27@1$1@1$0#k0>3x28@1$1@1$0#k0>3x29@1$1@1$0#k0>3x30@1$1@1$0#k0>3x31@1$1@1$0#k0>1v@1$1@1$0#k0@3$4@2$5@1$0#5@1$1@1$0#k0@5$6@1$0#5@1$1@1$0#k0@3$7@1$0#5+aKv$3@2$8@1$0#5+a^1@hf$2^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2@hf$2^i0^hf^he^hd^hc^hb^ha^h9^h8^1^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma apply_mem_none : ltac2:(zQ "a3!h9!jc!ik5!ije!l9!s1!o0!ind!iod!ipd&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>1m~0@3$6~0@2$8@2$9@2$7^1~2~2@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8^1").
Proof. reflexivity. Qed.

Lemma apply_mem_write : ltac2:(zQ "d4!h9!jc!s1!ije!ik5!l9!joe!jp5!o0!jpc!ind!iod!ipd&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$4~1&@2$3@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8@3$8~0@2$b@2$c@2$a^3~2~2@3$6~3@4$7@1$1@1$0#k0@1$2@1$1@1$0#8^2^1@1$4~3@3$9^3^2^1").
Proof. reflexivity. Qed.

Lemma apply_mem_delivered : ltac2:(zQ "c3!h9!jc!ik5!l9!ije!s1!o0!jpc!ind!iod!ipd!ju0&>0@1$1@1$0#k0@1$3@1$1@1$0#8&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>1m~0>1a@1$1@1$0#k0>2bs@1$5@1$1@1$0#8@3$6~0@2$9@2$a@2$8^3~2~2@2$b^2^1@3$7^3^2^1").
Proof. intros m a [|b bs]; reflexivity. Qed.

(* [comment removed for export] *)
Definition in_range : ltac2:(zQ "40!t3!ra!h9!jc>1a$0>1n$0>1x@1$3@1$2#k0$1") := ltac2:(zQ "80!h9!t3!jv5!kg3!ki2!ki9!kj0!jc\1a$1\1n$1\1x@1$7@1$0#k0@2$3@2$5^3@2$2@1$0#k0^1@2$6@2$2@1$0#k0^1@2$4^3^2").

Lemma apply_zeros_spec : ltac2:(zQ "h42!h9!jc!l9!kj7!kjd!ra!ije!kk4!t3!kka!m2!r3!joe!ik5!jp5!o0!ipd!koa!kse!ki2&@2$7@2$3Z^3@2$9^3@2$4+2+k0&@2$6@1$1@1$0#k0@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a$8>1n$8>1x@1$1@1$0#k0>0~0>0~0>0@2$3@2$h3^5^4@2$4+2+k0@3$f@1$2@1$1@1$0#8@3$h0^7@3$c~1@4$e@1$1@1$0#k0@1$1@1$0#k0@1$h1^6@2$a@1$0#k0^5@1$d~1^4M5\0$5@1$2@1$1@1$0#8@3$h2^6^5^4@2$b@1$1@1$0#8@2$a@1$0#8Z@1^7^4").
Proof.
  intros m a n x Ha Hn Han. cbn [apply_zeros zeros_cover existsb fst snd]. unfold in_range.
  rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma apply_unmaps_spec : ltac2:(zQ "h42!h9!jc!l9!kj7!kjd!ra!ije!kk4!t3!kka!kta!joe!ik5!jp5!o0!ind!koa!kse!ki2!m2&@2$7@2$3Z^3@2$9^3@2$4+2+k0&@2$6@1$1@1$0#k0@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a$8>1n$8>1x@1$1@1$0#k0>0~0>0~0>0@2$3@2$h2^5^4@2$4+2+k0@3$e@1$2@1$1@1$0#8@3$f^7@3$b~1@4$d@1$1@1$0#k0@1$1@1$0#k0@1$h0^6@2$h3@1$0#k0^5@1$c~1^4M5\0$5@1$2@1$1@1$0#8@3$h1^6^5^4@1$a@1$1@1$0#8@1^7^4").
Proof.
  intros m a n x Ha Hn Han. cbn [apply_unmaps zeros_cover existsb fst snd]. unfold in_range.
  rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.

Section MemEffects.
Variable segs : ltac2:(zQ "20!s1!hgb@1$0$1").

(* [comment removed for export] *)

Lemma rw_cells_CB_prefix_write : ltac2:(zQ "h10!h9!jc!lhd!li5!joe!lie!s1!ik5!lmf!ikb!l9!lod!lq8!ls5!t3!jpc!koa>1m>0@1$1@1$0#k0@1$a@1$1@1$0#8>1A$e>1n$9>4junk@1$6@1$1@1$0#8>2bs@1$6@1$1@1$0#8>0@4$8?4segs^5^4@3$4$2@2$5^3^2@1$7$2>0@2$c@2$3@1$1@1$0#8^2^4@4$8?4segs@3$f^7@1$h0^6^3^6@3$4$2@2$5@2$3@1$1@1$0#8^3^3@3$4$2@2$5@2$b^5@2$3@1$1@1$0#8^3@3$d@1$1@1$0#8@2$3@1$1@1$0#8^3^4@1$7$2").
Proof.
  intros m A n junk bs [[Hwf Hb] Hw] Hlen. cbn in Hwf. destruct Hwf as [Hj _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn. repeat split; try reflexivity. rewrite skipn_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (bytes_at_write_inside segs m A junk 0 bs Hb ltac:(lia) ltac:(cbn; lia)) as W.
    rewrite Z.add_0_r in W. unfold upd_bytes in W. cbn [firstn app Nat.add] in W. exact W.
  - cbn [cells_size csize]. cbn [cells_size csize] in Hw. replace (length bs + (n - length bs + 0))%nat with (n + 0)%nat by lia.
    apply wr_at_write. exact Hw.
Qed.

Lemma rw_cells_CB_store_ok : ltac2:(zQ "h10!h9!jc!ikb!lhd!ra!joe!s1!ik5!l9!s8!o0!lq8!t3!lse!lie!koa!lmf>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$c>1n$2>4junk@1$6@1$1@1$0#8>1k$2>0@4$h0?4segs^5^4@3$5$3@2$e^3^2@1$7$3>0@2$b^2^4@3$a$4@4$d?4segs^7@1$f^6^3$9").
Proof.
  intros m A n junk k [_ Hw] Hk. cbn [cells_size csize] in Hw.
  rewrite <- (Z.add_0_r A). apply (wr_at_store_ok segs m A (Z.of_nat (n + 0))); [exact Hw|lia|lia].
Qed.

Lemma mem_inv_syswrite : ltac2:(zQ "h00!h9!jc!s1!lhd!lta!joe!li5!ikb!ik5!l9!lq8!t3!jpc!lie!koa!lmf>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$b>1n$7>4junk@1$2@1$1@1$0#8>2bs@1$2@1$1@1$0#8>0@2$4?4segs^5>0@4$f?4segs^6^5@3$5$3@2$d^4^3@1$8$3>0@2$a@2$6@1$1@1$0#8^3^5@2$4?4segs@3$c^8@1$e^7^4").
Proof.
  intros. apply mem_inv_store; [assumption|]. eapply rw_cells_CB_store_ok; eauto.
Qed.

(* [comment removed for export] *)

Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : ltac2:(zQ "40!kk4!kj7!kka!kjd@2$0@2$1Z?1a@2$2?1a@2$3+2+k0").
Hypothesis Hn : ltac2:(zQ "40!kk4!kj7!kka!kjd@2$0@2$1Z?1n@2$2?1n@2$3+2+k0").
Hypothesis Han : ltac2:(zQ "30!ki2!kj7!kjd@2$1@2$0?1a?1n@2$2+2+k0").
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].

Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
  intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros x Hx. unfold wview in *. unfold m'. rewrite apply_zeros_spec by assumption.
  destruct (in_range a n x); [discriminate| exact Hx].
Qed.

Lemma bytes_at_zeros_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite zeros_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof. intros A k (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. apply wview_zeros_mono, H, Hi. Qed.

Lemma rw_cells_zeros_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
  - apply wr_at_zeros. exact Hw.
Qed.

Lemma ro_cells_zeros_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
  apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_zeros_mono; exact Hw|].
  unfold mrd in *. unfold m'. rewrite apply_zeros_spec by assumption.
  destruct (in_range a n (wa x)); [eexists; reflexivity|]. exists b. exact Hb.
Qed.

Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
  intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite zeros_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
  destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof. intros m0 H x Hx. apply wview_zeros_mono, H, Hx. Qed.

(* [comment removed for export] *)
Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
  intros Hinv Hro x b Hx. unfold m' in Hx. rewrite apply_zeros_spec in Hx by assumption.
  unfold in_range in Hx.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb] in Hx;
    try exact (Hinv _ _ Hx).
  apply Hro. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
  split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
  unfold mrd. rewrite zeros_inside. 2:{ rewrite wa_unsigned by lia. lia. }
  symmetry. apply nth_error_repeat. exact Hi.
Qed.

Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
  split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite zeros_inside; [discriminate|].
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
  split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_zeros_new.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_zeros_new.
Qed.

End Zeros.

(* [comment removed for export] *)

Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : ltac2:(zQ "40!kk4!kj7!kka!kjd@2$0@2$1Z?1a@2$2?1a@2$3+2+k0").
Hypothesis Hn : ltac2:(zQ "40!kk4!kj7!kka!kjd@2$0@2$1Z?1n@2$2?1n@2$3+2+k0").
Hypothesis Han : ltac2:(zQ "30!ki2!kj7!kjd@2$1@2$0?1a?1n@2$2+2+k0").
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].

Lemma unmaps_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m'. rewrite apply_unmaps_spec by assumption. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma bytes_at_unmaps_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_unmaps_other : forall A k,
  wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
  intros A k (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_unmaps_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
  - apply wr_at_unmaps_other; [exact Hw| exact Hd].
Qed.

Lemma ro_cells_unmaps_other : forall A cs,
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
  intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
  apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  assert (E : m' (wa x) = m (wa x)). { apply unmaps_outside. rewrite wa_unsigned by lia. lia. }
  split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
  intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite unmaps_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
  destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
  intros Hinv x b Hx. unfold m' in Hx. rewrite apply_unmaps_spec in Hx by assumption.
  destruct (in_range a n x); [discriminate|]. exact (Hinv _ _ Hx).
Qed.

(* [comment removed for export] *)
End Unmaps.

End MemEffects.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_wr_at : ltac2:(zQ "c0!s1!h9!t3!jc!l9!hgb!lhd!lu5!lv3!lmf!kj7!lvc>4segs@1$0$5>1m>0@1$3@1$1#k0@1$4@1$3@1$1#8>1A$2>2cs@1$0$6>1n$2>0@4$9^5^4^3^2>0@2$a^2@1$b@1$7^3@4$8^7^6^5^3").
Proof. intros segs m A cs n [_ (H0 & H1 & H)] Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma rw_cells_bytes_at : ltac2:(zQ "a0!s1!h9!jc!l9!t3!hgb!lhd!mg6!mh5!lmf>4segs@1$0$5>1m>0@1$2@1$1#k0@1$3@1$2@1$1#8>1A$4>2cs@1$0$6>0@4$9^4^3^2^1@4$8^5^4^3@1$7^2").
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma ro_cells_bytes_at : ltac2:(zQ "a0!s1!h9!jc!l9!t3!hgb!lhd!mg6!mh5!mi1>4segs@1$0$5>1m>0@1$2@1$1#k0@1$3@1$2@1$1#8>1A$4>2cs@1$0$6>0@4$9^4^3^2^1@4$8^5^4^3@1$7^2").
Proof. intros segs m A cs [_ H]. exact H. Qed.

(* [comment removed for export] *)
Ltac at_node_solve :=
  at_node_red; split_spine;
  first [ reflexivity | lia | assumption
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          end
        | idtac ].

(* [comment removed for export] *)
Ltac sys_mem_write :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Lemma apply_mem_zeros : ltac2:(zQ "b4!h9!jc!ije!ik5!joe!l9!ipd!s1!o0!ind!iod&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~1&@3$4~1^1~2>1m~0>1z~1@3$8~0@2$a@2$6@2$9^2~2~3@1$3@2$2@1$1@1$0#k0@1$7@1$1@1$0#8@2$6^2~3").
Proof. reflexivity. Qed.
Lemma apply_mem_unmaps : ltac2:(zQ "b5!h9!jc!ije!ik5!joe!l9!ind!s1!o0!iod!ipd&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~1&@3$4~1^1~2&@2$6^2~3>1m~0>1u~1@3$8~0@2$9@2$a~4~2@1$3@2$2@1$1@1$0#k0@1$7@1$1@1$0#8~4").
Proof. reflexivity. Qed.

Ltac transport_zeros segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros segs m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac sys_mem_zeros :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac transport_unmaps segs m a n Ha Hn Han :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2 H) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi H) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.

Ltac sys_mem_unmaps :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

(* [comment removed for export] *)
Ltac sys_nret :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).

(* [comment removed for export] *)
Definition sysret_val : ltac2:(zQ "20!h9!jc>1r@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!l9!t3!jc!mma!m2\1r@1$3@1$0#k0M1\1x@1$1$2@1$3@1$0#k0@1$4^1\1z$2@2$5@1$0#k0-1^1").
Definition sysret_errno : ltac2:(zQ "20!h9!jc>1r@1$1@1$0#k0>4errv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jc!l9!t3!mma!m2\1r@1$1@1$0#k0\4errv@1$1@1$0#k0M2\1x@1$2$3@1$1@1$0#k0@1$4^2\1e$3@2$5@1$0#k0^1^1").

Lemma errno_of_big : ltac2:(zQ "b0!h9!t3!kjd!mn6!jv5!r3!l9!o0!mma!kka!jc>1r@1$a@1$0#k0>0@2$9@2$3@2$2+2+k0+hgg0@2$4@1$0#k0^1@3$7@1$6$1@1$8^2@2$5$1@2$3@2$2+2+k0@2$4@1$0#k0^2").
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed.

(* [comment removed for export] *)
Lemma negw_errno : ltac2:(zQ "80!kjd!mn6!t3!kka!kk4!o0!h9!mnd>1u$2>0@2$4@2$3@2$1@2$0+2+k0+hgg0^1@2$3^1@2$0+2+k0@3$5$2@2$7@1$6#i0@2$1Z^2@2$1@2$0+2+k0^2").
Proof.
  intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : ltac2:(zQ "90!t3!kjd!kk4!o0!h9!kj7!kka!mo8!mnd>1z$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma unsigned_errno_ret : ltac2:(zQ "90!t3!kj7!kk4!o0!h9!mof!kjd!mn6!jv5>1e$0>0@2$2@2$1+1^1@2$1^1+vvf@3$3$0@2$8@1$4#k0@1$5^2@2$7@2$6+2+k0^2").
Proof. intros. rewrite errno_ret_unsigned by lia. reflexivity. Qed.

Lemma sextw_small : ltac2:(zQ "c0!h9!m2!kk4!o0!t3!ki2!kj7!kka!kjd!jc!mnd!jv5>1z$4>0@2$2@2$6Z^1@2$7^1@2$8+2+hf@3$3@1$9@1$0#k0@2$1@1$0#k0@2$a@1$0#i0@2$5@2$b@1$0#k0@2$1@1$0#k0^2Z@2$1@1$0#k0^2").
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_lo_nonneg : ltac2:(zQ "80!h9!t3!jc!s1!l9!hgb!mpc!kj7>4segs@1$3$5>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>2lo$1>2hi$1>0@4$6^4^3^2^1@2$7Z^3").
Proof. intros segs m lo hi (H & _). exact H. Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q ms,
  evt segs (fun ms' => impl segs atn t Q ms') ms -> impl segs atn t Q ms.
Proof. intros node segs atn R t Q ms H. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Ltac iprefix := apply impl_from_evt.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
