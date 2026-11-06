(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg RelSpec SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg Nodes FileSim AgentLib AgentNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned37Corelib4Init5Logickf2eq46Stdlib6ZArith6BinInt1Zm83addhf7Z_to_bvhf6bv_add37Corelib4Init9Datatypesp93natkf3and01Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBases0bword_to_natm82lem82ltm83powm86to_natp96optionp94Somep94list3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshiddmachine_statehid6ms_memhidcms_read_bytehid6ms_romhidh0word_to_le_bytes3h5LinuxProcessSemanticsfLinuxProcessSem5Statehqe8read_u6469OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hu83rdnhu87seg_romhqeeread_bytes_mapp94prodp96lengthhqe5ImpOkhqefcopy_iovecs_auxhqeaiov_import79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibWritev8WithSegs~~~~~~io19iov_arrayhqedgather_iovecsio18iov_bufs36Stdlib5Lists4Listiv06concatp94boolp94truehqefiovs_access_okbio1diov_ranges_okm86of_nat37Corelib4Init5Peanojk82lehqe9TASK_SIZEhqeh4copy_iovecs_accesseshqedimport_iovecshqeh6import_iovecs_accessesm83mulp94consp93nilp94pairhqeacap_iovecshqeaiovs_totalhqedSyscallEffecthqe6in_mem3h5LinuxProcessSemanticsfLinuxProcessSem5Monadkg57outcomehqe7FdEntry5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs9ReadWritekk98iovcnt32p93appp95falsekf2exkf3iff37Corelib5Lists7ListDefkq76firstnkq73mapkg52Okhqe9FdChannelhqe7MemCopyhqe5ModelhqecSyscallInputhqe7WriteEvhqe5eventhqe9fd_lookuphqeh3iov_prefix_accesseshqe5m_fdshqe9mkEffectUkk9bwritev_spec4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscalllm45w_is0hid6ms_gpr3h5LinuxProcessSemanticsfLinuxProcessSem3Runlqb9sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Specslu4csyscall_spec37Corelib4Init6Specifmi29proj1_siglqb5mkCfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~mkd8realizesmkd8wr_indexp94Nonehidems_svc_pendinghid8set_gpr0lqbh0advance_past_svchqe8m_haltedhqe9m_vm_lazymkd4TSetmkd5t_altmkd6t_emitkf1Ihf2BVhf4BvWfhu84getrhu84mksthidafetch_wordhid8is_ecall3h5LinuxProcessSemantics5Riscv7Preludenk85bvmaphu86regupdhu86v_addikq75skipn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypenp47Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma bv_add_Zform : ltac2:(zQ "70!h9!jc!k1!m3!o0!o6!p0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$6@1$0#k0^2^1@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma word_to_nat_Z : ltac2:(zQ "b0!r1!r7!m3!h9!rd!uf!vd!hg2!hg7!hgd!o6>1z$4>0@2$1@2$6Z^1@2$7^1@2$8+2+k0@3$2$0@1$5@2$a@1$3#k0^2@1$9^2").
Proof.
  intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

Lemma u64_roundtrip' : ltac2:(zQ "50!h9!jc!m3!o6!k1>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@1$0#k0@2$4@1$0#k0^1^1").
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_wall {SC : StepCfg} : forall segs c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  realizes segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  realizes segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs c ch bs K Hnb HK H. eapply rz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.
End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hi6!ns9@1$0$1").
Context {SC : StepCfg}.

Lemma read_u64_rdn : ltac2:(zQ "e0!h9!jc!hh6!m3!hhf!hi6!hm4!hn5!hnf!hof!hp9!htc!ii3!iia>2ms$6>1a@1$1@1$0#k0>1v@1$1@1$0#k0>0@3$3>0@1$1@1$0#k0@1$2@1$1@1$0#8@1$9^3@1$d?4segs>0@3$3@1$2@1$5@1$1@1$0#8@4$c?4segs@1$7^4^3N8@2$4@1$5@1$1@1$0#8@2$aN8^2@3$3@1$2@1$1@1$0#k0@2$b@1$8^5^4@2$4@1$1@1$0#k0^3").
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

Lemma read_bytes_map_rdn : ltac2:(zQ "e0!h9!jc!hi6!hh6!m3!hhf!uf!hm4!hn5!hnf!hof!ij5!ii3!iia>2ms$7>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$a^4@1$d?4segs>0@3$4@1$3@1$2@1$1@1$0#8@4$c?4segs@1$8^5^4@1$6^3@2$5@1$2@1$1@1$0#8^2@3$4@1$3@1$2@1$1@1$0#8@3$b@1$9^6^5^4@2$5@1$2@1$1@1$0#8^3").
Proof.
  intros ms a n bs Hrom H.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Lemma copy_iovecs_of_array : ltac2:(zQ "h01!h9!jc!ik7!m3!ike!hi6!hh6!hm4!hn5!hnf!hof!il7!im0!in3!is6!iia&@2$2@1$1@1$0#k0@1$1@1$0#k0>2ms$7>4iovs@1$5~0>3iov@1$1@1$0#k0>0@3$3>0@1$1@1$0#k0@1$6@1$1@1$0#8@1$a^3@1$f?4segs>0@3$e@1$8^4^2^3@3$3$d@3$c@1$9^5^3@2$4~0^4@1$b^4").
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  ndestruct Ha as (Hb & Hn & Hlt & Hr).
  cbn [length copy_iovecs_aux]. unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

Lemma gather_of_bufs : ltac2:(zQ "f0!h9!jc!hi6!hh6!m3!hhf!ik7!hm4!hn5!hnf!hof!it3!iu4!iia!jg3>2ms$7>4iovs@1$2@2$6@1$1@1$0#k0@1$1@1$0#k0>3bss@1$2@1$2@1$1@1$0#8>0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$a^3@1$d?4segs>0@3$c@1$8^4^3^2@3$4@1$3@1$2@1$1@1$0#8@2$b@1$9^5^4@2$5@1$2@1$1@1$0#8@2$e@1$1@1$0#8^3").
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_ranges_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_ranges_ok r
  end.

Lemma iovs_access_okb_of_ranges : ltac2:(zQ "90!h9!jc!jgd!hi6!ik7!jh4!m3!jhb!jie>4iovs@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>0@1$8^1@3$6$2@1$7^2$5").
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  fold (iovs_access_okb r). rewrite (access_okb_intro b n Hb), (IH Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_of_array : ltac2:(zQ "hd5!h9!jc!ik7!ike!m3!hnf!jjf!hi6!r7!jlc!o6!r1!hh6!hm4!hn5!hof!il7!jm2!jmf!jo8!jp9!in3!is6!jie!iia!o0!vd!jr4!k1&@2$2@1$1@1$0#k0@1$1@1$0#k0&@2$3~0^4&@2$3~0^7&@1$6~2&@2$a@1$0#k0~3>2ms$d>4iovs@1$7~0>3iov@1$1@1$0#k0>0@3$4>0@1$1@1$0#k0@1$c@1$1@1$0#8@1$f^3@1$h8?4segs>0@3$h6@1$e^4^2^3>0@2$8@2$9N2~1@2$9~1Nkg0>0@2$ha@2$h9@2$hc@1$0#k0^4@2$hb+h0@1$6@2$3~0^5$h1>0@1$h7^6@2$8@3$4$h5@3$h3@1$5^8^6~4@1$h0^7@3$4@1$7@2$2@1$1@1$0#k0$b@3$h4@1$5^8^6~4@3$h2@1$5^8^6~2").
Proof.
  intros ms iovs iov Hrom Harr Hlen Hiov Hrng.
  pose proof (u64_range iov) as Hi.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { rewrite word_to_nat_Z, Nat2Z.id by lia. reflexivity. }
  assert (E1 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 1) = false).
  { apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  assert (E0 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  assert (Emax : (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat (length iovs))))%Z = false).
  { apply Z.ltb_ge. unfold IOV_MAX. rewrite u64_lit; lia. }
  assert (Eacc : access_okb iov (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat (length iovs)))) = true).
  { unfold access_okb. rewrite u64_lit by lia. apply andb_true_iff. unfold TASK_SIZE in *. split; apply Z.leb_le; lia. }
  unfold import_iovecs, import_iovecs_accesses. rewrite E1, E0, Emax, Eacc. cbn [negb].
  rewrite Hwn, (copy_iovecs_of_array ms iovs iov Hrom Harr), (iovs_access_okb_of_ranges iovs Hrng).
  split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_of_array1 : ltac2:(zQ "ha2!h9!jc!ik7!r1!jra!js1!js7!m3!k1!hnf!jm2!o0!vd!o6!hi6!hh6!r7!hm4!hn5!hof!il7!jo8!jp9!in3!is6!iia&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0>2ms$h1>2b1@1$1@1$0#k0>2n1@1$1@1$0#k0>3iov@1$1@1$0#k0>0@3$7>0@1$1@1$0#k0@1$f@1$1@1$0#8@1$h3^4@1$h9?4segs>0@3$h8@1$h2^5^2@3$4~0@4$6@1$1@1$0#k0@1$1@1$0#k0^4^3~1>0@2$c@2$b@2$8@1$0#k0^3+h0$a>0@2$c@2$b@2$8@1$0#k0^6@2$8@1$0#k0^5$a@2$h0@3$7$h7@3$h5@1$9^8^5@2$d@1$0#k0+1@1$h4@3$4~0@4$6@1$1@1$0#k0@1$1@1$0#k0^7^6~1@3$7@1$e@2$2@1$1@1$0#k0$3@3$h6@1$9^8^5@2$d@1$0#k0+1@3$4@2$2@1$1@1$0#k0$3@4$6@1$1@1$0#k0$3^5Nh0@1$5@2$2@1$1@1$0#k0$3").
Proof.
  (intros ms b1 n1 iov Hrom nd_i1 Hiov Hrng; ndestruct nd_i1 as (Hb & Hn & Hlt & _)).
  pose proof (u64_range iov) as Hi. pose proof (u64_range b1). pose proof (u64_range n1).
  assert (Eacc : access_okb iov 16 = true).
  { unfold access_okb. apply andb_true_iff. unfold TASK_SIZE in *. split; apply Z.leb_le; lia. }
  assert (Eacc2 : access_okb b1 (Z.min (bv_unsigned n1) MAX_RW_COUNT) = true).
  { unfold access_okb. apply andb_true_iff. unfold TASK_SIZE, MAX_RW_COUNT in *. split; apply Z.leb_le; lia. }
  unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Eacc. cbn [negb].
  unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b1 Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n1 Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt), Eacc2. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cap_iovecs_id_30 : ltac2:(zQ "92!h9!jc!hi6!ik7!m3!jse!jtc!vd!hg7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4iovs~1>0@2$7@1$6^1@2$8+2+he@3$4~1@1$5^2^2").
Proof.
  intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
  unfold MAX_RW_COUNT. lia.
Qed.

Lemma writev_chan_outcome30 : ltac2:(zQ "if2!h9!jc!hi6!ik7!m3!r1!js1!jua!jvb!hhf!ike!hh6!r7!jlc!kj3!kje!ko2!vd!jjf!koe!jgd!kp4!kpc!kq1!kre!ks8!ksf!kt5!il7!ku2!kud!kv6!lg6!lh1!lha!it3!jo8!jp9!in3!li7!jtc!ljf!lk8!ll5!lp8!hg7!o6&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$6~0>2fd@1$1@1$0#k0>3iov@1$1@1$0#k0>6iovcnt@1$1@1$0#k0>1i$hf>1m$he>1o@1$e$7>2ch@1$1@1$0#k0>4iovs@1$2~0>2bs@1$2@1$1@1$0#8>0@3$4@1$b$f@2$i2@1$i9^5^9@2$9$f@1$hb^3>0@3$4$h4@1$ic^4$h5>0@3$4$i6@3$i4@1$8^8^a@1$h0^9@1$hc^4>0@2$h1@1$i8^5@2$id+2+he>0@3$4@1$b@1$2@1$1@1$0#8@2$i3@1$8^a^6@2$9@1$2@1$1@1$0#8^5>0@2$h1+1@1$h2@2$a@1$1@1$0#8^6=2CA@1$2@2$3@1$1@1$0#k0$5@3$i5@1$8^c^e@1$h0^d@2$h7@6$ib^h0^f^e^d^c^b@2$h6$5\1k$5@2$c@2$c@2$dN1^1@2$d^1@2$a@1$1@1$0#8^9@3$4@1$e$7^c@4$ha$7@6$ia@2$ie@1$0#k0@1$h2^1@1$6@2$3@1$1@1$0#k0@1$2@1$1@1$0#8~1~1@1$6$hd@3$h3@2$3@1$1@1$0#k0$5^2@2$i7^a^1^d@4$h9@1$1@1$0#8$i1@1$i0^b@3$h8@1$1@1$0#8^1^9").
Proof.
  intros fd iov iovcnt i m o ch iovs bs Hfd Hch Himp Htot Hg Hbs1.
  cbv zeta.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  pose proof (cap_iovecs_id_30 iovs Htot) as Hcap.
  assert (Herrk : forall k, (k <= length bs)%nat ->
            addr_is_error_b (len_word (firstn k bs)) = false).
  { intros k Hk. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (rewrite firstn_length_le by lia; unfold two_pow_64; lia).
    rewrite firstn_length_le by lia. lia. }
  unfold writev_spec. rewrite bind_input_get_model. rewrite Hfd, Hch. cbv iota.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ds <- choose (fun ds : list byte =>
                       (1 <= Z.of_nat (length ds))%Z
                       /\ (Z.of_nat (length ds) < two_pow_64)%Z
                       /\ addr_is_error_b (len_word ds) = false
                       /\ ds = firstn (length ds) bs) ;;
        emit (map (WriteEv ch) ds) ;;
        record_copyins (iov_prefix_accesses (cap_iovecs iovs) (length ds))
          (ret_only (len_word ds)))%sys i m o).
  { rewrite Himp. cbv zeta. unfold writev_gathered.
    rewrite Hcap, (gather_prefix_full _ _ _ Hg).
    replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (addr_is_error_b (len_word bs)) with false
      by (symmetry; rewrite <- (firstn_all bs); rewrite (Herrk (length bs)) by lia; reflexivity).
    reflexivity. }
  rewrite Hcap. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
      exists (length ds); rewrite <- Hds;
      assert (Hk : (length ds <= length bs)%nat)
        by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
    end.
    split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
  - (intros nd_i2; ndestruct nd_i2 as (k & Hk & ->)).
    assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
    neexists 4. split.
    + neexists 4. split.
      * exists (firstn k bs). split; [|reflexivity].
        rewrite Hlk. split; [lia|]. split; [unfold two_pow_64 in *; lia|].
        split; [apply Herrk; lia|reflexivity].
      * split; [|reflexivity]. neexists 4. split; [reflexivity|]. split; [|reflexivity].
        neexists 4. split; [reflexivity|]. split; reflexivity.
    + rewrite Hlk, !app_nil_r. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma writev_outcome : ltac2:(zQ "j63!h9!jc!ik7!m3!ike!o6!hi6!r7!jjf!r1!js1!jlc!rd!lq1!jua!vd!hh6!kj3!hn5!kje!hg2!hg7!k1!hhf!koe!kpc!kq1!kre!ks8!ksf!hm4!hnf!hof!lt7!mh2!kt5!ku2!kud!jm2!lg6!lh1!lha!jp9!li7!jtc!ljf!lk8!is6!iu4!jie!iia!jg3!o0!jr4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@2$4~0^9&@1$a~0>2ms$he>2x8@1$1@1$0#k0>5model$i5>2fd$c>3iov@1$1@1$0#k0>4iovs@1$6~0>3bss@1$6@1$6@1$1@1$0#8>0@3$3>0@1$1@1$0#k0@1$h0@1$1@1$0#8@1$i0^7@1$j2?4segs>0@3$3@1$h0$h3@2$i9@1$id^6@2$5@1$0#k0^5@2$h7$h3@1$i3@2$5@1$0#k0^5>0@2$7@2$h4Z^6@2$h4^6@2$h5+2+hf>0@3$3$c@2$h6@1$0#k0^9+k2>0@3$3@1$1@1$0#k0@2$d^bN0@2$5@1$0#k0^8>0@3$3@1$1@1$0#k0@2$d^cN1^8>0@3$3@1$1@1$0#k0@2$d^dN2@2$5@1$0#k0@1$8@2$4~0^8>0@2$7@2$bN1~1@2$b~1Nkg0>0@3$if@1$h2^f^b^a>0@3$j0@1$h2^h0^b^a>0@2$f@2$j4@2$h6@1$0#k0^d@2$j5+h0@1$8@2$4~0^c$i6>0@1$j1^d=2bs@1$6@1$1@1$0#8@2$j3@1$1@1$0#8^d=3tot$c@1$ic^f>0@2$f+1^1>0@2$f^2@2$h5+2+he=2CA@1$6@2$2@1$1@1$0#k0$9@3$ia@1$hf^h7^h3@2$5@1$0#k0@1$8@2$4~0^h2@2$7@3$3$c@1$8@2$4@1$1@1$0#8^5^4>1o@1$h1$e@2$ha@3$i2@3$i1?4segs^h9^h8^h7^1@2$h9$9\1k$9@2$7@2$7@2$bN1^1@2$b^1@2$4@1$1@1$0#8^7@3$3@1$h1$e^2@4$hd$e@6$ie@2$5@1$0#k0@1$8^1@1$a@2$2@1$1@1$0#k0@1$6@1$1@1$0#8~2~2@1$a$i4@3$h8@2$2@1$1@1$0#k0$9^3@2$ib^h5^1^h8@4$hc@1$1@1$0#8$i8@1$i7@2$5@1$0#k0^h7@3$hb@1$1@1$0#8^1^7").
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Hiov Hrng bs tot Ht1 Ht30 CA.
  pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs).
  { destruct iovs as [|[b1 n1] [|p r]]; [cbn in Hcnt; lia | |].
    - cbn [length Z.of_nat Pos.of_succ_nat]. destruct Hrng as [Hr1 _].
      exact (proj1 (import_iovecs_of_array1 ms b1 n1 iov Hrom Harr ltac:(cbn [length] in Hiov; lia) Hr1)).
    - apply (proj1 (import_iovecs_of_array ms _ iov Hrom Harr ltac:(cbn [length] in *; lia) Hiov Hrng)). }
  intros o.
  rewrite (syscall_spec_66 (sys_input segs ms x8) model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  subst CA. change (ms_read_byte ms) with (in_mem (sys_input segs ms x8)).
  replace (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (Z_to_bv 64 (Z.of_nat (length iovs))))
    with (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs)))))
    by (rewrite Hcnt32; reflexivity).
  apply (writev_chan_outcome30 _ _ _ _ model o (Z_to_bv 64 fd) iovs bs Hfd).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - rewrite Hcnt32, in_mem_si. exact Himp.
  - exact Ht30.
  - rewrite in_mem_si. exact Hg.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma rz_writev_pending : ltac2:(zQ "j66!h9!jc!m3!jlc!ike!ik7!r1!o6!hi6!hh6!r7!lq1!vd!jjf!hhf!mj7!rd!hn5!mk4!kje!jtc!mo8!mp4!hg2!hg7!k1!mq0!js1!kre!ks8!hm4!hof!mq7!mr9!ms5!kt5!kud!jm2!lg6!lh1!lha!ljf!mta!mu6!is6!iu4!jie!iia!mv3!mvb!ng4!jg3!o0!jr4&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$8~0&@2$4~0^d&@2$a@2$3N1^1@2$3^1@2$4@1$1@1$0#8^6&\1n$6~3&@3$f$6~4^1>2ms$he>2x8@1$1@1$0#k0>5model$i4>2fd$h0>3iov@1$1@1$0#k0>4iovs~1>3bss@1$8@1$8@1$1@1$0#8>1T>0$6$j0>0@3$2>0@1$1@1$0#k0@1$9@1$1@1$0#8@1$hf^8@1$if?4segs>0@3$2@1$9@1$1@1$0#k0@1$ia^7@1$ha@1$1@1$0#k0>0@3$2~1@1$ib^8@1$hb~0>0@3$2@1$9@1$1@1$0#k0@1$i0^b@2$e@1$1@1$0#k0^a>0@3$2@1$9$h3@2$i8@1$i9^a@2$7@1$0#k0^9@2$e$h3@1$i3@2$7@1$0#k0^9>0@2$a@2$h7Z^a@2$h7^a@2$h8+2+hf>0@3$2$h0@2$h9@1$0#k0^d+k2>0@3$2@1$1@1$0#k0@2$b^fN0@2$7@1$0#k0^c>0@3$2@1$1@1$0#k0@2$b^h0N1^c>0@3$2@1$1@1$0#k0@2$b^h1N2@2$7@1$0#k0@1$d@2$4~0^c>0@2$a@2$3N1~2@2$3~2Nkg0>0@3$ic@1$h1^h3^f^e>0@3$id@1$h1^h4^f^e>0@2$c@2$j4@2$h9@1$0#k0^h1@2$j5+h0@1$d@2$4~0^h0$i5>0@1$ie^h1=2bs@1$8@1$1@1$0#8@2$j3@1$1@1$0#8^h1>0@2$c+1@1$h4^h3>0@2$c@1$h4^h4@2$h8+2+he>0>1k$6>0@2$3N1^1>0@2$3^2@2$4@1$1@1$0#8^5@4$h5?4segs?2SC@2$h2@1$i2@2$i1^hd@2$7@1$0#k0@1$d^3^hb@1^h6^3@4$h5?4segs?2SC@2$h2^hb^h9@2$j1@1$h6^4\1i@1$h6^4@2$j2@4$hd@1$1@1$0#8$i7@1$i6@2$7@1$0#k0^h9@3$hc@1$1@1$0#8~5^5@1^h5~5").
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Hiov Hrng bs Ht1 Ht30 Hk.
  destruct (writev_outcome ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Hiov Hrng Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (rz_node segs (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hnode : node_ok segs (mkCfg ms model) (wr_index bs)
                    (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) model)).
  { apply (node_family segs ms model x8 (wr_index bs) effs (fun _ => model)
             (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) _ Hh Hsvc Hchk).
    - intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
    - (intros o nd_i3; ndestruct nd_i3 as (k & Hk' & ->)). exists (exist _ k Hk'). reflexivity.
    - intros i0. apply not_spurious_none. rewrite in_sysno_si, Hno. apply injected_arm_none_66.
    - intros _; exact Hh.
    - intros _; exact Hlazy. }
  destruct Hnode as [Hn1 Hn2]. split.
  - intros i. rewrite Enx. apply Hn1.
  - intros e st Hss. ndestruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2 : ltac2:(zQ "j99!h9!jc!hi6!m3!k1!hh6!o6!hhf!o0!koe!r1!jlc!ii3!nge!vd!nh2!nh7!hp9!nhe!ike!r7!jm2!ik7!mj7!uf!mk4!kje!ni6!iia!mo8!mp4!hg2!hg7!mq0!jgd!js1!jh4!kre!ks8!rd!nie!njc!kt5!kud!lg6!lh1!lha!ljf!mta!mu6!nme!nn7!no1!mv3!mvb!ng4!jjf&@2$h6@1$1@1$0#k0@1$1@1$0#k0&@3$f@1$0#5+aKv$d@2$h0@1$0#5+a&@2$7@1$2@1$1@1$0#8@2$h1N8^h1&@1$he@3$9@1$1@1$0#8^h9^h8&@2$h3@1$1@1$0#8@3$9@1$1@1$0#8^hb^ha&@2$b^1~4&@2$h4@2$bN1^1~5&\1n$a~6&@3$h7$a~7^1>4regs@2$j2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>5model$ib>1w@1$1@1$0#i0>2fd$i7>3iov@1$1@1$0#k0>2b1@1$1@1$0#k0>2n1@1$1@1$0#k0>2b2@1$1@1$0#k0>2n2@1$1@1$0#k0>3bs1@1$2@1$1@1$0#8>3bs2@1$2@1$1@1$0#8>1T>0$a$j5>0@3$3@1$5@1$1@1$0#i0@2$i8?4segs^d@2$7@1$1@1$0#i0^a>0@3$3$i2@1$i9^b$i4>0@3$3@1$5@1$1@1$0#k0@1$j0^d@1$i1@1$1@1$0#k0>0@3$3@1$2~0@1$j1^e@1$i3~0>0@3$3@1$5$ha@2$ie@1$if^f@2$6@1$0#k0^d@2$7$ha@1$ia@2$6@1$0#k0^d>0@2$h4@2$hfZ^e@2$hf^e@2$i0+2+hf>0@3$3@1$1@1$0#k0@2$h2^h4@3$f@1$0#5+h1Kv$d@2$h0@1$0#5+h1@2$6@1$0#k0+k2>0@3$3@1$1@1$0#k0@2$h2^h5~1@2$6@1$0#k0^h0>0@3$3@1$1@1$0#k0@2$h2^h6@3$f@1$0#5+bKv$d@2$h0@1$0#5+b^h0>0@3$3@1$1@1$0#k0@2$h2^h7@3$f@1$0#5+cKv$d@2$h0@1$0#5+c@2$6@1$0#k0+2>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^h6^h2N8~2>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^h7@2$6@1$0#k0@2$8@2$4@1$0#k0^h3+8N8~2>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^h8@2$6@1$0#k0@2$8@2$4@1$0#k0^h4+h0N8~2>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^h9@2$6@1$0#k0@2$8@2$4@1$0#k0^h5+h8N8~2>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^ha^h5@1$h8^h4@2$7@1$2@1$1@1$0#8^h1>0@3$3@1$5@1$2@1$1@1$0#8@4$c?4segs^hb^h4@1$h8^h3@2$7@1$2@1$1@1$0#8^h1>0@2$e@2$8@2$4@1$0#k0^h8+i0$h5>0@2$e@2$8@2$4@1$0#k0^h8@2$4@1$0#k0^h7$h5>0@2$e@2$8@2$4@1$0#k0^h7@2$4@1$0#k0^h6$h5>0@2$e+1@2$8@2$4@1$0#k0^h9@2$4@1$0#k0^h7>0@2$e@2$8@2$4@1$0#k0^ha@2$4@1$0#k0^h8@2$i0+2+he>0>1k$a>0@2$bN1^1>0@2$b^2@2$h3@1$1@1$0#8@3$9@1$1@1$0#8^ha^h9@4$hd?4segs?2SC@2$h9@5$hb?2fx@3$j3^i6~1@2$6@1$0#k0@1$j8^3@2$j4^i5+4^i4@1$hc?4segs^i3@1^h9^3@4$hd?4segs?2SC@2$h9@5$hb?2fx^i4^i3^i2@1$hc?4segs^i1@2$j6~3\1i~3@2$j7@4$i6@1$1@1$0#8$id@1$ic@2$6@1$0#k0^i0@3$i5@1$1@1$0#8~8@3$9@1$1@1$0#8^ha^h9@1^h8~8").
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hr1 Hr2 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
    | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev1 : ltac2:(zQ "j86!h9!jc!m3!hi6!o6!hh6!r1!jlc!k1!hhf!nge!nh2!nh7!nhe!vd!ike!r7!ii3!o0!ik7!mj7!hp9!mk4!kje!jm2!ni6!iia!mo8!mp4!hg2!hg7!mq0!jgd!js1!jh4!kre!ks8!rd!uf!nie!njc!kt5!kud!lg6!lh1!lha!ljf!mta!mu6!nme!nn7!no1!mv3!mvb!ng4!jjf&@2$h3@1$1@1$0#k0@1$1@1$0#k0&@3$b@1$0#5+aKv$a@2$c@1$0#5+a&@2$9@1$3@1$1@1$0#8@2$h5N8^e&@2$h0@2$7N1^1@2$7^1@2$f@1$1@1$0#8^h6&\1n$6~3&@3$h4$6~4^1>4regs@2$j1@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>5model$ia>1w@1$1@1$0#i0>2fd$i5>3iov@1$1@1$0#k0>2b1@1$1@1$0#k0>2n1@1$1@1$0#k0>3bs1@1$3@1$1@1$0#8>1T>0$6$j4>0@3$2@1$5@1$1@1$0#i0@2$i7?4segs^a@2$9@1$1@1$0#i0^7>0@3$2$i0@1$i8^8$i2>0@3$2@1$5@1$1@1$0#k0@1$if^a@1$hf@1$1@1$0#k0>0@3$2@1$3~0@1$j0^b@1$i1~0>0@3$2@1$5$h7@2$id@1$ie^c@2$4@1$0#k0^a@2$9$h7@1$i9@2$4@1$0#k0^a>0@2$h0@2$hdZ^b@2$hd^b@2$he+2+hf>0@3$2@1$1@1$0#k0@2$d^h1@3$b@1$0#5+h1Kv$a@2$c@1$0#5+h1@2$4@1$0#k0+k2>0@3$2@1$1@1$0#k0@2$d^h2~1@2$4@1$0#k0^d>0@3$2@1$1@1$0#k0@2$d^h3@3$b@1$0#5+bKv$a@2$c@1$0#5+b^d>0@3$2@1$1@1$0#k0@2$d^h4@3$b@1$0#5+cKv$a@2$c@1$0#5+c@2$4@1$0#k0+1>0@3$2@1$5@1$3@1$1@1$0#8@4$h1?4segs^h3^fN8~2>0@3$2@1$5@1$3@1$1@1$0#8@4$h1?4segs^h4@2$4@1$0#k0@2$h2@2$8@1$0#k0^h0+8N8~2>0@3$2@1$5@1$3@1$1@1$0#8@4$h1?4segs^h5^h0@1$i6^f@2$9@1$3@1$1@1$0#8^e>0@2$e@2$h2@2$8@1$0#k0^h2+h0$h8>0@2$e@2$h2@2$8@1$0#k0^h2@2$8@1$0#k0^h1$h8>0@2$e+1@2$8@1$0#k0^h2>0@2$e@2$8@1$0#k0^h3@2$he+2+he>0>1k$6>0@2$7N1^1>0@2$7^2@2$f@1$1@1$0#8^h5@4$hb?4segs?2SC@2$h6@5$h9?2fx@3$j2^hf~1@2$4@1$0#k0@1$j7^3@2$j3^he+4^hd@1$ha?4segs^hc@1^h5^3@4$hb?4segs?2SC@2$h6@5$h9?2fx^hd^hc^hb@1$ha?4segs^ha@2$j5@1$hc^h4\1i@1$hc^h4@2$j6@4$i4@1$1@1$0#8$ic@1$ib@2$4@1$0#k0^h9@3$i3@1$1@1$0#8~5^h5@1^h4~5").
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiov Hr1 Ht1 Ht30 Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
    | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma rz_writev2_wall : ltac2:(zQ "j63!h9!jc!hi6!m3!k1!o6!hh6!hhf!o0!ii3!nge!vd!nh2!nh7!hp9!nhe!koe!jm2!lh1!js1!ik7!jlc!ks8!uf!mk4!kje!lg6!ni6!iia!mo8!ng4!hg2!hg7!mq0!jgd!ike!r1!jh4!r7!nob!rd!nie!njc!kt5!kud!lha!ljf!mta!mu6!nme!nn7!no1!mv3!jjf&@2$h4@1$1@1$0#k0@1$1@1$0#k0&@3$c@1$0#5+aKv$a@2$d@1$0#5+a&@2$7@1$2@1$1@1$0#8@2$eN8^h1>4regs@2$j1@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$6@1$1@1$0#8>5model$ic>1w@1$1@1$0#i0>2fd$i8>3iov@1$1@1$0#k0>2b1@1$1@1$0#k0>2n1@1$1@1$0#k0>2b2@1$1@1$0#k0>2n2@1$1@1$0#k0>3bs1@1$2@1$1@1$0#8>3bs2@1$2@1$1@1$0#8>1K$j4>0@3$3@1$6@1$1@1$0#i0@2$i9?4segs^d@2$7@1$1@1$0#i0^a>0@3$3$i2@1$ia^b$i5>0@3$3@1$6@1$1@1$0#k0@1$if^d@1$i1@1$1@1$0#k0>0@3$3@1$2~0@1$j0^e@1$h3~0>0@3$3@1$6$h9@2$id@1$ie^f@2$5@1$0#k0^d@2$7$h9@1$ib@2$5@1$0#k0^d>0@2$i6@2$hfZ^e@2$hf^e@2$i0+2+hf>0@3$3@1$1@1$0#k0@2$f^h4@3$c@1$0#5+h1Kv$a@2$d@1$0#5+h1@2$5@1$0#k0+k2>0@3$3@1$1@1$0#k0@2$f^h5~1@2$5@1$0#k0^h0>0@3$3@1$1@1$0#k0@2$f^h6@3$c@1$0#5+bKv$a@2$d@1$0#5+b^h0>0@3$3@1$1@1$0#k0@2$f^h7@3$c@1$0#5+cKv$a@2$d@1$0#5+c@2$5@1$0#k0+2>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^h6^h2N8~2>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^h7@2$5@1$0#k0@2$8@2$4@1$0#k0^h3+8N8~2>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^h8@2$5@1$0#k0@2$8@2$4@1$0#k0^h4+h0N8~2>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^h9@2$5@1$0#k0@2$8@2$4@1$0#k0^h5+h8N8~2>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^ha^h5@1$h7^h4@2$7@1$2@1$1@1$0#8^h1>0@3$3@1$6@1$2@1$1@1$0#8@4$9?4segs^hb^h4@1$h7^h3@2$7@1$2@1$1@1$0#8^h1>0@2$b@2$8@2$4@1$0#k0^h8+i0$h1>0@2$b@2$8@2$4@1$0#k0^h8@2$4@1$0#k0^h7$h1>0@2$b@2$8@2$4@1$0#k0^h7@2$4@1$0#k0^h6$h1>0@2$b+1@2$8@2$4@1$0#k0^h9@2$4@1$0#k0^h7>0@2$b@2$8@2$4@1$0#k0^ha@2$4@1$0#k0^h8@2$i0+2+he>0@1^h6@1$h3$h2>0>1k$i4>0@2$h5N1^1>0@2$h5^2@2$i3@1$1@1$0#8@3$h0@1$1@1$0#8^hb^ha@4$hd?4segs?2SC@2$h8@5$hb?2fx@3$j2^i7~1@2$5@1$0#k0@1$j5^3@2$j3^i6+4^i5@1$hc?4segs^i4@2$he@4$h6@1$1@1$0#8$h2@1$ha@2$5@1$0#k0^i2@3$i7@1$1@1$0#8^3@3$h0@1$1@1$0#8^hc^hb^ha@4$hd?4segs?2SC@2$h8@5$hb?2fx^i5^i4^i3@1$hc?4segs^i2@2$he@4$h6@1$1@1$0#8$h2@1$ha@2$5@1$0#k0^i0@3$h0@1$1@1$0#8^ha^h9^h8").
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hr1 Hr2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma rz_writev1_wall : ltac2:(zQ "j53!h9!jc!m3!o6!hi6!hh6!k1!hhf!nge!nh2!nh7!nhe!vd!lh1!ii3!o0!js1!ik7!jlc!ks8!hp9!mk4!kje!jm2!lg6!ni6!iia!mo8!ng4!hg2!hg7!mq0!jgd!ike!r1!jh4!r7!nob!rd!uf!nie!njc!kt5!kud!lha!ljf!mta!mu6!nme!nn7!no1!mv3!jjf&@2$h1@1$1@1$0#k0@1$1@1$0#k0&@3$9@1$0#5+aKv$8@2$a@1$0#5+a&@2$7@1$4@1$1@1$0#8@2$h4N8^e>4regs@2$j0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>5model$ib>1w@1$1@1$0#i0>2fd$i6>3iov@1$1@1$0#k0>2b1@1$1@1$0#k0>2n1@1$1@1$0#k0>3bs1@1$4@1$1@1$0#8>1K$j3>0@3$2@1$5@1$1@1$0#i0@2$i8?4segs^a@2$7@1$1@1$0#i0^7>0@3$2$i0@1$i9^8$i3>0@3$2@1$5@1$1@1$0#k0@1$ie^a@1$hf@1$1@1$0#k0>0@3$2@1$4~0@1$if^b@1$h0~0>0@3$2@1$5$h6@2$ic@1$id^c@2$3@1$0#k0^a@2$7$h6@1$ia@2$3@1$0#k0^a>0@2$i4@2$hdZ^b@2$hd^b@2$he+2+hf>0@3$2@1$1@1$0#k0@2$b^h1@3$9@1$0#5+h1Kv$8@2$a@1$0#5+h1@2$3@1$0#k0+k2>0@3$2@1$1@1$0#k0@2$b^h2~1@2$3@1$0#k0^d>0@3$2@1$1@1$0#k0@2$b^h3@3$9@1$0#5+bKv$8@2$a@1$0#5+b^d>0@3$2@1$1@1$0#k0@2$b^h4@3$9@1$0#5+cKv$8@2$a@1$0#5+c@2$3@1$0#k0+1>0@3$2@1$5@1$4@1$1@1$0#8@4$e?4segs^h3^fN8~2>0@3$2@1$5@1$4@1$1@1$0#8@4$e?4segs^h4@2$3@1$0#k0@2$f@2$6@1$0#k0^h0+8N8~2>0@3$2@1$5@1$4@1$1@1$0#8@4$e?4segs^h5^h0@1$i7^f@2$7@1$4@1$1@1$0#8^e>0@2$c@2$f@2$6@1$0#k0^h2+h0$h7>0@2$c@2$f@2$6@1$0#k0^h2@2$6@1$0#k0^h1$h7>0@2$c+1@2$6@1$0#k0^h2>0@2$c@2$6@1$0#k0^h3@2$he+2+he>0@1^h2@1$h0$d>0>1k$i2>0@2$h2N1^1>0@2$h2^2@2$i1@1$1@1$0#8^h6@4$hb?4segs?2SC@2$h5@5$h9?2fx@3$j1^i0~1@2$3@1$0#k0@1$j4^3@2$j2^hf+4^he@1$ha?4segs^hd@2$hc@4$h3@1$1@1$0#8$d@1$h8@2$3@1$0#k0^hb@3$i5@1$1@1$0#8^3^h7^h6@4$hb?4segs?2SC@2$h5@5$h9?2fx^he^hd^hc@1$ha?4segs^hb@2$hc@4$h3@1$1@1$0#8$d@1$h8@2$3@1$0#k0^h9^h5^h4").
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiov Hr1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_writev1_zero : ltac2:(zQ "ib2!h9!jc!m3!o6!hh6!hi6!nge!nh2!nh7!hhf!nhe!k1!ik7!hp9!mk4!kje!jm2!ni6!ii3!iia!mo8!o0!vd!hg2!mq0!jgd!js1!jh4!r7!rd!nie!njc!kt5!kud!lha!ljf!mta!mu6!nme!nn7!no1!mv3!hg7&@2$c@1$1@1$0#k0@1$1@1$0#k0&@3$7@1$0#5+aKv$6@2$8@1$0#5+a>4regs@2$i6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>5model$i1>1w@1$1@1$0#i0>2fd$hd>3iov@1$1@1$0#k0>2b1@1$1@1$0#k0>1K$i9>0@3$2@1$4@1$1@1$0#i0@2$he?4segs^8@2$9@1$1@1$0#i0^5>0@3$2$h9@1$hf^6$hb>0@3$2@1$4@1$1@1$0#k0@1$i4^8@1$h8@1$1@1$0#k0>0@3$2@1$5~0@1$i5^9@1$ha~0>0@3$2@1$4$f@2$i2@1$i3^a@2$3@1$0#k0^8@2$9$f@1$i0@2$3@1$0#k0^8>0@2$hc@2$h7Z^9@2$h7^9@2$ia+2+hf>0@3$2@1$1@1$0#k0@2$a^f@3$7@1$0#5+h1Kv$6@2$8@1$0#5+h1@2$3@1$0#k0+k2>0@3$2@1$1@1$0#k0@2$a^h0~1@2$3@1$0#k0^b>0@3$2@1$1@1$0#k0@2$a^h1@3$7@1$0#5+bKv$6@2$8@1$0#5+b^b>0@3$2@1$1@1$0#k0@2$a^h2@3$7@1$0#5+cKv$6@2$8@1$0#5+c@2$3@1$0#k0+1>0@3$2@1$4@1$5@1$1@1$0#8@4$h2?4segs^h1^dN8@2$9@1$5@1$1@1$0#8@2$dN8^c>0@3$2@1$4@1$5@1$1@1$0#8@4$h2?4segs^h2@2$3@1$0#k0@2$h5@2$b@1$0#k0^e+8N8@2$9@1$5@1$1@1$0#8@2$dN8@2$3@1$0#k0Z>0@2$h6@2$h5@2$b@1$0#k0^f+h0$h0>0@2$h6@2$b@1$0#k0^f$h0>0@4$h4?4segs?2SC@2$e@5$h1?2fx@3$i7^h7~1@2$3@1$0#k0Z@2$i8^h6+4^h5@1$h3?4segs^h4^f@4$h4?4segs?2SC@2$e@5$h1?2fx^h8^h7^h6@1$h3?4segs^h5^h0").
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiov Hb1 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  destruct (import_iovecs_of_array1 ms b1 (Z_to_bv 64 0) iov eq_refl Harr Hiov
              ltac:(rewrite u64_lit by lia; lia)) as [Himp Hacc].
  eapply (rz_ret_only_copyins_silent segs ms model (getr regs 17)
            (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
  intros o.
  rewrite (syscall_spec_66 (sys_input segs ms (getr regs 17)) model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  change (Z_to_bv 64 1) with (iovcnt32 (Z_to_bv 64 1)) at 2.
  change (ms_read_byte ms) with (in_mem (sys_input segs ms (getr regs 17))).
  apply (writev_chan_zero_outcome _ _ _ _ model o (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] Hfd).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - rewrite in_mem_si. exact Himp.
  - cbn [iovs_total]. rewrite u64_lit by lia. reflexivity.
Qed.

End WithSegs.
(* [comment removed for export] *)
