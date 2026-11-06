(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk46lengthk44list37Corelib4Init5Peanomc2lek44Somek43natk46option37Corelib4Init5Logicpb2eqpb2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~r9cmemcmp_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hg65u8arr46Stdlib6ZArith6BinInt1Zhk96to_nat37Corelib4Init3Nathmb3add3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsho4cwrite_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hsb9upd_byteshsb2wahk93addhk92lehk96of_natk44boolk44trueho48store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ik94cellk44consk43nilik92CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iq08rw_cellspb3and36Stdlib5Lists4Listiud9nth_errorhk92ltpb5Falser96filledpb2or37Corelib5Lists7ListDefji96repeati27Z_to_bvhk96modulohk93powhk93subhk94landji93mapji93seqr94zseqiud7forallbhk93eqbi2bbv_unsignedpb3not37Corelib4Init6Specifjqf7sumboolk45falseiudblist_eq_dechk96eq_decr9alist_Z_eqbhsb3le4r93BC4hk93mulhsb3le8r93BC8hsb3le1ji96firstnr96copiedji95skipnmc2lti27bv_wrapi28bv_swrap3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseklbh0le_bytes_to_word02N03h5LinuxProcessSemantics5Riscv7Preludekq34sexthk93divi2abv_extractklbdZ_to_le_bytesklbdbytes_le_to_Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Bytes~~~~~~lg76le_valhk93lorhk93ltb3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypellb7Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section NulTerminated.
  Variables (A n : Z) (str slack : list byte).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.

End NulTerminated.

(* [comment removed for export] *)

Lemma skipn_cons_nth : forall {X} (l : list X) i a l', skipn i l = a :: l' -> nth_error l i = Some a /\ l' = skipn (S i) l.
Proof.
  intros X l i a l' H. split.
  - rewrite <- (firstn_skipn i l), H. rewrite nth_error_app2 by (rewrite firstn_length; pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia).
    rewrite firstn_length. replace (i - _)%nat with 0%nat by (pose proof (skipn_length i l) as L; rewrite H in L; cbn in L; lia). reflexivity.
  - replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, H. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
  match n with
  | O => Some 0
  | S n' =>
      match l, r with
      | a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
      | _, _ => None
      end
  end.

Lemma memcmp_model_total : ltac2:(zQ "c0!h9!hf!jf!lc!m5!o0!o5!oc!p2!qf!r4!v7>1l@1$4@1$2@1$0#8>1r@1$4@1$2@1$0#8>1n$7>0@2$5^1@2$3@1$2@1$0#8^3>0@2$5^2@2$3@1$2@1$0#8^3@2$a$1\1v$1@3$9@1$8$1@3$b^6^5^4@2$6$1^1").
Proof.
  intros l r n; revert l r; induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia; try (eexists; reflexivity).
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia| eexists; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithSegs.
Variable segs : ltac2:(zQ "20!m5!lp0@1$0$1").

Lemma u8arr_write_bytes : ltac2:(zQ "f0!h9!jf!lc!m5!hf!hk0!hm1!p2!hnd!o0!hrb!ig5!ih2!ih8!ihf>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1A$4>2bs@1$3@1$1@1$0#8>1i$4>2xs@1$3@1$1@1$0#8>0@4$5?4segs^5^4^3>0@2$eZ^3>0@2$9@2$8@1$6^4@2$2@1$1@1$0#8^3@2$2@1$1@1$0#8^5@4$5?4segs@3$a^8@1$c@2$d^7^5^4^7@3$b^6@1$6^5^4").
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma u8arr_store_ok_n : ltac2:(zQ "h00!h9!jf!qf!hf!ih8!ihf!ii5!iif!lc!m5!oc!p2!ij6!ijd!hk0!ih2>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>1A$3>2bs@1$9@1$1@1$0#8>1i$3>1n$a>1a@1$1@1$0#k0>0@4$e?4segs^6^5^4>0@2$5Z^4>0@2$5@2$4^5@1$6^4@1$6@2$8@1$1@1$0#8^6>0@3$2@1$1@1$0#k0^4@1$f@2$4^8^6@3$2$7@4$d?4segs^a^5^6$c").
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma rw_cells_CB_length : ltac2:(zQ "d0!h9!jf!oc!io5!iod!lc!m5!ip4!p2!qf!hf!ipa!itb>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$a>1n$2>2bs@1$6@1$1@1$0#8>0@4$c?4segs^4^3@3$4$3@2$b^2^1@1$7$3@3$9$2@2$5@1$1@1$0#8^2^3").
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.

(* [comment removed for export] *)
Definition filled : ltac2:(zQ "40!h9!jf!m5!hf>1c@1$1@1$0#8>2bs@1$2@1$1@1$0#8>1Q>0$3PP") := ltac2:(zQ "e0!h9!jf!hf!o5!lc!m5!p2!iu7!qf!jg0!ihf!jgd!ii5!hm1\1c@1$1@1$0#8\2bs@1$5@1$1@1$0#8\1Q>0$2P>1j$2>0@2$7@2$aZ^1@2$b^1@1$c@2$4@1$1@1$0#8^3>0@1^3^2@3$8@1$6@1$1@1$0#8@3$9@1$1@1$0#8^5@1$d^3@2$3@1$1@1$0#8^6").

Lemma filled_init : ltac2:(zQ "60!h9!jf!m5!jh3!hf!jhb>1c@1$1@1$0#8>2bs@1$2@1$1@1$0#8@3$5^2^1\0$4$3").
Proof. intros c bs j _ []. Qed.

Lemma nth_error_repeat' : forall {X} (x : X) k i, (i < k)%nat -> nth_error (repeat x k) i = Some x.
Proof. intros X x k; induction k as [|k IH]; intros [|i] H; cbn; try lia; auto. apply IH. lia. Qed.

Lemma filled_upd : ltac2:(zQ "h10!h9!jf!ii5!oc!hf!jhb!lc!m5!iu7!ji4!hnd!o0!jk0!ig5!ih8!ihf!jgd>1c@1$1@1$0#8>2bs@1$7@1$1@1$0#8>1Q>0$4P>1i$3>1k$3>0@3$5^5^4^3>0@2$b@2$a^3^2@2$6@1$1@1$0#8^5@3$5^7@3$d^6^4@3$c@1$1@1$0#8^7^3\1j$4@2$9@1^6^1@2$8@2$f@1$2^5^1@2$h0^1@2$e@1$2^5@1$2^4").
Proof.
  intros c bs Q i k HF Hk j Hj HQ. rewrite upd_bytes_length in Hj by (rewrite repeat_length; lia).
  rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
  destruct (Nat.leb_spec0 i (Z.to_nat j)); destruct (Nat.ltb_spec0 (Z.to_nat j) (i + k)); cbn [andb];
    first [ apply nth_error_repeat'; lia | destruct HQ as [HQ|HQ]; [apply HF; [lia| exact HQ] | exfalso; lia] ].
Qed.

Lemma filled_updZ : ltac2:(zQ "h20!h9!jf!hf!jhb!ihf!hm1!lc!m5!oc!iu7!ji4!hnd!o0!jk0!ig5!ih8!jgd!ii5>1c@1$1@1$0#8>2bs@1$7@1$1@1$0#8>1Q>0$2P>1i$2>1k$8>0@3$3^5^4^3>0@2$4Z^3>0@2$c@2$b@1$5^4^3@2$6@1$1@1$0#8^6@3$3^8@3$e^7@1$5^5@3$d@1$1@1$0#8^8^4\1j$2@2$a@1^7^1@2$9@2$4^6^1@2$h0^1@2$f^6@1$h1^5").
Proof.
  intros c bs Q i k HF Hi Hk j Hj HQ. apply (filled_upd c bs Q (Z.to_nat i) k HF Hk j Hj). destruct HQ; [left; assumption| right; lia].
Qed.

Lemma filled_all : ltac2:(zQ "c0!h9!jf!lc!m5!hf!iu7!qf!jk0!jhb!ihf!jgd!ii5>1c@1$1@1$0#8>2bs@1$3@1$1@1$0#8>1Q>0$4P>0@3$8^3^2^1>0>1j$4>0@2$5@2$9Z^1@2$a^1@1$b@2$2@1$1@1$0#8^4@1^4^2@3$6@1$3@1$1@1$0#8^4@3$7@1$1@1$0#8^5@2$2@1$1@1$0#8^4").
Proof.
  intros c bs Q HF HQ. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite nth_error_repeat' by lia. replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HF; [lia|]. apply HQ. lia.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma Z_to_bv8_mod : ltac2:(zQ "60!h9!jka!qf!hf!jl4!jf>1z$3@3$2@1$5@1$0#8@2$1@1$0#8^1@2$1@1$0#8@2$4^1+hg0").
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256)%Z. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_align_down : ltac2:(zQ "90!jle!hf!ihf!iu7!jm5!qf!jmc!jgd!jl4>1x$1>1j$1>0@2$3@2$2Z^2@2$7^2@2$0+2+k0>0@2$3@2$2Z^2@2$2^2+k0@3$5$1@2$6^4@2$4@2$0+2+k0@2$0+2^3@2$4^4@2$8^4@2$0+2^3").
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition zseq : ltac2:(zQ "30!m5!oc!hf>1n$1@1$0$2") := ltac2:(zQ "50!oc!jn4!jnb!hf!ii5\1n$0@4$1$0$3$4@2$2N0^1").
Lemma forallb_zseq : ltac2:(zQ "b0!iif!hf!ij6!qf!oc!iu7!jo2!jo9!ihf!jgd!ii5>1n$4>1f>0$1$0>0@3$3$0@3$7$1^1@1$6^2$2>1c$1>0@2$5@2$8Z^1@2$9^1@1$a^4@3$3$0@1^4^2$2").
Proof.
  intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
  exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma brute256_ok : ltac2:(zQ "90!iif!hf!ij6!qf!iu7!jo2!jo9!ihf!jgd>1P>0$1$0>0@3$3$0@3$6$1^1@1$5Nhg0$2>1c$1>0@2$4@2$7Z^1@2$8^1+hg0@3$3$0@1^4^2$2").
Proof. intros P H c Hc. exact (forallb_zseq 256 P H c Hc). Qed.

Lemma word_eq_of_eqb : ltac2:(zQ "a0!h9!qf!hf!jl4!jle!jka!iif!ij6!jp4!jf>1x$2>1y$2>0@3$1$6@2$8@2$3^2@2$4+2+k0@2$3^1@2$4+2+k0$7@3$1@1$9@1$0#k0@2$5@1$0#k0^3@2$5@1$0#k0^2").
Proof. intros x y H. apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma map_unsigned_inj : ltac2:(zQ "70!h9!jf!m5!hf!qf!jn4!jpb>2l1@1$2@1$1@1$0#8>2l2@1$2@1$1@1$0#8>0@3$4@1$2$3@4$5@1$1@1$0#8$3@1$6@1$0#8^2@4$5@1$1@1$0#8$3@1$6@1$0#8^1@3$4@1$2@1$1@1$0#8^3^2").
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx| apply IH; exact Hl].
Qed.

Definition list_Z_eqb : ltac2:(zQ "30!m5!hf!iif>2l1@1$0$1>2l2@1$0$1$2") := ltac2:(zQ "a0!hf!m5!qf!jq9!js4!iif!jsf!ij6!jt7!ju6\2l1@1$1$0\2l2@1$1$0M4\0@2$4@3$2@1$1$0^2^1@1$3@3$2@1$1$0^2^1$5@4$8$0$9^2^1\0@3$2@1$1$0^2^1$7\0@1$3@3$2@1$1$0^2^1$6").
Lemma list_Z_eqb_eq : ltac2:(zQ "60!m5!hf!qf!iif!ij6!jv0>2l1@1$0$1>2l2@1$0$1>0@3$2$3@2$5^2^1$4@3$2@1$0$1^3^2").
Proof. intros l1 l2. unfold list_Z_eqb. destruct (list_eq_dec Z.eq_dec l1 l2); [auto|discriminate]. Qed.

Lemma bcast_ok : ltac2:(zQ "h20!h9!hf!jf!m5!qf!jk0!iif!oc!ij6!iu7!jn4!jv0!jo2!jo9!ihf!jgd!jka!jpb>1F>0$1@1$3@1$2@1$0#8>1k$7>0@3$4$6@3$d$1\1c$1@2$b@4$a@1$2@1$0#8$1@1$h1@1$0#8@1^3^1@3$5$1^1^2@1$cNhg0$8>1c$1>0@2$9@2$eZ^1@2$f^1+hg0@3$4@1$3@1$2@1$0#8@1^5^2@3$5@1$2@1$0#8@2$h0@1$0#8^2^4").
Proof.
  intros F k H c Hc. apply map_unsigned_inj.
  pose proof (forallb_zseq 256 _ H c Hc) as E. cbn beta in E. apply list_Z_eqb_eq in E. rewrite E.
  rewrite map_repeat. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.

Lemma le4_bcast : ltac2:(zQ "d0!h9!jka!jf!m5!iu7!qf!jk0!hf!jvd!kg4!ihf!jgd!kga>1c$7>0@2$4@2$aZ^1@2$b^1+hg0@3$5@1$3@1$2@1$0#8@1$8@2$1@1$0#k0@2$c^2$9@3$6@1$2@1$0#8@2$1@1$0#8^2N4").
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (c * BC4))) 4). vm_compute. reflexivity. Qed.
Lemma le8_bcast : ltac2:(zQ "d0!h9!jka!jf!m5!iu7!qf!jk0!hf!kh1!kh8!ihf!jgd!kga>1c$7>0@2$4@2$aZ^1@2$b^1+hg0@3$5@1$3@1$2@1$0#8@1$8@2$1@1$0#k0@2$c^2$9@3$6@1$2@1$0#8@2$1@1$0#8^2N8").
Proof. apply (bcast_ok (fun c => le8 (Z_to_bv 64 (c * BC8))) 8). vm_compute. reflexivity. Qed.
Lemma le1_byte : ltac2:(zQ "a0!h9!jf!iod!m5!ip4!qf!khe!jl4!jka!jpb>1x@1$1@1$0#k0@3$5@1$3@1$1@1$0#8@1$6^1@3$2@1$1@1$0#8@2$8@1$0#8@2$7@2$9@1$0#k0^1+hg0@1$4@1$1@1$0#8").
Proof. intros x. cbn. rewrite <- Z_to_bv8_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition copied : ltac2:(zQ "40!m5!h9!jf!oc>3src@1$0@1$2@1$1#8>2bs@1$0@1$2@1$1#8>1k$3P") := ltac2:(zQ "80!h9!jf!m5!lc!oc!qf!ki5!iu7\3src@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8\1k$4@2$7@3$5$4@2$3@1$1@1$0#8^2@2$3@1$1@1$0#8^3@3$5@1$2@1$1@1$0#8@3$6@1$1@1$0#8^1^2@3$6@1$1@1$0#8^1^3").

Lemma copied_0 : ltac2:(zQ "70!h9!jf!lc!m5!oc!qf!kif>3src@1$3@1$1@1$0#8>2bs@1$3@1$1@1$0#8>0@3$5$4@2$2@1$1@1$0#8^1@2$2@1$1@1$0#8^2@3$6^3^2N0").
Proof. intros src bs H. split; [exact H| reflexivity]. Qed.

Lemma copied_all : ltac2:(zQ "80!h9!jf!m5!lc!oc!qf!o0!kif>3src@1$2@1$1@1$0#8>2bs@1$2@1$1@1$0#8>1k$4>0@3$7^3^2^1>0@2$6@2$3@1$1@1$0#8^4^2@3$5@1$2@1$1@1$0#8^4^5").
Proof.
  intros src bs k [Hl Hf] Hk. rewrite <- (firstn_all2 (n:=k) bs) by lia. rewrite <- (firstn_all2 (n:=k) src) by lia. exact Hf.
Qed.

Lemma firstn_app_len : forall {X} (a b : list X) k, k = length a -> firstn k (a ++ b) = a.
Proof. intros X a b k ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma app_firstn_mid_skipn : forall {X} (l : list X) p k,
  firstn p l ++ firstn k (skipn p l) ++ skipn (p + k) l = l.
Proof.
  intros X l p k. rewrite <- (firstn_skipn p l) at 4. f_equal.
  replace (skipn (p + k) l) with (skipn k (skipn p l)) by (rewrite skipn_skipn; f_equal; lia). apply firstn_skipn.
Qed.

Lemma copied_upd : ltac2:(zQ "c0!h9!jf!lc!m5!hnd!kif!oc!qf!o0!ki5!kj8!ig5>3src@1$3@1$1@1$0#8>2bs@1$3@1$1@1$0#8>1p$6>2xs@1$3@1$1@1$0#8>0@3$5^4^3^2>0@3$7@1$3@1$1@1$0#8@3$9@1$1@1$0#8@2$2@1$1@1$0#8^2@3$a@1$1@1$0#8^3^5^2>0@2$8@2$4^4@2$2@1$1@1$0#8^3@2$2@1$1@1$0#8^6@3$5^7@3$b^6^5^4@2$4^5@2$2@1$1@1$0#8^4").
Proof.
  intros src bs p xs [Hl Hf] Hx Hp. split.
  - rewrite upd_bytes_length by lia. exact Hl.
  - unfold upd_bytes. rewrite app_assoc.
    assert (L1 : length (firstn p bs ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
    rewrite (firstn_app_len (firstn p bs ++ xs)) by lia.
    transitivity (firstn (p + length xs) (firstn p src ++ xs ++ skipn (p + length xs) src)).
    + assert (L2 : length (firstn p src ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
      rewrite app_assoc, (firstn_app_len (firstn p src ++ xs)) by lia. rewrite Hf. reflexivity.
    + f_equal. etransitivity; [ | apply (app_firstn_mid_skipn src p (length xs))]. rewrite Hx. reflexivity.
Qed.

Lemma copied_updZ : ltac2:(zQ "h00!h9!jf!hm1!lc!m5!kif!qf!hnd!o0!ki5!kj8!hf!ig5!ih8!ihf!ii5>3src@1$4@1$1@1$0#8>2bs@1$4@1$1@1$0#8>1P$b>2xs@1$4@1$1@1$0#8>0@3$5^4^3@1$2^2>0@2$eZ^3>0@3$6@1$4@1$1@1$0#8@3$9@1$1@1$0#8@2$3@1$1@1$0#8^3@3$a@1$1@1$0#8@1$2^4^6^3>0@2$8@2$7@1$2^5@2$3@1$1@1$0#8^4@2$3@1$1@1$0#8^7@3$5^8@3$c^7@1$2^6^5@1$2@2$d^6@1$f@2$3@1$1@1$0#8^5").
Proof.
  intros src bs P xs HC HP Hx Hl. replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
  apply copied_upd; assumption.
Qed.

(* [comment removed for export] *)
Lemma window_ex : ltac2:(zQ "e0!h9!jf!m5!lc!oc!qf!hm1!iu7!r4!hnd!o0!ki5!kj8!hf>1l@1$2@1$1@1$0#8>1i$d>1k$4>0@2$a@2$9@1$6^2^1@2$3@1$1@1$0#8^3@2$8@1$2@1$1@1$0#8\2xs@1$2@1$1@1$0#8@2$7@3$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8^3@3$c@1$1@1$0#8@1$6^4^5^1@3$5$4@2$3@1$1@1$0#8^1^3").
Proof. intros l i k H. eexists. split; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.

Lemma window_nth : ltac2:(zQ "f0!h9!jf!m5!qf!hf!oc!jg0!hm1!p2!kk1!ki5!kj8!ih8!ihf!ii5>1l@1$2@1$1@1$0#8>2xs@1$2@1$1@1$0#8>4base$4>1k$5>1c$5>1i$4>0@3$3@1$2@1$1@1$0#8@3$a@1$1@1$0#8^3@3$b@1$1@1$0#8@1$7^4^6^5>0@2$dZ^5>0@2$9^4^5>0@3$3$4^4@2$c^7@1$e^5@3$3@1$8@1$1@1$0#8@3$6@1$1@1$0#8^a@1$7^5@3$6@1$1@1$0#8^9^6").
Proof.
  intros l xs base k c i H Hb Hc ->. rewrite <- H. rewrite nth_error_firstn.
  replace (Nat.ltb c k) with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma window_sub : ltac2:(zQ "e0!h9!jf!m5!oc!qf!ki5!kj8!hf!hm1!hnd!o0!ih8!ihf!ii5>1l@1$2@1$1@1$0#8>2xs@1$2@1$1@1$0#8>4base$7>1k$3>1c$3>1j$3>1i$7>0@3$4@1$2@1$1@1$0#8@3$5@1$1@1$0#8^4@3$6@1$1@1$0#8@1$8^5^7^6>0@2$cZ^6>0@2$a@2$9^5^4^6>0@3$4$7^4@2$b^8@1$d^6@3$4@1$2@1$1@1$0#8@3$5@1$1@1$0#8^6@3$6@1$1@1$0#8@1$8^5^b@3$5@1$1@1$0#8^6@3$6@1$1@1$0#8^7^a").
Proof.
  intros l xs base k c j i H Hb Hc ->. rewrite <- H.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn by lia. f_equal; [lia|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_range : ltac2:(zQ "60!h9!jpb!iu7!ihf!jgd!jf>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma bv_wrap32_eq : ltac2:(zQ "60!hf!qf!h9!jl4!jle!kk6>1z$0@3$1$0@2$5@1$2#i0^1@2$3^1@2$4+2+i0").
Proof. reflexivity. Qed.
Lemma bv_swrap32_eq : ltac2:(zQ "80!jle!hf!qf!h9!ih8!jl4!jm5!kl0>1z$1@3$2$1@2$7@1$3#i0^1@2$6@2$5@2$4^1@2$0+2+hf@2$0+2+i0@2$0+2+hf").
Proof. reflexivity. Qed.

Lemma le_bytes_to_word4 : ltac2:(zQ "a0!h9!jf!jpb!iod!ih8!kga!ip4!qf!hf!koa>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8@3$7$8@2$2@1$0#k0@1$9@3$3@1$1@1$0#8^4@3$3@1$1@1$0#8^3@3$3@1$1@1$0#8^2@3$3@1$1@1$0#8^1@1$6@1$1@1$0#8@2$4@2$4@2$4@2$2@1$0#8^4@2$5+hg0@2$2@1$0#8^3@2$5+hggg0@2$2@1$0#8^2@2$5+hggggg0@2$2@1$0#8^1").
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lw_unsigned4 : ltac2:(zQ "h00!h9!jf!jpb!iod!ih8!kga!jle!ip4!qf!kpf!hf!koa!ks9!kt1!jm5!kt8>2b0@1$1@1$0#8>2b1@1$1@1$0#8>2b2@1$1@1$0#8>2b3@1$1@1$0#8@3$8$a@2$2@1$0#k0@3$c@1$0#i0@1$0#k0@4$f@1$0#k0$9@1$0#i0@1$b@3$3@1$1@1$0#8^4@3$3@1$1@1$0#8^3@3$3@1$1@1$0#8^2@3$3@1$1@1$0#8^1@1$7@1$1@1$0#8@2$4@2$4@2$4@2$4@2$2@1$0#8^4@2$5+hg0@2$2@1$0#8^3@2$5+hggg0@2$2@1$0#8^2@2$5+hggggg0@2$2@1$0#8^1@2$5@2$e@2$6+2+k0@2$6+2+i0@2$d@2$2@1$0#8^1+o0").
Proof.
  intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma Z_to_le_bytes_to_Z : ltac2:(zQ "70!h9!jf!m5!lc!qf!ku5!kv6>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le4_of_mod32 : ltac2:(zQ "d0!h9!jf!qf!m5!hf!jpb!lc!oc!jn4!lk3!jvd!jl4!jle>1v@1$1@1$0#k0>2bs@1$3@1$1@1$0#8>0@3$2$7@2$6@1$1@1$0#8^1N4>0@3$2$4@2$b@2$5@1$0#k0^3@2$c+2+i0@1$9@4$8@1$1@1$0#8$4@1$5@1$0#8^2@3$2@1$3@1$1@1$0#8@1$a^4^3").
Proof.
  intros v bs Hl Hv. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le1_of_mod8 : ltac2:(zQ "b0!h9!jf!qf!jpb!iod!m5!ip4!hf!khe!jl4!jle>1v@1$1@1$0#k0>1b@1$1@1$0#8>0@3$2$7@2$9@2$3@1$0#k0^2@2$a+2+8@2$3@1$0#8^1@3$2@1$5@1$1@1$0#8@1$8^3@3$4@1$1@1$0#8^2@1$6@1$1@1$0#8").
Proof.
  intros v b Hv. unfold le1. rewrite <- (Z_to_le_bytes_mod 1 _ 8) by (cbn; lia). change (2^8) with (2^8) in *. rewrite Hv.
  cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma le1_zxb : ltac2:(zQ "90!h9!jf!iod!m5!ip4!qf!khe!jka!jpb>1b@1$1@1$0#8@3$5@1$3@1$1@1$0#8@1$6@2$7@1$0#k0@2$8@1$0#8^1@3$2@1$1@1$0#8^1@1$4@1$1@1$0#8").
Proof. intros b. apply le1_of_mod8. pose proof (byte_range b). rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia. Qed.

Lemma le4_lw : ltac2:(zQ "b0!h9!jf!m5!qf!lc!oc!kpf!koa!ks9!jvd!kt8>1w@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N4@3$3@1$2@1$1@1$0#8@1$9@3$8@1$0#i0@1$0#k0@4$a@1$0#k0$6@1$0#i0@1$7^2^2").
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma lor_add : ltac2:(zQ "90!hf!qf!ihf!jle!iu7!ih8!lkd!jgd!jl4>2hi$0>2lo$0>1k$0>0@2$2Z^1>0@2$4@2$2Z^3@2$7^3@2$3+2^2>0@3$1$0@2$8^5@2$3+2^3Z@3$1$0@2$6^6^5@2$5^6^5").
Proof.
  intros hi lo k Hk Hlo Hhi.
  assert (HL : Z.land hi lo = 0).
  { rewrite <- (Z.mod_small lo (2^k)) by lia. rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma lor_add' : ltac2:(zQ "90!hf!qf!ihf!jle!iu7!ih8!lkd!jgd!jl4>2lo$0>2hi$0>1k$0>0@2$2Z^1>0@2$4@2$2Z^4@2$7^4@2$3+2^2>0@3$1$0@2$8^4@2$3+2^3Z@3$1$0@2$6^6^5@2$5^6^5").
Proof. intros. rewrite Z.lor_comm, (lor_add hi lo k); lia. Qed.

(* [comment removed for export] *)
Lemma land_single_bit : ltac2:(zQ "90!hf!jle!iif!ihf!qf!ih8!jmc!ll4!jl4>1x$0>1k$0>0@2$3Z^2>0@2$3Z^2@3$4$0@2$6^4@2$1+2^3M2\0$2$0@2$7@2$8^4@2$1+2@2$5^3+1@2$1+2^3Z@2$1+2^3").
Proof.
  intros x k Hx Hk.
  assert (Hpk : 0 < 2^k < 2^(k+1)). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]. }
  rewrite (Z.land_comm x), <- (land_mod_pow2_r (2^k) x (k+1)) by lia.
  set (r := x mod 2^(k+1)).
  assert (Hr : 0 <= r < 2^(k+1)) by (subst r; apply Z.mod_pos_bound; lia).
  rewrite Z.pow_add_r in Hr by lia. change (2^1) with 2 in Hr.
  destruct (Z.ltb_spec0 r (2^k)) as [Hl|Hl].
  - rewrite Z.land_comm. apply zb_land_pow2_small; lia.
  - replace r with (Z.lor (2^k) (r - 2^k)).
    2:{ rewrite lor_add with (k := k); try lia. rewrite Z.mod_same; lia. }
    rewrite Z.land_lor_distr_r, Z.land_diag, (Z.land_comm (2^k)), zb_land_pow2_small by lia. apply Z.lor_0_r.
Qed.

Lemma land_bit_2 : ltac2:(zQ "70!hf!iif!qf!jmc!ihf!ll4!jl4>1x$0>0@2$4Z^1@3$2$0@2$3^2+2M1\0$1$0@2$5@2$6^2+4+2Z+2").
Proof. intros x Hx. exact (land_single_bit x 1 Hx ltac:(lia)). Qed.
Lemma land_bit_4 : ltac2:(zQ "70!hf!iif!qf!jmc!ihf!ll4!jl4>1x$0>0@2$4Z^1@3$2$0@2$3^2+4M1\0$1$0@2$5@2$6^2+8+4Z+4").
Proof. intros x Hx. exact (land_single_bit x 2 Hx ltac:(lia)). Qed.
Lemma land_bit_8 : ltac2:(zQ "70!hf!iif!qf!jmc!ihf!ll4!jl4>1x$0>0@2$4Z^1@3$2$0@2$3^2+8M1\0$1$0@2$5@2$6^2+h0+8Z+8").
Proof. intros x Hx. exact (land_single_bit x 3 Hx ltac:(lia)). Qed.

Lemma land_1 : ltac2:(zQ "40!hf!qf!jmc!jl4>1x$0@3$1$0@2$2^1+1@2$3^1+2").
Proof. intros x. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_3 : ltac2:(zQ "40!hf!qf!jmc!jl4>1x$0@3$1$0@2$2^1+3@2$3^1+4").
Proof. intros x. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

(* [comment removed for export] *)

Lemma firstn_S_nth : forall {X} (l : list X) p x, nth_error l p = Some x -> firstn (S p) l = firstn p l ++ [x].
Proof.
  intros X l; induction l as [|a l IH]; intros [|p] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH p x H). reflexivity.
Qed.

(* [comment removed for export] *)
