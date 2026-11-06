(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lej62ltj63pow04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib7ZBridge~~~~~~m45inr6435stdpp9bitvectorbdefinitionsqa2bvqabbv_unsigned01N46Stdlib6NArith6BinNat1Ntd2lej66moduloj64landhc2eqj63lorj64lxorj66shiftrj63div37Corelib4Init9Datatypeshib4boolj63b2zqa7Z_to_bvj63addj63ltbj63subqa9bv_signed3h5LinuxProcessSemantics5Riscv7Preludehn96bv_eqbj63eqbhn96bv_ltsj63lebhib4andb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hs76v_sltuhs75v_slths77v_sltiuqa7bv_wraphs76v_sltihib4truehc3iffhc3nothib5falsej66shiftl" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr64 : ltac2:(zQ "10!h9>1e$0P") := ltac2:(zQ "50!j0!h9!ke!l3!l8\1e$1@2$0@2$2Z^1@2$3^1@2$4+2+k0").

Lemma zr_word : ltac2:(zQ "40!le!q2!s7!sc>1x@1$2@1$0#k0@1$1@2$3@1$0#k0^1").
Proof. intros x. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. exact H. Qed.
Lemma zr_bv : ltac2:(zQ "60!ta!le!q2!v5!s7!sc>1n$0>1x@1$4^1>0@2$3^2@1$1#k0@1$2@2$5^3^2").
Proof.
  intros n x Hn. pose proof (bv_unsigned_in_range n x) as H. unfold bv_modulus, inr64 in *.
  split; [lia|]. apply Z.lt_le_trans with (2 ^ Z.of_N n)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_lit : ltac2:(zQ "60!j0!h9!q2!ke!l3!l8>1z$1>0@2$0@2$3Z^1@2$4^1@2$5+2+k0@1$2^2").
Proof. intros; assumption. Qed.
Lemma zr_mod64 : ltac2:(zQ "40!h9!q2!va!l8>1e$0@1$1@2$2^1@2$3+2+k0").
Proof. intros. unfold inr64. apply Z.mod_pos_bound. lia. Qed.
Lemma zr_mod : ltac2:(zQ "60!h9!ke!j0!q2!va!l8>1e$0>1k$0>0@2$2@2$1Z^1@2$1^1+k0@1$3@2$4^3@2$5+2^2").
Proof.
  intros e k Hk. unfold inr64. pose proof (Z.mod_pos_bound e (2^k) ltac:(apply Z.pow_pos_nonneg; lia)).
  split; [lia|]. apply Z.lt_le_trans with (2^k)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_mod_any : ltac2:(zQ "70!h9!j0!q2!ke!l3!va!l8>1e$0>1p$0>0@2$1@2$4Z^1@2$3^1@2$6+2+k0@1$2@2$5^3^2").
Proof. intros e p Hp. unfold inr64. pose proof (Z.mod_pos_bound e p ltac:(lia)). lia. Qed.
Lemma zr_land_l : ltac2:(zQ "40!h9!q2!hg3!ke>1a$0>1b$0>0@1$1^2>0@2$3Z^2@1$1@2$2^4^3").
Proof.
  intros a b [Ha Ha'] Hb. unfold inr64. pose proof (Z.land_nonneg a b) as Hn.
  split; [lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
  destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. lia. }
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_land a b ltac:(lia) Hb).
  assert (Z.log2 a < 64)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma zr_land_r : ltac2:(zQ "40!h9!q2!hg3!ke>1a$0>1b$0>0@2$3Z^2>0@1$1^2@1$1@2$2^4^3").
Proof. intros. rewrite Z.land_comm. apply zr_land_l; assumption. Qed.
(* [comment removed for export] *)
Lemma land_mask_mod : ltac2:(zQ "80!h9!hg3!l8!j0!hga!ke!l3!va>1e$0>1m$0>0@2$3@2$5Z^1@2$6^1@2$2+2+k0@3$4$0@2$1^3^2@2$1@2$7^3@2$2+2+k0^2").
Proof.
  intros e m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit m i) with false. { rewrite !andb_false_r. reflexivity. }
    symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma zr_land_lit : ltac2:(zQ "70!h9!j0!q2!hg3!ke!l3!l8>1e$0>1m$0>0@2$1@2$4Z^1@2$5^1@2$6+2+k0@1$2@2$3^3^2").
Proof.
  intros e m Hm. rewrite land_mask_mod by exact Hm. apply zr_land_r; [|exact Hm].
  apply Z.mod_pos_bound. lia.
Qed.
Lemma zr_lor : ltac2:(zQ "30!q2!h9!hgf>1a$1>1b$1>0@1$0^2>0@1$0^2@1$0@2$2^4^3").
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lor_range; lia. Qed.
Lemma zr_lxor : ltac2:(zQ "30!q2!h9!hh5>1a$1>1b$1>0@1$0^2>0@1$0^2@1$0@2$2^4^3").
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lxor_range; lia. Qed.
Lemma zr_shiftr : ltac2:(zQ "40!h9!q2!ke!hhc>1a$0>1k$0>0@1$1^2>0@2$2Z^2@1$1@2$3^4^3").
Proof. intros a k Ha Hk. unfold inr64 in *. apply Z_shiftr_range; lia. Qed.
Lemma zr_div : ltac2:(zQ "40!h9!q2!hi5!l3>1a$0>1k$0>0@1$1^2>0@2$3Z^2@1$1@2$2^4^3").
Proof.
  intros a k [Ha Ha'] Hk. unfold inr64. split. { apply Z.div_pos; lia. }
  apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma zr_b2z : ltac2:(zQ "30!hk3!q2!hkb>1b$0@1$1@1$2^1").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zr_ite : ltac2:(zQ "30!hk3!h9!q2>1b$0>1x$1>1y$1>0@1$2^2>0@1$2^2@1$2M0\1b$0$1^5^4^3").
Proof. intros [|]; auto. Qed.

Lemma inr64_unsigned_lit : ltac2:(zQ "60!le!h9!hga!q2!hl1!sc>1e$1>0@1$3^1@3$2$1@2$5@1$0#k0@2$4@1$0#k0^2^2").
Proof. intros e H. apply unsigned_lit. exact H. Qed.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lia ].

(* [comment removed for export] *)
Ltac zrange :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end
with zrange_nonneg :=
  lazymatch goal with
  | |- (0 <= ?e)%Z =>
      first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
            | apply Z.land_nonneg; left; zrange_nonneg
            | apply Z.lor_nonneg; split; zrange_nonneg
            | apply Z.lxor_nonneg; split; zrange_nonneg   (* [comment removed for export] *)
            | apply Z.shiftr_nonneg; zrange_nonneg
            | apply Z.shiftl_nonneg; zrange_nonneg
            | flia
            | is_var e; progress (unfold e); zrange_nonneg ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_mod64 : ltac2:(zQ "70!le!hl1!hga!h9!va!l8!s7>1e$3@3$2@1$6@1$0#k0@2$1@1$0#k0@2$4^1@2$5+2+k0@2$1@1$0#k0^1").
Proof.
  intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod. lia.
Qed.


(* [comment removed for export] *)
Lemma zb_land_pow2_small : ltac2:(zQ "70!h9!ke!l8!j0!hga!hg3!l3>1y$0>1k$0>0@2$3@2$1Z^2@2$6^2@2$2+2^1>0@2$1Z^2@3$4$0@2$5^4@2$2+2^3Z").
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i k) as [->|Hne].
  - rewrite Z.pow2_bits_true by lia. rewrite andb_true_r.
    apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
  - rewrite Z.pow2_bits_eqb by lia. replace (k =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma zb_lxor_pow2_small : ltac2:(zQ "80!h9!l8!ke!j0!hga!hlb!l3!hh5>1y$0>1k$0>0@2$3@2$2Z^2@2$6^2@2$1+2^1>0@2$2Z^2@3$4$0@2$7^4@2$1+2^3@2$5^4@2$1+2^3").
Proof. intros. symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_small; assumption. Qed.

Lemma zb_lxor_sign : ltac2:(zQ "90!l8!h9!j0!hga!hlb!ke!l3!hh5!va>1x$1>0@2$2@2$5Z^1@2$6^1@2$0+2+k0@3$3$1@2$7^2@2$0+2+jf@2$8@2$4^2@2$0+2+jf@2$0+2+k0").
Proof.
  intros x Hx. destruct (Z.lt_ge_cases x (2^63)).
  - rewrite zb_lxor_pow2_small by lia. rewrite Z.mod_small by lia. reflexivity.
  - set (y := (x - 2^63)%Z). replace x with (y + 2^63)%Z by lia.
    rewrite <- (zb_lxor_pow2_small y 63) at 1 by lia. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
    replace (y + 2^63 + 2^63)%Z with (y + 1 * 2^64)%Z by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zb_signed : ltac2:(zQ "a0!le!sc!hk3!h9!l8!hga!hm1!hm7!s7!hmd>1x@1$8@1$0#k0@3$5$3@2$9@1$0#k0^1M2\0$2$3@2$6@2$1@1$0#k0^1@2$4+2+jf@2$1@1$0#k0^1@2$7@2$1@1$0#k0^1@2$4+2+k0").
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. change (2^64 / 2)%Z with (2^63)%Z.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_eqb_Z : ltac2:(zQ "70!le!s7!sc!hk3!hga!hpf!hq9>1x@1$1@1$0#k0>1y@1$1@1$0#k0@3$4$3@3$5@1$0#k0^2^1@2$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof. reflexivity. Qed.

Lemma bv_lts_lxor : ltac2:(zQ "90!le!hh5!l8!s7!sc!hk3!hga!hqf!hm1>1x@1$3@1$0#k0>1y@1$3@1$0#k0@3$6$5@3$7@1$0#k0^2^1@2$8@2$1@2$4@1$0#k0^2@2$2+2+jf@2$1@2$4@1$0#k0^1@2$2+2+jf").
Proof.
  intros x y. unfold bv_lts. rewrite !zb_signed.
  pose proof (bv_unsigned_in_range 64 x) as Hx. pose proof (bv_unsigned_in_range 64 y) as Hy. unfold bv_modulus in *.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
  rewrite !zb_lxor_sign by lia.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)).
  - rewrite !Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite (Z.mod_small (bv_unsigned x + _)) by lia.
    rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite (Z.mod_small (bv_unsigned y + _)) by lia.
    rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia.
    rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_lts_zero_r : ltac2:(zQ "90!le!hk3!hga!hqf!hr9!l8!hl1!s7!sc>1x@1$7@1$0#k0@3$2$1@3$3@1$0#k0^1@2$6@1$0#k0Z@2$4@2$5+2+jf@2$8@1$0#k0^1").
Proof.
  intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite Z.ltb_lt, Z.leb_le; lia.
Qed.
(* [comment removed for export] *)
Lemma bv_lts_zero_l : ltac2:(zQ "a0!le!hm1!sc!hrf!hk3!hga!hqf!l8!hl1!s7>1x@1$9@1$0#k0@3$5$4@3$6@1$0#k0@2$8@1$0#k0Z^1@2$3@2$1Z@2$2@1$0#k0^1@2$1@2$2@1$0#k0^1@2$7+2+jf").
Proof.
  intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite andb_true_iff, !Z.ltb_lt; lia.
Qed.

(* [comment removed for export] *)
Lemma v_sltu_b2z : ltac2:(zQ "80!le!s7!sc!hga!ig6!hkb!hm1!hl1>1x@1$1@1$0#k0>1y@1$1@1$0#k0@3$3@1$1@1$0#k0@2$4^2^1@2$7@1$0#k0@1$5@2$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof. intros. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slt_b2z : ltac2:(zQ "a0!le!s7!hh5!l8!sc!hga!ih0!hkb!hm1!hl1>1x@1$1@1$0#k0>1y@1$1@1$0#k0@3$5@1$1@1$0#k0@2$6^2^1@2$9@1$0#k0@1$7@2$8@2$2@2$4@1$0#k0^2@2$3+2+jf@2$2@2$4@1$0#k0^1@2$3+2+jf").
Proof. intros. unfold v_slt, c_lts. rewrite bv_lts_lxor. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_sltiu_b2z : ltac2:(zQ "a0!le!s7!hga!h9!ih9!hkb!hm1!hl1!sc!ii4>1x@1$1@1$0#k0>3imm$3@3$2@1$1@1$0#k0@2$4^2^1@2$7@1$0#k0@1$5@2$6@2$8@1$0#k0^2@2$9@1$0#k0^1").
Proof. intros. unfold v_sltiu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slti_b2z : ltac2:(zQ "c0!le!l8!s7!hga!h9!iie!hlb!hkb!hm1!hh5!hl1!sc>1x@1$2@1$0#k0>3imm$4@3$3@1$2@1$0#k0@2$5^2^1@2$a@1$0#k0@1$7@2$8@2$9@2$b@1$0#k0^2@2$1+2+jf@2$6^1@2$1+2+jf").
Proof.
  intros. unfold v_slti, zsig. rewrite zb_signed.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  rewrite zb_lxor_sign by lia.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec0 (bv_unsigned x) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63) (imm + 2^63)); try reflexivity; exfalso; lia.
  - rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia.
    destruct (Z.ltb_spec0 (bv_unsigned x - 2^64) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63 + -1 * 2^64) (imm + 2^63)); try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma zb_b2z_if : ltac2:(zQ "40!hk3!h9!hga!hkb>1b$0@3$2$1@1$3^1M0\1b$0$1^1+1Z").
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_nonzero : ltac2:(zQ "70!hk3!hga!ij8!ik0!ik6!h9!hkb>1b$0@2$3@1$4@3$1$5@1$6^1Z@3$1$0^1$2").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : ltac2:(zQ "60!hk3!hga!ikc!ik0!h9!hkb>1b$0@2$3@3$1$4@1$5^1Z@3$1$0^1$2").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_range : ltac2:(zQ "40!hkb!ke!hk3!j0>1b$2@2$3@2$1Z@1$0^1@2$1@1$0^1+1").
Proof. intros [|]; cbv; split; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_land_mask : ltac2:(zQ "70!h9!l8!hga!hg3!ke!va!hm7>1x$0>1k$0>0@2$4Z^1@3$2$0@2$3^3@2$6@2$1+2^2+1@2$5^3@2$1+2^2").
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
Lemma zb_land_mask_l : ltac2:(zQ "70!h9!l8!hga!hg3!ke!va!hm7>1x$0>1k$0>0@2$4Z^1@3$2$0@2$3@2$6@2$1+2^2+1^3@2$5^3@2$1+2^2").
Proof. intros. rewrite Z.land_comm. apply zb_land_mask. assumption. Qed.


(* [comment removed for export] *)
Lemma zb_shl_shr : ltac2:(zQ "a0!h9!l3!va!l8!j0!hga!ke!il5!hhc!hm7>1x$0>1k$0>0@2$6Z^2>0@2$4@2$1Z^2@2$1^2+k0@3$5$0@2$8@2$2@2$7^4^3@2$3+2+k0^3@2$2^4@2$3+2@2$9+k0^3").
Proof.
  intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.
(* [comment removed for export] *)

Lemma zb_lor_eq0 : ltac2:(zQ "50!h9!hga!j0!ik0!hgf>1a$0>1b$0@2$3@3$1$0@2$4^2^1Z@2$2@3$1$0^2Z@3$1$0^1Z").
Proof. intros. apply Z.lor_eq_0_iff. Qed.
Lemma zb_land_lor_distr_l : ltac2:(zQ "40!h9!hg3!hgf!hga>1a$0>1b$0>1m$0@3$3$0@2$1@2$2^3^2^1@2$2@2$1^3^1@2$1^2^1").
Proof. intros. apply Z.land_lor_distr_l. Qed.

(* [comment removed for export] *)
Lemma zb_lxor_ones : ltac2:(zQ "80!h9!j0!hga!ke!l3!hh5!l8!hm7>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
  pose proof (Z.add_lnot_diag x).
  assert (E : Z.lxor x (Z.ones 64) = ((Z.lnot x) mod 2^64)%Z).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^64)) with (2^64 - 1)%Z.
  replace (Z.lnot x) with (-x - 1)%Z by lia.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac mlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zb_fold_lits :=
  repeat match goal with
  | |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;      (* [comment removed for export] *)
        lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
        let v := eval vm_compute in (z mod 18446744073709551616)%Z in
        replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Lemma unsigned_lit_land : ltac2:(zQ "60!le!h9!hga!hg3!hl1!sc>1e$1@3$2$1@2$5@1$0#k0@2$4@1$0#k0^1@2$3^1+vvvvvvvvvvvvvvvf").
Proof. intros. rewrite unsigned_lit_wrap. change 18446744073709551615%Z with (Z.ones 64). symmetry. apply Z.land_ones. lia. Qed.
Lemma zb_shl_shr_land : ltac2:(zQ "a0!h9!hg3!l3!hm7!j0!hga!ke!l8!il5!hhc>1x$0>1k$0>0@2$6Z^2>0@2$4@2$2Z^2@2$2^2+k0@3$5$0@2$9@2$1@2$8^4^3+vvvvvvvvvvvvvvvf^3@2$1^4@2$3@2$7+2@2$3+k0^3+1").
Proof.
  intros x k Hx Hk. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite zb_shl_shr, <- zb_land_mask by lia. reflexivity.
Qed.

Ltac zs_wrap e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])   (* [comment removed for export] *)
  end.
Ltac zs_idioms_in H :=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
(* [comment removed for export] *)
Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_land_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
Ltac zsimp :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.

Ltac zb_fold_lits_in H :=
  repeat match type of H with
  | context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
  | context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
  | context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
  | context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
  | context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  | context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
  end.

Ltac zsimp_in H :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zb_masks :=
  repeat match goal with
  | |- context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  | H : context [Z.land ?x ?m] |- _ =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac pose_word_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  | _ : context [bv_unsigned ?x] |- _ =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv_eqm : ltac2:(zQ "70!le!h9!hga!va!l8!hl1!s7>2e1$1>2e2$1>0@3$2$1@2$3^2@2$4+2+k0@2$3^1@2$4+2+k0@3$2@1$6@1$0#k0@2$5@1$0#k0^3@2$5@1$0#k0^2").
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.

Ltac word_eq_tac :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
(* [comment removed for export] *)
