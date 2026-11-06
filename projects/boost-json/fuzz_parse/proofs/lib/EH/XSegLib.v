(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare
  XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z37Corelib4Init5Logici23andi22eq46Stdlib6ZArith6BinInt1Zk12lek12ltk13pow35stdpp9bitvectorbdefinitionsm97Z_to_bvm9bbv_unsignedm92bv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~q34ELitq33env89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~v55elenZ37Corelib4Init9Datatypeshk93nathk94boolq33Envq32ebq32ev46Stdlib5Arith8PeanoNat3Natho03eqb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~hq29env_agreea9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib3APS3FPX5Sound~~~~~~huf4ext137Corelib4Init5Peanoik22le89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XAsanPlan2AP~~~~~~ilccexpr_vars_ltq34exprhq2cexpr_vars_ltilcekentry_vars_ltq36kentryhq2ekentry_vars_lthk94listilcakn_vars_lthq2akn_vars_ltilcasr_vars_lthq2asr_vars_ltq36edenothk94truev57know_okhk96optionv57regs_ok3h5LinuxProcessSemantics5Riscv7Preludejm15bvmapilcakentry_eqbhuf8ext_listhk96length37Corelib4Init3Natjr43addik22lt37Corelib5Lists7ListDefjt33nthhk94prodq35saddrhk94Somehk94pairv56estarthk94Nonek16of_natk13subk13addi24Truei22orhuf5kfootilcekentry_apart_bq32SAhufbkfoot_apartv59kentry_okilcfkentry_apart_bpq38mk_sprepilc6havoc1ilc7havoc1pilc8kn_havoc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~krd9mem_growsq39split_litilc6flat_xi23not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~li44getri21Iilcccaller_savedq34ridx36Stdlib5Lists4Listlo62Inm92BVm94BvWfli44mkstli47seg_romk16to_nati22exjt36repeat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslt68store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~mh96wbytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~mm16msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6XHoare~~~~~~mq86ret_oka9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX3FPX5Specs~~~~~~mue7kept_okli43rdnlo65NoDupilc8sr_freshq34EVarhk94andbjr43subilc3NCSho03lebho03ltb99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX3FPX~~~~~~noc8ext_callq36sr_updnoc7kept_okq36adenotilcbkwritable_xlt6h0word_to_le_bytesk14landk13mulk13lor3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseoj2dZ_to_le_bytesoj2dbytes_le_to_Zhk93nilq38sidecondhk95falseq34LHitq3bknow_lookupq34lresv54flata9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX3FPX9KnowTests~~~~~~os18piece_okilc7kread8ehk94consilc6kreadZjt36Foralljt33mapilcbkread_bytesq3ezbytes_le_to_Zilcacopy_factsk16modulo3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypepo27Segment" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma u64_lit : ltac2:(zQ "90!h9!hf!j6!jc!l9!le!m3!o6!p0>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.
Lemma u64_range : ltac2:(zQ "70!h9!p0!j6!l9!le!m3!pe>1w@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Module APS.
Import AX2. Import AX2S. Import AP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX. Context {fx : XPropExec.FPState}.
Section Sound.
Variable SEGS : ltac2:(zQ "20!iv2!pr7@1$0$1").

Lemma elenZ_lit : ltac2:(zQ "90!hf!j6!jc!u8!uf!hk1!l9!le!m3>1E$4>1z$0>0@2$1@2$6Z^1@2$7^1@2$8+2+k0@3$2$0@2$5^3@1$3^2^2").
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Definition ext1 : ltac2:(zQ "40!uf!hm1!h9!pe>1E$0>1v$1>1a@1$3@1$2#k0$0") := ltac2:(zQ "90!hm8!hm1!h9!pe!hn0!hn6!uf!hnb!hpb\1E$6\1v$1\1a@1$3@1$2#k0@2$4\1n$1M0\0$0@1$3@1$2#k0@2$8^1^3^2@2$7^4^1@1$5^3").

Lemma ext1_agree : ltac2:(zQ "60!hm1!h9!uf!hu2!ija!pe>1E$2>1v$0>1a@1$5@1$1#k0@3$3^2^3@3$4^3^2^1").
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma ext1_at : ltac2:(zQ "70!h9!pe!hm1!jc!uf!hnb!ija>1E$4>1v$2>1a@1$1@1$0#k0@3$3@1$1@1$0#k0@2$5@3$6^3^2^1^2^1").
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma env_agree_le : ltac2:(zQ "40!hm1!uf!hu2!il6>1b$0>2b'$0>1E$1>2E'$1>0@3$2^3^2^1>0@2$3^5^4@3$2^6^4^3").
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

Lemma env_agree_refl : ltac2:(zQ "30!hm1!uf!hu2>1b$0>1E$1@3$2^2^1^1").
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

Lemma env_agree_trans : ltac2:(zQ "30!uf!hu2!hm1>1b$2>2E1$0>2E2$0>2E3$0>0@3$1^4^3^2>0@3$1^5^3^2@3$1^6^5^3").
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

Lemma expr_vars_lt_eq : ltac2:(zQ "60!hm8!hm1!jc!ipe!iqe!ir5>1b$1>1e$4@3$2$0@2$3^2^1@2$5^2^1").
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.

Lemma kentry_vars_lt_eq : ltac2:(zQ "60!hm8!hm1!jc!is5!it7!iu0>1b$1>1K$4@3$2$0@2$3^2^1@2$5^2^1").
Proof.
  intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
    cbn -[AP.expr_vars_lt XAxSymRun3.expr_vars_lt]; unfold AP.saddr_vars_lt, XAxSymRun3.saddr_vars_lt; cbn [a_base];
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.

Lemma kn_vars_lt_eq : ltac2:(zQ "70!hm8!iv2!hm1!jc!iva!it7!jg8>1b$2>1k@1$1$5@3$3$0@2$4^2^1@2$6^2^1").
Proof. intros b k. induction k; cbn [AP.kn_vars_lt XAxSymRun3.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.

Lemma sr_vars_lt_eq : ltac2:(zQ "70!hm8!iv2!hm1!jc!jh6!iqe!ji4>1b$2>2sr@1$1$5@3$3$0@2$4^2^1@2$6^2^1").
Proof. intros b sr. induction sr; cbn [AP.sr_vars_lt XAxSymRun3.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.

Lemma edenot_agree' : ltac2:(zQ "b0!jc!jj2!uf!hm8!hm1!jjb!h9!ipe!iqe!hu2!pe>1b$4>1E$2>2E'$2>1e$8>0@3$9^4^3^2>0@3$0$3@2$7^5^2$5@3$0@1$a@1$6#k0@2$1^5^3@2$1^4^3").
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.

Lemma know_ok_agree' : ltac2:(zQ "d0!h9!uf!jk3!pe!hm8!iv2!hm1!jkd!jjb!jc!iva!it7!hu2>1b$6>1E$1>2E'$1>1M>0@1$3@1$0#k0@1$7@1$3@1$0#8>1k@1$5$b>0@3$c^5^4^3>0@3$9$4@2$a^6^2$8>0@4$2?4SEGS^6^4^3@4$2?4SEGS^6^5^4").
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.

Lemma regs_ok_agree' : ltac2:(zQ "d0!h9!uf!jl7!hm8!iv2!hm1!jjb!jc!jo7!jh6!iqe!hu2!pe>1b$5>1E$1>2E'$1>2sr@1$4$a>1R@2$8@1$0#5@1$c@1$0#k0>0@3$b^5^4^3>0@3$7$3@2$9^6^3$6>0@3$2^6^4^3@3$2^6^5^4").
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.

Lemma kentry_eqb_eq : ltac2:(zQ "50!it7!jc!hm8!jjb!jp0>1x$0>1y$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.

Lemma expr_vars_lt_mono : ltac2:(zQ "70!hm8!hm1!jjb!jc!ipe!il6!iqe>1b$1>2b'$1>1e$6>0@3$3$0@2$4^3^1$2>0@2$5^4^3@3$3$0@2$4^4^3$2").
Proof.
  intros b b' e H Hle. induction e; cbn [AP.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
  end.

Lemma ext_list_agree : ltac2:(zQ "70!iv2!hm1!h9!uf!hu2!jpe!pe>1E$3>2nx$1>4vals@1$0@1$6@1$2#k0@3$4^2^3@3$5^3^2^1").
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
  - apply env_agree_refl.
  - eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.

Lemma ext_list_at : ltac2:(zQ "d0!h9!pe!hm1!jqa!iv2!jc!js6!jsd!jua!uf!hnb!jpe!o6>1E$9>2nx$2>4vals@1$4@1$1@1$0#k0>1i$2>0@2$7^1@2$3@1$1@1$0#k0^2@3$5@1$1@1$0#k0@2$a@3$b^5^4^3@2$6^4^2@4$8@1$1@1$0#k0^2^3@2$c@1$0#k0Z").
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
  cbn [ext_list]. destruct i as [|i].
  - rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
    rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
  - replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

Definition upd : ltac2:(zQ "40!uf!hm1!h9!pe>1E$0>1J$1>1w@1$3@1$2#k0$0") := ltac2:(zQ "90!hm8!hm1!h9!pe!hn0!hn6!uf!hnb!hpb\1E$6\1J$1\1w@1$3@1$2#k0@2$4\1n$1M0\0$0@1$3@1$2#k0@2$8^1^3^2@2$7^4^1@1$5^3").

Definition kfoot : ltac2:(zQ "50!hf!jkd!jv1!uf!it7>1E$3>1K$4@1$1@2$2$0$0") := ltac2:(zQ "f6!hf!jv1!iqe!jv9!kg1!kg9!kh1!hk1!kha!it7!hm1!jkd!uf!ki2!kib&@4$5$0$0@2$6^4^2@2$7^4^1&@2$4@2$1$0$0~0&\1l$2~1&\1a$3~2&@4$5$0$0@2$6^5^3@2$7^5^2&@2$4@2$1$0$0~4\1E$c\1K$9M9\1K$9@1$b@2$1$0$0^1\1a$3\1w$a\1v$2@2$4@2$1$0$0@4$5$0$0@2$6^5^3@1$d^2~3\1a$3\1l$2\1k$a~5\2lo$0\2hi$0@2$4@2$1$0$0@4$5$0$0^2@2$e^1^2\1e$2\1m$0@1$8@2$1$0$0\1e$2\2lo$0\2hi$0@1$8@2$1$0$0\1a$3\1n$2~1\2a1$3\2n1$2\2a2$3\2n2$2@1$8@2$1$0$0\1a$3\1l$2\1c$0~5~3").

Definition kfoot_apart : ltac2:(zQ "30!hf!uf!it7>1E$1>1K$2>2lo$0>1n$0P") := ltac2:(zQ "a0!hf!jv1!jkd!kj1!l9!kj7!kje!uf!it7!kk3\1E$7\1K$8\2lo$0\1n$0M2\1x@1$2@2$1$0$0P@2$9^4^3\1p@2$1$0$0M1\1p@2$1$0$0P^1\1s$0\1l$0@2$6@2$4@2$3^2^1^5@2$4@2$3^5^4^2$5").

Lemma kentry_apart_b_sem : ltac2:(zQ "h10!h9!iqe!it7!pe!hm8!iv2!jkd!jjb!jc!hf!kkc!kle!uf!hk1!kh1!jk3!km3>1E$c>1M>0@1$3@1$0#k0@1$6@1$3@1$0#8>5allkn@1$5$2>1K$2>2ub$1>2uk$9>2un$1>0@4$f?4SEGS^7^6^5>0@3$8$4@5$a^6^4^3^2^5$7@4$h0^9^6@2$e^9@2$b^5^4@2$d^9^3").
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

Lemma kentry_keep_sem : ltac2:(zQ "e0!h9!pe!jkd!hf!kn2!p0!jc!kje!uf!it7!km3!kj1!l9!le>1E$8>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1K$9>2lo$3>1n$3>0@4$4?4SEGS^6^5^3>0@4$a^7^4^3^2>0>1x@1$1@1$0#k0>0@2$7@2$d@2$5@1$0#k0^1^5@2$c@2$b^5^4@2$5@1$0#k0^1@3$6@1$2@1$1@1$0#8@1^8^2@1^9^2@4$4?4SEGS^9^7^6").
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    ndestruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    ndestruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - (* [comment removed for export] *) ndestruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    ndestruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) ndestruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    ndestruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) ndestruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. ndestruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

Lemma kentry_apart_keep : ltac2:(zQ "h60!h9!pe!jkd!jc!kle!iqe!it7!kh1!kn2!p0!hm8!iv2!jjb!kje!hf!kkc!uf!hk1!jk3!kj1!l9!le>1E$h0>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>5allkn@1$b$6>1K$6>2ub$5>2uk$e>2un$5>0@4$h2?4SEGS^8^7^5>0@4$8?4SEGS^9^8^5>0@3$3$a@5$f^7^5^4^3^6$c>0>1x@1$1@1$0#k0>0@2$d@2$h5@2$9@1$0#k0^1@2$7^c@2$4^7^6@2$h4@2$h3@2$7^c@2$4^7^6@2$h1^c^5@2$9@1$0#k0^1@3$3@1$2@1$1@1$0#8@1^b^2@1^c^2@4$8?4SEGS^c^a^8").
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

Lemma kentry_apart_bp_eq : ltac2:(zQ "90!iqe!it7!hm8!iv2!jc!hf!kkc!kne!kp1>5allkn@1$3$1>2ub$0>2uk$5>2un$0>1K$1@3$4$2@6$7^5@4$8^5^4^3^2^4^3^2^1@5$6^5^4^3^2^1").
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq : ltac2:(zQ "80!it7!iv2!iqe!jc!hf!kpc!kq6!kp1>1k@1$1$0>2ub$2>2uk$4>2un$2>1K$0@3$3@1$1$0@6$6^5@4$7^5^4^3^2^4^3^2^1@5$5^5^4^3^2^1").
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

Lemma know_ok_havoc : ltac2:(zQ "h40!h9!pe!jkd!kle!iqe!kh1!jk3!p0!iv2!jc!kje!hf!kr1!uf!it7!hk1!kvb!kj1!l9!le>1E$d>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1k@1$8$e>1b$4>1o$b>1n$4>0@4$6?4SEGS^7^6^4>0>1x@1$1@1$0#k0>0@2$a@2$h3@2$7@1$0#k0^1@2$5^9@2$3^5^4@2$h2@2$h1@2$5^9@2$3^5^4@2$f^9^3@2$7@1$0#k0^1@3$9@1$2@1$1@1$0#8@1^8^2@1^9^2>0@2$h0^8^7@4$6?4SEGS^a^8@4$c^7^6^5^4").
Proof.
  intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn| | |]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

Lemma split_lit_denot : ltac2:(zQ "d0!iqe!h9!hf!jc!jj2!kg9!jv1!uf!lg8!kj1!o6!pe!p0>1E$7>1e$0>1b$0>1k$2>0@3$3@2$6$0$2@1$8^3@4$5$0$2^2^1@3$3@1$b@1$1#k0@2$4^5^4@2$a@1$1#k0@2$9@2$c@1$1#k0@2$4^5^3^2").
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma flat_x_sound : ltac2:(zQ "h60!h9!j6!kle!jj2!iqe!kh1!l9!pe!p0!hm8!iv2!jkd!jjb!jc!hf!lh4!uf!it7!jk3!kj1!le!m3>1E$h0>1M>0@1$7@1$0#k0@1$b@1$7@1$0#8>1k@1$a$h1>1b$4>3off$e>1n$4>0@4$h2?4SEGS^6^5^4>0@3$d$9@4$f^5^4^3^2$c@2$1@2$6Z@2$5^8@2$2^5^4@2$1@2$6@2$h3@2$5^8@2$2^5^4@2$8@1$0#k0@2$3^8^3@2$h5+2+k0@2$h4Z@2$8@1$0#k0@2$3^8^3").
Proof.
  intros E M k b off n HK H. unfold flat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

End Sound.
End FPX.
End APS.


Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX. Context {fx : XPropExec.FPState}.

Section Specs.
Variable SEGS : ltac2:(zQ "20!iv2!pr7@1$0$1").

Definition kept_ok : ltac2:(zQ "30!h9!jo7!pe>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "d0!h9!pe!jc!lhe!jo7!lm3!hm1!lmb!lmf!lnf!lp9!lpf!lq4\4regs@2$4@1$0#5@1$1@1$0#k0\5regs'@2$4@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@1$3@3$2@1$1@1$0#5^1@3$b@1$0#5ZKv$7@2$c@1$0#5Z>0@1$3@3$a$6@1$9^2$8@3$2@1$1@1$0#k0@2$5^4^3@2$5^5^3").

Definition fill_spec : ltac2:(zQ "10!hf>5entry$0>4cmax$0P") := ltac2:(zQ "hd1!h9!pe!jc!lmb!lm3!lpf!lq4!hf!jo7!o6!p0!j6!lqb!lr3!le!lre!hm8!jkd!jjb!ls7!lsc!mgd!ml7!mpe!mu4!nja!kj1!l9!m3&@3$5@1$0#5+aKv$3@2$6@1$0#5+a\5entry$7\4cmax$7>4mem0>0@1$1@1$0#k0@1$h1@1$1@1$0#8>1s@1$1@1$0#k0>1c@1$1@1$0#k0>1n$7>4regs@2$8@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@2$hbZ^3>0@2$e@2$ha@2$a@1$0#k0^6^4@2$hc+2+k0>0@3$2$h0@4$h5?4SEGS^8^7@1$f^5$h2>0@2$e@2$a@1$0#k0^7^a>0@1$h8^5>0@3$2@1$1@1$0#k0@2$4^7@3$5@1$0#5+1Kv$3@2$6@1$0#5+1^6>0@3$2@1$1@1$0#k0@2$4^8~0^b>0@3$2@1$1@1$0#k0@2$4^9@3$5@1$0#5+bKv$3@2$6@1$0#5+b^b>0@3$2@1$1@1$0#k0@2$4^a@3$5@1$0#5+cKv$3@2$6@1$0#5+c@2$9@1$0#k0^b@2$h3@2$8@1$0#5@1$1@1$0#k0\5regs'@2$8@1$0#5@1$1@1$0#k0@2$b@3$h7?4SEGS@5$c?2fx^c@2$9@1$0#k0^h2^h0@1$d?4SEGS@5$c?2fx^1^b@3$h6^h0^f@3$h4@1$1@1$0#8@2$9@1$0#8@2$a@1$0#k0^e@1$f^d@1$d?4SEGS@2$b@2$h9^c^1@3$2@1$1@1$0#k0@2$4^1~0^f").

Definition copy_spec : ltac2:(zQ "10!hf>5entry$0P") := ltac2:(zQ "i21!h9!pe!jc!p0!lmb!lm3!lpf!lq4!kj1!jqa!iv2!jo7!l9!jkd!j6!hf!lqb!lr3!le!m3!o6!kg1!hm8!hm1!jjb!ls7!kje!mgd!ml7!mpe!mu4!nk5!nja!lre&@3$6@1$0#5+aKv$4@2$7@1$0#5+a\5entry$f>4mem0>0@1$1@1$0#k0@1$d@1$1@1$0#8>3dst@1$1@1$0#k0>3src@1$1@1$0#k0>1n$f>2bs@1$a@1$1@1$0#8>4regs@2$b@1$0#5@1$1@1$0#k0>3ret@1$1@1$0#k0>0@2$cZ^4>0@3$2$h7@2$9@1$1@1$0#8^4@1$i1^5>0@3$2@1$d@1$a@1$1@1$0#8@4$hf?4SEGS^9^7@2$9@1$1@1$0#8^5@2$h5@1$a@1$1@1$0#8^5>0@3$2$h6@4$hb?4SEGS^a^9@2$9@1$1@1$0#8^6$h8>0@2$ha@2$c@2$8@2$3@1$0#k0^a^8@2$3@1$0#k0^9@2$c@2$8@2$3@1$0#k0^9^8@2$3@1$0#k0^a>0@2$h2@2$8@2$3@1$0#k0^a^9@2$h3+2+k0>0@2$h2@2$8@2$3@1$0#k0^c^a@2$h3+2+k0>0@1$he^8>0@3$2@1$1@1$0#k0@2$5^a@3$6@1$0#5+1Kv$4@2$7@1$0#5+1^9>0@3$2@1$1@1$0#k0@2$5^b~0^f>0@3$2@1$1@1$0#k0@2$5^c@3$6@1$0#5+bKv$4@2$7@1$0#5+b^f>0@3$2@1$1@1$0#k0@2$5^d@3$6@1$0#5+cKv$4@2$7@1$0#5+c@2$h4@1$0#k0^f@2$h9@2$b@1$0#5@1$1@1$0#k0\5regs'@2$b@1$0#5@1$1@1$0#k0@2$e@3$hd?4SEGS@5$h0?2fx^f@2$h4@1$0#k0^h5^h4@1$h1?4SEGS@5$h0?2fx^1^e@3$hc^h4^h3^h0@1$h1?4SEGS@2$e@2$i0^f^1@3$2@1$1@1$0#k0@2$5^1~0^h3").

End Specs.

Lemma reg_of_ridx : ltac2:(zQ "70!h9!hm1!jc!pe!lnf!ki2!o6>1r@1$3@1$0#5>1n$1>0@3$2$1@1$4^2^1@3$2@1$3@1$0#5^3@2$6@1$0#5@1$5^2").
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : ltac2:(zQ "h10!h9!pe!jc!iqe!iv2!lmb!lhe!jua!jo7!u8!jj2!uf!lnf!jl7!lm3!lpf!lq4>1E$b>2sr@1$4$3>1R@2$8@1$0#5@1$1@1$0#k0>0>1r@1$1@1$0#5>0@1$6@3$2@1$1@1$0#5^1@3$f@1$0#5ZKv$5@2$h0@1$0#5Z@3$2@1$1@1$0#k0@2$e^3^2@2$a^5@4$7$3@1$c^2^4@1$9Z@3$d^4^3^2").
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : ltac2:(zQ "30!hm1!lmf!nkc@2$2$0$1").
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : ltac2:(zQ "90!hm1!iqe!iv2!jua!u8!jc!lhe!nl5!lp9>3cs0@1$2$0>2nx$0>2sr@1$2$1>1i$0>0@1$6@3$8$0^1^4@3$5$1@4$3$1^2@3$7^3^5^4@1$4Z@4$3$1^2^3@1$4Z").
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : ltac2:(zQ "c0!hm1!iqe!iv2!jua!jqa!jc!js6!jsd!nl5!u8!nm1!nkc>3cs0@1$2$0>2nx$0>2sr@1$2$1>1j$0>0@2$b$0^4>0@2$7^2@2$4$0^5@3$5$1@4$3$1@4$3$0^3^6N0@3$8^4^6^5@1$9Z@1$a@2$6^5^3").
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

Definition ext_call : ltac2:(zQ "50!h9!uf!hm1!jo7!pe>1E$1>2nx$2>2R'@2$3@1$0#5@1$4@1$0#k0$1") := ltac2:(zQ "h40!h9!hm1!hm8!pe!nm8!js6!nn0!jua!jo7!nn7!lmf!hn0!hn6!uf!hnb!lm3!nne!no5!ki2!o6\1E$d\2nx$1\2R'@2$8@1$0#5@1$3@1$0#k0@2$b\1n$1M2\0$2@1$3@1$0#k0@2$4@2$h0^3^1@2$h1^1@2$5^3$9@2$f^2@2$h3@1$0#5@1$h2@4$7$1@2$6^1^3$aN0@2$e^4^1@1$c^3").

Lemma ext_call_agree : ltac2:(zQ "70!h9!hm1!jo7!uf!hu2!nt2!pe>1E$3>2nx$1>2R'@2$2@1$0#5@1$6@1$0#k0@3$4^2^3@3$5^3^2^1").
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : ltac2:(zQ "h00!h9!hm1!pe!jc!js6!jsd!jua!jo7!nn7!lmf!uf!hnb!lm3!nt2!ki2!o6>1E$a>2nx$1>2R'@2$7@1$0#5@1$2@1$0#k0>1j$1>0@2$5^1$8@3$3@1$2@1$0#k0@2$b@3$d^5^4^3@2$4^4^2@2$c^3@2$f@1$0#5@1$e@4$6$1^2$9N0").
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : ltac2:(zQ "b0!hm8!hm1!jjb!jc!iqe!iv2!jsd!jua!ipe!jh6!u8>1b$1>2sr@1$5$4>1r$1>0@3$3$0@2$9^3^2$2>0@2$6^2Ni0@3$3$0@2$8^5@4$7$4^3^4@1$aZ$2").
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma regs_after_call : ltac2:(zQ "h80!iqe!h9!jkd!jc!pe!hm8!iv2!jjb!jo7!lmf!nl5!jl7!hm1!kj7!j6!ipe!jh6!jj2!uf!nte!lm3!nt2!nu7!o6>1E$h2>2sr@1$6$0>1R@2$8@1$1#5@1$4@1$1#k0>2R'@2$8@1$1#5@1$4@1$1#k0>2nx$c>2rv@1$2$0>0@3$b^6^5^4>0@3$3$5@2$h0^3^6$7>0@2$h6^6^5>0M2\2rv@1$2$0P^4\1e$0@2$e@3$3$5@2$f^6^1$7@3$3@1$4@1$1#k0@2$h4^7@2$h7@1$1#5+a@2$h1^a^1$d@3$b@3$h5^a^6^7M2\2rv@1$2$0@1$6$0^5\1e$0@3$h3@3$a^a$9^7Na^1@3$a^9$9^6^7").
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - ndestruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

Section KnowTests.
Variable segs : ltac2:(zQ "20!iv2!pr7@1$0$1").

Lemma adenot_SA : ltac2:(zQ "a0!h9!kle!jc!hf!nv2!uf!iqe!kh1!o6!pe>1E$5>1b$6>3off$3@3$2@1$9@1$0#k0@2$4^3@2$1^2^1@2$8@1$0#k0@2$7^3@2$1^2^1").
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

Lemma kwritable_x_sound : ltac2:(zQ "h80!h9!kle!kh1!l9!hm8!iv2!jjb!j6!jc!iqe!it7!hk1!jk3!pe!hm1!jkd!hf!mgd!nvb!uf!kj1!ki2!m3!o6>1E$h3>1M>0@1$d@1$0#k0@1$f@1$d@1$0#8>5allkn@1$5$a>1k@1$5$a>1b$9>3off$h0>1n$9>0@4$c?4segs^7^6^5>0@4$c?4segs^8^7^5>0@3$8$4@5$h2^7^6^5^4^3$6@2$7>1m$e>0@2$3@1$h5^1@2$b^b^5@3$8$4@4$h1?4segs^b@2$h7@1$0#k0@2$2^c@2$1^8^7^2$6@2$7@2$3Z@2$2^a@2$1^6^5@2$3@2$h4@2$2^a@2$1^6^5@2$b^a^4@2$h6+2+k0").
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. ndestruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

Definition piece_ok : ltac2:(zQ "70!h9!iqe!pe!hm1!jkd!hf!uf>1E$6>1M>0@1$2@1$0#k0@1$4@1$2@1$0#8>1b$1>3off$5>1w$3>1v$1P") := ltac2:(zQ "h30!h9!pe!iv2!jc!hm1!jkd!j6!iqe!kg1!jqa!ls7!hf!oga!kle!jj2!uf!kh1!nk5!o6\1E$f\1M>0@1$1@1$0#k0@1$5@1$1@1$0#8\1b$7\3off$b\1w$4\1v$7@2$a@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@2$6@3$3@1$5@1$2@1$1@1$0#8@4$h1?4segs^6@2$h2@1$0#k0@2$h0^7@2$d^5^4^3@2$8@1$2@1$1@1$0#8^1@2$6@3$3$4@2$9@1$1@1$0#8^1^3@3$3@1$2@1$1@1$0#8@2$c^3@2$e^7^2^1").

Lemma land_shl_disjoint : ltac2:(zQ "80!hf!l9!m3!j6!jc!ohf!le!oi6>1a$0>1b$0>1k$0>0@2$1Z^3>0@2$1Z^2>0@2$3@2$1Z^4@2$6^4@2$2+2^3@3$4$0@2$5@2$7^6@2$2+2^4^5Z").
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : ltac2:(zQ "90!hf!l9!m3!oi6!j6!jc!kj1!oic!le>1a$0>1b$0>1k$0>0@2$1Z^3>0@2$1Z^2>0@2$4@2$1Z^4@2$8^4@2$2+2^3@3$5$0@2$7@2$3^6@2$2+2^4^5@2$6@2$3^6@2$2+2^4^5").
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : ltac2:(zQ "70!h9!pe!iv2!jqa!jc!om1!on2>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$5@2$3@1$1@1$0#8^1@1$6^1^1").
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : ltac2:(zQ "90!h9!pe!jqa!iv2!jc!il6!on2!oga!o6>2bs@1$3@1$1@1$0#8>0@2$5@2$2@1$1@1$0#8^1N8@3$4@1$3@1$1@1$0#8@2$7@2$2@1$1@1$0#8^2@2$8@1$0#k0@1$6^2^2").
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma lookup_piece : ltac2:(zQ "h80!oo3!hm8!iv2!il6!h9!iqe!ooa!pe!op5!hm1!jkd!j6!jc!hf!ope!kle!uf!it7!oq5!or3!ora!jk3!ph1!ki2>1E$h0>1M>0@1$7@1$4#k0@1$a@1$7@1$4#8>1k@1$2$h1>1b$5>3off$d>1w$9>1v$5>2hs@1$2$1>0@4$h5?4segs^8^7^6>0@2$b@2$3N1^4@2$3^4N8>0@3$c$h3@8$h2?4segs^8^7^6^5$8@1$0$1@1$0$6@3$e^4@1$0$6^3>0@3$h4^b@2$f^8^7@1$h7^6@6$h6^c^b^9^8^7^6").
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. ndestruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : ltac2:(zQ "f0!iqe!jkd!h9!pe!kg1!iv2!jc!hf!phd!kle!uf!it7!ora!jk3!ph1>1E$a>1M>0@1$3@1$2#k0@1$1@1$3@1$2#8>1k@1$5$b>1b$0>3off$7>1v$0>0@4$d?4segs^6^5^4>0@3$6@1$1$0@4$8?4segs^5^4^3@2$4$0^2>0@3$c^8@2$9^5^4+8@6$e^9^8^6^5N8^4").
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : ltac2:(zQ "h60!h9!pe!hf!iv2!jkd!kg1!j6!jc!kle!o6!pi8!oo3!pj0!uf!iqe!it7!kh1!ora!jk3!nk5!l9!le>1E$d>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>1k@1$3$f>1b$e>3off$2>1z$2>0@4$h2?4segs^6^5^4>0@3$7@1$4$2@5$c?4segs^5^4^3N1@2$5$2^2>0@3$h1^8@2$8^5^4+1@2$6@3$7@1$4@1$3@1$1@1$0#8@4$h3?4segs^8@2$9@1$0#k0@2$h0^9@2$8^6^5N1@2$5@1$3@1$1@1$0#8@3$a@1$1@1$0#8@2$9@1$0#8^4@1$b@1$1@1$0#8@2$6@2$h4Z^4@2$h5^4+hg0").
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. ndestruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : ltac2:(zQ "ha0!hf!h9!iv2!pe!jkd!j6!jc!kle!kh1!l9!kg1!hm1!o6!jqa!pja!pk4!pkb!uf!iqe!it7!jk3!nk5!kj1!le!ki2!m3>1E$h1>1M>0@1$3@1$1#k0@1$4@1$3@1$1#8>1k@1$2$h3>3len$b>1b$h2>3off$0>2zs@1$2$0>0@4$h4?4segs^7^6^5>0@3$6@1$4@1$2$0@5$h0?4segs^5^6^4^3@2$a@1$2$0^2>0@2$9Z@2$8^9@2$7^5^4>0@2$9@2$h6@2$8^a@2$7^6^5@1$h8^7@2$h9+2+k0@2$5@3$6@1$4@1$2@1$3@1$1#8@4$h5?4segs^a@2$c@1$1#k0@2$8^b@2$7^7^6^8@2$a@1$2@1$3@1$1#8@4$f$0@1$3@1$1#8\1z$0@2$c@1$1#8^1^5@2$5@3$6$b@2$d$0^5^8@3$e$0\1z$0@2$5@2$9Z^1@2$h7^1+hg0^5").
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    ndestruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : ltac2:(zQ "d0!hf!h9!iv2!j6!jc!pja!pk4!on2!pla!l9!le!o6!pe>2zs@1$2$0>0@3$5$0\1z$0@2$3@2$9Z^1@2$a^1+hg0^1@3$4$0@1$8^2@1$7@4$6$0@1$c@1$1#8\1z$0@2$b@1$1#8^1^2").
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma copy_facts_sound : ltac2:(zQ "h91!h9!pe!iv2!kle!kh1!jkd!l9!jc!it7!lre!kg1!hf!hm1!j6!iqe!jk3!nk5!kj1!m3!o6!jqa!ls7!il6!pmb!uf&>0@1$1@1$0#k0@1$5@1$1@1$0#8>1E$h8>1M~0>1k@1$2$8>2sb$e>2db$e>4fuel$c>2sk$b>2dk$b>1n$b>2kc@1$2$8>0@4$f?4segs^a^9^8>0@3$7@1$5@1$2$8@8$h7?4segs^6^9^8^5^7^4^3@2$a@1$2$8^2>0@2$6Z^4>0@2$h6@1$9^5^8>0@2$6Z@2$4^e@2$3^b^8>0@2$6@2$h1@2$4^f@2$3^c^9^7@2$h2+2+k0>0@2$6Z@2$4^h0@2$3^c^9>0@2$6@2$h1@2$4^h1@2$3^d^a^9@2$h2+2+k0@2$h5@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@2$d@3$7$c@2$h4@1$1@1$0#8^1@1$9^b@2$d@3$7@1$5@1$2@1$1@1$0#8@4$h0?4segs^h2@2$h3@1$0#k0@2$4^h3@2$3^h0^d@1$9^b@2$a@1$2@1$1@1$0#8^1>2M'~0>0@3$7@1$5@1$2@1$1@1$0#8@4$h0?4segs^1@2$h3@1$0#k0@2$4^h4@2$3^h0^d@1$9^c@2$a@1$2@1$1@1$0#8^2@4$f?4segs^h5^2^c").
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* [comment removed for export] *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { (intros w v kr Hw Hwn nd_i1 Hr ->; ndestruct nd_i1 as (bsP & HrdP & HlenP & HvP)).
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      ndestruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        ndestruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

Section W.
Variable SEGS : ltac2:(zQ "20!iv2!pr7@1$0$1").

Lemma w_split_lit_denot : ltac2:(zQ "d0!iqe!h9!hf!jc!jj2!kg9!jv1!uf!lg8!kj1!o6!pe!p0>1E$7>1e$0>1b$0>1k$2>0@3$3@2$6$0$2@1$8^3@4$5$0$2^2^1@3$3@1$b@1$1#k0@2$4^5^4@2$a@1$1#k0@2$9@2$c@1$1#k0@2$4^5^3^2").
Proof. intros. eapply split_lit_denot; eassumption. Qed.

Lemma w_know_ok_havoc : ltac2:(zQ "h40!h9!pe!jkd!kle!iqe!kh1!jk3!p0!iv2!jc!kje!hf!kr1!uf!it7!hk1!kvb!kj1!l9!le>1E$d>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1k@1$8$e>1b$4>1o$b>1n$4>0@4$6?4SEGS^7^6^4>0>1x@1$1@1$0#k0>0@2$a@2$h3@2$7@1$0#k0^1@2$5^9@2$3^5^4@2$h2@2$h1@2$5^9@2$3^5^4@2$f^9^3@2$7@1$0#k0^1@3$9@1$2@1$1@1$0#8@1^8^2@1^9^2>0@2$h0^8^7@4$6?4SEGS^a^8@4$c^7^6^5^4").
Proof. intros. eapply know_ok_havoc; eassumption. Qed.

Lemma w_flat_x_sound : ltac2:(zQ "h60!h9!j6!kle!jj2!iqe!kh1!l9!pe!p0!hm8!iv2!jkd!jjb!jc!hf!lh4!uf!it7!jk3!kj1!le!m3>1E$h0>1M>0@1$7@1$0#k0@1$b@1$7@1$0#8>1k@1$a$h1>1b$4>3off$e>1n$4>0@4$h2?4SEGS^6^5^4>0@3$d$9@4$f^5^4^3^2$c@2$1@2$6Z@2$5^8@2$2^5^4@2$1@2$6@2$h3@2$5^8@2$2^5^4@2$8@1$0#k0@2$3^8^3@2$h5+2+k0@2$h4Z@2$8@1$0#k0@2$3^8^3").
Proof. intros. eapply flat_x_sound; eassumption. Qed.

Lemma split_lit_vars : ltac2:(zQ "a0!iqe!jc!hf!hm8!jjb!ipe!hm1!kg9!jv1!lg8>1e$0>1b$0>1k$2>1m$6>0@3$1@2$8$0$2@1$9^4@4$7$0$2^3^2>0@3$1$3@2$5^2^5$4@3$1$3@2$5^3^5$4").
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma wbytes_fill_at : ltac2:(zQ "h00!h9!pe!jkd!hf!kj1!l9!p0!kg1!j6!jc!lsc!ml7!le!m3!lre!o6>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>1s@1$1@1$0#k0>1b@1$1@1$0#8>1n$3>1i$3>0@2$5@2$4@2$6@1$0#k0^4^2@2$d+2+k0>0@2$8@2$5Z^2@2$c^2^3@3$9@1$2@1$1@1$0#8@4$b^7^6@3$a@1$1@1$0#8^5@1$e^4@2$f@1$0#k0@2$4@2$6@1$0#k0^6^3@2$7@1$1@1$0#8^5").
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : ltac2:(zQ "60!h9!o6!jc!hf!pn9!pe>1c$3@3$2@1$5@1$0#8@2$1@1$0#8@2$4^1+hg0@2$1@1$0#8^1").
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

End W.

End FPX.
End APSX.
(* [comment removed for export] *)
