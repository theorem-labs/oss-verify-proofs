(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec SeqExec StoreOk AgentLib Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsPrintfFirst.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hc4exprhc4EAluhc4ELit3h5LinuxProcessSemantics5Riscv5Instrn07ALU_ADDn07ALU_ANDn07ALU_SRLhc4EVar46Stdlib6ZArith6BinInt1Zr93addr93divr93mul04Nposr92le35stdpp9bitvectorbdefinitionsuebbv_unsigned37Corelib4Init5Logichh92eque2bvhh93and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hjf6ASP_HIhjf6ASP_LO89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsSxKit4FPX1~~~~~~hq43shwhq43shxhc6edenothc3envhc2evr93sub37Corelib4Init9Datatypesige6optionue7Z_to_bvige4Someige4list37Corelib5Lists7ListDefika6Forallhq44shkn79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~in37know_ok69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~is3floaded_segmentsr92ltika3mapige4consige3nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsji6h0word_to_le_byteshc2SAin36estartr96of_natige3nathq46kbyteshq46zbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jq53rdnhc6kentryin34flatr93pow" s.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition shx : ltac2:(zQ "20!h9!lb>1o$0$1") := ltac2:(zQ "70!m2!m9!p4!h9!pe!q8!r2\1o$3@3$0$4@3$0$2@3$0$5@3$0$2@1$6N0@1$1^1@1$1+3@1$1+nvvvogg0@1$1-8").
Definition shw : ltac2:(zQ "10!h9>3spz$0>1o$0$0") := ltac2:(zQ "40!h9!t1!t7!td\3spz$0\1o$0@2$3+8@2$2@2$1@2$2@2$1^2^1+8+nvvvogg0+8").

Lemma shx_denot : ltac2:(zQ "e0!u3!u9!hgb!hid!h9!hj3!hj8!hp0!hpa!hu6!hud!hv4!hvd!ig3>1E$c>2sp@1$5@1$0#k0>1o$4>0@3$3@1$5@1$0#k0@2$d^3N0^2>0@2$1$8@2$2@1$0#k0^3>0@2$1@2$2@1$0#k0^4$7>0@2$6@2$1-hggg0^4@2$1^4Z@3$3$4@2$2@1$0#k0@2$b^7@1$a^5@2$9@2$2@1$0#k0^6^5").
Proof.
  intros E sp o E0 Hlo Hhi Ho. unfold ASP_LO, ASP_HI in *. unfold shx, shw. cbn [edenot]. rewrite E0.
  cbn [alu64 alu].
  rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  change (3 mod 2 ^ 64)%Z with 3%Z. change (63 mod 2 ^ 64)%Z with 63%Z.
  change (Z.land 3 63) with 3%Z. change (2147450880 mod 2 ^ 64)%Z with 2147450880%Z.
  change ((-8) mod 2 ^ 64)%Z with 18446744073709551608%Z.
  replace ((bv_unsigned sp + o mod 2 ^ 64) mod 2 ^ 64)%Z with (bv_unsigned sp + o)%Z.
  2:{ rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
  rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
  rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma shw_range : ltac2:(zQ "90!u9!hu6!hj8!t1!h9!hp0!hpa!t7!ig8>3spz$4>1o$4>0@2$2@2$0$6^2@2$0^2$5>0@2$2@2$0-vs0^2@2$0^2-k0@2$2@2$2@2$0@2$1$6^3@2$1^4^3@2$0@2$1^4^3@2$1$5^3@2$2@2$0@2$3+nvvvogg0@2$7@2$8^4+hgg0+8@2$1^4^3@2$0@2$3@2$1^4^3+8@2$3+nvvvogg0@2$7^4+8").
Proof.
  (* [comment removed for export] *)
  intros spz o H Ho. unfold ASP_LO, ASP_HI in *.
  assert (M8 : forall a b, (a <= b -> a / 8 <= b / 8)%Z) by (intros; apply Z.div_le_mono; lia).
  assert (MONO : forall s1 s2, (s1 <= s2 -> shw s1 o <= shw s2 o)%Z).
  { intros s1 s2 Hs. unfold shw. pose proof (M8 (s1 + o) (s2 + o))%Z.
    pose proof (M8 ((s1 + o) / 8 + 2147450880) ((s2 + o) / 8 + 2147450880))%Z. lia. }
  split; [split; apply MONO; lia|]. unfold shw.
  set (q := ((spz + o) / 8)%Z). assert (8 * q <= spz + o < 8 * q + 8)%Z by (subst q; Z.div_mod_to_equations; lia).
  set (r := ((q + 2147450880) / 8)%Z). assert (8 * r <= q + 2147450880 < 8 * r + 8)%Z by (subst r; Z.div_mod_to_equations; lia).
  set (t := ((spz - 4096) / 8)%Z). assert (8 * t <= spz - 4096 < 8 * t + 8)%Z by (subst t; Z.div_mod_to_equations; lia).
  set (u := (spz / 8)%Z). assert (8 * u <= spz < 8 * u + 8)%Z by (subst u; Z.div_mod_to_equations; lia).
  lia.
Qed.

(* [comment removed for export] *)
Fixpoint shkn (offs : list Z) : list kentry :=
  match offs with
  | [] => []
  | o :: r => KRange (shx o) (shw ASP_LO o) (shw ASP_HI o) :: KZero (SA (shx o) 0) (ELit 8) :: shkn r
  end.

Lemma shkn_ok : ltac2:(zQ "h70!u3!hj3!u9!h9!hgb!ii6!hj8!hid!t1!t7!ij0!ija!ik2!im1!hp0!hpa!imb!hvd!ig3!ir8!iv8!jgb!ig8>1E$h1>3mem>1x@1$1@1$0#k0@1$5@1$1@1$0#8>2sp@1$1@1$0#k0>4offs@1$c$3>0@3$7@1$1@1$0#k0@2$h2^4N0^2>0@2$2$f@2$4@1$0#k0^3>0@2$2@2$4@1$0#k0^4$e>0@3$d$3\1o$3@2$6@2$2-vs0^1@2$2^1-k0^4>0>1a$3>0@2$6@2$2@2$8+nvvvogg0@2$9@2$h6@2$4@1$0#k0^7+hgg0+8^1@2$h5^1@2$8+nvvvogg0@2$9@2$4@1$0#k0^7+8@3$7@1$5@1$1@1$0#8@1^9@2$a@1$0#k0^2@2$b@1$1@1$0#8@2$a@1$0#8Z@4$h3$h4^9^8@1$h0^6").
Proof.
  intros E mem sp offs E0 Hlo Hhi Hoffs Qsh0. induction offs as [|o r IH]; [constructor|].
  inversion Hoffs as [|o' r' Ho Hr]; subst o' r'.
  pose proof (shx_denot E sp o E0 Hlo Hhi ltac:(lia)) as SHX.
  npose (shw_range (bv_unsigned sp) o (conj Hlo Hhi) Ho) as (SR1 & SR2 & SR3).
  cbn [shkn]. constructor; [|constructor; [|apply IH; exact Hr]].
  - apply krange_intro. rewrite SHX. exact SR1.
  - eapply (kzero_intro RSEGS E mem (shx o) (edenot E (shx o)) 0 (ELit 8) 8);
      [reflexivity | reflexivity | rewrite SHX; unfold ASP_LO in *; clear - SR2 Hlo; Z.div_mod_to_equations; lia | lia
      | rewrite SHX; unfold ASP_HI in *; clear - SR3 Hhi; Z.div_mod_to_equations; lia |].
    intros i Hi. rewrite SHX. apply Qsh0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint kbytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kread RSEGS kn b k 1, kbytes kn b (k + 1) n' with
            | Some (ELit v), Some r => Some (v :: r)
            | _, _ => None
            end
  end.
Definition zbytes : ltac2:(zQ "40!ik2!u3!h9!hj3>2vs@1$0$2@1$0@1$3@1$1#8") := ltac2:(zQ "60!h9!u3!ik2!jh0!ij0!hj3\2vs@1$2$0@4$3$0@1$5@1$1#8\1v$0@2$4@1$1#8^1^1").

Lemma word_to_le_bytes_1 : ltac2:(zQ "90!u3!hj3!ij0!jh7!ik2!jhf!hid!h9!jld>1v$7@3$6@1$4@1$1@1$0#8@2$8N1@2$2@1$0#k0^1@3$3@1$1@1$0#8@2$2@1$0#8^1@1$5@1$1@1$0#8").
Proof.
  intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate.
Qed.

Lemma kbytes_rdn : ltac2:(zQ "h80!ik2!u3!h9!hj3!ii6!jn2!ija!hid!jn7!iv8!jo1!joa!jp1!jpb!ju0!hvd!lb!ju7!jv0!ir8!t1!jgb!jv8!ij0>1E$f>1M>0@1$3@1$1#k0@1$4@1$3@1$1#8>2kn@1$0$h1>1b$h0>1n$b>1k$2>2vs@1$0$2>0@4$h3$9^7^6^5>0@3$7@1$4@1$0$2@4$c^6^5^3^4@2$6@1$0$2^2>0@3$h2^9@2$5^6^4@1$a^5>0@2$h5@2$h4@2$8^a@2$5^7^5@1$a^6@2$h6+2+k0@3$7@1$4@1$0@1$3@1$1#8@4$e$9^a@2$h7@1$1#k0@2$8^b@2$5^8^6^7@2$6@1$0@1$3@1$1#8@1$d^5").
Proof.
  intros E M kn b n. induction n as [|n IH]; intros k vs HK Hb Hf Hlt.
  - cbn in Hb. injection Hb as <-. reflexivity.
  - cbn [kbytes] in Hb. destruct (kread RSEGS kn b k 1) as [[v| | | | | | |]|] eqn:Hr; try discriminate.
    destruct (kbytes kn b (k + 1) n) as [r|] eqn:Hr2; [|discriminate]. injection Hb as <-.
    change (S n) with (1 + n)%nat. cbn [zbytes map].
    change (Z_to_bv 8 v :: map (fun v0 => Z_to_bv 8 v0) r) with ([Z_to_bv 8 v] ++ zbytes r).
    assert (Hf1 : flat E (SA b k) (Z.of_nat 1)) by (unfold flat in *; cbn [Z.of_nat] in *; lia).
    pose proof (kread_rdn RSEGS E M kn b k 1 (ELit v) HK Hr ltac:(lia) ltac:(lia) Hf1) as R1.
    assert (R1' : rdn RSEGS M (Z_to_bv 64 (estart E (SA b k))) 1 = Some [Z_to_bv 8 v]).
    { rewrite <- (flat_u E _ _ Hf1), Z_to_bv_bv_unsigned. cbn [edenot] in R1. rewrite word_to_le_bytes_1 in R1. exact R1. }
    apply rdn_app_Z; [exact R1' | | unfold flat in Hf1; lia | lia].
    assert (Hf2 : flat E (SA b (k + 1)) (Z.of_nat n)) by (unfold flat, estart in *; cbn [a_base a_off Z.of_nat] in *; lia).
    replace (estart E (SA b k) + Z.of_nat 1)%Z with (estart E (SA b (k + 1))) by (unfold estart; cbn [a_base a_off]; lia).
    apply IH; [assumption | assumption | assumption | unfold estart in *; cbn [a_base a_off] in *; lia].
Qed.

(* [comment removed for export] *)
Lemma kbytes_rdn_sp : ltac2:(zQ "h80!u3!ik2!hj3!h9!t1!ii6!hid!hgb!ija!joa!iv8!jp1!jpb!ju0!r2!hvd!ig3!ju7!ir8!u9!jgb!jo1!jv8!ij0>1E$f>1M>0@1$2@1$0#k0@1$5@1$2@1$0#8>2kn@1$1$h1>1i$9>2sp@1$2@1$0#k0>1k$3>1n$9>2vs@1$1$3>0@4$h2$a^8^7^6>0@3$6@1$2@1$0#k0@2$h0^9^6^5>0@3$6@1$5@1$1$3@4$b^8@1$e^7^5^4@2$8@1$1$3^3>0@2$h3Z@2$4@2$7@1$0#k0^7^6>0@2$h4@2$4@2$4@2$7@1$0#k0^8^7@1$h5^6@2$h6+2+k0@3$6@1$5@1$1@1$2@1$0#8@4$d$a^c@2$h7@1$0#k0@2$4@2$7@1$0#k0^9^8^7@2$8@1$1@1$2@1$0#8@1$c^6").
Proof.
  intros E M kn i sp k n vs HK Ei Hb H0 H1.
  assert (ES : estart E (SA (EVar i) k) = (bv_unsigned sp + k)%Z) by (unfold estart; cbn [a_base a_off edenot]; rewrite Ei; reflexivity).
  rewrite <- ES. apply (kbytes_rdn E M kn (EVar i) n k vs HK Hb); [unfold flat; rewrite ES; lia | rewrite ES; lia].
Qed.
End FPX1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
