(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf7Z_to_bv37Corelib4Init5Logick62eq01Z46Stdlib6ZArith6BinInt1Zm26modulom23powhf2bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~oe5v_addm23addoe5v_subm23suboe5v_mulm23mulhfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hg16edenothg14expr3h5LinuxProcessSemantics5Riscv5Instrhl27ALU_ADDhg14EAluhg13envhl27ALU_SUBhl25M_MULhg13EMdhg14ELit37Corelib4Init9Datatypeshr33nathg14EVarhg12evk63andm22lem22lthr34bool3h5LinuxProcessSemantics5Riscv7Preludehv86bv_eqbm23eqbhv86bv_ltum23ltbhv86bv_ltshr34listhr36optionhr34Someoe3rdnm26of_nathr33app37Corelib4Init3Natin83add3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeip17Segmentk61Ik63not69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~itbccallee_saved36Stdlib5Lists4Listjia2Inhf2BVhf4BvWfhr36length37Corelib4Init5Peanojl92lthv85bvmapoe4getr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~jo39junk_vals69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jsb7vals_evoe7v_addiwhr34conshr33nil37Corelib5Lists7ListDefki83nth" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma zbv_mod : ltac2:(zQ "70!h9!jc!la!lf!na!o3!o9>1z$3@3$2@1$6@1$0#k0@2$1@1$0#k0@2$4^1@2$5+2+k0@2$1@1$0#k0^1").
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Z.mod_mod. lia.
Qed.

Lemma vadd_ZZ : ltac2:(zQ "70!h9!jc!lf!la!s9!t1!o9>1x$2>1y$2@3$3@1$6@1$0#k0@2$4@2$1@1$0#k0^2@2$1@1$0#k0^1@2$1@1$0#k0@2$5^2^1").
Proof.
  intros x y. unfold v_add. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Z.add_mod by lia. apply zbv_mod.
Qed.

Lemma vsub_ZZ : ltac2:(zQ "70!h9!jc!lf!la!t7!tf!o9>1x$2>1y$2@3$3@1$6@1$0#k0@2$4@2$1@1$0#k0^2@2$1@1$0#k0^1@2$1@1$0#k0@2$5^2^1").
Proof.
  intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Zminus_mod. apply zbv_mod.
Qed.

Lemma vmul_ZZ : ltac2:(zQ "70!h9!jc!lf!la!u5!ud!o9>1x$2>1y$2@3$3@1$6@1$0#k0@2$4@2$1@1$0#k0^2@2$1@1$0#k0^1@2$1@1$0#k0@2$5^2^1").
Proof.
  intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- zbv_mod, <- Z.mul_mod by lia. apply zbv_mod.
Qed.

Lemma word_Z : ltac2:(zQ "50!h9!o9!la!jc!v3>1w@1$1@1$0#k0@3$2@1$1@1$0#k0^1@2$3@1$0#k0@2$4@1$0#k0^1").
Proof. intros w. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma vadd_wZ : ltac2:(zQ "80!h9!jc!o9!la!lf!s9!t1!v3>1w@1$2@1$0#k0>1y$4@3$3@1$2@1$0#k0@2$5^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6@2$7@1$0#k0^2^1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_Zw : ltac2:(zQ "80!h9!jc!o9!la!lf!s9!t1!v3>1x$4>1w@1$2@1$0#k0@3$3@1$2@1$0#k0@2$5@2$1@1$0#k0^2^1@2$1@1$0#k0@2$6^2@2$7@1$0#k0^1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vadd_ZZ. Qed.
Lemma vadd_ww : ltac2:(zQ "70!h9!o9!v3!la!s9!t1!jc>1w@1$1@1$0#k0>2w'@1$1@1$0#k0@3$3@1$1@1$0#k0@2$4^2^1@2$6@1$0#k0@2$5@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof. intros. reflexivity. Qed.
Lemma vsub_wZ : ltac2:(zQ "80!h9!jc!o9!la!lf!t7!tf!v3>1w@1$2@1$0#k0>1y$4@3$3@1$2@1$0#k0@2$5^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6@2$7@1$0#k0^2^1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vsub_Zw : ltac2:(zQ "80!h9!jc!o9!la!lf!t7!tf!v3>1x$4>1w@1$2@1$0#k0@3$3@1$2@1$0#k0@2$5@2$1@1$0#k0^2^1@2$1@1$0#k0@2$6^2@2$7@1$0#k0^1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vsub_ZZ. Qed.
Lemma vmul_wZ : ltac2:(zQ "80!h9!jc!o9!la!lf!u5!ud!v3>1w@1$2@1$0#k0>1y$4@3$3@1$2@1$0#k0@2$5^2@2$1@1$0#k0^1@2$1@1$0#k0@2$6@2$7@1$0#k0^2^1").
Proof. intros w y. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.
Lemma vmul_Zw : ltac2:(zQ "80!h9!jc!o9!la!lf!u5!ud!v3>1x$4>1w@1$2@1$0#k0@3$3@1$2@1$0#k0@2$5@2$1@1$0#k0^2^1@2$1@1$0#k0@2$6^2@2$7@1$0#k0^1").
Proof. intros x w. rewrite (word_Z w) at 1. apply vmul_ZZ. Qed.

(* [comment removed for export] *)
Lemma ed_add : ltac2:(zQ "90!hk0!hka!la!h9!hn6!s9!ho1!ho9!o9>1E$7>1a$1>1b$1@3$2@1$8@1$3#k0@2$0^3@3$6$4^2^1@2$5@2$0^3^2@2$0^3^1").
Proof. intros. cbn [edenot]. apply alu_add. Qed.
Lemma ed_sub : ltac2:(zQ "90!hk0!hka!la!h9!hp0!t7!ho1!ho9!o9>1E$7>1a$1>1b$1@3$2@1$8@1$3#k0@2$0^3@3$6$4^2^1@2$5@2$0^3^2@2$0^3^1").
Proof. intros. cbn [edenot]. apply alu_sub. Qed.
Lemma ed_mul : ltac2:(zQ "90!hk0!hka!la!h9!hpb!u5!hq4!ho9!o9>1E$7>1a$1>1b$1@3$2@1$8@1$3#k0@2$0^3@3$6$4^2^1@2$5@2$0^3^2@2$0^3^1").
Proof. intros. cbn [edenot]. apply m_mul. Qed.
Lemma ed_lit : ltac2:(zQ "80!h9!la!lf!hqb!hk0!ho9!jc!o9>1E$5>1z$2@3$1@1$7@1$0#k0@2$4^2@1$3^1@2$6@1$0#k0^1").
Proof. reflexivity. Qed.
Lemma ed_var : ltac2:(zQ "80!hsb!la!h9!ht2!hk0!ho9!hta!o9>1E$5>1n$0@3$1@1$7@1$2#k0@2$4^2@1$3^1@2$6^2^1").
Proof. reflexivity. Qed.
End FPX1.

(* [comment removed for export] *)
Ltac not_arith t :=
  lazymatch t with
  | v_add _ _ => fail | v_sub _ _ => fail | v_mul _ _ => fail | Z_to_bv _ _ => fail
  | _ => idtac
  end.

Ltac ed_lin pins :=
  rewrite ?ed_add, ?ed_sub, ?ed_mul, ?ed_lit, ?ed_var, ?alu_add, ?alu_sub, ?m_mul; cbn [ev];
  pins;
  repeat match goal with
         | |- context [v_add (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vadd_ZZ x y)
         | |- context [v_sub (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vsub_ZZ x y)
         | |- context [v_mul (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (vmul_ZZ x y)
         | |- context [v_add ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vadd_wZ w y)
         | |- context [v_add (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vadd_Zw x w)
         | |- context [v_sub ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vsub_wZ w y)
         | |- context [v_sub (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vsub_Zw x w)
         | |- context [v_mul ?w (Z_to_bv 64 ?y)] => not_arith w; rewrite (vmul_wZ w y)
         | |- context [v_mul (Z_to_bv 64 ?x) ?w] => not_arith w; rewrite (vmul_Zw x w)
         | |- context [v_add ?w ?w'] => not_arith w; not_arith w'; rewrite (vadd_ww w w')
         end.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Lemma eqb_ZZ : ltac2:(zQ "b1!h9!hu0!lf!hu6!hub!o3!jc!hv0!la!ihe!ii8&@2$1@2$3Z^2@2$4^2@2$5+2+k0>1a$2>1b$2>0~0>0~0@3$8$7@3$9@1$0#k0@2$6@1$0#k0^4@2$6@1$0#k0^3@2$a^4^3").
Proof. intros. unfold bv_eqb. rewrite !u_small by lia. reflexivity. Qed.
Lemma ltu_ZZ : ltac2:(zQ "b1!h9!hu0!lf!hu6!hub!o3!jc!hv0!la!iie!ij8&@2$1@2$3Z^2@2$4^2@2$5+2+k0>1a$2>1b$2>0~0>0~0@3$8$7@3$9@1$0#k0@2$6@1$0#k0^4@2$6@1$0#k0^3@2$a^4^3").
Proof. intros. unfold bv_ltu. rewrite !u_small by lia. reflexivity. Qed.
Lemma lts_ZZ : ltac2:(zQ "b1!h9!hu0!lf!hu6!hub!o3!jc!hv0!la!ije!ij8&@2$1@2$3Z^2@2$4^2@2$5+2+jf>1a$2>1b$2>0~0>0~0@3$8$7@3$9@1$0#k0@2$6@1$0#k0^4@2$6@1$0#k0^3@2$a^4^3").
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !bv_signed_small; rewrite ?u_small; try lia.
  all: change (bv_half_modulus 64) with (2 ^ 63)%Z; lia.
Qed.
End FPX2.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_small z) by lia
      end
  end.

(* [comment removed for export] *)
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma rdn_app_Z : ltac2:(zQ "h20!h9!o9!ik8!il0!ila!la!im2!jc!hsb!t1!im8!in1!ioa!lf!is6!hu6!hub!o3>4segs@1$2$e>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a$d>2n1$8>2n2$8>2b1@1$2@1$1@1$0#8>2b2@1$2@1$1@1$0#8>0@3$5@1$3@1$2@1$1@1$0#8@4$6^7^6@2$7@1$0#k0^5^4@2$4@1$2@1$1@1$0#8^2>0@3$5@1$3@1$2@1$1@1$0#8@4$6^8^7@2$7@1$0#k0@2$9^6@1$a^5^4@2$4@1$2@1$1@1$0#8^2>0@2$fZ^7>0@2$h0@2$9^8@1$a^7@2$h1+2+k0@3$5@1$3@1$2@1$1@1$0#8@4$6^b^a@2$7@1$0#k0^9@2$c^8^7@2$4@1$2@1$1@1$0#8@3$b@1$1@1$0#8^6^5").
Proof.
  intros segs m a n1 n2 b1 b2 H1 H2 Ha Hn.
  apply rdn_app; [exact H1|]. rewrite w_add_nat, u_small by lia. exact H2.
Qed.

Lemma callee_saved_no0 : ltac2:(zQ "80!h9!o9!it1!it5!jha!jjd!jk3!jk8@1$3@3$5@1$1@1$0#5Kd@3$6@1$0#5ZKv$2@2$7@1$0#5Z@1$1@1$0#5$4").
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

(* [comment removed for export] *)
Lemma vals_ev_junk : ltac2:(zQ "f0!h9!o9!in1!jkf!ik8!hsb!la!ioa!jmd!jn3!jnc!jre!kg4!im8!jc>4vals@1$4@1$1@1$0#k0>1R@2$9@1$0#5@1$1@1$0#k0>1i$5>0@2$8^1Ni0@3$6@1$1@1$0#k0@2$c@3$2@1$1@1$0#k0^4@1$b^3@2$7@2$3@1$1@1$0#k0^4^2@2$a^3@2$e@1$0#5@1$d^2").
Proof.
  intros vals R i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals.
  rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_id_errno : ltac2:(zQ "80!h9!o9!la!kgf!hu6!o3!tf!v3>1x@1$1@1$0#k0>0@2$4@2$6@2$5+2+k0+vvf@2$7@1$0#k0^1@3$2@1$1@1$0#k0@2$3^2Z^2").
Proof.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  intros x Hx. pose proof (u64_range x) as Hr. unfold v_addiw. rewrite Z.add_0_r.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  replace ((bv_unsigned x + 2 ^ 31) mod 2 ^ 32)%Z with (bv_unsigned x + 2 ^ 31 - 2 ^ 64)%Z by
    (apply Z.mod_unique with (q := (2 ^ 32)%Z); lia).
  symmetry. apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma rdn_byte_Z : ltac2:(zQ "h40!h9!o9!ik8!il0!jc!ila!hsb!la!im2!t1!im8!kh9!ki1!jmd!kjf!lf!is6!hu6!hub!o3>4segs@1$2$h0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a$f>1n$6>2bs@1$2@1$1@1$0#8>1j$6>0@3$7@1$3@1$2@1$1@1$0#8@4$8^6^5@2$4@1$0#k0^4^3@2$5@1$2@1$1@1$0#8^2>0@2$d^2^4>0@2$h1Z^6>0@2$h2@2$9^7@1$a^4@2$h3+2+k0@3$7@1$3@1$2@1$1@1$0#8@4$8^a^9@2$4@1$0#k0@2$9^8@1$a^5N1@2$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8@4$e@1$1@1$0#8^5^6@2$4@1$0#8Z@1$c@1$1@1$0#8").
Proof.
  intros segs m a n bs j H Hj Ha Hn.
  pose proof (rdn_nth segs m n (Z_to_bv 64 a) bs j H Hj) as R. rewrite w_add_nat, u_small in R by lia. exact R.
Qed.

Lemma nth_app_l : forall {A} (l l' : list A) (d : A) j, (j < length l)%nat -> nth j (l ++ l') d = nth j l d.
Proof. intros. apply app_nth1. assumption. Qed.

Lemma In_nth_neq : forall {A} (l : list A) (x d : A) j, ~ In x l -> (j < length l)%nat -> nth j l d <> x.
Proof. intros A l x d j Hn Hj E. apply Hn. rewrite <- E. apply nth_In. exact Hj. Qed.
End FPX3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
