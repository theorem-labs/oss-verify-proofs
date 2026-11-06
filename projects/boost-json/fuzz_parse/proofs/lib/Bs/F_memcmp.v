(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmcdmachine_state3h5LinuxProcessSemantics5Riscv7Preluder35bvmap37Corelib4Init5Logicu12exu13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hg05asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hk48bytes_athfbbv_unsignedk14Nonek13nilu12eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hqa3ivlhqa3mkRhqa5munchhqa5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ig62MSig66ret_pchk47mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ile7seg_romhf7Z_to_bv46Stdlib6ZArith6BinInt1Zir22lek16lengthir23addir26of_natir23powir22lt37Corelib5Lists7ListDefiv75skipnir26to_natk14Somek13nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8F_memcmp~~~~~~jiebmemcmp_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jnb3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~jrdcmemcmp_model" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope bv_scope.

Definition memcmp_post : ltac2:(zQ "70!h9!jc!l9!m0!m9!q3!t9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2ls@1$2@1$1@1$0#8>2rs@1$2@1$1@1$0#8>1v$4>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>0$5P") := ltac2:(zQ "h81!h9!jc!v5!va!hjb!m0!l9!q3!hne!hoa!hp8!hpf!hq5!m9!t9!hu6!hud!hv4!hvd!ik3!ik9!il3!ipd!iq8&>0@1$1@1$0#k0@1$5@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$e@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2a0@1$1@1$0#k0\2a1@1$1@1$0#k0\2ls@1$6@1$1@1$0#8\2rs@1$6@1$1@1$0#8\1v$d\1m~0\3ms'$7@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$3@3$c$7^h0@7$h3@hf$h0^i8^i7^i6^i5^f^e^d^i4^i3@2$h7@1$0#k0^h2^c^b^a^9^8^7^6^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^5^4^3^2^h8@1$h4^i8^h7@1$a@1$1@1$0#k0^1@1$h6$4@2$3@3$h1@1$b$f^h1^1@2$3@3$h2$4^h1^1@2$3@2$h5$4^1@2$3@4$8$4^1@2$9@1$0#k0^h6^h4@4$8$4^1@2$9@1$0#k0^h5^h3").

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : ltac2:(zQ "20!hjb!il3@2$1$0?1m").
  Hypothesis LS : ltac2:(zQ "40!h9!hjb!hne!hoa@4$2$1?1m@2$3@1$0#k0?2a0?2ls").
  Hypothesis RS : ltac2:(zQ "40!h9!hjb!hne!hoa@4$2$1?1m@2$3@1$0#k0?2a1?2rs").
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).
  (* [comment removed for export] *)
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  Lemma bounds : ltac2:(zQ "90!h9!isa!hoa!va!it0!it9!iu0!iua!jc@2$3@2$1Z@2$2@1$0#k0?2a0@2$3@2$1@2$5@2$2@1$0#k0?2a0@1$6@2$4@1$8@1$0#8?2ls@2$7+2+k0@2$3@2$1Z@2$2@1$0#k0?2a1@2$1@2$5@2$2@1$0#k0?2a1@1$6@2$4@1$8@1$0#8?2rs@2$7+2+k0").
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  Lemma byte_range : ltac2:(zQ "60!h9!hoa!va!isa!iv1!jc>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma memcmp_loop : ltac2:(zQ "h90!h9!jc!iq8!m9!iu0!jge!hjb!it9!iv1!jh7!hoa!hp8!ji1!ji8!m0!va!hq5!jmc!jr6!hud!ik3!ipd!jvb!isa!iua>1k$d>1i$3>3x13@1$1@1$0#k0>3x14@1$1@1$0#k0>0@2$h7Z^3>0@2$f@2$8Z@1$4^5@2$8@1$4^5@2$h8+2+k0>0@3$h0@1$e$3@3$h6@3$5@1$1@1$0#8@1$9^5?2ls@3$5@1$1@1$0#8@1$9^5?2rs^6@2$c$3?1v@3$h2$6@h8$h1?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?2a0?2a1?2ls?2rs?1v?1m@7$h4@hf$h3?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@2$2@1$0#k0@2$7@2$a@1$0#k0?2a0^6@2$2@1$0#k0@2$7@2$a@1$0#k0?2a1^6@2$2@1$0#k0@1$4^7^5^4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$2@1$0#k0+hqijn0?2fc@1$b@1$1@1$0#k0?1m@1$h5$6").
  Proof.
    induction k as [|k IH]; intros i x13 x14 Hi Hk HW; pose proof bounds as BD; [lia|].
    cbn [memcmp_model] in HW.
    destruct (skipn (Z.to_nat i) ls) as [|a l'] eqn:EL; [discriminate|].
    destruct (skipn (Z.to_nat i) rs) as [|b r'] eqn:ER; [discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
    pose proof (u8ro_read asegs m A ls i a _ LS Hna ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read asegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD2.
    zstep. zstep. clear RD1 RD2. zstep. if_cases Ke; zify_cond Ke.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) Ke) in HW. injection HW as <-.
      zstep. zstep. finish.
    - rewrite (proj2 (Z.eqb_eq _ _) Ke) in HW.
      zstep. zstep. zstep. zstep.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
      replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
      if_cases K; zify_cond K.
      + apply (IH (i + 1)%Z); try lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HW.
      + (* [comment removed for export] *)
        assert (k = 0%nat) by lia. subst k. cbn in HW. injection HW as <-.
        zstep. zstep. finish.
  Qed.

  Lemma memcmp_body : ltac2:(zQ "h10!h9!m9!hjb!hp8!ji1!m0!hq5!jmc!jr6!hud!ik3!ipd!jvb!jh7!iq8!jc!hoa>0@3$6@1$5$1@3$c?2ls?2rs@1$d@2$h0@1$0#k0?2a2@2$4$1?1v@3$8$2@h8$7?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?2a0?2a1?2ls?2rs?1v?1m@7$a@hf$9?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$e@1$0#k0+hqijmc?2fc@1$3@1$f@1$0#k0?1m@1$b$2").
  Proof.
    intros HM; pose proof bounds as BD.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) replace (Z.to_nat n) with 0%nat in HM by lia. cbn in HM. injection HM as <-. zstep. zstep. finish.
    - eapply evt_eq.
      2:{ apply (memcmp_loop (Z.to_nat n) 0 a3 a4); try lia. cbn [Z.to_nat skipn]. exact HM. }
      unfold mkR. rewrite !Z_to_bv_plus0. repeat f_equal. rewrite Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
End Proofs.

Lemma memcmp_spec : ltac2:(zQ "h50!h9!jc!hjb!m9!hoa!l9!m0!hne!hp8!ji1!hq5!t9!jmc!jr6!hud!ik3!il3!ipd!jvb!jh7!iq8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$b@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>2ls@1$5@1$1@1$0#8>2rs@1$5@1$1@1$0#8>1v$3>0@4$7$2^4@2$4@1$0#k0^hc^3>0@4$7$2^5@2$4@1$0#k0^hc^3>0@3$a@1$6$3@3$h2^5^4@1$h3@2$4@1$0#k0^hc@2$9$3^3>0@2$h0$2^7@3$d$2@h8$c^i9^i8^i7^i6^i2^i1^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^a^9^i0^hf^7^6^5^8@7$f@hf$e^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a@2$h4@1$0#k0+hqijmc^9@1$8@1$1@1$0#k0^8@1$h1$2").
Proof. intros until v. intros LS RS HM MI. apply memcmp_body; assumption. Qed.
(* [comment removed for export] *)
