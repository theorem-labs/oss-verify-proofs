(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export StartupTac RefMemcpyLib.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick13andk12eq01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~m33at_69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~q15v_add46Stdlib6ZArith6BinInt1Zu42leu42ltu43powhf7Z_to_bv37Corelib4Init9Datatypeshh66option37Corelib5Lists7ListDefhj86firstn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hl96wbytesu46to_nathj83nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib4MEMK~~~~~~hqd4memkhh64listhh64Somehh64conshh63nilq13rdnhqd2b_u43addhh64boolhh63nathh64true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsijc8store_oku46of_nat3h5LinuxProcessSemantics5Riscv5Instrio85instrhh65falsehh64prodijcdmachine_state3h5LinuxProcessSemantics5Riscv7Preludeit75bvmapq14mksthh64pairk11Iijc9MachineOkijcafetch_wordijc8is_ecallijcemachine_resultijc4step3h5LinuxProcessSemantics5Riscv7DecodeCjlaadecode_anyio8|41L1o1a1dio83SZ1it76bv_eqbq14getrq16regupdq16v_addihf2BVhf4BvWfhf9bv_signedhfbbv_unsignedio85Store69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib~~~~~~jv42b_hj86repeat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib5MSETK~~~~~~kje5msetku44landu43mulu43lorq16v_slliq14v_ork12or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SumsLib4FPX4~~~~~~kqf2M8u46modulou46shiftrijch0word_to_le_bytes3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelhb7Segmentio86ALU_ORio82Opjv44cpyH" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.
End FPX1.

(* [comment removed for export] *)
Ltac code_at_vm :=
  cbn [code_at Z.add Pos.add Pos.succ];
  repeat split;
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac zlit_at :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)%Z] =>
      is_Z_lit x; is_Z_lit y;
      let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac fold_at_vars :=
  repeat match goal with
         | |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
         end.

(* [comment removed for export] *)
Ltac vn :=
  gres; rwH; imm_norm; unfold btgt;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.

(* [comment removed for export] *)
Ltac an F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vn
  | _ => stepi F D; vn
  end.

(* [comment removed for export] *)
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

(* [comment removed for export] *)
Ltac ab_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

Ltac ab_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

(* [comment removed for export] *)
Ltac aret F D k :=
  stepjr F D k ltac:(gres; rwH; reflexivity);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      end.

(* [comment removed for export] *)
Ltac condz :=
  rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

(* [comment removed for export] *)
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

Lemma v_add_at : ltac2:(zQ "b0!h9!jc!l5!lb!m0!pb!tc!vc!hg1!hg6!hgc>1a@1$1@1$0#k0>1z$4>0@2$2@2$7Z^1@2$8^1@2$9+2+k0@3$3@1$1@1$0#k0@2$6^3@2$a@1$0#k0^2@2$5^3^2").
Proof. intros a z Hz. unfold v_add, at_. rewrite (u_Z2bv z) by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
  cHn : (0 <= n)%Z;
  cHlen : length bs = Z.to_nat n;
  cHsrc : rdn segs mem0 src (length bs) = Some bs;
  cHdst : store_ok segs mem0 dst (length bs) = true;
  cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.
End FPX2.

Section MEMK.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!hv4!ll0@1$0$1").
  Variable mem0 : ltac2:(zQ "30!h9!jc!hie>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variables dst src : word.
  Variable n : Z.
  Variable bs : ltac2:(zQ "30!hv4!h9!jc@1$0@1$2@1$1#8").
  Hypothesis HOK : ltac2:(zQ "10!lmb@6$0?4segs?4mem0?3dst?3src?1n?2bs").

  Let Hn := cHn _ _ _ _ _ _ HOK.
  Let Hlen := cHlen _ _ _ _ _ _ HOK.
  Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
  Let Hdst := cHdst _ _ _ _ _ _ HOK.
  Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
  Let Hnws := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk : ltac2:(zQ "40!h9!jc!hie!m0>1k$3>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "60!hkf!h9!m0!hp3!hpd!jc\1k$2@3$3?4mem0?3dst@3$0@1$5@1$1#8@1$4^1?2bs").
  (* [comment removed for export] *)
  Definition b_ : ltac2:(zQ "30!h9!m0!jc>1j$1@1$2@1$0#8") := ltac2:(zQ "60!h9!hq6!m0!hpd!hgc!jc\1j$2@4$1@1$5@1$0#8@1$3^1?2bs@2$4@1$0#8Z").

  Lemma memk_n : ltac2:(zQ "60!h9!jc!hie!lb!hp3!huc@3$3>0@1$1@1$0#k0@1$2@1$1@1$0#8@1$5?1n@3$4?4mem0?3dst?2bs").
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma rd_src1 : ltac2:(zQ "h00!h9!vc!jc!hv4!m0!hvc!ig4!igc!hie!l5!lb!pb!ih3!ih9!huc!ihf>1k$4>1j$4>0@2$9@2$1Z^2@2$1^2?1n>0@2$1Z^2>0@2$1@2$f^3+1?1n@3$a@1$8@1$3@1$2@1$0#8@4$c?4segs@1$e^5@2$b?3src^4N1@2$5@1$3@1$2@1$0#8@3$6@1$2@1$0#8@1$d^4@1$7@1$2@1$0#8").
  Proof.
    intros k j Hk Hj H1. unfold memk, b_.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
      rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
    - rewrite length_firstn, Hlen, at_u; cbn; lia.
    - rewrite at_u; cbn; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  Lemma wr_dst : ltac2:(zQ "b0!m0!vc!ii5!iid!ij4!lb!in3!pb!huc!ihf!inf>1k$0>1j$0>1m$3>0@2$1Z^2>0@2$1@2$9^3@1$a^2?1n@3$5$2@4$6?4segs@1$8^5@2$7?3dst^4^3$4").
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at segs mem0 dst (length bs)); try assumption; rewrite ?Hlen; lia.
  Qed.

  Lemma memk_extend1 : ltac2:(zQ "d0!h9!jc!huc!ihf!vc!ig4!igc!hie!lb!m0!hp3!pb!ih9>1k$9>0@2$4Z^1>0@2$4@2$3^2+1?1n@3$8>0@1$1@1$0#k0@1$7@1$1@1$0#8@3$a@1$2^3@2$b?3dst^3@3$5@1$1@1$0#8@1$c^3@1$6@1$1@1$0#8@1$2@2$3^3+1").
  Proof.
    intros k Hk H1. unfold memk, b_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite <- sub_nth by (rewrite Hlen; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lbu : ltac2:(zQ "i60!h9!jc!m0!lb!vc!ii5!hie!iqc!hvc!ir5!ire!is6!ivd!jg6!huc!ihf!jgd!jh5!l5!jh9!ji6!jj4!jk0!jl2!jo0!joe!jpb!jq2!pb!jqc!jr3!jrc!ih9!js5!jsa!hgc!jt1!jtd>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$6@1$1@1$0#8>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1k$2>2j0$2>1j$2>0@3$3@1$6@1$1@1$0#i0@2$h4?4segs^9@2$8@1$1@1$0#i0^7>0@3$3$5@1$h5^8$9>0@3$3@1$6@2$a$7$2@1$h8^9@2$8@2$a$7$2@4$h0$7$2@5$h9$ha$9^8^7^6+4>0@3$3@1$1@1$0#k0@2$hd^d^8@2$hc?3src^5>0@3$3$2@2$f^6@2$i4@1$0#c^8^5>0@2$h2@2$4Z^8@2$4^8?1n>0@2$4Z^7>0@2$4@2$f^8+1?1n@3$3@1$h6$b@2$h7?4segs@5$d?2fx^h2^h1@1$e^b^h0@2$h3$b@5$d?2fxM5\0$5@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^e@3$i1@1$0#5ZKv$h1@2$i2@1$0#5Z^h2@3$he^h2^e@2$i3@1$0#k0@2$i5@1$0#8@1$i0^9@2$hf^h1+4@1$e^b^h0").
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : ltac2:(zQ "i00!h9!jc!lb!m0!hie!iqc!ihf!hvc!ire!is6!jqc!jg6!huc!vc!ii5!ir5!jgd!jh9!ji6!jj4!jk0!jl2!jo0!jpb!jub!ivd!pb!jrc!ih9!hgc!jt1!jtd>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$4@1$1@1$0#8>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1k$3>2k0$3>1v@1$1@1$0#k0>0@3$2@1$4@1$1@1$0#i0@2$h2?4segs^9@2$7@1$1@1$0#i0^7>0@3$2$e@1$h3^8$f>0@3$2@1$4@2$8$5$3@1$h6^9@2$7@2$8$5$3@4$h0$5$3@4$h8$h7^8^7^6+4>0@3$2@1$1@1$0#k0@2$a^d^9@2$ha?3dst^5>0@3$2$3@2$6^6@2$he@1$0#c^8^7>0@3$2@1$1@1$0#k0@2$a^f^a^6>0@3$2@1$1@1$0#8@2$hd@1$0#8@2$hf@1$0#k0^7@1$hc^9>0@2$dZ^a>0@2$d@2$6^b+1?1n@3$2@1$h4$9@2$h5?4segs@5$b?2fx^h3^h2@1$c^c^h1@2$h1$9@5$b?2fx^h3@2$hb^h2+4@1$c@2$6^c+1^h1").
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k) by lia.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; cbn; lia.
  Qed.

End MEMK.

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma sb_val_b : ltac2:(zQ "80!h9!kie!hgc!jc!jtd!hv4!lb!m0>2bs@1$5@1$3@1$0#8>1j$7@3$6@1$3@1$0#8@2$2@1$0#8@2$4@1$0#k0@2$2@1$0#k0@2$4@1$0#8@2$1^2^1@2$1^2^1").
Proof.
  intros bs j. pose proof (u8_range (b_ bs j)). rewrite u_Z2bv by lia. apply Z_to_bv_bv_unsigned.
Qed.
End FPX3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSETK.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!hv4!ll0@1$0$1").
  Variable mem0 : ltac2:(zQ "30!h9!jc!hie>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable s : word.
  Variable n : Z.
  Variable b : ltac2:(zQ "20!h9!jc@1$1@1$0#8").
  Hypothesis Hn : ltac2:(zQ "10!vc@2$0Z?1n").
  Hypothesis Hnw : ltac2:(zQ "50!h9!ihf!hg1!hg6!jtd@2$2@2$1@2$4@1$0#k0?1s?1n@2$3+2+k0").
  Hypothesis Hok : ltac2:(zQ "50!ii5!ij4!lb!in3!hpd@3$2$0@4$3?4segs?4mem0?1s@1$4?1n$1").

  Definition msetk : ltac2:(zQ "40!h9!jc!hie!m0>1k$3>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "60!kj4!h9!m0!hp3!hpd!jc\1k$2@3$3?4mem0?1s@3$0@1$5@1$1#8?1b@1$4^1").

  Lemma wr_s : ltac2:(zQ "b0!m0!vc!ii5!iid!ij4!lb!in3!pb!kne!ihf!inf>1k$0>1j$0>1m$3>0@2$1Z^2>0@2$1@2$9^3@1$a^2?1n@3$5$2@4$6?4segs@1$8^5@2$7?1s^4^3$4").
  Proof.
    intros k j m Hj Hm. unfold msetk.
    apply (store_ok_at segs mem0 s (Z.to_nat n)); try assumption; lia.
  Qed.

  Lemma msetk_extend : ltac2:(zQ "d0!h9!jc!kne!iid!hie!lb!kj4!m0!hp3!pb!ihf!vc!inf>1k$7>1m$3>0@2$bZ^2@3$5>0@1$1@1$0#k0@1$4@1$1@1$0#8@3$8@1$2^3@2$9?1s^3@3$6@1$1@1$0#8?1b^2@1$2@2$a^3@1$c^2").
  Proof.
    intros k m Hk. unfold msetk.
    replace (Z.to_nat (k + Z.of_nat m)) with (Z.to_nat k + m)%nat by lia.
    rewrite repeat_app, wbytes_app, repeat_length. f_equal. f_equal. lia.
  Qed.

  Lemma msetk_extend1 : ltac2:(zQ "c0!h9!jc!kne!ig4!igc!hie!lb!m0!hp3!pb!ihf!vc>1k$7>0@2$bZ^1@3$6>0@1$1@1$0#k0@1$5@1$1@1$0#8@3$8@1$2^2@2$9?1s^2@3$3@1$1@1$0#8?1b@1$4@1$1@1$0#8@1$2@2$a^2+1").
  Proof. intros k Hk. apply (msetk_extend k 1). exact Hk. Qed.
End MSETK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX4. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma land_shl_disjoint : ltac2:(zQ "80!m0!vc!hg6!l5!lb!ko7!hg1!koe>1a$0>1b$0>1k$0>0@2$1Z^3>0@2$1Z^2>0@2$3@2$1Z^4@2$6^4@2$2+2^3@3$4$0@2$5@2$7^6@2$2+2^4^5Z").
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : ltac2:(zQ "90!m0!vc!hg6!koe!l5!lb!ihf!kp4!hg1>1a$0>1b$0>1k$0>0@2$1Z^3>0@2$1Z^2>0@2$4@2$1Z^4@2$8^4@2$2+2^3@3$5$0@2$7@2$3^6@2$2+2^4^5@2$6@2$3^6@2$2+2^4^5").
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma v_slli_mul : ltac2:(zQ "a0!h9!jc!lb!m0!kpa!vc!koe!hg6!hgc!jtd>1x@1$1@1$0#k0>1k$3>0@2$5Z^1@3$2@1$1@1$0#k0@2$4^3^2@2$8@1$0#k0@2$6@2$9@1$0#k0^3@2$7+2^2").
Proof. intros x k Hk. unfold v_slli. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma v_or_shl : ltac2:(zQ "c0!h9!hg6!koe!m0!vc!hg1!hgc!jc!jtd!lb!kq3!ihf>1x@1$7@1$0#k0>1a$3>1k$3>0@2$4Z^2>0@2$4Z^2>0@2$5@2$2^4@2$1+2^3@2$1+2+k0>0@2$5@2$8@1$0#k0^6@2$1+2^4@3$9@1$7@1$0#k0@2$a@2$6@1$0#k0@2$2^6@2$1+2^5^7@2$6@1$0#k0@2$b@2$2^6@2$1+2^5@2$8@1$0#k0^7").
Proof.
  intros x a k Ha Hk Hak Hx. pose proof (u64_range x). unfold v_or.
  pose proof (Z.pow_nonneg 2 k ltac:(lia)).
  rewrite u_Z2bv by nia. rewrite lor_shl_disjoint by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.

Lemma M8_digit : ltac2:(zQ "a0!m0!lb!kqa!koe!l5!kue!vc!hg1!kv4!kvd>1c$0>1k$0>0@2$4@2$6Z^2@2$7^2+hg0>0@2$2@3$1$0^2Z@2$2@3$1$0^2+1@2$2@3$1$0^2+2@2$2@3$1$0^2+3@2$2@3$1$0^2+4@2$2@3$1$0^2+5@2$2@3$1$0^2+6@3$1$0^2+7@3$1$0@2$8@2$9@2$3^4$5@2$3+8^3+hg0^4").
Proof.
  intros c k Hc Hk. unfold M8. rewrite Z.shiftr_div_pow2 by lia.
  assert (G : forall Mhi Mlo B, (0 < B)%Z -> (Mhi * B + Mlo = 72340172838076673)%Z -> (0 <= Mlo)%Z ->
             (255 * Mlo < B)%Z -> (Mhi mod 256 = 1)%Z ->
             (c * 72340172838076673 / B mod 256 = c)%Z).
  { intros Mhi Mlo B HB HM Hlo Hlt Hm1.
    replace (c * 72340172838076673)%Z with (c * Mhi * B + c * Mlo)%Z by nia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (c * Mlo) B) by nia.
    rewrite Z.add_0_r, <- Zmult_mod_idemp_r, Hm1, Z.mul_1_r. apply Z.mod_small. lia. }
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
  - apply (G 72340172838076673 0 1)%Z; reflexivity || lia.
  - apply (G 282578800148737 1 (2^8))%Z; try reflexivity; lia.
  - apply (G 1103823438081 257 (2^16))%Z; try reflexivity; lia.
  - apply (G 4311810305 65793 (2^24))%Z; try reflexivity; lia.
  - apply (G 16843009 16843009 (2^32))%Z; try reflexivity; lia.
  - apply (G 65793 4311810305 (2^40))%Z; try reflexivity; lia.
  - apply (G 257 1103823438081 (2^48))%Z; try reflexivity; lia.
  - apply (G 1 282578800148737 (2^56))%Z; try reflexivity; lia.
Qed.

Lemma byte_eq_mod : ltac2:(zQ "60!h9!m0!lb!kv4!hgc!jc>1x$1>1y$1>0@3$2$1@2$3^2+hg0@2$3^1+hg0@3$2@1$5@1$0#8@2$4@1$0#8^3@2$4@1$0#8^2").
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(* [comment removed for export] *)
Lemma rep8_bytes : ltac2:(zQ "d0!h9!hgc!jc!hv4!l5!lb!kj4!m0!lg6!kue!vc!hg1!koe>1c$7>0@2$4@2$aZ^1@2$b^1+hg0@3$5@1$3@1$2@1$0#8@2$8N8@2$1@1$0#k0@2$c^2$9@3$6@1$2@1$0#8@2$1@1$0#8^2N8").
Proof.
  intros c Hc. unfold word_to_le_bytes. rewrite u_Z2bv by (unfold M8; lia).
  cbn [Z_to_le_bytes repeat]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
  pose proof (M8_digit c) as D.
  repeat match goal with
  | |- (_ :: _) = (_ :: _) => f_equal
  | |- Z_to_bv 8 _ = Z_to_bv 8 _ => apply byte_eq_mod; rewrite (Z.mod_small c 256) by lia
  | |- [] = [] => reflexivity
  end.
  - rewrite <- (D 0%Z) at 2 by lia. rewrite Z.shiftr_0_r || (cbn [Z.mul]; rewrite Z.shiftr_0_r). reflexivity.
  - apply (D 1%Z); lia.
  - apply (D 2%Z); lia.
  - apply (D 3%Z); lia.
  - apply (D 4%Z); lia.
  - apply (D 5%Z); lia.
  - apply (D 6%Z); lia.
  - apply (D 7%Z); lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_or_at : ltac2:(zQ "i01!h9!jc!lb!hie!m0!iqc!hvc!ii5!ir5!ire!is6!jqc!jg6!hv4!jgd!jh5!ll0!jh9!ji6!jj4!jk0!jl2!jo0!llb!lm5!jq2!ivd!jr3!jrc!kq3!js5!jsa&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.
End FPX4.

(* [comment removed for export] *)
Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
