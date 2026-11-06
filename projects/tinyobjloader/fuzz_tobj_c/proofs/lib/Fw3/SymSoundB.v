(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "prod"; "pair"; "Some"; "nat"; "length"; "andb"; "fst"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sv_below"; "sstate"; "swf"; "ss_next"; "valuation"; "eval"; "sprop"; "tfact"; "dflt_inv"; "sobj"; "ss_fregs"; "odefault"; "ss_facts"; "ss_objs"; "elem_holds"; "freg_sv"; "rd_bytes"; "reg_sv"; "ss_fcsr"; "ss_pc"; "ss_resv"; "dflt_wf"; "mem_match"; "obj_holds"; "obj_wf"; "regs_match"; "rl"; "sfcsr"; "smatch"; "sprop_below"; "ss_regs"; "tf_expr"; "SAlu"; "SAluW"; "SExt"; "SLit"; "SMd"; "SMdW"; "agree_below"; "oaddr"; "ob_dflt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_reg"; "regZ"; "set_pc"; "split_addr"; "add_cancel"; "add_fact"; "addk_base"; "addlit_view"; "and_mask_fold"; "and_mask_fold2"; "as_addlit"; "get_freg"; "get_reg"; "mk_add_nn"; "mk_addk"; "mk_alu"; "mk_alu_f"; "mk_aluw"; "mk_ext"; "mk_md"; "mk_mdw"; "mk_sub_nn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "lt"; "add"; "to_nat"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"; "rset"; "with_pc"; "is_x0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA"; "core_of"; "ms_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "bvmap"; "bvmap_set"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma list_set_length : forall {A} (l : list A) n x, length (list_set l n x) = length l.
Proof. induction l; intros [|n] x; cbn; auto. Qed.

Lemma nth_list_set : forall {A} (l : list A) n m x d,
  (n < length l)%nat ->
  nth m (list_set l n x) d = if Nat.eqb m n then x else nth m l d.
Proof.
  induction l as [|h t IH]; intros n m x d Hn; cbn in Hn; [lia|].
  destruct n as [|n], m as [|m]; cbn; auto.
  rewrite IH by lia. reflexivity.
Qed.

Lemma forallb_list_set : forall {A} (f : A -> bool) (l : list A) n x,
  forallb f l = true -> f x = true -> forallb f (list_set l n x) = true.
Proof.
  induction l as [|h t IH]; intros n x Hl Hx; cbn; auto.
  cbn in Hl. apply andb_prop in Hl as [Hh Ht].
  destruct n; cbn; rewrite ?Hx, ?Hh, ?Ht; cbn; auto.
Qed.

Lemma forallb_nth : forall {A} (f : A -> bool) (l : list A) n d,
  forallb f l = true -> f d = true -> f (nth n l d) = true.
Proof.
  induction l as [|h t IH]; intros n d Hl Hd; destruct n; cbn; auto;
    cbn in Hl; apply andb_prop in Hl as [Hh Ht]; auto.
Qed.

Lemma Forall_nth' : forall {A} (P : A -> Prop) (l : list A) n d,
  Forall P l -> P d -> P (nth n l d).
Proof.
  induction l as [|h t IH]; intros n d Hl Hd; destruct n; cbn; auto;
    inversion Hl; auto.
Qed.

Lemma regZ_range : ltac2:(tb__ "0|1|
S3dQ5A1S1S5dZ0S43R1A1M0A2S5eG0Z20A2A2Fr;").
Proof. intros r. unfold regZ. pose proof (bv_unsigned_in_range 5 r) as H. change (bv_modulus 5) with 32 in H. lia. Qed.

Lemma is_x0_regZ : ltac2:(tb__ "0|0|
S3dQ5A1S0S3S67R1A1S5cS43R1A1Z0A2A3Fr;").
Proof. reflexivity. Qed.

Lemma reg_eq_of_regZ : ltac2:(tb__ "0|1|
S3dQ5A1M0G0S0S3aS43R2A1S43R1A1A3S0G0R3R2A3F_;Fr2;Fr1;").
Proof. intros. apply bv_eq. exact H. Qed.

Ltac swf_split H :=
  unfold swf in H;
  repeat (apply andb_prop in H; destruct H as [H ?]).

Lemma swf_regs_len : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0SaSbS10S2fR2A1A2U20A3F_;FS;").
Proof. intros S H. swf_split H. apply Nat.eqb_eq. assumption. Qed.

Lemma swf_fregs_len : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0SaSbS10S1bR2A1A2U20A3F_;FS;").
Proof. intros S H. swf_split H. apply Nat.eqb_eq. assumption. Qed.

Lemma swf_regs_below : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0S3S5aS10S11S14R2A1A1S2fR2A1A3S4A3F_;FS;").
Proof. intros S H. swf_split H. assumption. Qed.

Lemma swf_fregs_below : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0S3S5aS10S11S14R2A1A1S1bR2A1A3S4A3F_;FS;").
Proof. intros S H. swf_split H. assumption. Qed.

Lemma swf_objs : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0S3S5aS1aS29S14R2A1A1S1eR2A1A3S4A3F_;FS;").
Proof. intros S H. swf_split H. assumption. Qed.

Lemma swf_facts : ltac2:(tb__ "0|0|
S12S0S3S13R1A1S4A3S0S3S5aS17S2eS14R2A1A1S1dR2A1A3S4A3F_;FS;").
Proof. intros S H. swf_split H. assumption. Qed.

Lemma get_reg_below : ltac2:(tb__ "0|0|
S12S3dQ5A1S0S3S13R2A1S4A3S0S3S11S14R3A1S4eR3R2A2A2S4A3F_;Fr;FS;").
Proof.
  intros S r H. unfold get_reg, reg_sv.
  destruct (regZ r =? 0); [reflexivity|].
  apply forallb_nth; [apply swf_regs_below; exact H | reflexivity].
Qed.

Lemma get_freg_below : ltac2:(tb__ "0|0|
S12S3dQ5A1S0S3S13R2A1S4A3S0S3S11S14R3A1S4dR3R2A2A2S4A3F_;Fr;FS;").
Proof.
  intros S r H. unfold get_freg, freg_sv.
  apply forallb_nth; [apply swf_fregs_below; exact H | reflexivity].
Qed.

Lemma sv_below_mono : ltac2:(tb__ "0|0|
S3bS3bS10S6fR3R2A2S0S3S11R4R2A2S4A3S0S3S11R4R3A2S4A3F_;F_;Fe;Fm;Fn;").
Proof.
  intros n m e Hle. induction e; cbn; intros H; auto;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
  apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
Qed.

Lemma lit_below : ltac2:(tb__ "0|0|
S3bS3aS0S3S11R2S34R1A1A2S4A3Fz;Fn;").
Proof. reflexivity. Qed.

Lemma addk_base_below : ltac2:(tb__ "0|0|
S3bS10S3aS0S3S11R3R2A2S4A3S0S3S11R4S48R3R2A2A2S4A3F_;Fs;Fb;Fn;").
Proof.
  intros n b s Hb. unfold addk_base. destruct (snorm s =? 0); cbn; rewrite ?Hb; reflexivity.
Qed.

Lemma as_addlit_below : ltac2:(tb__ "0|1|
S3bS10S10S3aS0S6S7S10S3aA2M0A1S4cR3A1S9G0S8S10S3aR2R1A4A2A3S0S3S11R5R4A2S4A3S0S3S11R6R4A2S4A3F_;F_;Fx;Fb;Fa;Fn;").
Proof.
  intros n a b x H Ha. destruct a; cbn in H; try discriminate.
  destruct op; try discriminate. destruct a2; try discriminate.
  inversion H; subst. cbn in Ha. apply andb_prop in Ha as [Hb _]. exact Hb.
Qed.

Lemma mk_addk_below : ltac2:(tb__ "0|0|
S3bS10S3aS0S3S11R3R2A2S4A3S0S3S11R4S50R3R2A2A2S4A3F_;Fk;Fa;Fn;").
Proof.
  intros n a k Ha. unfold mk_addk.
  assert (G : sv_below n match as_addlit a with
                         | Some (b, x) => addk_base b (x + k)
                         | None => addk_base a k
                         end = true).
  { destruct (as_addlit a) as [[b x]|] eqn:E.
    - apply addk_base_below. eapply as_addlit_below; eauto.
    - apply addk_base_below. exact Ha. }
  destruct a; try exact G. reflexivity.
Qed.

Lemma below_SAlu : ltac2:(tb__ "0|0|
S3bS58S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S31R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof. intros. cbn. rewrite H, H0. reflexivity. Qed.
Lemma below_SAluW : ltac2:(tb__ "0|0|
S3bS58S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S32R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof. intros. cbn. rewrite H, H0. reflexivity. Qed.
Lemma below_SMd : ltac2:(tb__ "0|0|
S3bS59S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S35R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof. intros. cbn. rewrite H, H0. reflexivity. Qed.
Lemma below_SMdW : ltac2:(tb__ "0|0|
S3bS59S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S36R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof. intros. cbn. rewrite H, H0. reflexivity. Qed.
Lemma below_SExt : ltac2:(tb__ "0|0|
S3bS3S3cS10S0S3S11R4R1A2S4A3S0S3S11R5S33R4R3R2A3A2S4A3F_;Fa;Fw;Fsgn;Fn;").
Proof. intros. cbn. exact H. Qed.

Lemma addlit_view_below : ltac2:(tb__ "0|0|
S3bS10S10S3aS0S7S10S3aA2S49R3A1S8S10S3aR2R1A4A3S0S3S11R5R4A2S4A3S0S3S11R6R4A2S4A3F_;F_;Fk;Fb;Fe;Fn;").
Proof.
  intros n e b k H He. unfold addlit_view in H.
  destruct (as_addlit e) as [[b' k']|] eqn:E.
  - inversion H; subst. eapply as_addlit_below; eauto.
  - inversion H; subst. exact He.
Qed.

Lemma mk_sub_nn_below : ltac2:(tb__ "0|0|
S3bS10S10S0S3S11R3R2A2S4A3S0S3S11R4R2A2S4A3S0S3S11R5S57R4R3A2A2S4A3F_;F_;Fb;Fa;Fn;").
Proof.
  intros n a b Ha Hb. unfold mk_sub_nn.
  destruct (addlit_view a) as [ba x]. destruct (addlit_view b) as [bb y].
  destruct (sv_eqb ba bb); [reflexivity | apply below_SAlu; assumption].
Qed.

Lemma add_cancel_below : ltac2:(tb__ "0|0|
S3bS10S10S10S0S3S11R4R2A2S4A3S0S6S10A1S46R4R3A2S9S10R2A2A3S0S3S11R6R3A2S4A3F_;F_;Fr;Fb;Fa;Fn;").
Proof.
  intros n a b r Hb H. unfold add_cancel in H.
  destruct b as [| |op b1 b2| | | | |]; try discriminate. destruct op; try discriminate.
  destruct (sv_eqb a b2); [|discriminate]. injection H as <-.
  cbn in Hb. apply andb_prop in Hb as [Hb _]. exact Hb.
Qed.

Lemma mk_add_nn_below : ltac2:(tb__ "0|0|
S3bS10S10S0S3S11R3R2A2S4A3S0S3S11R4R2A2S4A3S0S3S11R5S4fR4R3A2A2S4A3F_;F_;Fb;Fa;Fn;").
Proof.
  intros n a b Ha Hb. unfold mk_add_nn.
  destruct (add_cancel a b) as [r|] eqn:E1; [exact (add_cancel_below n a b r Hb E1)|].
  destruct (add_cancel b a) as [r|] eqn:E2; [exact (add_cancel_below n b a r Ha E2)|].
  apply below_SAlu; assumption.
Qed.

Lemma mk_alu_below : ltac2:(tb__ "0|0|
S3bS58S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S51R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof.
  intros n op a b Ha Hb. unfold mk_alu, mk_alu_nl, mk_alu_ln, mk_alu_nn.
  destruct a, b, op;
  first [ reflexivity
        | apply mk_addk_below; assumption
        | apply mk_sub_nn_below; assumption
        | apply mk_add_nn_below; assumption
        | apply below_SAlu; assumption
        | destruct (_ =? _); first [assumption | apply below_SAlu; assumption]
        | destruct (sv_eqb _ _); first [reflexivity | assumption | apply below_SAlu; assumption] ].
Qed.

Lemma mk_aluw_below : ltac2:(tb__ "0|0|
S3bS58S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S53R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof.
  intros n op a b Ha Hb. unfold mk_aluw. destruct a, b;
  first [ reflexivity | apply below_SAluW; assumption ].
Qed.

Lemma mk_md_below : ltac2:(tb__ "0|0|
S3bS59S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S55R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof.
  intros n op a b Ha Hb. unfold mk_md. destruct a, b;
  first [ reflexivity | apply below_SMd; assumption ].
Qed.

Lemma mk_mdw_below : ltac2:(tb__ "0|0|
S3bS59S10S10S0S3S11R4R2A2S4A3S0S3S11R5R2A2S4A3S0S3S11R6S56R5R4R3A3A2S4A3F_;F_;Fb;Fa;Fop;Fn;").
Proof.
  intros n op a b Ha Hb. unfold mk_mdw. destruct a, b;
  first [ reflexivity | apply below_SMdW; assumption ].
Qed.

Lemma mk_ext_below : ltac2:(tb__ "0|0|
S3bS3S3cS10S0S3S11R4R1A2S4A3S0S3S11R5S54R4R3R2A3A2S4A3F_;Fa;Fw;Fsgn;Fn;").
Proof.
  intros n sgn w a Ha. unfold mk_ext. destruct a; try reflexivity;
  destruct (_ && _)%bool; first [ assumption | apply below_SExt; assumption ].
Qed.

Lemma and_mask_fold_below : ltac2:(tb__ "0|0|
S3bS5S17A1S10S3aS10S0S3S11R5R3A2S4A3S0S6S10A1S4aR5R4R3A3S9S10R2A2A3S0S3S11R7R3A2S4A3F_;F_;Fr;Fk;Fe;Ffacts;Fn;").
Proof.
  intros n facts e k r He H. unfold and_mask_fold in H.
  destruct e as [|i|op a b|op a b| | | |]; try discriminate.
  - destruct (_ && _ && _)%bool; [inversion H; reflexivity|].
    destruct (match high_mask_j k with Some _ => _ | None => None end); [|discriminate]. inversion H; subst. exact He.
  - destruct op; try discriminate.
    + destruct a as [|i| | | | | |]; try discriminate. destruct b; try discriminate.
      destruct (_ && _ && _)%bool; [inversion H; reflexivity|].
      destruct (match high_mask_j k with Some _ => _ | None => None end); [|discriminate]. inversion H; subst.
      apply addk_base_below. cbn in He. apply andb_prop in He as [He _]. exact He.
    + destruct a; try discriminate. destruct b as [|i|op2 a2 b2| | | | |]; try discriminate.
      * destruct (_ && _ && _)%bool; [inversion H; reflexivity| discriminate].
      * destruct op2; try discriminate. destruct a2; try discriminate. destruct b2; try discriminate.
        destruct (_ && _ && _)%bool; [inversion H; reflexivity| discriminate].
  -   destruct op; try discriminate.
    + destruct a; try discriminate. destruct b; try discriminate.
      destruct (_ && _ && _ && _)%bool; [inversion H; reflexivity| discriminate].
    + destruct a; try discriminate. destruct b as [|i|op2 a2 b2| | | | |]; try discriminate.
      * destruct (_ && _ && _ && _)%bool; [inversion H; reflexivity| discriminate].
      * destruct op2; try discriminate. destruct a2; try discriminate. destruct b2; try discriminate.
        destruct (_ && _ && _ && _)%bool; [inversion H; reflexivity| discriminate].
Qed.

Lemma and_mask_fold2_below : ltac2:(tb__ "0|0|
S3bS5S17A1S10S3aS10S0S3S11R5R3A2S4A3S0S6S10A1S4bR5R4R3A3S9S10R2A2A3S0S3S11R7R3A2S4A3F_;F_;Fr;Fk;Fe;Ffacts;Fn;").
Proof.
  intros n facts e k r He H. unfold and_mask_fold2 in H.
  destruct (and_mask_fold facts e k) as [r0|] eqn:E.
  - injection H as <-. exact (and_mask_fold_below n facts e k r0 He E).
  - unfold and_mask_gen in H. destruct ((0 <=? k) &&& (k <? 2 ^ align_sv facts e)); [|discriminate].
    injection H as <-. reflexivity.
Qed.

Lemma mk_alu_f_below : ltac2:(tb__ "0|0|
S3bS5S17A1S58S10S10S0S3S11R5R2A2S4A3S0S3S11R6R2A2S4A3S0S3S11R7S52R6R5R4R3A4A2S4A3F_;F_;Fb;Fa;Fop;Ffacts;Fn;").
Proof.
  intros n facts op a b Ha Hb. pose proof (mk_alu_below n op a b Ha Hb) as M. unfold mk_alu_f.
  destruct op; try exact M.
  {   destruct b as [k| | | | | | |]; try exact M.
    destruct ((0 <=? k) &&& (k <? 2 ^ align_sum facts a)); [|exact M].
    apply mk_alu_below; assumption. }
  destruct b as [k| | | | | | |].
  1:{ destruct (and_mask_fold2 facts a k) as [r|] eqn:E; [exact (and_mask_fold2_below n facts a k r Ha E) | exact M]. }
  all: destruct a as [k'| | | | | | |]; try exact M;
    (destruct (and_mask_fold2 facts _ k') as [r|] eqn:E; [exact (and_mask_fold2_below n facts _ k' r Hb E) | exact M]).
Qed.

Lemma reg_sv_set_reg : ltac2:(tb__ "0|2|
S12S3dQ5A1S10S3aS0S3S13R4A1S4A3S1S5dZ0M0R2A2S5eR2Z20A2A2S0S10S22S42R6R5R4A3R3A2S3S10L_;ScS5cR3S43R5A1M1A2SeS5cG1G0A2A1A2R4S22R6R3A2X3x2A3F_;F_;Fr;Fe;Frd;FS;").
Proof.
  intros S rd e r Hwf Hr. pose proof (swf_regs_len S Hwf) as Hlen.
  unfold set_reg, reg_sv. pose proof (regZ_range rd) as Hrd.
  destruct (Z.eqb_spec (regZ rd) 0) as [E|E].
  - cbn. rewrite Bool.andb_false_r. reflexivity.
  - cbn [ss_regs]. rewrite Bool.andb_true_r.
    destruct (Z.eqb_spec r 0) as [Er|Er].
    + subst. destruct (Z.eqb_spec 0 (regZ rd)); [lia|reflexivity].
    + rewrite nth_list_set by (rewrite Hlen; lia).
      destruct (Nat.eqb_spec (Z.to_nat r) (Z.to_nat (regZ rd))) as [En|En];
      destruct (Z.eqb_spec r (regZ rd)) as [Ez|Ez]; try reflexivity; exfalso; lia.
Qed.

Lemma reg_get_set : ltac2:(tb__ "0|3|
S6dQ5M0S3dQ40A1M1A2S3dG0A1M2G2G1S0G1S64S6eG0G1R3R1R4A5R2A2S3G1L_;S6cG0R2R3A3R1S64R4R2A2X3x2A3Fv;Fr;Frd;Fm;").
Proof.
  intros m rd r v. unfold reg_get.
  destruct (bv_eqb r rd) eqn:E.
  - unfold bv_eqb in E. apply Z.eqb_eq in E. assert (r = rd) by (apply bv_eq; exact E). subst.
    rewrite bvmap_get_set_same. reflexivity.
  - rewrite bvmap_get_set_other; [reflexivity|].
    intros Heq. subst. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate.
Qed.

Lemma regs_match_rset : ltac2:(tb__ "0|1|
S15S12S3fS3dQ5A1S10S3dQ40A1M0G0G0S6S3dQ8A1A1F_;S0S3S13R7A1S4A3S2aR9R8R7A3S0G0S16RaR6A2R5A3S2aRbS42RaR8R7A3S69R9S65R8R6S66R5S68R9A1A2A3R4A3A3F_;F_;F_;Fm';Fpc;Fv;Fe;Frd;Fms;FS;Frho;").
Proof.
  intros rho S ms rd e v pc m' Hwf Hrm Hev r Hr.
  unfold ms_of, rset, core_of, with_pc, with_regs. cbn [c_regs].
  pose proof (regZ_range r) as Hrr. pose proof (regZ_range rd) as Hrd.
  rewrite reg_sv_set_reg by (auto; unfold regZ; lia).
  rewrite is_x0_regZ.
  change (bv_unsigned r) with (regZ r).
  destruct (Z.eqb_spec (regZ rd) 0) as [E|E]; cbn [ms_regs c_regs negb andb].
  - rewrite Bool.andb_false_r. apply Hrm. exact Hr.
  - rewrite Bool.andb_true_r. rewrite reg_get_set. unfold bv_eqb.
    change (bv_unsigned r) with (regZ r). change (bv_unsigned rd) with (regZ rd).
    destruct (Z.eqb_spec (regZ r) (regZ rd)); [symmetry; exact Hev | apply Hrm; exact Hr].
Qed.

Ltac swf_solve :=
  repeat (apply andb_true_intro; split);
  first [ assumption
        | rewrite list_set_length; assumption
        | apply forallb_list_set; assumption
        | reflexivity ].

Lemma swf_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S3S13R3A1S4A3S0S3S11S14R4A1R2A2S4A3S0S3S13S42R5R4R3A3A1S4A3F_;F_;Fe;Frd;FS;").
Proof.
  intros S rd e Hwf He. unfold set_reg. destruct (regZ rd =? 0); [exact Hwf|].
  unfold swf in *. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in *.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  swf_solve.
Qed.

Lemma set_reg_proj : ltac2:(tb__ "0|1|
S12S3dQ5A1S10S1S0S3aS24S42R3R2R1A3M0A1S24R3A1A3S1S0S5S10A1S1bG0A1S1bR3A1A3S1S0S2cS23G0A1S23R3A1A3S1S0S6S10A1S25G0A1S25R3A1A3S1S0S5S1aA1S1eG0A1S1eR3A1A3S1S0S5S17A1S1dG0A1S1dR3A1A3S0S3bS14G0A1S14R3A1A3A2A2A2A2A2A2Fe;Frd;FS;").
Proof. intros. unfold set_reg. destruct (regZ rd =? 0); cbn; repeat split; reflexivity. Qed.

Lemma ss_fregs_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S5S10A1S1bS42R3R2R1A3A1S1bR3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_fcsr_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S2cS23S42R3R2R1A3A1S23R3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_resv_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S6S10A1S25S42R3R2R1A3A1S25R3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_objs_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S5S1aA1S1eS42R3R2R1A3A1S1eR3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_facts_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S5S17A1S1dS42R3R2R1A3A1S1dR3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_next_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S3bS14S42R3R2R1A3A1S14R3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.
Lemma ss_pc_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S0S3aS24S42R3R2R1A3A1S24R3A1A3Fe;Frd;FS;").
Proof. intros. apply set_reg_proj. Qed.

Lemma freg_sv_set_reg : ltac2:(tb__ "0|0|
S12S3dQ5A1S10S3aS0S10S20S42R4R3R2A3R1A2S20R4R1A2A3Fr;Fe;Frd;FS;").
Proof. intros. unfold freg_sv. rewrite ss_fregs_set_reg. reflexivity. Qed.
Lemma freg_sv_set_pc : ltac2:(tb__ "0|0|
S12S3aS3aS0S10S20S44R3R2A2R1A2S20R3R1A2A3Fr;Fpc;FS;").
Proof. reflexivity. Qed.
Lemma reg_sv_set_pc : ltac2:(tb__ "0|0|
S12S3aS3aS0S10S22S44R3R2A2R1A2S22R3R1A2A3Fr;Fpc;FS;").
Proof. reflexivity. Qed.

Lemma swf_set_pc : ltac2:(tb__ "0|0|
S12S3aS0S3S13S44R2R1A2A1S13R2A1A3Fpc;FS;").
Proof. reflexivity. Qed.

Lemma swf_add_fact : ltac2:(tb__ "0|0|
S12S17S0S3S13R2A1S4A3S0S3S2eS14R3A1R2A2S4A3S0S3S13S47R4R3A2A1S4A3F_;F_;Fp;FS;").
Proof.
  intros S p Hwf Hp. unfold swf in *.
  cbn [add_fact ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts forallb] in *.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  rewrite Hp. swf_solve.
Qed.

Section S.
Variable segs : list Segment.

Lemma rd_bytes_same_mem : ltac2:(tb__ "0|3|
S3fS3fS3dQ40A1M0SaS0G0S6S3dQ8A1M1A1F_;M2S40R3A1S40R4A1A3S0G2S41R4A1S41R5A1A3S0S6S5G1A1A1S21R5R4R3A3S21R6R4R3A3A3F_;F_;Fk;Fa;Fms';Fms;").
Proof using .
  intros ms ms' a k Hm Hr. revert a. induction k; intros a; cbn; [reflexivity|].
  unfold rd, ms_read_byte. rewrite Hm, Hr, IHk. reflexivity.
Qed.

Lemma elem_holds_rd_ext : ltac2:(tb__ "0|3|
S15S3fS3fS3aS5S7S3aS3aA2M0A1S5S18A1SaG0S0S6G0A1S5bG0R4R2A3S9G0R1A2A3S0S6S5S3dQ8A1A1A1S21R7S3eQ40S5fR6SdS3aS3aR2A3A2A2M1S60SfS3aS3aR2A3A1M2A3S21R8G1G2A3A3F_;Ff;Fi;S1fR7R6R4R3R2A5S1fR8R6R5R4R3A5F_;F_;Ftmpl;Fflds;Fa0;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' a0 flds tmpl Hrd (vals & Hlen & Hf & Ht).
  exists vals. split; [exact Hlen|]. split; [|exact Ht].
  intros i f Hi. rewrite (Hrd i f Hi). exact (Hf i f Hi).
Qed.

Lemma elem_holds_exprs : ltac2:(tb__ "0|1|
S15S15S3fS3aS5S7S3aS3aA2A1S5S18A1S61S18S18S0S3dQ40A1S16R7S30R1A1M0A2S16R6G0A2A3Lt;R1A3S1fR7R5R4R3R2A5S1fR7R6R5R4R3A5F_;F_;Ftmpl;Fflds;Fa0;Fms;Frho';Frho;").
Proof using .
  intros rho rho' ms a0 flds tmpl He (vals & Hlen & Hf & Ht).
  exists vals. split; [exact Hlen|]. split; [exact Hf|].
  apply Forall_forall. intros t Hin.
  apply (proj1 (tf_holds_expr rho rho' vals t (proj1 (Forall_forall _ _) He t Hin))).
  exact (proj1 (Forall_forall _ _) Ht t Hin).
Qed.

Lemma dflt_inv_same_mem : ltac2:(tb__ "0|1|
S15S1cS3aS3aS3aS3fS3fS0S3dQ40A1S6S3dQ8A1A1F_;M0S40R1A1S40R2A1A3S0G0S41R2A1S41R3A1A3S19R9R8R7R6R5R4A6S19RaR9R8R7R6R4A6F_;F_;F_;Fms';Fms;Fhi;Flo;Fb;Fd;Frho;").
Proof using .
  intros rho d b lo hi ms ms' Hm Hr H. destruct d; cbn in *; try exact H.
  destruct H as (He & Hf & Hle & Hall). split; [exact He|]. split; [exact Hf|]. split; [exact Hle|].
  intros k Hk. apply (elem_holds_rd_ext rho ms ms'); [|exact (Hall k Hk)].
  intros i f _. apply rd_bytes_same_mem; assumption.
Qed.

Lemma dflt_inv_agree : ltac2:(tb__ "0|0|
S3bS15S15S1cS3aS3aS3aS3fS37R8R7R6A3S0S3S26R9R6A2S4A3S19R9R7R6R5R4R3A6S19R9R8R7R6R5R4A6F_;F_;F_;Fms;Fhi;Flo;Fb;Fd;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' d b lo hi ms Hag Hwf H. destruct d; cbn in *; try exact H.
  - destruct Hag as (_ & B & _). rewrite <- B. exact H.
  - destruct Hag as (_ & B & _). rewrite <- B. exact H.
  - apply andb_prop in Hwf as [Hc Ht].
    rewrite <- (eval_agree n rho rho' cnt Hag Hc).
    destruct H as (He & Hf & Hle & Hall). split; [exact He|]. split; [exact Hf|]. split; [exact Hle|].
    intros k Hk. apply (elem_holds_exprs rho rho'); [|exact (Hall k Hk)].
    apply Forall_forall. intros t Hin. eapply eval_agree; [exact Hag|].
    exact (proj1 (forallb_forall _ _) Ht t Hin).
Qed.

Lemma dflt_inv_exprs : ltac2:(tb__ "0|3|
S15S15S1cS3aS3aS3aS3fS3bS0S5S3dQ8A1A1S2bR8R1A2S2bR7R1A2A3Fl;S1cOLd;R6S2S2S2S3bS2Ll;M0G0S3aS10S5S7S3aS3aA2A1S5S18A1S1S0S3dQ40A1M1S16RcR3A2S16RbR3A2A3S61S18S18S0G1S16RdS30R1A1M2A2S16RcG2A2A3Lt;R1A3A2Ltmpl;Lflds;Lcnt;Lesz;X1cx6S19R9R7R6R5R4R3A6S19R9R8R7R6R5R4A6F_;F_;F_;Fms;Fhi;Flo;Fb;Fd;Frho';Frho;").
Proof using .
  intros rho rho' d b lo hi ms Hl Hd H. destruct d; cbn in *; try exact H; try (rewrite <- Hl; exact H).
  destruct Hd as [Hc Ht]. rewrite <- Hc.
  destruct H as (He & Hf & Hle & Hall). split; [exact He|]. split; [exact Hf|]. split; [exact Hle|].
  intros k Hk. apply (elem_holds_exprs rho rho'); [exact Ht | exact (Hall k Hk)].
Qed.

Lemma obj_wf_dflt : ltac2:(tb__ "0|0|
S3bS1aS0S3S29R2R1A2S4A3S0S3S26R3S39R2A1A2S4A3F_;Fo;Fn;").
Proof using . intros n o H. unfold obj_wf in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma obj_holds_same_mem : ltac2:(tb__ "0|1|
S15S3fS3fS1aS0S3dQ40A1S6S3dQ8A1A1F_;M0S40R2A1S40R3A1A3S0G0S41R3A1S41R4A1A3S28Vsegs;R6R5R3A4S28Vsegs;R7R5R4A4F_;F_;F_;Fo;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' o Hm Hr (Hb & Hw & Hc & Hd & Hl).
  split; [exact Hb|]. split; [rewrite Hm; exact Hw|]. split; [|split; [|eapply dflt_inv_same_mem; eauto]].
  - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as H.
    unfold cell_holds in *. rewrite (rd_bytes_same_mem ms ms') by assumption. exact H.
  - intros off Hoff Hcov. specialize (Hd off Hoff Hcov).
    destruct (ob_dflt o); cbn in *; unfold rd, ms_read_byte in *; rewrite ?Hm, ?Hr; exact Hd.
Qed.

Lemma mem_match_same_mem : ltac2:(tb__ "0|1|
S15S5S1aA1S3fS3fS0S3dQ40A1S6S3dQ8A1A1F_;M0S40R1A1S40R2A1A3S0G0S41R2A1S41R3A1A3S27Vsegs;R6R5R4A4S27Vsegs;R7R6R4A4F_;F_;F_;Fms';Fms;Fobjs;Frho;").
Proof using .
  intros rho objs ms ms' Hm Hr (Hall & Hdisj & Hfr). split; [|split; [exact Hdisj|]].
  - apply Forall_forall. intros o Hin. eapply obj_holds_same_mem; eauto.
    exact (proj1 (Forall_forall _ _) Hall o Hin).
  - intros a Ha. rewrite Hm. apply Hfr. exact Ha.
Qed.

Lemma smatch_rd_pc : ltac2:(tb__ "0|3|
S15S12S5S6bA1M0S3fS6aS3dQ5A1S10S3dQ40M1A1M2S3aS2dVsegs;R9R8S8G0S62R7S63R6R5A2A4A4S0S3S11S14R9A1R4A2S4A3S0G2S16RbR5A2R4A3S2dVsegs;RcS44S42RbR7R6A3R4A2S8G0S62RaS63S69R9S65R7R5S66S3eG1R4A2S68R9A1A2A3S40R9A1A3R8A2A4A4F_;F_;F_;Fpc';Fv;Fe;Frd;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md rd e v pc' Hsm He Hev.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hshape : forall P : machine_state -> Prop,
            (forall regs, P {| ms_regs := regs; ms_fregs := ms_fregs ms; ms_pc_val := Z_to_bv 64 pc';
                              ms_svc_pending := None; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                              ms_mem := ms_mem ms; ms_rom := ms_rom ms |}) ->
            P (ms_of ms (rset rd v (with_pc (Z_to_bv 64 pc') (core_of ms))) (ms_mem ms))).
  { intros P HP. unfold ms_of, rset, with_pc, with_regs, core_of. destruct (is_x0 rd); cbn; apply HP. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [rewrite swf_set_pc; apply swf_set_reg; assumption|].
  split; [apply Hshape; intros; reflexivity|].
  split; [apply Hshape; intros; reflexivity|].
  split; [exact Hhalt|].
  split; [apply Hshape; intros; exact Hrom|].
  split; [apply Hshape; intros; exact Hroc|].
  split; [eapply regs_match_rset; eauto|].
  split; [apply Hshape; intros regs r; cbn [ms_fregs];
          rewrite freg_sv_set_pc, freg_sv_set_reg; apply Hfregs|].
  cbn [ss_fcsr ss_resv ss_objs ss_facts set_pc].
  rewrite ss_fcsr_set_reg, ss_resv_set_reg, ss_objs_set_reg, ss_facts_set_reg.
  split; [apply Hshape; intros; exact Hfcsr|].
  split; [apply Hshape; intros; exact Hresv|].
  split; [|exact Hfacts].
  apply Hshape. intros regs. apply (mem_match_same_mem rho (ss_objs S) ms); [reflexivity|reflexivity|exact Hmem].
Qed.
End S.

Lemma split_addr_sound : ltac2:(tb__ "0|0|
S15S10S10S3aS0S7S10S3aA2S45R3A1S8S10S3aR2R1A4A3S0S3dQ40A1S16R5R4A2S38R5R3R2A3A3F_;Foff;Fbase;Fae;Frho;").
Proof.
  intros rho ae base off H. unfold oaddr.
  assert (G : forall e, match as_addlit e with Some (b, k) => (b, k) | None => (e, 0) end = (base, off) ->
                        eval rho e = Z_to_bv 64 (bv_unsigned (eval rho base) + off)).
  { intros e He. destruct (as_addlit e) as [[b k]|] eqn:E.
    - inversion He; subst. rewrite (as_addlit_sound rho e base off E). apply bv_add_Z.
    - inversion He; subst. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  unfold split_addr in H. destruct ae; first [inversion H; subst; cbn; reflexivity | apply G; exact H].
Qed.

Lemma split_addr_below : ltac2:(tb__ "0|0|
S3bS10S10S3aS0S7S10S3aA2S45R3A1S8S10S3aR2R1A4A3S0S3S11R5R4A2S4A3S0S3S11R6R4A2S4A3F_;F_;Foff;Fbase;Fae;Fn;").
Proof.
  intros n ae base off H Hb.
  assert (G : forall e, sv_below n e = true ->
             match as_addlit e with Some (b, k) => (b, k) | None => (e, 0) end = (base, off) ->
             sv_below n base = true).
  { intros e He Heq. destruct (as_addlit e) as [[b k]|] eqn:E.
    - inversion Heq; subst. eapply as_addlit_below; eauto.
    - inversion Heq; subst. exact He. }
  unfold split_addr in H. destruct ae; first [inversion H; subst; reflexivity | eapply G; eauto].
Qed.
