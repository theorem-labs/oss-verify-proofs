From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bsegs_asegs : bsegs = asegs.
Proof. reflexivity. Qed.

Lemma rw_aconst_at : forall m A cs, ACONST m -> In (A, cs) aconst_cells -> rw_cells asegs m A cs.
Proof.
  intros m A cs (H & _) Hin. rewrite Forall_forall in H. exact (H (A, cs) Hin).
Qed.

Lemma rw_kw_sh0 : forall E m (e : expr) (x : Z),
  edenot E e = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> sh0 m x ->
  kentry_ok asegs E m (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 (ELit 0)).
Proof.
  intros E m e x He Hx HS. apply (rw_kword_sh0 asegs SHBASE E m e x); [exact HS | exact He | exact Hx | unfold SHBASE; lia | ].
  assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SHBASE. lia.
Qed.

Definition rw_syms_same (sr0 sr' : list expr) (l : list reg) : bool :=
  forallb (fun r : reg => expr_eqb (sr_get sr' r) (sr_get sr0 r)) l.

Lemma rw_syms_same_sound : forall E sr0 R sr' R' (l : list reg),
  regs_ok E sr0 R -> regs_ok E sr' R' -> rw_syms_same sr0 sr' l = true -> forall r, In r l -> getr R' r = getr R r.
Proof.
  intros E sr0 R sr' R' l H0 H1 Hs r Hr. unfold rw_syms_same in Hs. rewrite forallb_forall in Hs.
  pose proof (expr_eqb_eq _ _ (Hs r Hr)) as He.
  transitivity (edenot E (sr_get sr' r)); [exact (H1 r)|]. rewrite He. symmetry. exact (H0 r).
Qed.

Ltac rrwB HR r := let G := fresh "G" in rreg HR r G; rewrite G.

Ltac val_zB :=
  unfold wz, sh; rewrite ?ASHADOW_BASE_val; evs; wnormB;
  first [ reflexivity | f_equal; first [ dlia | change (2 ^ 3) with 8; dlia ] ].

Ltac regB := first [ evs; reflexivity | val_zB ].

Ltac rw_exB Hms :=
  lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ ?R' _ ?mm _) => exists R', mm end.

Ltac keptB HR HR' l := intros r Hr; exact (rw_syms_same_sound _ _ _ _ _ l HR HR' ltac:(vm_compute; reflexivity) r Hr).

Definition rw_keep (P : Prop) : Prop := P.

Ltac stash_disjB := repeat match goal with H : ?A \/ ?B |- _ => change (rw_keep (A \/ B)) in H end.

Ltac unstashB := unfold rw_keep in *.

Ltac rw_seed1B :=
  unfold wz, sh in *; rewrite ?ASHADOW_BASE_val in *; evs;
  first [ assumption
        | eapply eq_trans; [eassumption|]; wnormB;
          first [ reflexivity | f_equal; first [ dlia | change (2 ^ 3) with 8; dlia ] ] ].

Ltac rw_seedB :=
  apply regs_ok_srs; [apply regs_ok_seed|];
  repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | rw_seed1B] |]);
  apply Forall_nil.

Ltac rw_addrB := unfold estart, elenZ; cbn [a_base a_off]; evs; wnormB; rewrite ?u64_of_Z by dlia; dlia.

Ltac rw_shB :=
  first
  [ assumption
  | match goal with H : sh0 ?M ?y |- sh0 ?M ?z => replace z with y by dlia; exact H end
  | match goal with H : gz ?M ?a ?n |- sh0 ?M ?z => replace z with (a + (z - a)) by lia; apply H; dlia end ].

Ltac kentryB :=
  lazymatch goal with
  | |- kentry_ok _ _ _ (KRange _ _ _) => cbn [kentry_ok]; evs; wnormB; rewrite ?u64_of_Z by dlia; dlia
  | |- kentry_ok _ _ _ (KAlign _ _) => cbn [kentry_ok]; split; [lia | evs; wnormB; rewrite ?u64_of_Z by dlia; dlia]
  | |- kentry_ok _ _ _ (KDisj _ _ _ _) => cbn [kentry_ok]; unstashB; rw_addrB
  | |- kentry_ok _ ?E ?M (KImg ?lo ?hi) =>
      match goal with MI : mem_inv asegs M |- _ => exact (kimg_of_mem_inv E M lo hi MI ltac:(lia) ltac:(lia)) end
  | |- kentry_ok _ ?E ?M (KWr ?a ?en) =>
      first
      [ match goal with ST : stk _ M ?lo ?hi |- _ =>
          apply (kwr_of_stk asegs E M lo hi a en ST); rw_addrB end
      | match goal with W : wr_at _ M ?p ?n |- _ =>
          apply (rw_kwr asegs E M a en p n W); rw_addrB end ]
  | |- kentry_ok _ ?E ?M (KWord (SA (ELit 0) ?A) 8 (ELit ?W)) =>
      match goal with HA : ACONST M |- _ =>
        apply (kword_of_rw_cells asegs E M A [C8 (wz W)] 0%nat (C8 (wz W)));
        [ apply (rw_aconst_at M A _ HA); unfold aconst_cells; cbn [In]; repeat (first [left; reflexivity | right])
        | reflexivity | reflexivity | lia | rw_addrB | lia | lia | reflexivity ] end
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 (ELit 0)) =>
      eapply (rw_kw_sh0 E M e); [sc_valB | dlia | rw_shB]
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 ?ek) =>
      match goal with Hs : shk M ?p ?kv |- _ => eapply (kshadow E M e p kv ek); [sc_valB | dlia | dlia | sc_valB | exact Hs] end
  | |- kentry_ok _ ?E ?M (KWord ?a ?k ?e) =>
      first
      [ match goal with H : fldA M ?p k ?x |- _ =>
          apply (rw_kword_fld asegs E M a k e p x H); [rw_addrB | lia | rw_addrB | lia | sc_valB] end
      | match goal with H : fldw asegs M ?p k ?x |- _ =>
          apply (rw_kword_fldw asegs E M a k e p x H); [rw_addrB | lia | rw_addrB | lia | evs; first [reflexivity | assumption]] end ]
  end.

Ltac disj1B :=
  cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; cbn [Z.of_nat Pos.of_succ_nat];
  first [ lia
        | evs; wnormB; rewrite ?u64_of_Z by dlia; first [ dlia | unstashB; dlia ] ].

Ltac disjB := cbn [firstn]; repeat (apply Forall_cons; [disj1B |]); apply Forall_nil.

Lemma rw_fld_post_sx4 : forall E M log (k : nat) (a : saddr) (e : expr) (A V : Z),
  log_flat E log -> nth_error log k = Some (SE a 4 (EExt true 0 4 e)) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + 4 <= estart E (e_addr e')) (firstn k log) ->
  estart E a = A -> edenot E e = Z_to_bv 64 V ->
  fld asegs (mem_denot E M log) A 4 V.
Proof.
  intros E M log k a e A V Hf Hk Hd Hs He.
  pose proof (rw_fld_post asegs E M log k a 4 (EExt true 0 4 e) A (ext_Z true 0 4 (bv_unsigned (Z_to_bv 64 V))) Hf Hk Hd Hs
                ltac:(cbn [edenot]; rewrite He; reflexivity)) as HF.
  assert (EQ : word_to_le_bytes 4 (Z_to_bv 64 (ext_Z true 0 4 (bv_unsigned (Z_to_bv 64 V)))) = word_to_le_bytes 4 (Z_to_bv 64 V)).
  { apply HCommon.word_to_le_bytes_low; [lia|]. intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi.
    apply (HCommon.testbit_mod_eq _ _ 32); [| lia].
    unfold ext_Z. change (8 * N.of_nat 4)%N with 32%N. rewrite (HCommon.bv_swrap_mod 32). change (Z.of_N 32) with 32.
    change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite Z.div_1_r, Z.mod_mod by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity. }
  unfold fld in *. rewrite <- EQ. exact HF.
Qed.

Ltac fld_postB_at k :=
  unfold fldA;
  first [ eapply (rw_fld_post asegs _ _ _ k); [ eassumption | reflexivity | disjB | rw_addrB | val_zB ]
        | eapply (rw_fld_post_sx4 _ _ _ k); [ eassumption | reflexivity | disjB | rw_addrB | val_zB ] ].

Ltac fldw_postB_at k :=
  eapply (rw_fldw_post asegs _ _ _ k); [ eassumption | reflexivity | disjB | rw_addrB | evs; first [reflexivity | assumption] ].

Ltac pickB j := lazymatch j with O => left | S ?k => right; pickB k end.

Ltac munch1B j :=
  cbn [inside e_addr e_width]; pickB j; unfold estart; cbn [a_base a_off]; cbn [Z.of_nat Pos.of_succ_nat];
  evs; wnormB; rewrite ?u64_of_Z by dlia; split; dlia.

Ltac munch_listB js := lazymatch js with nil => apply Forall_nil | cons ?j ?t => apply Forall_cons; [munch1B j | munch_listB t] end.

Ltac munchB_at js := apply rw_munch; [ assumption | munch_listB js ].

Ltac knowB := change bsegs with asegs; kn_eval; unfold know_ok; repeat (apply Forall_cons; [kentryB |]); apply Forall_nil.
