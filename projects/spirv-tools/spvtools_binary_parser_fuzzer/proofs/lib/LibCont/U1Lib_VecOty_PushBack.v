(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow_6b2e0.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6a53c_6a5b4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6a53c : bv 32 := 0xff010113.
Lemma F_6a53c : fetch_word Ubsan.M.loaded_segments (0x6a57c : word) = Some W_6a53c.
Proof. vm_refl. Qed.
Lemma D_6a53c : decode_any W_6a53c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a540 : bv 32 := 0x00113423.
Lemma F_6a540 : fetch_word Ubsan.M.loaded_segments (0x6a580 : word) = Some W_6a540.
Proof. vm_refl. Qed.
Lemma D_6a540 : decode_any W_6a540 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a544 : bv 32 := 0x00813023.
Lemma F_6a544 : fetch_word Ubsan.M.loaded_segments (0x6a584 : word) = Some W_6a544.
Proof. vm_refl. Qed.
Lemma D_6a544 : decode_any W_6a544 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a548 : bv 32 := 0x00050413.
Lemma F_6a548 : fetch_word Ubsan.M.loaded_segments (0x6a588 : word) = Some W_6a548.
Proof. vm_refl. Qed.
Lemma D_6a548 : decode_any W_6a548 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a54c : bv 32 := 0x00853603.
Lemma F_6a54c : fetch_word Ubsan.M.loaded_segments (0x6a58c : word) = Some W_6a54c.
Proof. vm_refl. Qed.
Lemma D_6a54c : decode_any W_6a54c = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a550 : bv 32 := 0x01053503.
Lemma F_6a550 : fetch_word Ubsan.M.loaded_segments (0x6a590 : word) = Some W_6a550.
Proof. vm_refl. Qed.
Lemma D_6a550 : decode_any W_6a550 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a554 : bv 32 := 0x02a67663.
Lemma F_6a554 : fetch_word Ubsan.M.loaded_segments (0x6a594 : word) = Some W_6a554.
Proof. vm_refl. Qed.
Lemma D_6a554 : decode_any W_6a554 = Some (Branch BC_GEU 12 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a558 : bv 32 := 0x00460513.
Lemma F_6a558 : fetch_word Ubsan.M.loaded_segments (0x6a598 : word) = Some W_6a558.
Proof. vm_refl. Qed.
Lemma D_6a558 : decode_any W_6a558 = Some (OpImm ALU_ADD 10 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a55c : bv 32 := 0x00400693.
Lemma F_6a55c : fetch_word Ubsan.M.loaded_segments (0x6a59c : word) = Some W_6a55c.
Proof. vm_refl. Qed.
Lemma D_6a55c : decode_any W_6a55c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a560 : bv 32 := 0x04a6f863.
Lemma F_6a560 : fetch_word Ubsan.M.loaded_segments (0x6a5a0 : word) = Some W_6a560.
Proof. vm_refl. Qed.
Lemma D_6a560 : decode_any W_6a560 = Some (Branch BC_GEU 13 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a564 : bv 32 := 0x04060663.
Lemma F_6a564 : fetch_word Ubsan.M.loaded_segments (0x6a5a4 : word) = Some W_6a564.
Proof. vm_refl. Qed.
Lemma D_6a564 : decode_any W_6a564 = Some (Branch BC_EQ 12 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a568 : bv 32 := 0x00367693.
Lemma F_6a568 : fetch_word Ubsan.M.loaded_segments (0x6a5a8 : word) = Some W_6a568.
Proof. vm_refl. Qed.
Lemma D_6a568 : decode_any W_6a568 = Some (OpImm ALU_AND 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a56c : bv 32 := 0x04069263.
Lemma F_6a56c : fetch_word Ubsan.M.loaded_segments (0x6a5ac : word) = Some W_6a56c.
Proof. vm_refl. Qed.
Lemma D_6a56c : decode_any W_6a56c = Some (Branch BC_NE 13 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a570 : bv 32 := 0x0005a583.
Lemma F_6a570 : fetch_word Ubsan.M.loaded_segments (0x6a5b0 : word) = Some W_6a570.
Proof. vm_refl. Qed.
Lemma D_6a570 : decode_any W_6a570 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a574 : bv 32 := 0x0205ce63.
Lemma F_6a574 : fetch_word Ubsan.M.loaded_segments (0x6a5b4 : word) = Some W_6a574.
Proof. vm_refl. Qed.
Lemma D_6a574 : decode_any W_6a574 = Some (Branch BC_LT 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a578 : bv 32 := 0x00b62023.
Lemma F_6a578 : fetch_word Ubsan.M.loaded_segments (0x6a5b8 : word) = Some W_6a578.
Proof. vm_refl. Qed.
Lemma D_6a578 : decode_any W_6a578 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a57c : bv 32 := 0x00c0006f.
Lemma F_6a57c : fetch_word Ubsan.M.loaded_segments (0x6a5bc : word) = Some W_6a57c.
Proof. vm_refl. Qed.
Lemma D_6a57c : decode_any W_6a57c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a580 : bv 32 := 0x00040513.
Lemma F_6a580 : fetch_word Ubsan.M.loaded_segments (0x6a5c0 : word) = Some W_6a580.
Proof. vm_refl. Qed.
Lemma D_6a580 : decode_any W_6a580 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a584 : bv 32 := 0x5c1000ef.
Lemma F_6a584 : fetch_word Ubsan.M.loaded_segments (0x6a5c4 : word) = Some W_6a584.
Proof. vm_refl. Qed.
Lemma D_6a584 : decode_any W_6a584 = Some (Jal 1 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a588 : bv 32 := 0x00500593.
Lemma F_6a588 : fetch_word Ubsan.M.loaded_segments (0x6a5c8 : word) = Some W_6a588.
Proof. vm_refl. Qed.
Lemma D_6a588 : decode_any W_6a588 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a58c : bv 32 := 0x00a43423.
Lemma F_6a58c : fetch_word Ubsan.M.loaded_segments (0x6a5cc : word) = Some W_6a58c.
Proof. vm_refl. Qed.
Lemma D_6a58c : decode_any W_6a58c = Some (Store SZ8 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a590 : bv 32 := 0x02b56063.
Lemma F_6a590 : fetch_word Ubsan.M.loaded_segments (0x6a5d0 : word) = Some W_6a590.
Proof. vm_refl. Qed.
Lemma D_6a590 : decode_any W_6a590 = Some (Branch BC_LTU 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a594 : bv 32 := 0xffc50513.
Lemma F_6a594 : fetch_word Ubsan.M.loaded_segments (0x6a5d4 : word) = Some W_6a594.
Proof. vm_refl. Qed.
Lemma D_6a594 : decode_any W_6a594 = Some (OpImm ALU_ADD 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a598 : bv 32 := 0x00357513.
Lemma F_6a598 : fetch_word Ubsan.M.loaded_segments (0x6a5d8 : word) = Some W_6a598.
Proof. vm_refl. Qed.
Lemma D_6a598 : decode_any W_6a598 = Some (OpImm ALU_AND 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a59c : bv 32 := 0x00051a63.
Lemma F_6a59c : fetch_word Ubsan.M.loaded_segments (0x6a5dc : word) = Some W_6a59c.
Proof. vm_refl. Qed.
Lemma D_6a59c : decode_any W_6a59c = Some (Branch BC_NE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5a0 : bv 32 := 0x00813083.
Lemma F_6a5a0 : fetch_word Ubsan.M.loaded_segments (0x6a5e0 : word) = Some W_6a5a0.
Proof. vm_refl. Qed.
Lemma D_6a5a0 : decode_any W_6a5a0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5a4 : bv 32 := 0x00013403.
Lemma F_6a5a4 : fetch_word Ubsan.M.loaded_segments (0x6a5e4 : word) = Some W_6a5a4.
Proof. vm_refl. Qed.
Lemma D_6a5a4 : decode_any W_6a5a4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5a8 : bv 32 := 0x01010113.
Lemma F_6a5a8 : fetch_word Ubsan.M.loaded_segments (0x6a5e8 : word) = Some W_6a5a8.
Proof. vm_refl. Qed.
Lemma D_6a5a8 : decode_any W_6a5a8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5ac : bv 32 := 0x00008067.
Lemma F_6a5ac : fetch_word Ubsan.M.loaded_segments (0x6a5ec : word) = Some W_6a5ac.
Proof. vm_refl. Qed.
Lemma D_6a5ac : decode_any W_6a5ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6a53c_6a5b4.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablVia.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts U1Facts ContStmts2 U1Lib_Vec32_PbSlow_6b2e0.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_VecOty_PushBack.U1_code_6a53c_6a5b4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts TablVia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac rdA H := peel; rdn_fix H.
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.
Ltac cmpz := pin; unfold c_ltu, c_eq, c_lts, bv_ltu, bv_lts, bv_eqb; imm_norm; rewrite ?u64_of_Z by lia; rewrite ?bv_signed_small64 by lia;
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | reflexivity].
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.

Ltac rdWa a' :=
  lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with a' by lia end;
  peel; apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia.
Lemma nodup_fst_fun : forall (l : list (Z * Z)) q k k',
  List.NoDup (map fst l) -> In (q, k) l -> In (q, k') l -> k = k'.
Proof.
  induction l as [|[q0 k0] l IH]; intros q k k' ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|x l' Hnin ND']; subst.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - injection E1 as -> ->. exfalso. apply Hnin. change q with (fst (q, k')). apply in_map. exact H2.
  - injection E2 as -> ->. exfalso. apply Hnin. change q with (fst (q, k)). apply in_map. exact H1.
  - exact (IH q k k' ND' H1 H2).
Qed.

Lemma lw_small : forall x, 0 <= x < 2 ^ 31 -> v_lw (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply bv_eq. rewrite u_lw_lo, u64_of_Z by lia. reflexivity. Qed.

Section OtyPushBack.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition u1c6a4d8 : vec_consts := {| vc_entry := 0x6a57c; vc_stack := 96 |}.

  Lemma FAST : forall (fx : FPState) R M (sp ret v b cap len src x : Z),
    getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    0 <= len < cap -> cap < 2 ^ 40 -> 16 <= b -> b mod 16 = 0 -> b + 4 * cap <= 2 ^ 63 -> 16 <= sp -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    0 <= x < 2 ^ 31 -> 0 <= src -> src + 4 <= 2 ^ 63 ->
    (v + 24 <= sp - 16 \/ sp <= v) -> (src + 4 <= sp - 16 \/ sp <= src) -> (v + 24 <= b \/ b + 4 * cap <= v) -> b + 4 * cap <= sp - 16 ->
    store_ok SEGS M (Z_to_bv 64 (sp - 16)) 16 = true -> mdef M v 24 -> mdef M b (4 * cap) ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * len))) ->
    rdn SEGS M (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) ->
    rdn SEGS M (Z_to_bv 64 src) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 x)) ->
    ret_ok (Z_to_bv 64 ret) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6a57c) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret)
                     (wbytes (wbytes (wslots M sp [getr R 8%bv; Z_to_bv 64 ret])
                        (Z_to_bv 64 (b + 4 * len)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x))))
                        (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * len + 4)))) (seg_rom SEGS))
      /\ getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 8%bv = getr R 8%bv /\ getr R' 1%bv = Z_to_bv 64 ret
      /\ (forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r).
  Proof using.
    intros fx R M sp ret v b cap len src x Hra Hsp Ha0 Ha1 Hlen Hcap Hb16 Hbal Hbc Hsp16 Hsphi Hv0 Hv1 Hx Hs0 Hs1 WINv WINs Hvb Hbsp HOK HDv HDb F1 F2 SRC Hret.
    assert (He4 : (b + 4 * len) mod 4 = 0).
    { pose proof (Z_div_mod_eq_full b 16) as E. rewrite Hbal in E. replace (b + 4 * len) with ((4 * (b / 16) + len) * 4) by lia. apply Z_mod_mult. }
    eexists. split.
    - norm_pc.
      sv F_6a53c D_6a53c (Z_to_bv 64 (sp - 16)).
      stw F_6a540 D_6a540 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_6a544 D_6a544 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      sv F_6a548 D_6a548 (Z_to_bv 64 v).
      ld_step F_6a54c D_6a54c (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * len))) (Z_to_bv 64 (b + 4 * len)) ltac:(rdA F1) ltac:(b2z8).
      ld_step F_6a550 D_6a550 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdA F2) ltac:(b2z8).
      stepb_ft F_6a554 D_6a554 ltac:(cmpz).
      stepiv F_6a558 D_6a558 (Z_to_bv 64 (b + 4 * len + 4)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      stepiv F_6a55c D_6a55c (Z_to_bv 64 4) ltac:(gres; pin; imm_norm; reflexivity).
      stepb_ft F_6a560 D_6a560 ltac:(cmpz).
      stepb_ft F_6a564 D_6a564 ltac:(cmpz).
      stepiv F_6a568 D_6a568 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact He4).
      stepb_ft F_6a56c D_6a56c ltac:(apply c_eq_refl).
      ld_step F_6a570 D_6a570 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdA SRC) ltac:(apply lwu_val; lia).
      stepb_ft F_6a574 D_6a574 ltac:(rewrite ?getr_zero; rewrite lw_small by lia; cmpz).
      stw F_6a578 D_6a578 (Z_to_bv 64 (b + 4 * len)) (v_lw (Z_to_bv 64 x))
          ltac:(store_ok_peel; apply (mdef_store_ok_off SEGS M b (4 * cap) (4 * len) 4 HDb); lia).
      stepj F_6a57c D_6a57c.
      stepiv F_6a588 D_6a588 (Z_to_bv 64 5) ltac:(gres; pin; imm_norm; reflexivity).
      stw F_6a58c D_6a58c (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (b + 4 * len + 4))
          ltac:(store_ok_peel; apply (mdef_store_ok_off SEGS M v 24 8 8 HDv); lia).
      stepb_ft F_6a590 D_6a590 ltac:(cmpz).
      stepiv F_6a594 D_6a594 (Z_to_bv 64 (b + 4 * len)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
      stepiv F_6a598 D_6a598 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact He4).
      stepb_ft F_6a59c D_6a59c ltac:(apply c_eq_refl).
      ld_step F_6a5a0 D_6a5a0 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdWa (sp - 8)) ltac:(b2z8).
      ld_step F_6a5a4 D_6a5a4 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(rdWa (sp - 16)) ltac:(b2z8).
      sv F_6a5a8 D_6a5a8 (Z_to_bv 64 sp).
      stepjr F_6a5ac D_6a5ac (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      cbn [wslots Zlen length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
      lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
      repeat first [reflexivity | exact Hret | lia | progress f_equal].
    - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
  Qed.

  Lemma SLOW_PRE : forall (fx : FPState) R M (sp ret v b cap src : Z),
    getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    0 <= cap < 2 ^ 40 -> 0 <= b -> b + 4 * cap <= 2 ^ 63 -> 16 <= sp -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    (v + 24 <= sp - 16 \/ sp <= v) ->
    store_ok SEGS M (Z_to_bv 64 (sp - 16)) 16 = true ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) ->
    rdn SEGS M (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) ->
    exists Rn,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6a57c) M (seg_rom SEGS))
                  (@mkst fx Rn (Z_to_bv 64 0x6b384) (wslots M sp [getr R 8%bv; Z_to_bv 64 ret]) (seg_rom SEGS))
      /\ getr Rn 10%bv = Z_to_bv 64 v /\ getr Rn 11%bv = Z_to_bv 64 src /\ getr Rn 1%bv = Z_to_bv 64 0x6a5c8
      /\ getr Rn 2%bv = Z_to_bv 64 (sp - 16) /\ getr Rn 8%bv = Z_to_bv 64 v
      /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
      /\ (forall r, In r [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r).
  Proof using.
    intros fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 Hcap Hb0 Hbc Hsp16 Hsphi Hv0 Hv1 WINv HOK F1 F2.
    eexists. split.
    - norm_pc.
      sv F_6a53c D_6a53c (Z_to_bv 64 (sp - 16)).
      stw F_6a540 D_6a540 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_6a544 D_6a544 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      sv F_6a548 D_6a548 (Z_to_bv 64 v).
      ld_step F_6a54c D_6a54c (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdA F1) ltac:(b2z8).
      ld_step F_6a550 D_6a550 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdA F2) ltac:(b2z8).
      stepb_tk F_6a554 D_6a554 ltac:(cmpz).
      sv F_6a580 D_6a580 (Z_to_bv 64 v).
      stepj F_6a584 D_6a584.
      cbn [wslots Zlen length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
      lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
      repeat first [reflexivity | lia | apply bv_eq; vm_compute; reflexivity | progress f_equal].
    - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
  Qed.

  Lemma SLOW_POST : forall (fx : FPState) R2 Mx (sp ret v e : Z) (s0v : word),
    getr R2 10%bv = Z_to_bv 64 e -> getr R2 2%bv = Z_to_bv 64 (sp - 16) -> getr R2 8%bv = Z_to_bv 64 v ->
    20 <= e -> e <= 2 ^ 47 -> (e - 4) mod 4 = 0 -> 16 <= sp -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 -> (v + 24 <= sp - 16 \/ sp <= v) ->
    mdef Mx v 24 ->
    rdn SEGS Mx (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS Mx (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    ret_ok (Z_to_bv 64 ret) ->
    exists R',
      msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6a5c8) Mx (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) (wbytes Mx (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 e))) (seg_rom SEGS))
      /\ getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 8%bv = s0v /\ getr R' 1%bv = Z_to_bv 64 ret
      /\ (forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R2 r).
  Proof using.
    intros fx R2 Mx sp ret v e s0v G10 G2 G8 He20 He47 He4 Hsp16 Hsphi Hv0 Hv1 WINv HDv L1 L2 Hret.
    eexists. split.
    - norm_pc.
      stepiv F_6a588 D_6a588 (Z_to_bv 64 5) ltac:(gres; pin; imm_norm; reflexivity).
      stw F_6a58c D_6a58c (Z_to_bv 64 (v + 8)) (Z_to_bv 64 e) ltac:(apply (mdef_store_ok_off SEGS Mx v 24 8 8 HDv); lia).
      stepb_ft F_6a590 D_6a590 ltac:(cmpz).
      stepiv F_6a594 D_6a594 (Z_to_bv 64 (e - 4)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
      stepiv F_6a598 D_6a598 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact He4).
      stepb_ft F_6a59c D_6a59c ltac:(apply c_eq_refl).
      ld_step F_6a5a0 D_6a5a0 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (sp - 8) by lia end; peel; exact L1) ltac:(b2z8).
      ld_step F_6a5a4 D_6a5a4 (word_to_le_bytes 8 s0v) s0v
        ltac:(lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with (sp - 16) by lia end; peel; exact L2) ltac:(b2z8).
      sv F_6a5a8 D_6a5a8 (Z_to_bv 64 sp).
      stepjr F_6a5ac D_6a5ac (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
      repeat first [reflexivity | exact Hret | lia | progress f_equal].
    - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
  Qed.

  Theorem vec32_push_backU_6a4d8_spec : vec32_push_backU_stmt SEGS Ly.L MI ST (2 ^ 31) u1c6a4d8.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v b cap src x xs K.
    cbn [vc_entry vc_stack u1c6a4d8]. lazy zeta.
    intros CB Ha0 Ha1 VEC OBJ Hv8 SRC Hx SOBJ Hs0 Hs1 Hs4 SRCV HNMAX ROOM CONT.
    pose proof CB as CB0. destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    pose proof VEC as VEC0. destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE).
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (96 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM.
    assert (Hcap : 0 <= cap < 2 ^ 40) by (unfold vgrow in HNMAX; lia).
    pose proof OBJ as OBJ0. pose proof SOBJ as SOBJ0. destruct OBJ as [PLv WINv]. destruct SOBJ as [PLs WINs].
    assert (WINv' : v + 24 <= sp - (96 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (96 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (96 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (96 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    assert (WINs' : src + 4 <= sp - (96 + (16 + MALLOC_STACK MI)) \/ sp <= src).
    { destruct (Z.lt_ge_cases src sp); [left|right; lia].
      destruct (Z.lt_ge_cases (src + 4) (sp - (96 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases src (sp - (96 + (16 + MALLOC_STACK MI)))).
      - apply (WINs (sp - (96 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINs src); unfold zwin; lia. }
    hide WINv'. hide WINs'.
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (96 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (96 + (16 + MALLOC_STACK MI))) (96 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    set (M1 := wslots M sp [getr R 8%bv; Z_to_bv 64 ret]).
    assert (ST1 : stores_in (zwin (sp - 16) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp [getr R 8%bv; Z_to_bv 64 ret]); unfold Zlen; cbn; lia. }
    assert (AG1 : forall lo hi, (hi <= sp - 16 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
    { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
    unfold fld in F0, F1, F2, SRC.
    destruct (Z.lt_ge_cases (Zlen xs) cap) as [LT|GE].
    -
      unhide Hb. destruct Hb as [[Hb00 Hc00]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
      destruct (live_range SEGS Ly.L MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hbce).
      assert (HDb : mdef M b (4 * cap)) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
      assert (Hbown : forall a, b <= a < b + 4 * cap -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
      assert (Hb16 : 16 <= b) by (pose proof (Z_div_mod_eq_full b 16) as E; rewrite Hal in E; lia).
      unhide WINv'. unhide WINs'.
      destruct (FAST fx R M sp ret v b cap (Zlen xs) src x Hra Hsp Ha0 Ha1 ltac:(lia) ltac:(lia) Hb16 Hal Hbc ltac:(lia) ltac:(lia) Hv0 Hv1 Hx Hs0 Hs1
                     ltac:(lia) ltac:(lia) Hdj ltac:(lia) ltac:(ok_sub HOK) HDv HDb F1 F2 SRC Hret)
        as (R' & RUN & R'2 & R'8 & R'1 & R'S).
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN | ].
      fold M1.
      set (M2 := wbytes M1 (Z_to_bv 64 (b + 4 * Zlen xs)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)))).
      set (M3 := wbytes M2 (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs + 4)))).
      assert (ST3 : stores_in (fun a => zwin (sp - 16) sp a \/ zwin (b + 4 * Zlen xs) (b + 4 * Zlen xs + 4) a
                                        \/ zwin (v + 8) (v + 16) a) M M3).
      { unfold M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1|] | | |] | | |];
          rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia;
          intros a Ha; unfold zwin in *; lia. }
      eapply (CONT A R' M3 model b cap).
      +   constructor.
        * eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST3 |].
          intros a [Hw|[Hbuf|Hhd]].
          -- apply WIN. unfold zwin in *; lia.
          -- apply Hbown. unfold zwin in Hbuf. lia.
          -- apply HDR. unfold zwin in Hhd. lia.
        * exact MS.
        * reflexivity.
        * reflexivity.
        * eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST3 |].
          intros a Ha. pose proof (offimg_sep a) as OS.
          destruct Ha as [Hw|[Hbuf|Hhd]].
          -- destruct (OS (proj2 (WIN a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
          -- destruct (OS (proj2 (Hbown a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
          -- destruct (OS (proj2 (HDR a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [first [rewrite R'1; symmetry; exact Hra | rewrite R'2; symmetry; exact Hsp | exact R'8 | apply R'S; in_cs] |]). destruct Hr.
      +
        hide Hdj.
        assert (AG3 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                  (hi <= sp - 16 \/ sp <= lo) -> (hi <= b + 4 * Zlen xs \/ b + 4 * Zlen xs + 4 <= lo) ->
                  (hi <= v + 8 \/ v + 16 <= lo) -> agree_on (zwin lo hi) M M3).
        { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact ST3|]. intros a Ha. unfold zwin in *. lia. }
        unfold CRep.vec32. rewrite Zlen_app1.
        split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact ST3|exact HDv]|].
        split; [lia|]. split; [right; repeat split; try assumption; try lia|].
        split. { eapply fld_agree; [lia|cbn; lia|exact F0|]. apply AG3; cbn; unhide Hdj; lia. }
        split. { unfold fld, M3. replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia.
                 apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
        split. { eapply fld_agree; [lia|cbn; lia|exact F2|]. apply AG3; cbn; unhide Hdj; lia. }
        intros i Hi. destruct (Z.lt_ge_cases i (Zlen xs)) as [Hlt|Hge].
        * destruct (FE i ltac:(lia)) as [Hr HF]. rewrite Znth_app_l by lia. split; [exact Hr|].
          eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG3; cbn; unhide Hdj; lia.
        * replace i with (Zlen xs) by lia. rewrite Znth_app_r1. split; [lia|].
          unfold fld, M3, M2. unhide Hdj. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
          rewrite sw_of_lw by lia. apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia.
      + left. repeat split; try reflexivity. exact LT.
      + apply eff_store.
        * intros a HF HW. apply (proj1 ST3). intros [Hw|[Hbuf|Hhd]].
          -- apply HW. unfold W_of, zwin in *. cbn. lia.
          -- apply HF. right; left. split; [lia|]. unfold zwin in *. lia.
          -- apply HF. left. unfold zwin in *. lia.
        * exact (proj2 ST3).
    -
      assert (LEN : Zlen xs = cap) by lia.
      assert (Hb0 : 0 <= b) by (unhide Hb; destruct Hb as [[-> _]|(Hbp & _)]; lia).
      assert (Hbc4 : b + 4 * cap <= 2 ^ 63) by (unhide Hb; destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & _)]; lia).
      unhide WINv'.
      destruct (SLOW_PRE fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 Hcap Hb0 Hbc4 ltac:(lia) ltac:(lia) Hv0 Hv1 ltac:(lia)
                  ltac:(ok_sub HOK) ltac:(rewrite <- LEN; exact F1) F2)
        as (Rn & RUNA & Rn10 & Rn11 & Rn1 & Rn2 & Rn8 & Rn3 & Rn4 & RnS).
      fold M1 in RUNA.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUNA | ].
      assert (AI1 : ainv MI A M1 model).
      { eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia. }
      assert (SX1 : sx_inv ST s M1).
      { eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
        intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption. }
      eapply (vec32_pbslow_6b2e0_spec MI ST MALLOC_STACK_pos NEW fx A s Rn M1 model (sp - 16) 0x6a5c8 v b cap src x xs K);
        cbn [vc_entry vc_stack u1c6b2e0]; unfold NEW_STACK.
      +   constructor.
        * exact AI1.
        * exact MS.
        * eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
        * exact SX1.
        * exact SXH.
        * constructor.
          -- exact Rn1.
          -- unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
          -- lia.
          -- exact Rn2.
          -- replace (sp - 16) with (sp - 16 * 1) by lia. apply mod16_sub. exact Hsp16.
          -- lia.
          -- rewrite Rn3. exact Hgp.
          -- rewrite Rn4. exact Htp.
        * lia.
        * unfold stack_room. eapply stores_in_store_ok; [exact ST1|]. ok_sub HOK.
        * intros a Ha. apply Hwin. unfold zwin in *. lia.
        * exact Hown_sx.
        * exact Herr_sx.
      + exact Rn10.
      + exact Rn11.
      +   eapply (vec32_frame MI); [exact VEC0 |]. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold vec32_fp, zwin in *. unhide Hb.
        destruct Ha as [Ha|[Hbnz Ha]]; [lia|]. destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
        destruct (live_range SEGS Ly.L MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hbce). lia.
      + exact LEN.
      + split; [exact PLv | intros a Ha Hw; apply (WINv a Ha); unfold zwin in *; lia].
      + exact Hv8.
      + unfold fld. change (fld SEGS M1 src 4 x). eapply fld_agree; [lia| cbn; lia | exact SRC |]. apply AG1; cbn; unhide WINs'; lia.
      + exact Hx.
      + split; [exact PLs | intros a Ha Hw; apply (WINs a Ha); unfold zwin in *; lia].
      + exact Hs0. + exact Hs1. + exact Hs4.
      + exact SRCV.
      + exact HNMAX.
      + exact (ROOM LEN).
      +
        intros A' R2 M' model' b' RB VEC' R2a0 LAP EFF.
        destruct RB as [AI' MS' Hfs' Hfds' SX' KEPT'].
        pose proof VEC' as (_ & _ & HDv' & Hlen' & Hb' & _).
        assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (KEPT' 2%bv) by in_cs; exact Rn2).
        assert (R2_8 : getr R2 8%bv = Z_to_bv 64 v) by (rewrite (KEPT' 8%bv) by in_cs; exact Rn8).

        assert (AGf : agree_on (zwin (sp - 16) sp) M1 M').
        { eapply (agree_hi_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_img); [exact EFF | exact AI1 | exact AI' | lia | lia | | | cbn; lia].
          - replace (sp - (sp - 16)) with 16 by lia. intros i Hi. eapply stores_in_mdef; [exact ST1 | | exact Hi]. intros k Hk. replace (sp - 16 + k) with (sp - (96 + (16 + MALLOC_STACK MI)) + (96 + MALLOC_STACK MI + k)) by lia. apply HDW. lia.
          - intros a Ha [Hz|[Hz|Hz]]; unfold zwin in *.
            + lia.
            + unhide Hb. destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
              destruct (live_range SEGS Ly.L MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hbce). lia.
            + destruct Hb' as [[-> Hc']|(Hbp' & Hal' & Hcp' & Hbc' & HIn' & Hdj')]; [unfold vgrow in Hc'; lia|].
              destruct (live_range SEGS Ly.L MI A' M' model' b' (4 * vgrow cap) AI' HIn') as (_ & _ & _ & Hbce'). lia. }
        assert (SL1 : rdn SEGS M1 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
        { unfold M1. replace (sp - 8) with (sp - 8 * 1) by lia. rewrite (wslots_read SEGS M sp [getr R 8%bv; Z_to_bv 64 ret] 1) by (unfold Zlen; cbn; lia). reflexivity. }
        assert (SL2 : rdn SEGS M1 (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))).
        { unfold M1. replace (sp - 16) with (sp - 8 * 2) by lia. rewrite (wslots_read SEGS M sp [getr R 8%bv; Z_to_bv 64 ret] 2) by (unfold Zlen; cbn; lia). reflexivity. }
        assert (SLr : rdn SEGS M' (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
        { rewrite (rdn_agree_win SEGS M1 M'); [exact SL1 | lia | cbn; lia | eapply agree_on_weaken; [exact AGf|]; intros a' Ha'; unfold zwin in *; cbn in Ha'; lia]. }
        assert (SLs : rdn SEGS M' (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))).
        { rewrite (rdn_agree_win SEGS M1 M'); [exact SL2 | lia | cbn; lia | eapply agree_on_weaken; [exact AGf|]; intros a' Ha'; unfold zwin in *; cbn in Ha'; lia]. }
        destruct Hb' as [[Hb'0 Hc']|(Hbp' & Hal' & Hcp' & Hbc' & HIn' & Hdj')]; [unfold vgrow in Hc'; lia|].
        destruct (live_range SEGS Ly.L MI A' M' model' b' (4 * vgrow cap) AI' HIn') as (_ & _ & _ & Hbce').
        assert (Hb'16 : 16 <= b') by (pose proof (Z_div_mod_eq_full b' 16) as E; rewrite Hal' in E; lia).
        assert (He4 : (b' + 4 * (cap + 1) - 4) mod 4 = 0).
        { pose proof (Z_div_mod_eq_full b' 16) as E. rewrite Hal' in E. replace (b' + 4 * (cap + 1) - 4) with ((4 * (b' / 16) + cap) * 4) by lia. apply Z_mod_mult. }
        destruct (SLOW_POST fx R2 M' sp ret v (b' + 4 * (cap + 1)) (getr R 8%bv) ltac:(rewrite R2a0, LEN; reflexivity) R2_2 R2_8 ltac:(lia) ltac:(unfold vgrow in Hbce'; lia) He4
                    ltac:(lia) ltac:(lia) Hv0 Hv1 ltac:(lia) HDv' SLr SLs Hret)
          as (R' & RUNP & R'2 & R'8 & R'1 & R'S).
        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | exact RUNP | ].
        set (M'' := wbytes M' (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b' + 4 * (cap + 1))))).
        assert (ST'' : stores_in (zwin (v + 8) (v + 16)) M' M'').
        { unfold M''. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia. }
        assert (PLv' : placed MI A' v 24).
        { destruct PLv as [Hst|(q & k & Hin & Hq & Hqk)]; [left; exact Hst | right].
          cbn in LAP. destruct LAP as (lv1 & LADD & LREST).
          assert (Hin1 : In (q, k) lv1) by (eapply live_add_keeps; [exact LADD | exact Hin]).
          exists q, k. split; [| split; [exact Hq | exact Hqk]].
          unfold del_if in LREST. destruct (Z.eqb_spec b 0) as [Hbz|Hbnz].
          - cbn in LREST. rewrite LREST. exact Hin1.
          - cbn in LREST. destruct LREST as (lv2 & LDEL & ->). eapply live_del_keeps; [exact LDEL | exact Hin1 |].
            intros ->. unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            pose proof (proj1 (NoDup_ListNoDup _) (ai_live_nodup MI A M model AI)) as ND.
            pose proof (nodup_fst_fun (live MI A) b k (4 * cap) ND Hin HIn) as ->. lia. }
        assert (HDR' : forall a, v <= a < v + 24 -> ~ owned MI A' a /\ ~ in_ranges [(0x10000, 0x124000)] a).
        { intros a Ha. exact (placed_sep A' M' model' v 24 a AI' PLv' Ha). }
        eapply (CONT A' R' M'' model' b' (vgrow cap)).
        *   constructor.
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI' | exact ST'' |]. intros a Ha. apply HDR'. unfold zwin in Ha; lia.
          -- exact MS'.
          -- exact Hfs'.
          -- exact Hfds'.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX' | exact ST'' |].
             intros a Ha. destruct (offimg_sep a (proj2 (HDR' a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
          -- intros r Hr; unfold callee_saved in Hr.
             repeat (destruct Hr as [<-|Hr]; [first [rewrite R'1; symmetry; exact Hra | rewrite R'2; symmetry; exact Hsp | exact R'8
                                                     | rewrite (R'S _) by in_cs; rewrite (KEPT' _) by in_cs; first [rewrite Rn3; reflexivity | rewrite Rn4; reflexivity | apply RnS; in_cs] ] |]).
             destruct Hr.
        *
          assert (AG'' : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= v + 8 \/ v + 16 <= lo) -> agree_on (zwin lo hi) M' M'').
          { intros lo hi H1 H2 H3. eapply stores_in_agree; [exact ST''|]. intros a Ha. unfold zwin in *. lia. }
          unfold CRep.vec32. unfold CRep.vec32 in VEC'. rewrite Zlen_app1, LEN in VEC' |- *.
          destruct VEC' as (_ & _ & _ & _ & _ & G0' & G1' & G2' & GE').
          split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact ST''|exact HDv']|].
          split; [unfold vgrow; lia|].
          split. { right. split; [lia|]. split; [exact Hal'|]. split; [lia|]. split; [lia|]. split; [exact HIn' | exact Hdj']. }
          split. { eapply fld_agree; [lia|cbn; lia|exact G0'|]. apply AG''; cbn; lia. }
          split. { unfold fld, M''. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. unfold vgrow in *. lia. }
          split. { eapply fld_agree; [lia|cbn; lia|exact G2'|]. apply AG''; cbn; lia. }
          intros i Hi. destruct (GE' i Hi) as [Hr HF]. split; [exact Hr|].
          eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG''; cbn; unfold vgrow in *; lia.
        * right. split; [exact LEN|]. split; [reflexivity|]. exact LAP.
        *
          eapply eff_weaken.
          -- eapply (eff_trans MI); [ | | intros a Ha; apply (stack_sep A' M'' model' a); [eapply (stores_in_ainv SEGS Ly.L MI); [exact AI' | exact ST'' | intros a' Ha'; apply HDR'; unfold zwin in Ha'; lia] | unfold W_of in Ha; cbn in Ha; lia]].
             ++ eapply (eff_trans MI); [ | | intros a Ha; apply (stack_sep A' M' model' a AI'); unfold W_of in Ha; cbn in Ha; lia].
                ** eapply (eff_of_stores SEGS Ly.L MI); [exact ST1 | intros a Ha; right; unfold W_of, zwin in *; cbn; lia].
                ** eapply (eff_widen SEGS Ly.L MI); [exact EFF | cbn; lia | cbn; lia].
             ++ apply (eff_store MI A' M' M'' _ (fun a => zwin v (v + 24) a)); [| exact (proj2 ST'')].
                intros a HF HW. apply (proj1 ST''). intros Hz. apply HF. unfold zwin in *. lia.
          -- intros a [[H|H]|H]; [exact H | exact H | left; exact H].
  Qed.
End OtyPushBack.
