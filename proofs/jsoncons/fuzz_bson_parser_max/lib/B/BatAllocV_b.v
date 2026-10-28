(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatClassId_b BatClassId2_b BatCombAllocHit_b BatAllocC_b BatAllocD_b BatAllocE_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_d1_addr (ab rz n : Z) : Z := 2147450880 + (ab + rz + n / 8 * 8) / 8.
Definition art_d1_mem (M : word -> option byte) (ab rz n : Z) : word -> option byte :=
  if n mod 8 =? 0 then M else Wn 1 M (art_d1_addr ab rz n) (n mod 8).
Definition art_d1_kept (r : reg) : Prop :=
  r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 22%bv.

Lemma art_d1_grows : forall M ab rz n, mem_grows M (art_d1_mem M ab rz n).
Proof. intros. unfold art_d1_mem. destruct (_ =? _); [apply mem_grows_refl | apply Wn_grows]. Qed.
Lemma cell_d1_other : forall M ab rz n b m u, 0 <= art_d1_addr ab rz n -> art_d1_addr ab rz n + 1 < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 ->
  (n mod 8 <> 0 -> apart (art_d1_addr ab rz n) 1 b (Z.of_nat m)) -> cellA M b m u -> cellA (art_d1_mem M ab rz n) b m u.
Proof. intros M ab rz n b m u H1 H2 H3 H4 A C. unfold art_d1_mem. destruct (Z.eqb_spec (n mod 8) 0) as [E|NE]; [exact C|]. apply cell_Wn_other; [lia|cbn; lia|lia|lia|exact (A NE)|exact C]. Qed.
Lemma art_d1_outside : forall M ab rz n (x : word), 0 <= art_d1_addr ab rz n -> art_d1_addr ab rz n + 1 < 2 ^ 64 ->
  (n mod 8 <> 0 -> U x <> art_d1_addr ab rz n) -> art_d1_mem M ab rz n x = M x.
Proof. intros M ab rz n x H1 H2 Hx. unfold art_d1_mem. destruct (Z.eqb_spec (n mod 8) 0) as [E|NE]; [reflexivity|]. specialize (Hx NE). rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia]. Qed.
Lemma wr_d1 : forall M ab rz n b m, wrA M b m -> wrA (art_d1_mem M ab rz n) b m.
Proof. intros. eapply wr_grows; [apply art_d1_grows | assumption]. Qed.
Lemma art_layout_d1 : forall M ab rz n, 0 <= art_d1_addr ab rz n -> art_d1_addr ab rz n + 1 < 2 ^ 64 ->
  apart (art_d1_addr ab rz n) 1 0x1366c8 0xc000 -> apart (art_d1_addr ab rz n) 1 0x1d1768 256 -> art_layout M -> art_layout (art_d1_mem M ab rz n).
Proof. intros M ab rz n H1 H2 A1 A2 L. unfold art_d1_mem. destruct (_ =? _); [exact L|]. apply art_layout_Wn; [lia|cbn; lia|exact A1|exact A2|exact L]. Qed.

(* [comment removed for export] *)
Definition art_e_mem (M : word -> option byte) (sp ab rz n b1 : Z) : word -> option byte :=
  if rz =? 16 then Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (sp - 8) 0x52d18) (sp - 16) 1) (sp - 24) n) (sp - 32) ab
  else Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x52d18) (sp - 16) 1) (sp - 24) n) (sp - 32) ab.
Lemma art_e_grows : forall M sp ab rz n b1, mem_grows M (art_e_mem M sp ab rz n b1).
Proof. intros. unfold art_e_mem. destruct (_ =? _); repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl. Qed.
Lemma cell_e_other : forall M sp ab rz n b1 b m u, 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> 16 <= rz -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 ->
  apart (sp - 32) 32 b (Z.of_nat m) -> apart ab 16 b (Z.of_nat m) -> apart (ab + rz - 16) 16 b (Z.of_nat m) ->
  cellA M b m u -> cellA (art_e_mem M sp ab rz n b1) b m u.
Proof.
  intros M sp ab rz n b1 b m u Hsp Hsp' Hab Hab' Hrz Hb Hm A1 A2 A3 C. unfold art_e_mem. unfold apart in A1, A2, A3.
  destruct (_ =? _); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); exact C.
Qed.
Lemma art_e_outside : forall M sp ab rz n b1 (x : word), 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> 16 <= rz ->
  ~ (sp - 32 <= U x < sp) -> ~ (ab <= U x < ab + 16) -> ~ (ab + rz - 16 <= U x < ab + rz) -> art_e_mem M sp ab rz n b1 x = M x.
Proof.
  intros M sp ab rz n b1 x Hsp Hsp' Hab Hab' Hrz N1 N2 N3. unfold art_e_mem.
  destruct (_ =? _); repeat (rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]); reflexivity.
Qed.
Lemma art_e_state : forall M sp ab rz n b1, 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> 32 <= rz \/ rz = 16 -> apart (sp - 32) 32 (ab + rz - 16) 16 ->
  cellA (art_e_mem M sp ab rz n b1) (ab + rz - 16) 1 2.
Proof.
  intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz A. unfold art_e_mem. unfold apart in A.
  destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); apply cell_Wn_hit; cbn; lia.
Qed.
Lemma art_e_type : forall M sp ab rz n b1, 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> 32 <= rz \/ rz = 16 -> apart (sp - 32) 32 (ab + rz - 16) 16 ->
  0 <= b1 -> cellA (art_e_mem M sp ab rz n b1) (ab + rz - 15) 1 (Z.land b1 243).
Proof.
  intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz A Hb1. unfold art_e_mem. unfold apart in A.
  destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); apply cell_Wn_hit; cbn; lia.
Qed.
Lemma cell_e_hi16 : forall M sp ab rz n b1 u, 32 <= sp -> sp < 2 ^ 64 -> 0 <= ab -> ab + rz < 2 ^ 64 -> (rz = 16 \/ 32 <= rz) ->
  apart (sp - 32) 32 (ab + rz - 14) 2 -> cellA M (ab + rz - 14) 2 u -> cellA (art_e_mem M sp ab rz n b1) (ab + rz - 14) 2 u.
Proof.
  intros M sp ab rz n b1 u Hsp Hsp' Hab Hab' Hrz A C. unfold art_e_mem. unfold apart in A.
  destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); exact C.
Qed.
Lemma wr_e : forall M sp ab rz n b1 b m, wrA M b m -> wrA (art_e_mem M sp ab rz n b1) b m.
Proof. intros. eapply wr_grows; [apply art_e_grows | assumption]. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_d1_run : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> n + rz <= 65536 ->
  art_layout M -> cellA M (0x13d438 + 85) 1 1 -> (n mod 8 <> 0 -> wrA M (art_d1_addr ab rz n) 1) ->
  exists regs',
    msteps ASEGS (mkst regs (0x52a9c : word) M rom) (mkst regs' (0x52b30 : word) (art_d1_mem M ab rz n) rom)
    /\ (forall r : reg, art_d1_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hprim L Cpp Wsh.
  unfold art_d1_mem, art_d1_addr in *.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|NE].
  - exists regs. split; [|intros r _; reflexivity].
    apply (art_alloc_d1_none regs M rom n H9 H22 ltac:(lia) E).
  - eexists. split.
    + apply (art_alloc_d1_part_fn regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 ltac:(lia) NE Hprim L Cpp (Wsh NE)).
    + intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_d2b_run : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 65536 -> (rs + rz) mod 8 = 0 ->
  exists regs',
    msteps ASEGS (mkst regs (0x52b88 : word) M rom) (mkst regs' (0x52c74 : word) M rom)
    /\ getr regs' 11 = Z_to_bv 64 (AsanTab.class_id (rs + rz))
    /\ (forall r : reg, art_cid2_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom rs rz H11 H19 Hs Hs8.
  destruct (Z.leb_spec (rs + rz) 512) as [LE|GT].
  - eexists. split; [|split].
    + apply (art_alloc_d2b_small_fn regs M rom rs rz H11 H19 ltac:(lia)).
    + gres. f_equal. symmetry. apply class_id_small. lia.
    + intros r Hr. unfold art_cid2_kept in Hr. decompose [and] Hr. kept_solve.
  - destruct (art_classid2_hi_run regs M rom (Z_to_bv 64 (rs + rz)) H19) as (r' & RUN & P11 & K).
    exists r'. split; [|split].
    + eapply msteps_trans; [apply (art_alloc_d2b_big regs M rom rs rz H11 H19 ltac:(lia)) | exact RUN].
    + rewrite P11. apply art_cid_w_ok; lia.
    + exact K.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_e_run : forall regs (M rom : word -> option byte) (raw0 : word) (sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) ->
  32 <= sp -> sp + 128 < 2 ^ 64 -> 0x696000 + 32 <= sp -> kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 1 <= n < 2 ^ 40 ->
  0 <= b1 < 256 -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= loff -> tp + loff + 4 < 2 ^ 64 -> ret_ok raw0 ->
  cellA M 0x138120 8 loff -> cellA M (tp + loff) 4 0 -> apart (tp + loff) 4 (ab + rz - 16) 16 ->
  cellA M (ab + rz - 16 + 1) 1 b1 -> wrA M (ab + rz - 16) 16 -> wrA M (sp - 32) 32 -> art_layout M -> cellA M 0x1d1700 8 0 ->
  apart (ab + rz - 16) 16 (sp - 32) 160 -> apart ab 16 (sp - 32) 160 ->
  cellA M (sp + 120) 8 (U raw0) -> cellA M (sp + 112) 8 s0v -> cellA M (sp + 104) 8 s1v -> cellA M (sp + 96) 8 s2v -> cellA M (sp + 88) 8 s3v -> cellA M (sp + 80) 8 s4v -> cellA M (sp + 72) 8 s5v -> cellA M (sp + 64) 8 s6v -> cellA M (sp + 56) 8 s7v -> cellA M (sp + 48) 8 s8v -> cellA M (sp + 40) 8 s9v -> cellA M (sp + 32) 8 s10v -> cellA M (sp + 24) 8 s11v ->
  16 <= rz <= 2048 -> rz mod 16 = 0 -> wrA M ab 16 -> cellA M 0x10360 8 0xcc6e96b9cc6e96b9 ->
  exists regs',
    msteps ASEGS (mkst regs (0x52cc4 : word) M rom) (mkst regs' raw0 (art_e_mem M sp ab rz n b1) rom)
    /\ getr regs' 10 = Z_to_bv 64 (ab + rz) /\ getr regs' 2 = Z_to_bv 64 (sp + 128) /\ getr regs' 1 = raw0
    /\ getr regs' 8 = Z_to_bv 64 s0v /\ getr regs' 9 = Z_to_bv 64 s1v /\ getr regs' 18 = Z_to_bv 64 s2v /\ getr regs' 19 = Z_to_bv 64 s3v
    /\ getr regs' 20 = Z_to_bv 64 s4v /\ getr regs' 21 = Z_to_bv 64 s5v /\ getr regs' 22 = Z_to_bv 64 s6v /\ getr regs' 23 = Z_to_bv 64 s7v
    /\ getr regs' 24 = Z_to_bv 64 s8v /\ getr regs' 25 = Z_to_bv 64 s9v /\ getr regs' 26 = Z_to_bv 64 s10v /\ getr regs' 27 = Z_to_bv 64 s11v
    /\ (forall r : reg, In r [3; 4]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
  intros Hrz Hrz16 Wab Cmag. unfold art_e_mem.
  destruct (Z.eqb_spec rz 16) as [E|NE].
  - eexists. split. apply (art_alloc_e16_fn regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24 E).
    zsplit; try (gres; reflexivity).
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; gres; reflexivity.
  - assert (Hrz32 : 32 <= rz <= 2048). { pose proof (Z.div_mod rz 16 ltac:(lia)). lia. }
    eexists. split. apply (art_alloc_e32_fn regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24 Hrz32 Hrz16 Wab Cmag).
    zsplit; try (gres; reflexivity).
    intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; gres; reflexivity.
Qed.
End FPX.
