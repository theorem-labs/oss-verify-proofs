(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of musl memchr rewritten as a walk of musl strlen (0x9f3cc) of plugin-hostd/fuzz_command's ASan build, as libreac/fuzz_disco's lib/A/Rt/StrlenMusl.v states it; only the lemmas and tactics that walk uses are kept, its read-only premise is the two constant words 0x10358 and 0x10370, and the module paths and addresses are this image's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
(* musl's word-loop constants as this image holds them (strlen 0x9f410 `ld a3,-152(a1)` reads 0x10370, 0x9f414
   `ld a4,-180(a4)` reads 0x10358). *)
Definition sl_HIGHS : Z := 0x10358.
Definition sl_ONES : Z := 0x10370.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma slm_fetch_lit : forall (p : word) (w : bv 32),
clookup tfibmusl_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word tfibsegs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply tfibmusl_tbl_ok. exact H.
Qed.
End e.
Local Ltac ftac := apply slm_fetch_lit; vm_compute; reflexivity.
Local Ltac stepiv' F D vv tac := let F' := litF F in stepiv F' D vv tac.
Local Ltac exact_lit F := let F' := litF F in exact F'.
Local Ltac rodc :=
let v1 := eval cbv in sl_HIGHS in
let v2 := eval cbv in sl_ONES in
let H1 := fresh "HrodH" in let H2 := fresh "HrodO" in
assert (H1 : sl_HIGHS = v1) by reflexivity;
assert (H2 : sl_ONES = v2) by reflexivity.
Local Ltac msteps_done :=
lazymatch goal with
| |- msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
first [ apply mst_refl
| replace q with p by (symmetry; bveq); apply mst_refl ]
end.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition auipc_imm20 (w : Z) : Z :=
match decode_any (Z_to_bv 32 w) with Some (Auipc _ imm, _) => bv_unsigned imm | _ => 0 end.
Definition ld_imm12 (w : Z) : Z :=
match decode_any (Z_to_bv 32 w) with Some (Load _ _ _ _ imm, _) => bv_unsigned imm | _ => 0 end.
Lemma FS_000 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) = Some (0x00757593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_000 : decode_any (0x00757593%bv : bv 32) = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_004 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x4)) = Some (0x00050613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_004 : decode_any (0x00050613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_008 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) = Some (0x02058a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_008 : decode_any (0x02058a63%bv : bv 32) = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_00c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0xc)) = Some (0x00054583%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_00c : decode_any (0x00054583%bv : bv 32) = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_010 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x10)) = Some (0x06058c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_010 : decode_any (0x06058c63%bv : bv 32) = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_014 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x14)) = Some (0x00150613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_014 : decode_any (0x00150613%bv : bv 32) = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_018 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x18)) = Some (0x00050593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_018 : decode_any (0x00050593%bv : bv 32) = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_01c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) = Some (0x00158693%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_01c : decode_any (0x00158693%bv : bv 32) = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_020 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x20)) = Some (0x0076f693%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_020 : decode_any (0x0076f693%bv : bv 32) = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_024 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) = Some (0x00068c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_024 : decode_any (0x00068c63%bv : bv 32) = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_028 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x28)) = Some (0x00064683%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_028 : decode_any (0x00064683%bv : bv 32) = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_02c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x2c)) = Some (0x00160613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_02c : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_030 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x30)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_030 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_034 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x34)) = Some (0xfe0694e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_034 : decode_any (0xfe0694e3%bv : bv 32) = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_038 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x38)) = Some (0x0480006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_038 : decode_any (0x0480006f%bv : bv 32) = Some (Jal 0 72, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_04c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x4c)) = Some (0xff760593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_04c : decode_any (0xff760593%bv : bv 32) = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_050 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x50)) = Some (0xff860613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_050 : decode_any (0xff860613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_054 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) = Some (0x00863783%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_054 : decode_any (0x00863783%bv : bv 32) = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_058 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x58)) = Some (0x00860613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_058 : decode_any (0x00860613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_05c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x5c)) = Some (0x40f68833%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_05c : decode_any (0x40f68833%bv : bv 32) = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_060 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x60)) = Some (0x00f867b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_060 : decode_any (0x00f867b3%bv : bv 32) = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_064 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x64)) = Some (0x00e7f7b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_064 : decode_any (0x00e7f7b3%bv : bv 32) = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_068 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x68)) = Some (0x00858593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_068 : decode_any (0x00858593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_06c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x6c)) = Some (0xfee784e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_06c : decode_any (0xfee784e3%bv : bv 32) = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_070 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x70)) = Some (0x00064683%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_070 : decode_any (0x00064683%bv : bv 32) = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_074 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x74)) = Some (0x00160613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_074 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_078 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x78)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_078 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_07c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x7c)) = Some (0xfe069ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_07c : decode_any (0xfe069ae3%bv : bv 32) = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_080 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x80)) = Some (0x40a58533%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_080 : decode_any (0x40a58533%bv : bv 32) = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_084 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x84)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_084 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_088 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x88)) = Some (0x40a50533%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_088 : decode_any (0x40a50533%bv : bv 32) = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_08c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x8c)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_08c : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Definition tfib_strlen_w03c : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x3c).
Definition tfib_strlen_w040 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x40).
Definition tfib_strlen_w044 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x44).
Definition tfib_strlen_w048 : Z := Eval vm_compute in tblw tfibmusl_tbl (tfib_A_musl_strlen + 0x48).
Definition tfib_strlen_i03c : Z := Eval vm_compute in auipc_imm20 tfib_strlen_w03c.
Definition tfib_strlen_i040 : Z := Eval vm_compute in auipc_imm20 tfib_strlen_w040.
Definition tfib_strlen_i044 : Z := Eval vm_compute in ld_imm12 tfib_strlen_w044.
Definition tfib_strlen_i048 : Z := Eval vm_compute in ld_imm12 tfib_strlen_w048.
Definition tfib_strlen_aui1 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) (Z.shiftl (bv_signed (Z_to_bv 20 tfib_strlen_i03c)) 12)).
Definition tfib_strlen_aui2 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (tfib_A_musl_strlen + 0x40)) (Z.shiftl (bv_signed (Z_to_bv 20 tfib_strlen_i040)) 12)).
Lemma FS_03c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) = Some (Z_to_bv 32 tfib_strlen_w03c).
Proof. ftac. Qed.
Lemma DS_03c : decode_any (Z_to_bv 32 tfib_strlen_w03c) = Some (Auipc 11 (Z_to_bv 20 tfib_strlen_i03c), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_040 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x40)) = Some (Z_to_bv 32 tfib_strlen_w040).
Proof. ftac. Qed.
Lemma DS_040 : decode_any (Z_to_bv 32 tfib_strlen_w040) = Some (Auipc 14 (Z_to_bv 20 tfib_strlen_i040), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_044 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x44)) = Some (Z_to_bv 32 tfib_strlen_w044).
Proof. ftac. Qed.
Lemma DS_044 : decode_any (Z_to_bv 32 tfib_strlen_w044) = Some (Load SZ8 true 13 11 (Z_to_bv 12 tfib_strlen_i044), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_048 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_strlen + 0x48)) = Some (Z_to_bv 32 tfib_strlen_w048).
Proof. ftac. Qed.
Lemma DS_048 : decode_any (Z_to_bv 32 tfib_strlen_w048) = Some (Load SZ8 true 14 14 (Z_to_bv 12 tfib_strlen_i048), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_strlen_ld_targets :
bv_unsigned (v_addi (Z_to_bv 64 tfib_strlen_aui1) (bv_signed (Z_to_bv 12 tfib_strlen_i044))) = sl_ONES /\
bv_unsigned (v_addi (Z_to_bv 64 tfib_strlen_aui2) (bv_signed (Z_to_bv 12 tfib_strlen_i048))) = sl_HIGHS.
Proof. vm_compute. split; reflexivity. Qed.
Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma nth_app_nul_in : forall (s : list byte) j, (j < length s)%nat -> In (nth j (s ++ [NUL]) NUL) s.
Proof. intros s j Hj. rewrite app_nth1 by lia. apply nth_In. lia. Qed.
Lemma nth_app_nul_last : forall s : list byte, nth (length s) (s ++ [NUL]) NUL = NUL.
Proof. intros s. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma rdn_total : forall segs mem n (a : word),
(forall k, (k < n)%nat -> rdn segs mem (a + nat_to_word k) 1 <> None) ->
exists bs, rdn segs mem a n = Some bs.
Proof.
intros segs mem n. induction n as [|n IH]; intros a Hk.
- exists []. reflexivity.
- pose proof (Hk 0%nat ltac:(lia)) as H0. rewrite word_add_nat_0 in H0.
cbn [rdn] in H0 |- *.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|exfalso; apply H0; reflexivity].
destruct (IH (a + 1)%bv) as [bs Hbs].
{ intros k Hk'. replace (a + 1 + nat_to_word k)%bv with (a + nat_to_word (S k))%bv
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply Hk. lia. }
rewrite Hbs. eexists. reflexivity.
Qed.
Lemma rdn_ext1 : forall segs n m1 m2 (a : word),
(forall k, (k < n)%nat -> rdn segs m1 (a + nat_to_word k) 1 = rdn segs m2 (a + nat_to_word k) 1) ->
rdn segs m1 a n = rdn segs m2 a n.
Proof.
intros segs n. induction n as [|n IH]; intros m1 m2 a Hk; [reflexivity|].
pose proof (Hk 0%nat ltac:(lia)) as H0. rewrite word_add_nat_0 in H0.
cbn [rdn] in H0 |- *.
destruct (match m1 a with Some b => Some b | None => seg_rom segs a end) as [b1|];
destruct (match m2 a with Some b => Some b | None => seg_rom segs a end) as [b2|];
try discriminate H0.
- injection H0 as ->. rewrite (IH m1 m2 (a + 1)%bv); [reflexivity|].
intros k Hk'. replace (a + 1 + nat_to_word k)%bv with (a + nat_to_word (S k))%bv
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply Hk. lia.
- reflexivity.
Qed.
Lemma rom_reads_of_None : forall segs (mem : word -> option byte) (lo hi : Z),
(forall a : word, lo <= bv_unsigned a < hi -> mem a = None) ->
forall a : Z, 0 <= lo -> hi <= 2^64 -> lo <= a < hi ->
rdn segs mem (Z_to_bv 64 a) 1 = rdn segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Proof.
intros segs mem lo hi Hnone a Hlo Hhi Ha. cbn [rdn].
rewrite Hnone by (rewrite u_Z2bv by lia; lia). reflexivity.
Qed.
Definition C1 : Z := 72340172838076672.
Lemma ALLONES_ones : HZ.ALLONES = Z.ones 64.
Proof. reflexivity. Qed.
Lemma sub_C1_lxor : forall x, 0 <= x < 2^64 ->
(C1 - x) mod 2^64 = Z.lxor ((x + HZ.ONESNEG) mod 2^64) HZ.ALLONES.
Proof.
intros x Hx.
set (y := (x + HZ.ONESNEG) mod 2^64).
assert (Hy : 0 <= y < 2^64) by (subst y; apply Z.mod_pos_bound; lia).
assert (E1 : (C1 - x) mod 2^64 = 2^64 - 1 - y).
{ subst y. unfold C1, HZ.ONESNEG.
destruct (Z_lt_dec (x + 18374403900871474943) (2^64)) as [Hl|Hg].
- rewrite (Z.mod_small (x + _)) by lia.
symmetry. apply Z.mod_unique_pos with (q := 0); lia.
- replace ((x + 18374403900871474943) mod 2^64) with (x + 18374403900871474943 - 2^64)
by (apply Z.mod_unique_pos with (q := 1); lia).
symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E1. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, ALLONES_ones, Z.testbit_ones_nonneg by lia.
replace (2 ^ 64 - 1 - y) with ((Z.lnot y) mod 2^64).
2:{ unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (-y)) 1 (2^64)) by lia.
rewrite Z.mod_small by lia. lia. }
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (i <? 64) eqn:Ei; cbn [andb].
- destruct (Z.testbit y i); reflexivity.
- rewrite (Z_testbit_high 64 y i); [reflexivity|lia|lia|apply Z.ltb_ge in Ei; lia].
Qed.
Lemma haszero_ref_Z : forall x, 0 <= x < 2^64 ->
Z.land (Z.lor ((C1 - x) mod 2^64) x) HZ.HIGHS = HZ.HIGHS - HZ.Tz x.
Proof.
intros x Hx. rewrite sub_C1_lxor by exact Hx.
set (y := (x + HZ.ONESNEG) mod 2^64).
assert (Hy : 0 <= y < 2^64) by (subst y; apply Z.mod_pos_bound; lia).
unfold HZ.Tz. fold y.
set (U := Z.land (Z.lor (Z.lxor y HZ.ALLONES) x) HZ.HIGHS).
set (T := Z.land (Z.land y (Z.lxor x HZ.ALLONES)) HZ.HIGHS).
assert (Hdisj : Z.land U T = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. subst U T.
rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.lxor_spec.
rewrite ALLONES_ones, Z.testbit_ones_nonneg by lia.
destruct (i <? 64) eqn:Ei.
- destruct (Z.testbit y i), (Z.testbit x i), (Z.testbit HZ.HIGHS i); reflexivity.
- apply Z.ltb_ge in Ei.
rewrite (Z_testbit_high 64 y i), (Z_testbit_high 64 x i) by lia. reflexivity. }
assert (Hunion : Z.lor U T = HZ.HIGHS).
{ apply Z.bits_inj'. intros i Hi. subst U T.
rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.lxor_spec.
rewrite ALLONES_ones, Z.testbit_ones_nonneg by lia.
destruct (i <? 64) eqn:Ei.
- destruct (Z.testbit y i), (Z.testbit x i), (Z.testbit HZ.HIGHS i); reflexivity.
- apply Z.ltb_ge in Ei.
rewrite (Z_testbit_high 64 HZ.HIGHS i) by (unfold HZ.HIGHS; lia).
rewrite !andb_false_r. reflexivity. }
pose proof (Z.add_nocarry_lxor U T Hdisj) as Hsum.
rewrite (Z.lxor_lor U T Hdisj), Hunion in Hsum. lia.
Qed.
Lemma haszero_ref : forall v : word,
bv_unsigned (v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS))
= HZ.HIGHS - HZ.Tz (bv_unsigned v).
Proof.
intros v. pose proof (u64_range v) as Hv.
pose proof (HZ.Tz_range (bv_unsigned v)) as HT.
unfold v_and, v_or, v_sub.
rewrite (u_Z2bv C1) by (unfold C1; lia).
rewrite (u_Z2bv HZ.HIGHS) by (unfold HZ.HIGHS; lia).
rewrite (Z_to_bv_unsigned 64 (C1 - _)), bv_wrap64_mod.
assert (H1 : 0 <= (C1 - bv_unsigned v) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
assert (H2 : 0 <= Z.lor ((C1 - bv_unsigned v) mod 2 ^ 64) (bv_unsigned v) < 2^64)
by (apply Z_lor_range; lia).
rewrite (u_Z2bv (Z.lor _ _)) by lia.
rewrite u_Z2bv.
- apply haszero_ref_Z. exact Hv.
- apply Z.land_nonneg. right. unfold HZ.HIGHS. lia.
- pose proof (HZ.land_le_r (Z.lor ((C1 - bv_unsigned v) mod 2 ^ 64) (bv_unsigned v)) HZ.HIGHS ltac:(unfold HZ.HIGHS; lia)).
unfold HZ.HIGHS in *. lia.
Qed.
Lemma step_op_at : forall segs regs pc mem rom w op rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
alu64 op (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_op_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
End f.
Local Ltac stepov F0 D vv tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_op_at with (v := vv);
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Local Ltac steplbu F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Local Ltac stepbt F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Local Ltac stepbf F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Local Ltac stepret F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_jalr_x0; [ exact F | reflexivity | exact D | gr; reflexivity ]
| step_simpl; imm_norm ].
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0.
Proof. reflexivity. Qed.
Lemma eqb_w_true : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a = b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_eq. exact Hab. Qed.
Lemma eqb_w_false : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a <> b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_neq. exact Hab. Qed.
End g.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable s : list byte.
Variable p : word.
Variable mem rom : word -> option byte.
Definition SP : Z := bv_unsigned p.
Definition SLn : Z := Z.of_nat (length s).
Definition SE : Z := SP + SLn.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hp0 : 1 <= bv_unsigned p.
Hypothesis Hfit : bv_unsigned p + Z.of_nat (length s) + 8 < 2 ^ 64.
Hypothesis Hstr : forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Hypothesis Hrd : forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None.
Hypothesis Hrom : forall a : Z, (sl_HIGHS <= a < sl_HIGHS + 8) \/ (sl_ONES <= a < sl_ONES + 8) ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Lemma SE_eq : SE = bv_unsigned p + Z.of_nat (length s). Proof. reflexivity. Qed.
Lemma SP_eq : SP = bv_unsigned p. Proof. reflexivity. Qed.
Lemma SLn_eq : SLn = Z.of_nat (length s). Proof. reflexivity. Qed.
Ltac epl := pose proof SE_eq; pose proof SP_eq; pose proof SLn_eq; pose proof (u64_range p).
Lemma sl_str_nz : forall j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL <> NUL.
Proof. intros j Hj Hc. apply Hnul. rewrite <- Hc. apply nth_app_nul_in. exact Hj. Qed.
Lemma sl_byte_at : forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (SP + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Proof. intros j Hj. unfold SP. apply Hstr. exact Hj. Qed.
Lemma sl_mod8_le : forall q, SP <= q <= SE -> q mod 8 = 0 -> SE mod 8 <= SLn.
Proof.
intros q Hq Hq8. epl.
pose proof (Z.div_mod SE 8 ltac:(lia)) as HD. pose proof (Z.div_mod q 8 ltac:(lia)) as HQ.
pose proof (Z.mod_pos_bound SE 8 ltac:(lia)) as HM.
assert (Hdiv : q / 8 <= SE / 8) by (apply Z.div_le_mono; lia).
unfold SE, SP, SLn in *. lia.
Qed.
Lemma sl_done : forall regs (r : Z),
0 <= r < 2 ^ 64 -> getr regs 10 = p -> getr regs 11 = Z_to_bv 64 r ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x80)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = v_sub (Z_to_bv 64 r) p
/\ (forall x : reg, x <> 10%bv -> getr regs' x = getr regs x).
Proof.
intros regs r Hr H10 H11. epl.
eexists. split.
- norm_pc.
stepov FS_080 DS_080 (v_sub (Z_to_bv 64 r) p) ltac:(rewrite alu_sub; gr; rewrite H10, H11; reflexivity).
stepret FS_084 DS_084. msteps_done.
- split; [gr; reflexivity|]. intros x Hx10. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma sl_sub_len : forall r, r = SE -> v_sub (Z_to_bv 64 r) p = Z_to_bv 64 SLn.
Proof.
intros r ->. epl. unfold v_sub. f_equal.
rewrite (u_Z2bv SE) by (unfold SE, SP, SLn in *; lia).
unfold SE, SP, SLn in *. lia.
Qed.
Lemma sl_tail : forall d regs (q : Z),
(d <= length s)%nat -> q = SE - Z.of_nat d ->
getr regs 10 = p -> getr regs 12 = Z_to_bv 64 q -> getr regs 11 = Z_to_bv 64 (q - 1) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x70)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 SLn
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> getr regs' x = getr regs x).
Proof.
induction d as [|d IH]; intros regs q Hd Hq H10 H12 H11; epl.
-
subst q. rewrite Z.sub_0_r in *.
assert (Hb : nth (length s) (s ++ [NUL]) NUL = NUL) by apply nth_app_nul_last.
set (regs1 := regupd (regupd (regupd regs 13 (Z_to_bv 64 0)) 12 (Z_to_bv 64 (SE + 1))) 11 (Z_to_bv 64 SE)).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x70)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x80)) mem rom)).
{ norm_pc.
steplbu FS_070 DS_070
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_0;
replace (Z_to_bv 64 SE) with (Z_to_bv 64 (SP + Z.of_nat (length s))) by (f_equal; unfold SE, SP, SLn in *; lia);
rewrite sl_byte_at by lia; rewrite Hb; reflexivity).
stepiv' FS_074 DS_074 (Z_to_bv 64 (SE + 1))
ltac:(gr; rewrite H12; imm_norm; unfold v_addi; rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); reflexivity).
stepiv' FS_078 DS_078 (Z_to_bv 64 SE)
ltac:(gr; rewrite H11; imm_norm; unfold v_addi; rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
stepbf FS_07c DS_07c
ltac:(gr; cbn [branch_taken]; unfold bv_eqb; rewrite u_zext8, u_lit0;
vm_compute; reflexivity).
subst regs1. msteps_done. }
destruct (sl_done regs1 SE) as (regs' & Hms & Ha0 & Hfr).
{ unfold SE, SP, SLn in *. lia. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity). exact Hms.
+ split; [rewrite Ha0; apply sl_sub_len; reflexivity|].
intros x Hx10 Hx11 Hx12 Hx13. rewrite (Hfr x Hx10). subst regs1.
rewrite !getr_other by assumption. reflexivity.
-
assert (Hidx : (length s - S d < length s)%nat) by lia.
set (b := nth (length s - S d) (s ++ [NUL]) NUL).
assert (Hb : b <> NUL) by (apply sl_str_nz; lia).
assert (Hqj : q = SP + Z.of_nat (length s - S d)) by (subst q; unfold SE, SP, SLn in *; lia).
set (regs1 := regupd (regupd (regupd regs 13 (Z_to_bv 64 (bv_unsigned b))) 12 (Z_to_bv 64 (q + 1))) 11 (Z_to_bv 64 q)).
destruct (IH regs1 (q + 1)) as (regs' & Hms & Ha0 & Hfr).
{ lia. }
{ subst q. unfold SE, SP, SLn in *. lia. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. f_equal. lia. }
exists regs'. split.
+ eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
steplbu FS_070 DS_070
ltac:(gr; rewrite H12; imm_norm; rewrite v_addi_0; rewrite Hqj; rewrite sl_byte_at by lia; reflexivity).
fold b.
stepiv' FS_074 DS_074 (Z_to_bv 64 (q + 1))
ltac:(gr; rewrite H12; imm_norm; unfold v_addi; rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); reflexivity).
stepiv' FS_078 DS_078 (Z_to_bv 64 q)
ltac:(gr; rewrite H11; imm_norm; unfold v_addi; rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
stepbt FS_07c DS_07c
ltac:(gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
subst regs1. msteps_done.
+ split; [exact Ha0|].
intros x Hx10 Hx11 Hx12 Hx13. rewrite (Hfr x Hx10 Hx11 Hx12 Hx13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma sl_word_at : forall w, SP <= w -> w + 8 <= SE - SE mod 8 + 8 ->
exists bs, rdn tfibsegs mem (Z_to_bv 64 w) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> w + Z.of_nat i <= SE ->
nth i bs NUL = nth (Z.to_nat (w - SP) + i) (s ++ [NUL]) NUL).
Proof.
intros w Hlo Hhi. epl.
assert (Hm2 : 0 <= SE mod 8 < 8) by (apply Z.mod_pos_bound; unfold SE, SP, SLn in *; lia).
destruct (rdn_total tfibsegs mem 8 (Z_to_bv 64 w)) as [bs Hbs].
{ intros k Hk. rewrite word_add_nat, u_Z2bv by (unfold SE, SP, SLn in *; lia).
destruct (Z_lt_le_dec SE (w + Z.of_nat k)) as [Hpast|Hin].
- apply Hrd. unfold SE, SP, SLn in *. lia.
- replace (w + Z.of_nat k) with (SP + Z.of_nat (Z.to_nat (w - SP) + k)) by lia.
rewrite sl_byte_at by (unfold SE, SP, SLn in *; lia). discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi HiE.
pose proof (rdn_nth tfibsegs mem 8 (Z_to_bv 64 w) bs i Hbs ltac:(lia)) as Hn1.
rewrite word_add_nat, u_Z2bv in Hn1 by (unfold SE, SP, SLn in *; lia).
pose proof (sl_byte_at (Z.to_nat (w - SP) + i)%nat ltac:(unfold SE, SP, SLn in *; lia)) as Hn2.
replace (SP + Z.of_nat (Z.to_nat (w - SP) + i)) with (w + Z.of_nat i) in Hn2 by lia.
rewrite Hn1 in Hn2. injection Hn2 as Hn3. exact Hn3.
Qed.
Lemma sl_words : forall k regs (w : Z),
w + 8 * Z.of_nat k = SE - SE mod 8 ->
SP <= w -> SE mod 8 <= SLn ->
getr regs 10 = p ->
getr regs 12 = Z_to_bv 64 (w - 8) ->
getr regs 11 = Z_to_bv 64 (w - 9) ->
getr regs 13 = Z_to_bv 64 C1 ->
getr regs 14 = Z_to_bv 64 HZ.HIGHS ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 SLn
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
x <> 15%bv -> x <> 16%bv -> getr regs' x = getr regs x).
Proof.
induction k as [|k IH]; intros regs w Hk Hpw HrL H10 H12 H11 H13 H14.
all: epl.
all: assert (Hm2 : 0 <= SE mod 8 < 8) by (apply Z.mod_pos_bound; unfold SE, SP, SLn in *; lia).
all: assert (Hwle : w <= SE - SE mod 8) by lia.
all: destruct (sl_word_at w) as (bs & Hbs & Hlen & Hnth); [lia|lia|].
all: set (x := bytes_le_to_Z bs).
all: pose proof (bytes_le_to_Z_range bs Hlen) as Hx; fold x in Hx.
all: set (v := Z_to_bv 64 x).
all: assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
all: set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS)).
all: set (regs6 := regupd (regupd (regupd (regupd (regupd (regupd regs 15 v)
12 (Z_to_bv 64 w))
16 (v_sub (Z_to_bv 64 C1) v))
15 (v_or (v_sub (Z_to_bv 64 C1) v) v))
15 tw)
11 (Z_to_bv 64 (w - 1))).
all: assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) mem rom)
(mkst regs6 (Z_to_bv 64 (tfib_A_musl_strlen + 0x6c)) mem rom)).
1,3: norm_pc;
(chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[exact_lit FS_054 | reflexivity | exact DS_054
| rewrite H12; imm_norm;
replace (v_addi (Z_to_bv 64 (w - 8)) 8) with (Z_to_bv 64 w)
by (unfold v_addi; rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia);
exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ]);
stepiv' FS_058 DS_058 (Z_to_bv 64 w)
ltac:(gr; rewrite H12; imm_norm; unfold v_addi;
rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia);
stepov FS_05c DS_05c (v_sub (Z_to_bv 64 C1) v) ltac:(rewrite alu_sub; gr; rewrite H13; reflexivity);
stepov FS_060 DS_060 (v_or (v_sub (Z_to_bv 64 C1) v) v) ltac:(rewrite alu_or; gr; reflexivity);
stepov FS_064 DS_064 tw ltac:(rewrite alu_and; gr; rewrite H14; reflexivity);
stepiv' FS_068 DS_068 (Z_to_bv 64 (w - 1))
ltac:(gr; rewrite H11; imm_norm; unfold v_addi;
apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; rewrite Zplus_mod_idemp_l; f_equal; lia);
subst regs6; msteps_done.
all: assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz x) by (subst tw; rewrite haszero_ref, Hv; reflexivity).
all: pose proof (HZ.Tz_range x) as HT.
-
assert (Hw : w = SE - SE mod 8) by lia.
assert (HTnz : HZ.Tz x <> 0).
{ apply (HZ.Tz_haszero x (Z.to_nat (SE mod 8))); [lia|lia| |].
- subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
replace (Z.to_nat (w - SP) + Z.to_nat (SE mod 8))%nat with (length s) by (unfold SE, SP, SLn in *; lia).
rewrite nth_app_nul_last. reflexivity.
- intros j Hj. subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
apply byte_nz_u. apply sl_str_nz. unfold SE, SP, SLn in *. lia. }
destruct (sl_tail (Z.to_nat (SE mod 8)) regs6 w) as (regs' & Hms & Ha0 & Hfr).
{ unfold SE, SP, SLn in *. lia. }
{ lia. }
{ subst regs6. gr. exact H10. }
{ subst regs6. gr. reflexivity. }
{ subst regs6. gr. first [reflexivity | f_equal; lia]. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs6 1) by (subst regs6; gr; reflexivity); exact Hms].
norm_pc.
stepbf FS_06c DS_06c
ltac:(subst regs6; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
subst regs6. msteps_done.
+ split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13). subst regs6.
rewrite !getr_other by assumption. reflexivity.
-
assert (HTz : HZ.Tz x = 0).
{ apply HZ.Tz_nozero; [lia|]. intros i Hi. subst x. rewrite zb_of_bytes by lia. fold NUL.
rewrite Hnth by (unfold SE, SP, SLn in *; lia). apply byte_nz_u. apply sl_str_nz.
unfold SE, SP, SLn in *. lia. }
destruct (IH regs6 (w + 8)) as (regs' & Hms & Ha0 & Hfr).
{ lia. } { lia. } { exact HrL. }
{ subst regs6. gr. exact H10. }
{ subst regs6. gr. f_equal. lia. }
{ subst regs6. gr. f_equal. lia. }
{ subst regs6. gr. exact H13. }
{ subst regs6. gr. exact H14. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs6 1) by (subst regs6; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_06c DS_06c
ltac:(subst regs6; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, HTz, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r, Z.eqb_refl; reflexivity).
subst regs6. msteps_done.
+ split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs6. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma rd_ONES : exists bs, rdn tfibsegs mem (Z_to_bv 64 sl_ONES) 8 = Some bs /\ bytes_le_to_Z bs = C1.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 sl_ONES)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. right. lia.
Qed.
Lemma rd_HIGHS8 : exists bs, rdn tfibsegs mem (Z_to_bv 64 sl_HIGHS) 8 = Some bs /\ bytes_le_to_Z bs = HZ.HIGHS.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 sl_HIGHS)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. left. lia.
Qed.
Lemma sl_aligned : forall regs (q : Z),
SP <= q <= SE -> q mod 8 = 0 ->
getr regs 10 = p -> getr regs 12 = Z_to_bv 64 q ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 SLn
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
x <> 15%bv -> x <> 16%bv -> getr regs' x = getr regs x).
Proof.
intros regs q Hq Hq8 H10 H12. epl.
pose proof (sl_mod8_le q Hq Hq8) as HrL.
assert (Hm2 : 0 <= SE mod 8 < 8) by (apply Z.mod_pos_bound; unfold SE, SP, SLn in *; lia).
destruct rd_ONES as (bs1 & Hbs1 & Hv1).
destruct rd_HIGHS8 as (bs2 & Hbs2 & Hv2).
pose proof tfib_strlen_ld_targets as [LT1 LT2].
set (regs1 := regupd (regupd (regupd (regupd (regupd (regupd regs
11 (Z_to_bv 64 tfib_strlen_aui1))
14 (Z_to_bv 64 tfib_strlen_aui2))
13 (Z_to_bv 64 C1))
14 (Z_to_bv 64 HZ.HIGHS))
11 (Z_to_bv 64 (q - 9)))
12 (Z_to_bv 64 (q - 8))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x3c)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x54)) mem rom)).
{ norm_pc.
stepiv' FS_03c DS_03c (Z_to_bv 64 tfib_strlen_aui1) ltac:(bveq).
stepiv' FS_040 DS_040 (Z_to_bv 64 tfib_strlen_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FS_044 | reflexivity | exact DS_044
| gr; match goal with |- rdn _ _ ?a _ = _ =>
replace a with (Z_to_bv 64 sl_ONES) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FS_048 | reflexivity | exact DS_048
| gr; match goal with |- rdn _ _ ?a _ = _ =>
replace a with (Z_to_bv 64 sl_HIGHS) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepiv' FS_04c DS_04c (Z_to_bv 64 (q - 9))
ltac:(gr; rewrite H12; imm_norm; unfold v_addi;
rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
stepiv' FS_050 DS_050 (Z_to_bv 64 (q - 8))
ltac:(gr; rewrite H12; imm_norm; unfold v_addi;
rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
subst regs1. msteps_done. }
assert (HD8 : SE - SE mod 8 = 8 * (SE / 8)) by (pose proof (Z.div_mod SE 8 ltac:(lia)); lia).
assert (HQ8 : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Hdiv : q / 8 <= SE / 8) by (apply Z.div_le_mono; unfold SE, SP, SLn in *; lia).
destruct (sl_words (Z.to_nat (SE / 8 - q / 8)) regs1 q) as (regs' & Hms & Ha0 & Hfr).
{ rewrite Z2Nat.id by lia. lia. }
{ lia. } { exact HrL. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
- eapply msteps_trans; [exact Hpre|].
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity). exact Hms.
- split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma sl_pro_head : forall regs (j : nat),
SP + Z.of_nat j + 1 < 2 ^ 64 -> getr regs 11 = Z_to_bv 64 (SP + Z.of_nat j) ->
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) mem rom)
(mkst (regupd (regupd regs 13 (Z_to_bv 64 (SP + Z.of_nat j + 1))) 13
(Z_to_bv 64 ((SP + Z.of_nat j + 1) mod 8))) (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) mem rom).
Proof.
intros regs j Hlt H11. epl.
assert (Hm8 : 0 <= (SP + Z.of_nat j + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
norm_pc.
stepiv' FS_01c DS_01c (Z_to_bv 64 (SP + Z.of_nat j + 1))
ltac:(gr; rewrite H11; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepiv' FS_020 DS_020 (Z_to_bv 64 ((SP + Z.of_nat j + 1) mod 8))
ltac:(gr; imm_norm; unfold v_andi; rewrite u_Z2bv by lia;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
msteps_done.
Qed.
Lemma sl_pro : forall m regs (j : nat),
SP mod 8 <> 0 -> (0 < m)%nat -> Z.of_nat j + Z.of_nat m = 8 - SP mod 8 -> (j < length s)%nat ->
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 (SP + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 (SP + Z.of_nat j + 1) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x1c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 SLn
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
x <> 15%bv -> x <> 16%bv -> getr regs' x = getr regs x).
Proof.
induction m as [|m IH]; intros regs j HA Hm Hjm Hj H10 H11 H12; [lia|]; epl;
assert (HA8 : 0 <= SP mod 8 < 8) by (apply Z.mod_pos_bound; lia);
assert (HSP8 : SP = 8 * (SP / 8) + SP mod 8) by (apply Z.div_mod; lia);
assert (Hjlt : SP + Z.of_nat j + 1 < 2 ^ 64) by (unfold SE, SP, SLn in *; lia);
set (regs1 := regupd (regupd regs 13 (Z_to_bv 64 (SP + Z.of_nat j + 1))) 13
(Z_to_bv 64 ((SP + Z.of_nat j + 1) mod 8)));
pose proof (sl_pro_head regs j Hjlt H11) as Hpre;
fold regs1 in Hpre.
destruct (Z.eq_dec ((SP + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
+
destruct (sl_aligned regs1 (SP + Z.of_nat j + 1)) as (regs' & Hms & Ha0 & Hfr).
{ unfold SE, SP, SLn in *. lia. }
{ exact Hal. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. exact H12. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_024 DS_024 ltac:(subst regs1; gr; rewrite Hal; vm_compute; reflexivity).
msteps_done.
* split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs1. rewrite !getr_other by assumption. reflexivity.
+
set (b := nth (S j) (s ++ [NUL]) NUL).
set (regs2 := regupd (regupd (regupd regs1 13 (Z_to_bv 64 (bv_unsigned b)))
12 (Z_to_bv 64 (SP + Z.of_nat j + 2)))
11 (Z_to_bv 64 (SP + Z.of_nat j + 1))).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x24)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_strlen + 0x34)) mem rom)).
{ norm_pc.
stepbf FS_024 DS_024 ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
steplbu FS_028 DS_028
ltac:(subst regs1; gr; rewrite H12; imm_norm; rewrite v_addi_0;
replace (Z_to_bv 64 (SP + Z.of_nat j + 1)) with (Z_to_bv 64 (SP + Z.of_nat (S j))) by (f_equal; lia);
rewrite sl_byte_at by lia; reflexivity).
fold b.
stepiv' FS_02c DS_02c (Z_to_bv 64 (SP + Z.of_nat j + 2))
ltac:(subst regs1; gr; rewrite H12; imm_norm; unfold v_addi;
rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
stepiv' FS_030 DS_030 (Z_to_bv 64 (SP + Z.of_nat j + 1))
ltac:(subst regs1; gr; rewrite H11; imm_norm; unfold v_addi;
rewrite u_Z2bv by (unfold SE, SP, SLn in *; lia); f_equal; lia).
subst regs2 regs1. msteps_done. }
destruct (Nat.eq_dec (S j) (length s)) as [HjL|HjL].
*
assert (Hb : b = NUL) by (subst b; rewrite HjL; apply nth_app_nul_last).
destruct (sl_done regs2 (SP + Z.of_nat j + 1)) as (regs' & Hms & Ha0 & Hfr).
{ unfold SE, SP, SLn in *. lia. }
{ subst regs2 regs1. gr. exact H10. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FS_034 DS_034
ltac:(subst regs2 regs1; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0, Hb; vm_compute; reflexivity).
stepj' FS_038 DS_038. msteps_done.
-- split.
++ rewrite Ha0. apply sl_sub_len. unfold SE, SP, SLn in *. lia.
++ intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
*
assert (Hb : b <> NUL) by (apply sl_str_nz; lia).
assert (Hm' : (0 < m)%nat).
{ destruct m; [|lia]. exfalso. apply Hal.
replace (SP + Z.of_nat j + 1) with (8 * (SP / 8 + 1)) by lia.
rewrite Z.mul_comm. apply Z_mod_mult. }
destruct (IH regs2 (S j)) as (regs' & Hms & Ha0 & Hfr).
{ exact HA. } { exact Hm'. } { lia. } { lia. }
{ subst regs2 regs1. gr. exact H10. }
{ subst regs2 regs1. gr. first [reflexivity | f_equal; lia]. }
{ subst regs2 regs1. gr. first [reflexivity | f_equal; lia]. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_034 DS_034
ltac:(subst regs2 regs1; gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
subst regs2 regs1. msteps_done.
-- split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma ref_strlen_sec : forall regs,
getr regs 10 = p ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 SLn
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
x <> 15%bv -> x <> 16%bv -> getr regs' x = getr regs x).
Proof.
intros regs H10. epl.
assert (HA8 : 0 <= SP mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd regs 11 (Z_to_bv 64 (SP mod 8))) 12 (Z_to_bv 64 SP)).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) mem rom)).
{ norm_pc.
stepiv' FS_000 DS_000 (Z_to_bv 64 (SP mod 8))
ltac:(gr; rewrite H10; imm_norm; unfold v_andi;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepiv' FS_004 DS_004 (Z_to_bv 64 SP)
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; unfold SP; symmetry; apply Z_to_bv_bv_unsigned).
subst regs1. msteps_done. }
destruct (Z.eq_dec (SP mod 8) 0) as [HA|HA].
-
destruct (sl_aligned regs1 SP) as (regs' & Hms & Ha0 & Hfr).
{ unfold SE, SP, SLn in *. lia. }
{ exact HA. }
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FS_008 DS_008 ltac:(subst regs1; gr; rewrite HA; vm_compute; reflexivity).
msteps_done.
+ split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs1. rewrite !getr_other by assumption. reflexivity.
-
set (b0 := nth 0 (s ++ [NUL]) NUL).
set (regs2 := regupd regs1 11 (Z_to_bv 64 (bv_unsigned b0))).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_strlen + 0x8)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_strlen + 0x10)) mem rom)).
{ norm_pc.
stepbf FS_008 DS_008 ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
steplbu FS_00c DS_00c
ltac:(subst regs1; gr; rewrite H10; imm_norm; rewrite v_addi_0;
replace p with (Z_to_bv 64 (SP + Z.of_nat 0)) by (unfold SP; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned);
rewrite sl_byte_at by lia; reflexivity).
subst regs2 regs1. msteps_done. }
destruct (Nat.eq_dec (length s) 0) as [HL0|HL0].
+
assert (Hb : b0 = NUL) by (subst b0; destruct s; [reflexivity | cbn in HL0; lia]).
eexists. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
norm_pc.
stepbt FS_010 DS_010
ltac:(subst regs2 regs1; gr; rewrite Hb; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; vm_compute; reflexivity).
stepov FS_088 DS_088 (v_sub p p) ltac:(rewrite alu_sub; subst regs2 regs1; gr; rewrite H10; reflexivity).
stepret FS_08c DS_08c. try (subst regs2 regs1). gr. msteps_done.
* split.
-- gr. unfold v_sub, SLn. rewrite HL0. apply bv_eq. rewrite Z.sub_diag.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
cbn. reflexivity.
-- intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
+
assert (Hb : b0 <> NUL) by (apply sl_str_nz; lia).
set (regs3 := regupd (regupd regs2 12 (Z_to_bv 64 (SP + 1))) 11 (Z_to_bv 64 SP)).
destruct (sl_pro (Z.to_nat (8 - SP mod 8)) regs3 0) as (regs' & Hms & Ha0 & Hfr).
{ exact HA. } { lia. } { cbn [Z.of_nat]. lia. } { lia. }
{ subst regs3 regs2 regs1. gr. exact H10. }
{ subst regs3 regs2 regs1. gr. first [reflexivity | f_equal; lia]. }
{ subst regs3 regs2 regs1. gr. first [reflexivity | f_equal; lia]. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FS_010 DS_010
ltac:(subst regs2 regs1; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FS_014 DS_014 (Z_to_bv 64 (SP + 1))
ltac:(subst regs2 regs1; gr; rewrite H10; imm_norm; unfold v_addi; unfold SP; reflexivity).
stepiv' FS_018 DS_018 (Z_to_bv 64 SP)
ltac:(subst regs2 regs1; gr; rewrite H10; imm_norm; rewrite v_addi_0;
unfold SP; symmetry; apply Z_to_bv_bv_unsigned).
subst regs3 regs2 regs1. msteps_done.
* split; [exact Ha0|].
intros y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16. rewrite (Hfr y Hy10 Hy11 Hy12 Hy13 Hy14 Hy15 Hy16).
subst regs3 regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
End h.
Theorem musl_strlen_walk :
forall (s : list byte) (p : word) (mem rom : word -> option byte) regs,
~ In NUL s ->
1 <= bv_unsigned p ->
bv_unsigned p + Z.of_nat (length s) + 8 < 2 ^ 64 ->
(forall j, (j <= length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
(forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None) ->
(forall a : Z, (sl_HIGHS <= a < sl_HIGHS + 8) \/ (sl_ONES <= a < sl_ONES + 8) ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
getr regs 10 = p ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_strlen) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv ->
x <> 15%bv -> x <> 16%bv -> getr regs' x = getr regs x).
Proof.
intros s p mem rom regs Hnul Hp0 Hfit Hstr Hrd Hrom H10.
change (Z_to_bv 64 tfib_A_musl_strlen) with (Z_to_bv 64 (tfib_A_musl_strlen + 0x0)).
exact (ref_strlen_sec s p mem rom Hnul Hp0 Hfit Hstr Hrd Hrom regs H10).
Qed.
End g.
