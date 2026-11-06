(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBTemplate.v, with its module names changed; 218 of its 260 lines of code are new or changed and 146 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition CA_GP : Z := 0xa5b20.
Definition CA_SEG : Z := 0xE50.
Definition CA_RET : Z := 0x1298.

Fixpoint ca_bchunks (base : Z) (L : list byte) : list YP09.chunk :=
match L with
| nil => nil
| b :: L' => YP09.mkChunk base (CVal 1 (SLit (bv_unsigned b))) :: ca_bchunks (base + 1) L'
end.

Fixpoint ca_zchunks (base : Z) (L : list Z) : list YP09.chunk :=
match L with
| nil => nil
| v :: L' => YP09.mkChunk base (CVal 1 (SLit v)) :: ca_zchunks (base + 1) L'
end.

Fixpoint ca_wchunks (base : Z) (L : list byte) : list YP09.chunk :=
match L with
| b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: L' =>
  YP09.mkChunk base (CVal 8 (SLit (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7]))) :: ca_wchunks (base + 8) L'
| _ => nil
end.

Definition ca_syn_list : list (list byte) := [RO_lit_21200;RO_lit_21280;RO_lit_212c0;RO_lit_21320;RO_lit_213a0;RO_lit_21400;RO_lit_21460;RO_lit_214c0;RO_lit_21540;RO_lit_215e0;RO_lit_21620;RO_lit_216a0;RO_lit_212c0;RO_lit_216c0;RO_lit_21720;RO_lit_217a0;RO_lit_216a0;RO_lit_216a0;RO_lit_21820;RO_lit_21180;RO_lit_211a0;RO_lit_21100].
Definition ca_name_list : list (list byte) := [RO_lit_211e0;RO_lit_21260;RO_lit_212a0;RO_lit_212e0;RO_lit_21360;RO_lit_213e0;RO_lit_21440;RO_lit_214a0;RO_lit_21520;RO_lit_215c0;RO_lit_21600;RO_lit_21680;RO_lit_21140;RO_lit_21160;RO_lit_21700;RO_lit_21780;RO_lit_217c0;RO_lit_217e0;RO_lit_21800;RO_lit_21840;RO_lit_21860;RO_lit_21100].
Definition ca_syn_addr (k : nat) : Z := nth k [0x21200;0x21280;0x212c0;0x21320;0x213a0;0x21400;0x21460;0x214c0;0x21540;0x215e0;0x21620;0x216a0;0x212c0;0x216c0;0x21720;0x217a0;0x216a0;0x216a0;0x21820;0x21180;0x211a0;0x21100] 0.
Definition ca_name_addr (k : nat) : Z := nth k [0x211e0;0x21260;0x212a0;0x212e0;0x21360;0x213e0;0x21440;0x214a0;0x21520;0x215c0;0x21600;0x21680;0x21140;0x21160;0x21700;0x21780;0x217c0;0x217e0;0x21800;0x21840;0x21860;0x21100] 0.
Definition ca_syn_bytes (k : nat) : list byte := nth k ca_syn_list nil.
Definition ca_name_bytes (k : nat) : list byte := nth k ca_name_list nil.
Definition ca_syn_sh (k : nat) : list Z := nth k [[0;0;0;0;0;0;0;5];[1];[0;3];[0;0;1];[0;0;1];[0;0;0;7];[0;0;7];[0;0;0;0;3];[0;0;0;0;0;0;0;0;0;0;1];[0;4];[0;0;0;0;0;4];[6];[0;3];[0;0;0;5];[0;0;0;0;4];[0];[6];[6];[0;2];[0;6];[0;0;1];[5]] nil.

Definition ca_syn (k : nat) : YP09.region :=
YP09.mkRegion None (ca_syn_addr k) (ca_syn_addr k + Z.of_nat (length (ca_syn_bytes k))) 0 0
(ca_bchunks (ca_syn_addr k) (ca_syn_bytes k)).
Definition ca_synsh (k : nat) : YP09.region :=
YP09.mkRegion None (SHADOW_OFF + ca_syn_addr k / 8) (SHADOW_OFF + ca_syn_addr k / 8 + Z.of_nat (length (ca_syn_sh k))) 0 0
(ca_zchunks (SHADOW_OFF + ca_syn_addr k / 8) (ca_syn_sh k)).
Definition ca_gparsed : YP09.region :=
YP09.mkRegion None CA_GP (CA_GP + 672) 0 0 (ca_wchunks CA_GP RO_g_parsed).
Definition ca_gpsh : YP09.region :=
YP09.mkRegion None (SHADOW_OFF + 0x14b64) (SHADOW_OFF + 0x14ba6) 0 0 [YP09.mkChunk (SHADOW_OFF + 0x14b64) (CZero 66)].
Definition ca_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 112 0 8
(map (fun j => YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 13)).
Definition ca_facts (mn mx : Z) : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF mn mx 0)] [] [].
Definition ca_regs (k : nat) : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
 9 (SLit (CA_GP + 24 * Z.of_nat k))) 18 (SLit SHADOW_OFF)) 19 (SOff 32 0))
 21 (SLit (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)))) 22 (SLit CA_GP).
Definition ca_ss (k : nat) (mn mx : Z) : sstate :=
mkSS CA_SEG (ca_regs k) [ca_frame; ca_gparsed; ca_gpsh; ca_synsh k; ca_syn k] None (ca_facts mn mx).

Lemma ca_opt_zero : forall (o : option byte), option_map (fun b : byte => bv_unsigned b) o = Some 0 -> o = Some (Z_to_bv 8 0).
Proof.
intros [b|] H; [|discriminate]. cbn [option_map] in H. injection H as H. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned, H. reflexivity.
Qed.

Lemma ca_opt_byte : forall (o : option byte) (b : byte),
option_map (fun x : byte => bv_unsigned x) o = Some (bv_unsigned b) -> o = Some b.
Proof.
intros [c|] b H; [|discriminate]. cbn [option_map] in H. injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Lemma ca_opt_val : forall (o : option byte) (v : Z), 0 <= v < 256 ->
option_map (fun x : byte => bv_unsigned x) o = Some v -> o = Some (Z_to_bv 8 v).
Proof.
intros [c|] v Hv H; [|discriminate]. cbn [option_map] in H. injection H as H. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite H. symmetry. apply Z.mod_small. exact Hv.
Qed.

Ltac ca_pick t := first [exact (proj1 t) | exact t | ca_pick (proj2 t)].

Lemma ca_ro_syn : forall rd, cmd_ro_bytes rd -> forall k, (k < 22)%nat -> abytes_atR rd (ca_syn_addr k) (ca_syn_bytes k).
Proof.
intros rd H k Hk. unfold cmd_ro_bytes in H.
do 22 (destruct k as [|k]; [cbn [ca_syn_addr ca_syn_bytes ca_syn_list nth]; ca_pick H|]). lia.
Qed.

Lemma ca_ro_name : forall rd, cmd_ro_bytes rd -> forall k, (k < 22)%nat -> abytes_atR rd (ca_name_addr k) (ca_name_bytes k).
Proof.
intros rd H k Hk. unfold cmd_ro_bytes in H.
do 22 (destruct k as [|k]; [cbn [ca_name_addr ca_name_bytes ca_name_list nth]; ca_pick H|]). lia.
Qed.

Lemma ca_ro_gp : forall rd, cmd_ro_bytes rd -> abytes_atR rd CA_GP RO_g_parsed.
Proof. intros rd H. unfold cmd_ro_bytes in H. unfold CA_GP. ca_pick H. Qed.

Lemma ca_syn_bound : forall k, (k < 22)%nat ->
0x21100 <= ca_syn_addr k /\ ca_syn_addr k mod 8 = 0 /\
ca_syn_addr k + Z.of_nat (length (ca_syn_bytes k)) <= 0x21880 /\
8 * Z.of_nat (length (ca_syn_sh k)) - 8 < Z.of_nat (length (ca_syn_bytes k)) <= 8 * Z.of_nat (length (ca_syn_sh k)).
Proof.
intros k Hk. do 22 (destruct k as [|k]; [vm_compute; repeat split; intro; discriminate|]). lia.
Qed.

Definition aexp_eq_dec : forall x y : aexp, {x = y} + {x <> y}.
Proof. decide equality; (apply Z.eq_dec || apply Nat.eq_dec). Defined.
Definition aval_eq_dec : forall x y : aval, {x = y} + {x <> y}.
Proof. decide equality; (apply aexp_eq_dec || apply Z.eq_dec). Defined.
Definition acell_eq_dec : forall x y : acell, {x = y} + {x <> y}.
Proof. decide equality; (apply aval_eq_dec || apply Nat.eq_dec || apply aexp_eq_dec). Defined.

Lemma ca_in_dec : forall (x : acell) (l : list acell),
(if in_dec acell_eq_dec x l then true else false) = true -> In x l.
Proof. intros x l H. destruct (in_dec acell_eq_dec x l) as [Y|N]; [exact Y | discriminate]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).

Lemma ca_byte_val : forall (m : word -> option byte) a (b : byte),
YP09.mbyte SEGS m a = Some b -> YI04.val_mem SEGS m a 1 (bv_unsigned b).
Proof.
intros m a b H k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
rewrite (YI04.le_byte_small (bv_unsigned b) 1 0) by (cbn [Z.of_nat]; change (2 ^ (8 * 1)) with 256; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ca_zbyte_val : forall (m : word -> option byte) a v, 0 <= v < 256 ->
YP09.mbyte SEGS m a = Some (Z_to_bv 8 v) -> YI04.val_mem SEGS m a 1 v.
Proof.
intros m a v Hv H k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
rewrite (YI04.le_byte_small v 1 0) by (cbn [Z.of_nat]; change (2 ^ (8 * 1)) with 256; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma ca_bchunks_ok : forall E (m : word -> option byte) base L,
(forall i, (i < length L)%nat -> YP09.mbyte SEGS m (base + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0))) ->
Forall (YP09.chunk_ok SEGS E m 0) (ca_bchunks base L).
Proof.
intros E m base L. revert base. induction L as [|b L IH]; intros base HB; cbn [ca_bchunks]; [constructor|].
constructor.
- apply (YI04.chunk_ok_val SEGS E m 0 base 1 (SLit (bv_unsigned b)) (bv_unsigned b)).
  + reflexivity.
  + pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
    change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  + cbn. lia.
  + rewrite Z.add_0_l. apply ca_byte_val.
    pose proof (HB 0%nat ltac:(cbn [length]; lia)) as H0. cbn [Z.of_nat nth] in H0.
    rewrite Z.add_0_r in H0. exact H0.
- apply IH. intros i Hi. replace (base + 1 + Z.of_nat i) with (base + Z.of_nat (S i)) by lia.
  exact (HB (S i) ltac:(cbn [length] in *; lia)).
Qed.

Lemma ca_zchunks_ok : forall E (m : word -> option byte) base L,
Forall (fun v => 0 <= v < 256) L ->
(forall i, (i < length L)%nat -> YP09.mbyte SEGS m (base + Z.of_nat i) = Some (Z_to_bv 8 (nth i L 0))) ->
Forall (YP09.chunk_ok SEGS E m 0) (ca_zchunks base L).
Proof.
intros E m base L. revert base. induction L as [|v L IH]; intros base HR HB; cbn [ca_zchunks]; [constructor|].
inversion HR as [|vv ll Hv HRest]; subst.
constructor.
- apply (YI04.chunk_ok_val SEGS E m 0 base 1 (SLit v) v).
  + reflexivity.
  + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  + cbn. lia.
  + rewrite Z.add_0_l. apply ca_zbyte_val; [lia|].
    pose proof (HB 0%nat ltac:(cbn [length]; lia)) as H0. cbn [Z.of_nat nth] in H0.
    rewrite Z.add_0_r in H0. exact H0.
- apply IH; [exact HRest|]. intros i Hi. replace (base + 1 + Z.of_nat i) with (base + Z.of_nat (S i)) by lia.
  exact (HB (S i) ltac:(cbn [length] in *; lia)).
Qed.

Lemma ca_word_val : forall (m : word -> option byte) base (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
(forall i, (i < 8)%nat -> YP09.mbyte SEGS m (base + Z.of_nat i) = Some (nth i [b0;b1;b2;b3;b4;b5;b6;b7] (Z_to_bv 8 0))) ->
YI04.val_mem SEGS m base 8 (bytes_le_to_Z [b0;b1;b2;b3;b4;b5;b6;b7]).
Proof.
intros m base b0 b1 b2 b3 b4 b5 b6 b7 HB k Hk.
rewrite (HB k Hk). f_equal.
pose proof (bytes_le_to_Z_bound [b0;b1;b2;b3;b4;b5;b6;b7]) as Hbd. cbn [length] in Hbd.
pose proof (bytes_le_to_Z_nonneg [b0;b1;b2;b3;b4;b5;b6;b7]) as Hnn.
rewrite (YI04.le_byte_small (bytes_le_to_Z [b0;b1;b2;b3;b4;b5;b6;b7]) 8 k) by lia.
assert (Hn : nth_error [b0;b1;b2;b3;b4;b5;b6;b7] k = Some (nth k [b0;b1;b2;b3;b4;b5;b6;b7] (Z_to_bv 8 0)))
by (apply nth_error_nth'; cbn [length]; lia).
pose proof (YA0j.nth_error_le_byte [b0;b1;b2;b3;b4;b5;b6;b7] k _ Hn) as Hb.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite Hb. reflexivity.
Qed.

Lemma ca_wchunks_okn : forall n E (m : word -> option byte) base L, (length L <= n)%nat ->
(forall i, (i < length L)%nat -> YP09.mbyte SEGS m (base + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0))) ->
Forall (YP09.chunk_ok SEGS E m 0) (ca_wchunks base L).
Proof.
induction n as [|n IH]; intros E m base L Hn HB.
- destruct L as [|b L]; [cbn [ca_wchunks]; constructor|]. cbn [length] in Hn. lia.
- destruct L as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 L]]]]]]]];
  try (cbn [ca_wchunks]; constructor; fail).
  cbn [ca_wchunks]. constructor.
  + apply (YI04.chunk_ok_val SEGS E m 0 base 8 (SLit (bytes_le_to_Z [b0;b1;b2;b3;b4;b5;b6;b7]))
      (bytes_le_to_Z [b0;b1;b2;b3;b4;b5;b6;b7])).
    * reflexivity.
    * pose proof (bytes_le_to_Z_bound [b0;b1;b2;b3;b4;b5;b6;b7]) as Hbd.
      pose proof (bytes_le_to_Z_nonneg [b0;b1;b2;b3;b4;b5;b6;b7]) as Hnn.
      cbn [length] in Hbd. change (2 ^ (8 * Z.of_N 8)) with (2 ^ (8 * Z.of_nat 8)). lia.
    * cbn. lia.
    * rewrite Z.add_0_l. apply ca_word_val. intros i Hi.
      assert (Hlt : (i < length (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: L))%nat) by (cbn [length]; lia).
      pose proof (HB i Hlt) as HBi.
      destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth] in HBi |- *; try exact HBi; cbn [length] in Hi; lia.
  + apply (IH E m (base + 8) L); [cbn [length] in Hn; lia|].
    intros i Hi. replace (base + 8 + Z.of_nat i) with (base + Z.of_nat (8 + i)) by lia.
    exact (HB (8 + i)%nat ltac:(cbn [length] in *; lia)).
Qed.

Lemma ca_wchunks_ok : forall E (m : word -> option byte) base L,
(forall i, (i < length L)%nat -> YP09.mbyte SEGS m (base + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0))) ->
Forall (YP09.chunk_ok SEGS E m 0) (ca_wchunks base L).
Proof. intros E m base L HB. exact (ca_wchunks_okn (length L) E m base L (le_n _) HB). Qed.

Lemma ca_bytes_mbyte : forall (W : world SEGS) mem a L,
abytes_atR (aview SEGS (w_H W) mem) a L ->
forall i, (i < length L)%nat -> YP09.mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0)).
Proof. intros W mem a L H i Hi. apply ca_opt_byte. exact (H i Hi). Qed.

Definition ca_sv (regs0 : bvmap 5 word) : list word :=
[getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20;
 getr regs0 21; getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27].
Definition ca_extra (s3v : Z) (regs0 : bvmap 5 word) : list word := Z_to_bv 64 s3v :: ca_sv regs0.
Definition ca_frame_at (W : world SEGS) (mem : word -> option byte) (sp : Z) (regs0 : bvmap 5 word) : Prop :=
forall j, (j < 13)%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) mem) (sp + 104 - 8 * Z.of_nat j) 8
(bv_unsigned (nth j (ca_sv regs0) (Z_to_bv 64 0))).

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_zsh_range : forall ly S (W : world SEGS) mem md r a n,
AR SEGS B ly S W mem md -> In r Tfib_zero_shadow ->
fst r mod 8 = 0 -> a mod 8 = 0 -> fst r <= a -> a + 8 * n <= fst r + snd r -> 0 <= n ->
forall i, 0 <= i < n -> YP09.mbyte SEGS (mrestrict (w_H W) mem) (SHADOW_OFF + a / 8 + i) = Some (Z_to_bv 8 0).
Proof.
intros ly S W mem md r a n HAR Hin Hr Ha Hlo Hhi Hn i Hi.
pose proof (cmd_zshadow_sub SEGS B LAWS HB ly S W mem md r a (8 * n) HAR Hin Hr Ha Hlo Hhi) as HZ.
apply ca_opt_zero.
replace (SHADOW_OFF + a / 8 + i) with (shadow_of_addr SHADOW_OFF a + i) by (unfold shadow_of_addr; lia).
apply HZ. rewrite (Z.mul_comm 8 n), Z_div_mult by lia. lia.
Qed.

Lemma ca_const_byte : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> In (z1 (ANum a) v) (Tfib_const_abs ++ Tfib_const_shadow) -> 0 <= v < 256 ->
YP09.mbyte SEGS (mrestrict (w_H W) mem) a = Some (Z_to_bv 8 v).
Proof.
intros ly S W mem md a v HAR Hin Hv.
pose proof (am_const B ly S (aview SEGS (w_H W) mem) (proj1 HAR)) as HC.
rewrite (ts_const B HB ly) in HC. unfold Tfib_const in HC.
rewrite Forall_forall in HC.
pose proof (HC (z1 (ANum a) v) ltac:(apply in_or_app; right; exact Hin)) as HH.
unfold cell_holds, z1, c1 in HH. cbn [c_at c_w c_val aeval] in HH.
pose proof (HH 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
apply ca_opt_val; [exact Hv|]. unfold aview in H0. rewrite H0. f_equal.
cbn [aeval]. unfold YG0f.le_byte.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

End e.
End f.
End d.
