(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 996 of its 1134 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_scan.v (a working branch
   50b05668b91 line), the same lemma names over B's own code (B listing: capstone over the unstripped twin of
   fs.asan-ubsan, sha256 b1566a1c..., bytes 0x8164c .. 0x81b5c equal to the pinned image's).
   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane). *)
(* check_as_written (fs.asan-ubsan 0x8164c): the SCAN LOOP of the inlined expected_body (fs.c:78-90), machine code
   0x8170c .. 0x81800 (head 0x8170c), walked with the token engine (FSW_K fsw_aj_run_to_tokU) from the loop state of
   FSW_caw_defs (caw_ss1). One lemma, caw_scan_loop, in continuation-passing form: from the head state at text index j
   the machine reaches one of B's two loop exits, and the goal is any Q that a continuation hypothesis discharges there
   (caw_post):
   - the NUL after the last character: `beqz a2` at 0x8179c to 0x81804, state caw_ssX, b64_scan of the rest is
     Some (sx', pad'), six[0, m') holds sx';
   - a refused character (no whitespace, '=' or sextet, or a sextet after '='): `bltz t4` / `bnez t3` at 0x817b8 /
     0x817bc straight to 0x81a78 (`jal __wrap_free` of six) with s5 = SIZE_MAX, state caw_ssB, b64_scan of the rest is
     None (A's code re-read the byte at its single exit; B's does not).
   Proved by induction on the rest of the text; one iteration per character class of the classification (0x8170c ..
   0x8176c, the same tests as A's), each class walked with the branches the engine leaves undecided taken by hand
   (SRr_sym_branch), and the atoms re-keyed at the next head by YL09.st_ok_reabs.
   B's UBSan traps in the loop (`beq s3, a7` 0x8177c, `blt a2, t3` 0x817ac, `bltu a3, a4` 0x817c0, all to the `unimp`
   at 0x81ad4) are DECIDED UNTAKEN by the engine (MEASURED, probe runs over the pinned image): s3 = text + j lies in
   [4096, CAW_CEIL] and a7 is SIZE_MAX; `addiw a2, t3, 1` folds to t3 + 1 since pad <= 3145728; a3 = ~six (atom 30)
   lies above every m. No branch to 0x81ad4 is left to the walk and no __asan_report_* call is reached (the shadow
   checks at 0x81780 and 0x817c8 are the token engine's, discharged by caw_SHs).
   The frame the continuation gets is the runs' own: each iteration's write windows are the stack frame
   [spE - 64, spE) and the byte six[m] of the head (FSW_caw_defs caw_six1), also when the iteration stores nothing,
   so memory is kept outside [six, six + m' + 1) (m' the sextets at the exit) and the stack window.
   The loop's shadow entries are caw_SHs: FSW_caw_defs caw_SH1 and the byte text + j + 1 through a1 (atom 36), which
   the check at 0x81780 reads.
   Section hypotheses: none. Every premise is stated in caw_scan_loop; its assumptions are Rocq's primitive
   integers / strings / arrays and functional_extensionality_dep (toolchain/allowed-axioms.txt), through the kit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL02 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_caw_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_caw_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the pure facts of the scan ---- *)
Lemma caw_scan_app : forall l1 l2 pad six,
  WriterSpec.b64_scan pad six (l1 ++ l2) =
  match WriterSpec.b64_scan pad six l1 with Some (s, p) => WriterSpec.b64_scan p s l2 | None => None end.
Proof.
induction l1 as [|c l1 IH]; intros l2 pad six; [reflexivity|].
cbn [app WriterSpec.b64_scan].
destruct (WriterSpec.b64_ws c); [apply IH|]. destruct (c =? 61); [apply IH|].
destruct (WriterSpec.b64v c) as [v|]; [|reflexivity]. destruct (pad =? 0); [apply IH | reflexivity].
Qed.
Lemma caw_scan_bound : forall l pad six six' pad', WriterSpec.b64_scan pad six l = Some (six', pad') ->
  (length six <= length six')%nat /\ pad <= pad' /\
  Z.of_nat (length six') + pad' <= Z.of_nat (length six) + pad + Z.of_nat (length l).
Proof.
induction l as [|c l IH]; intros pad six six' pad' H; cbn [WriterSpec.b64_scan] in H.
- injection H as <- <-. cbn [length]. lia.
- cbn [length]. destruct (WriterSpec.b64_ws c); [apply IH in H; lia|].
  destruct (c =? 61); [apply IH in H; lia|].
  destruct (WriterSpec.b64v c) as [v|]; [|discriminate]. destruct (pad =? 0); [|discriminate].
  apply IH in H. rewrite length_app in H. cbn [length] in H. lia.
Qed.
Lemma caw_scan_six : forall l pad six six' pad', WriterSpec.b64_scan pad six l = Some (six', pad') ->
  Forall (fun v => 0 <= v < 64) six -> Forall (fun v => 0 <= v < 64) six'.
Proof.
induction l as [|c l IH]; intros pad six six' pad' H Hs; cbn [WriterSpec.b64_scan] in H.
- injection H as <- <-. exact Hs.
- destruct (WriterSpec.b64_ws c); [exact (IH _ _ _ _ H Hs)|].
  destruct (c =? 61); [exact (IH _ _ _ _ H Hs)|].
  destruct (WriterSpec.b64v c) as [v|] eqn:Ev; [|discriminate]. destruct (pad =? 0); [|discriminate].
  apply (IH _ _ _ _ H). apply Forall_app. split; [exact Hs|]. constructor; [|constructor].
  unfold WriterSpec.b64v in Ev.
  destruct ((65 <=? c) && (c <=? 90)) eqn:A1; [injection Ev as <-; apply andb_prop in A1 as [A1 A2];
    apply Z.leb_le in A1; apply Z.leb_le in A2; lia|].
  destruct ((97 <=? c) && (c <=? 122)) eqn:A3; [injection Ev as <-; apply andb_prop in A3 as [A3 A4];
    apply Z.leb_le in A3; apply Z.leb_le in A4; lia|].
  destruct ((48 <=? c) && (c <=? 57)) eqn:A5; [injection Ev as <-; apply andb_prop in A5 as [A5 A6];
    apply Z.leb_le in A5; apply Z.leb_le in A6; lia|].
  destruct (c =? 43); [injection Ev as <-; lia|]. destruct (c =? 47); [injection Ev as <-; lia | discriminate].
Qed.
Lemma caw_firstn_S : forall (l : list Z) j, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l 0].
Proof.
induction l as [|x l IH]; intros j Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
Lemma caw_skipn_S : forall (l : list Z) j, (j < length l)%nat -> skipn j l = nth j l 0 :: skipn (S j) l.
Proof.
induction l as [|x l IH]; intros j Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
(* one step of the scan at index j: the prefix scan and the scan of the rest both move by the character at j *)
Lemma caw_scan_step : forall (tb : list Z) j sx pad sx' pad',
  (j < length tb)%nat -> WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  WriterSpec.b64_scan pad sx [nth j tb 0] = Some (sx', pad') ->
  WriterSpec.b64_scan 0 [] (firstn (S j) tb) = Some (sx', pad') /\
  WriterSpec.b64_scan pad sx (skipn j tb) = WriterSpec.b64_scan pad' sx' (skipn (S j) tb).
Proof.
intros tb j sx pad sx' pad' Hj H1 H2. split.
- rewrite caw_firstn_S by exact Hj. rewrite caw_scan_app, H1. exact H2.
- rewrite (caw_skipn_S tb j Hj). change (nth j tb 0 :: skipn (S j) tb) with ([nth j tb 0] ++ skipn (S j) tb).
  rewrite caw_scan_app, H2. reflexivity.
Qed.
(* the step that refuses *)
Lemma caw_scan_stop : forall (tb : list Z) j pad sx,
  (j < length tb)%nat -> WriterSpec.b64_scan pad sx [nth j tb 0] = None ->
  WriterSpec.b64_scan pad sx (skipn j tb) = None.
Proof.
intros tb j pad sx Hj H. rewrite (caw_skipn_S tb j Hj).
change (nth j tb 0 :: skipn (S j) tb) with ([nth j tb 0] ++ skipn (S j) tb). rewrite caw_scan_app, H. reflexivity.
Qed.
(* the end of the text *)
Lemma caw_skipn_end : forall (tb : list Z) j, (S j = length tb)%nat -> skipn (S j) tb = [].
Proof. intros tb j H. apply skipn_all2. lia. Qed.

(* ---- brute force over a character class ---- *)
Definition zrange (lo hi : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat (hi - lo + 1))).
Lemma zrange_all : forall (f : Z -> bool) lo hi, forallb f (zrange lo hi) = true -> forall c, lo <= c <= hi -> f c = true.
Proof.
intros f lo hi H c Hc. unfold zrange in H. rewrite forallb_forall in H. apply H. apply in_map_iff.
exists (Z.to_nat (c - lo)). split; [rewrite Z2Nat.id by lia; lia|]. apply in_seq. lia.
Qed.
(* the value of a symbolic expression over atom 37 alone, at the character c *)
Definition Ec (c : Z) : env := mkEnv (fun _ => Z_to_bv 64 c) (fun _ => []).
Definition only37 (v : sv) : bool := sv_atoms_pd (fun n => Nat.eqb n 37) (fun _ => false) v.
Lemma caw_den37 : forall E c v, ew E 37 = Z_to_bv 64 c -> only37 v = true -> sv_denot E v = sv_denot (Ec c) v.
Proof.
intros E c v H Hv. symmetry. apply (sv_denot_agree_pd (fun n => Nat.eqb n 37) (fun _ => false)); [|exact Hv].
split; [|intros d Hd; discriminate Hd]. intros n Hn. apply Nat.eqb_eq in Hn. subst n. cbn [ew Ec]. symmetry. exact H.
Qed.
Lemma caw_br37 : forall E c cnd a b, ew E 37 = Z_to_bv 64 c -> only37 a = true -> only37 b = true ->
  branch_taken cnd (sv_denot E a) (sv_denot E b) = branch_taken cnd (sv_denot (Ec c) a) (sv_denot (Ec c) b).
Proof. intros E c cnd a b H Ha Hb. rewrite (caw_den37 E c a H Ha), (caw_den37 E c b H Hb). reflexivity. Qed.

(* ---- the class facts the walk needs, each checked over its class ---- *)
Definition caw_wsx : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 37 0)) (SLit 1).
Definition caw_slx : sv := SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 37 (-47)) (SLit 1)) (SLit (-1))) (SLit 63).
Definition caw_azx (d : Z) : sv := SAlu ALU_ADD (SAlu ALU_AND (SOff 37 0) (SLit 255)) (SLit d).
Definition caw_C1 : acond := mkAC BC_LTU (SLit 25) (SOff 37 (-65)).
Definition caw_C2 : acond := mkAC BC_LTU (SLit 25) (SOff 37 (-97)).
Definition caw_C3 : acond := mkAC BC_LTU (SLit 9) (SOff 37 (-48)).
Lemma caw_bf_C1 : forall c, 1 <= c <= 64 ->
  branch_taken BC_LTU (sv_denot (Ec c) (SLit 25)) (sv_denot (Ec c) (SOff 37 (-65))) = true.
Proof.
intros c Hc. apply (zrange_all (fun c => branch_taken BC_LTU (sv_denot (Ec c) (SLit 25)) (sv_denot (Ec c) (SOff 37 (-65))))
  1 64); [vm_compute; reflexivity | lia].
Qed.
Lemma caw_bf_C2 : forall c, 1 <= c <= 96 ->
  branch_taken BC_LTU (sv_denot (Ec c) (SLit 25)) (sv_denot (Ec c) (SOff 37 (-97))) = true.
Proof.
intros c Hc. apply (zrange_all (fun c => branch_taken BC_LTU (sv_denot (Ec c) (SLit 25)) (sv_denot (Ec c) (SOff 37 (-97))))
  1 96); [vm_compute; reflexivity | lia].
Qed.
Lemma caw_bf_C3 : forall c, 1 <= c <= 47 ->
  branch_taken BC_LTU (sv_denot (Ec c) (SLit 9)) (sv_denot (Ec c) (SOff 37 (-48))) = true.
Proof.
intros c Hc. apply (zrange_all (fun c => branch_taken BC_LTU (sv_denot (Ec c) (SLit 9)) (sv_denot (Ec c) (SOff 37 (-48))))
  1 47); [vm_compute; reflexivity | lia].
Qed.
(* the whitespace test of 0x81770-0x81778: taken (t5 = 0) exactly for the characters that are not whitespace *)
Lemma caw_bf_ws : forall c, 1 <= c <= 61 ->
  branch_taken BC_EQ (sv_denot (Ec c) caw_wsx) (sv_denot (Ec c) (SLit 0)) = negb (WriterSpec.b64_ws c).
Proof.
intros c Hc. apply Bool.eqb_prop.
apply (zrange_all (fun c => Bool.eqb (branch_taken BC_EQ (sv_denot (Ec c) caw_wsx) (sv_denot (Ec c) (SLit 0)))
  (negb (WriterSpec.b64_ws c))) 1 61); [vm_compute; reflexivity | lia].
Qed.
(* the value -1 the classification leaves for a character below '/' that is no letter, digit or '+': bltz taken *)
Lemma caw_bf_sl : forall c, 1 <= c <= 46 ->
  branch_taken BC_LT (sv_denot (Ec c) caw_slx) (sv_denot (Ec c) (SLit 0)) = true.
Proof.
intros c Hc. apply (zrange_all (fun c => branch_taken BC_LT (sv_denot (Ec c) caw_slx) (sv_denot (Ec c) (SLit 0))) 1 46);
  [vm_compute; reflexivity | lia].
Qed.
Lemma caw_bf_AZ : forall c, 65 <= c <= 90 ->
  branch_taken BC_LT (sv_denot (Ec c) (caw_azx (-65))) (sv_denot (Ec c) (SLit 0)) = false /\
  sv_denot (Ec c) (caw_azx (-65)) = Z_to_bv 64 (c - 65).
Proof.
intros c Hc. split.
- apply negb_true_iff.
  apply (zrange_all (fun c => negb (branch_taken BC_LT (sv_denot (Ec c) (caw_azx (-65))) (sv_denot (Ec c) (SLit 0))))
    65 90); [vm_compute; reflexivity | lia].
- apply bv_eq. rewrite unsigned_lit_small by lia. apply Z.eqb_eq.
  apply (zrange_all (fun c => bv_unsigned (sv_denot (Ec c) (caw_azx (-65))) =? c - 65) 65 90);
    [vm_compute; reflexivity | lia].
Qed.
Lemma caw_bf_az : forall c, 97 <= c <= 122 ->
  branch_taken BC_LT (sv_denot (Ec c) (caw_azx (-71))) (sv_denot (Ec c) (SLit 0)) = false /\
  sv_denot (Ec c) (caw_azx (-71)) = Z_to_bv 64 (c - 71).
Proof.
intros c Hc. split.
- apply negb_true_iff.
  apply (zrange_all (fun c => negb (branch_taken BC_LT (sv_denot (Ec c) (caw_azx (-71))) (sv_denot (Ec c) (SLit 0))))
    97 122); [vm_compute; reflexivity | lia].
- apply bv_eq. rewrite unsigned_lit_small by lia. apply Z.eqb_eq.
  apply (zrange_all (fun c => bv_unsigned (sv_denot (Ec c) (caw_azx (-71))) =? c - 71) 97 122);
    [vm_compute; reflexivity | lia].
Qed.
Lemma caw_bf_09 : forall c, 48 <= c <= 57 -> sv_denot (Ec c) (caw_azx 4) = Z_to_bv 64 (c + 4).
Proof.
intros c Hc. apply bv_eq. rewrite unsigned_lit_small by lia. apply Z.eqb_eq.
apply (zrange_all (fun c => bv_unsigned (sv_denot (Ec c) (caw_azx 4)) =? c + 4) 48 57); [vm_compute; reflexivity | lia].
Qed.
(* what b64_scan does with one character *)
Lemma caw_scan1 : forall c pad sx, WriterSpec.b64_scan pad sx [c] =
  if WriterSpec.b64_ws c then Some (sx, pad) else if c =? 61 then Some (sx, pad + 1) else
  match WriterSpec.b64v c with Some v => if pad =? 0 then Some (sx ++ [v], pad) else None | None => None end.
Proof.
intros c pad sx. cbn [WriterSpec.b64_scan].
destruct (WriterSpec.b64_ws c); [reflexivity|]. destruct (c =? 61); [reflexivity|].
destruct (WriterSpec.b64v c); [|reflexivity]. destruct (pad =? 0); reflexivity.
Qed.
Definition caw_bad (c : Z) : bool :=
  negb (WriterSpec.b64_ws c) && negb (c =? 61) && match WriterSpec.b64v c with None => true | Some _ => false end.
Lemma caw_bad_scan : forall c pad sx, caw_bad c = true -> WriterSpec.b64_scan pad sx [c] = None.
Proof.
intros c pad sx H. unfold caw_bad in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff in H2. rewrite caw_scan1, H1, H2.
destruct (WriterSpec.b64v c); [discriminate | reflexivity].
Qed.
Lemma caw_bf_bad : forall c lo hi, forallb caw_bad (zrange lo hi) = true -> lo <= c <= hi -> caw_bad c = true.
Proof. intros c lo hi H Hc. exact (zrange_all caw_bad lo hi H c Hc). Qed.
Lemma caw_ws_scan : forall c pad sx, WriterSpec.b64_ws c = true -> WriterSpec.b64_scan pad sx [c] = Some (sx, pad).
Proof. intros c pad sx H. rewrite caw_scan1, H. reflexivity. Qed.
Lemma caw_pad_scan : forall pad sx, WriterSpec.b64_scan pad sx [61] = Some (sx, pad + 1).
Proof. reflexivity. Qed.
Lemma caw_val_scan : forall c v pad sx, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  WriterSpec.b64_scan pad sx [c] = if pad =? 0 then Some (sx ++ [v], pad) else None.
Proof.
intros c v pad sx H1 H2 H3. rewrite caw_scan1, H1, H3.
replace (c =? 61) with false by (symmetry; apply Z.eqb_neq; exact H2). reflexivity.
Qed.
(* the value classes: not whitespace, not '=', and their sextet *)
Definition caw_vcls (lo hi d : Z) : bool :=
  forallb (fun c => negb (WriterSpec.b64_ws c) && negb (c =? 61) &&
    match WriterSpec.b64v c with Some v => v =? c + d | None => false end) (zrange lo hi).
Lemma caw_vcls_ok : forall lo hi d c, caw_vcls lo hi d = true -> lo <= c <= hi ->
  WriterSpec.b64_ws c = false /\ c <> 61 /\ WriterSpec.b64v c = Some (c + d).
Proof.
intros lo hi d c H Hc. pose proof (zrange_all _ lo hi H c Hc) as Hx. cbv beta in Hx.
apply andb_prop in Hx as [Hx H3]. apply andb_prop in Hx as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff in H2. apply Z.eqb_neq in H2.
split; [exact H1|]. split; [exact H2|]. destruct (WriterSpec.b64v c) as [v|]; [|discriminate].
apply Z.eqb_eq in H3. subst v. reflexivity.
Qed.

(* ---- the shape of a run's memory: the write windows are the stack frame and the byte six[m] ---- *)
Lemma caw_in_wrange_skel : forall E rs rs' a, skeleton rs = skeleton rs' -> in_wrange E rs a -> in_wrange E rs' a.
Proof.
intros E rs rs' a Hsk (r & Hin & Ha).
assert (Hs : In (skel r) (skeleton rs')) by (rewrite <- Hsk; apply in_map; exact Hin).
unfold skeleton in Hs. apply in_map_iff in Hs as (r' & Heq & Hin').
exists r'. split; [exact Hin'|]. unfold skel in Heq. injection Heq as E1 E2 E3 E4 E5.
rewrite E1, E4, E5. exact Ha.
Qed.
Lemma caw_in_wrange1 : forall E a, in_wrange E caw_mem1 a ->
  (bv_unsigned (ew E 2) - 64 <= a < bv_unsigned (ew E 2)) \/ (bv_unsigned (ew E 40) <= a < bv_unsigned (ew E 40) + 1).
Proof.
intros E a (r & Hin & Ha). unfold caw_mem1 in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold caw_stk, caw_txt1, caw_six1 in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.
Lemma caw_frame_run : forall E rs (m m' : word -> option byte) sp q,
  skeleton rs = skeleton caw_mem1 -> frame_of E rs m m' ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 40) = q ->
  forall x : word, ~ (sp - 64 <= bv_unsigned x < sp) -> ~ (q <= bv_unsigned x < q + 1) -> m' x = m x.
Proof.
intros E rs m m' sp q Hsk HF H2 H40 x Hx1 Hx2. apply HF. intros Hin.
apply (caw_in_wrange_skel E rs caw_mem1 _ Hsk) in Hin. apply caw_in_wrange1 in Hin. lia.
Qed.
Lemma caw_mbyte_keep : forall (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' P a Hk Ha HP. unfold mbyte, mrestrict. rewrite (Hk (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact HP.
Qed.
Lemma caw_U0 : forall E n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v.
Proof.
intros E n v H. rewrite U_SOff, Z.add_0_r, H. apply zcanon_id. subst v. unfold M64. apply u64_range.
Qed.
Lemma caw_ew_lit : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma caw_ew_ewset : forall E K v n, (n < K)%nat -> ew (ewset E K v) n = ew E n.
Proof. intros E K v n H. cbn [ew ewset]. destruct (Nat.eqb_spec n K); [lia | reflexivity]. Qed.

Lemma caw_den0 : forall E n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. reflexivity. Qed.
Lemma caw_w_of_u : forall (w : word) v, bv_unsigned w = v -> w = Z_to_bv 64 v.
Proof. intros w v H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.


(* ---- the loop's own shadow entries (FSW_caw_defs caw_SH1 and the byte text + j + 1 through a1, atom 36, which the
   check at 0x81780 reads), the re-keyed atoms, the exit states ---- *)
Definition caw_SHs : list shent := [mkSHE 35 1 2; mkSHE 40 0 1; mkSHE 36 0 1].
(* the atoms kept across iterations: 0 .. 34 (the registers of the entry, ~six (30), ra (31), the shadow base, six,
   want) *)
Definition caw_P (n : nat) : bool := Nat.ltb n 35.
Definition caw_facts1n : facts := mkFacts (f_atoms (caw_facts1 1 255)) [] [].
(* the states at the two loop exits: the registers of the loop state, the stack frame; atoms 35 = s3 (text + j'),
   38 = a4 (m, the sextets written), 39 = t3 (pad). caw_ssX at the NUL (0x81804), caw_ssB at the refused character
   (0x81a78, `jal __wrap_free` of six, s5 = SIZE_MAX) *)
Definition caw_factsX : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (30%nat, mkAF CAW_NLO CAW_NHI 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (35%nat, mkAF 4096 CAW_CEIL 0);
           (38%nat, mkAF 0 3145728 0);
           (39%nat, mkAF 0 3145728 0)]
          [] [].
Definition caw_ssXp (pc : Z) : sstate := mkSS pc caw_regs1 [caw_stk] None caw_factsX.
Definition caw_ssX : sstate := caw_ssXp 0x81804.
Definition caw_ssB : sstate := caw_ssXp 0x81a78.
(* the env of the re-keyed state: atoms 35 .. 44 from the registers s3 a1 a2 a4 t3, six + m, the next character,
   t4 t5 t6 *)
Definition caw_reenv (E : env) (regs : bvmap 5 word) (v40 v41 : word) : env :=
  havoc E 35 [getr regs 19%bv; getr regs 11%bv; getr regs 12%bv; getr regs 14%bv; getr regs 28%bv; v40; v41;
              getr regs 29%bv; getr regs 30%bv; getr regs 31%bv].
Lemma caw_reenv_old : forall E regs v40 v41 n, (n < 35)%nat -> ew (caw_reenv E regs v40 v41) n = ew E n.
Proof. intros E regs v40 v41 n Hn. apply ew_havoc_old. exact Hn. Qed.
Lemma caw_reenv_agree : forall E regs v40 v41, env_agree_pd caw_P PT E (caw_reenv E regs v40 v41).
Proof.
intros E regs v40 v41. split; [|intros d _; reflexivity].
intros n Hn. unfold caw_P in Hn. apply Nat.ltb_lt in Hn. apply caw_reenv_old. exact Hn.
Qed.
Lemma caw_reenv_agree35 : forall E regs v40 v41, env_agree 35 E (caw_reenv E regs v40 v41).
Proof. intros E regs v40 v41. split; [|reflexivity]. intros n Hn. apply caw_reenv_old. exact Hn. Qed.
Lemma caw_reenv_obl : forall E regs v40 v41,
  Forall (fun rj : bv 5 * nat => ew (caw_reenv E regs v40 v41) (snd rj) = getr regs (fst rj)) (reabs_obl caw_P caw_regs1).
Proof.
intros E regs v40 v41.
match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
repeat constructor.
Qed.
Lemma caw_reenv_35 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 35 = getr regs 19%bv.
Proof. reflexivity. Qed.
Lemma caw_reenv_36 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 36 = getr regs 11%bv.
Proof. reflexivity. Qed.
Lemma caw_reenv_37 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 37 = getr regs 12%bv.
Proof. reflexivity. Qed.
Lemma caw_reenv_38 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 38 = getr regs 14%bv.
Proof. reflexivity. Qed.
Lemma caw_reenv_39 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 39 = getr regs 28%bv.
Proof. reflexivity. Qed.
Lemma caw_reenv_40 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 40 = v40.
Proof. reflexivity. Qed.
Lemma caw_reenv_41 : forall E regs v40 v41, ew (caw_reenv E regs v40 v41) 41 = v41.
Proof. reflexivity. Qed.

Section scan.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable W : world tfibsegs.
(* the run's journal: from (lyA, SA, W0, mem0, md0) at sp0 with STK bytes of stack and footprint FP, to the current
   (lyc, Sc) with the user-poisoned ranges Up and k allocator events; the loop keeps lyc / Sc / Up / k *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (lyA : alayout) (SA : astate) (W0 : world tfibsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (Up : list (Z * Z)) (k : Z).
(* the text tb at t, the block six of size bytes, the entry sp spE (atom 2) *)
Variables (t : Z) (tb : list Z) (six size spE : Z).

(* what does not change along the loop. The text bound is cstr_ok's (FSH_Gen.v, CTX-drop S0: p + |l| + 1 <=
   alloc_ceiling): the loop reads t[0 .. |tb|] byte by byte (`lbu` at 0x81794 and the NUL), never an aligned word *)
Definition caw_static : Prop :=
  Forall (fun c => c <> 0) tb /\ Z.of_nat (length tb) <= 3145728 /\
  4096 <= t /\ t + Z.of_nat (length tb) + 1 <= alloc_ceiling /\
  (forall x, t <= x <= t + Z.of_nat (length tb) -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  4096 <= six /\ six + size <= alloc_ceiling /\ Z.of_nat (length tb) <= size /\
  (forall x, six <= x < six + size -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  (t + Z.of_nat (length tb) + 1 <= six \/ six + size <= t) /\
  alloc_ceiling <= spE - 64 /\ sp0 - STK <= spE - 64 /\ spE <= sp0 /\ spE <= 2 ^ 47 /\
  (forall a, six <= a < six + size -> awr_byte tfibsegs B STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc) lyc own (frames SA) a).
(* the facts of the machine's memory m the loop keeps: the text and its NUL, their shadow, the shadow of six, six
   writable *)
Definition caw_memf (m : word -> option byte) : Prop :=
  garr8 tfibsegs (mrestrict (w_H W) m) t (tb ++ [0]) /\
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF t (Z.of_nat (length tb) + 1) /\
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF six size /\
  (forall a, six <= a < six + size -> writable_at tfibsegs (mrestrict (w_H W) m) a).
(* six[0, |sx|) holds the sextets sx *)
Definition caw_six (m : word -> option byte) (sx : list Z) : Prop :=
  forall i, (i < length sx)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (six + Z.of_nat i) 1 (nth i sx 0).
(* the atoms of the loop state at text index j with m sextets written and pad '=' seen *)
Definition caw_atoms (E : env) (j m : nat) (pad : Z) : Prop :=
  ew E 2 = Z_to_bv 64 spE /\ ew E 33 = Z_to_bv 64 six /\
  ew E 35 = Z_to_bv 64 (t + Z.of_nat j) /\ ew E 36 = Z_to_bv 64 (t + Z.of_nat j + 1) /\
  ew E 37 = Z_to_bv 64 (nth j tb 0) /\ ew E 38 = Z_to_bv 64 (Z.of_nat m) /\ ew E 39 = Z_to_bv 64 pad /\
  ew E 40 = Z_to_bv 64 (six + Z.of_nat m) /\ ew E 41 = Z_to_bv 64 (nth (S j) (tb ++ [0]) 0).
(* what the continuation gets at the exit, for a loop entered at index j0 with (sx0, pad0) on the memory m0: the
   NUL exit caw_ssX when b64_scan accepts the rest, the refusal exit caw_ssB when it refuses it *)
Definition caw_post (E0 : env) (m0 : word -> option byte) (j0 : nat) (sx0 : list Z) (pad0 : Z)
  (ms' : machine_state) (mdc' : Model) : Prop :=
  exists E' j' mf pad',
  (forall n, (n < 35)%nat -> ew E' n = ew E0 n) /\
  ew E' 35 = Z_to_bv 64 (t + Z.of_nat j') /\ ew E' 38 = Z_to_bv 64 (Z.of_nat mf) /\ ew E' 39 = Z_to_bv 64 pad' /\
  (j0 <= j' <= length tb)%nat /\ (length sx0 <= mf)%nat /\
  match WriterSpec.b64_scan pad0 sx0 (skipn j0 tb) with
  | Some (sxf, padf) => st_ok tfibsegs E' caw_ssX (restrict (w_H W) ms') /\
      j' = length tb /\ mf = length sxf /\ pad' = padf /\
      Forall (fun v => 0 <= v < 64) sxf /\ caw_six (ms_mem ms') sxf
  | None => st_ok tfibsegs E' caw_ssB (restrict (w_H W) ms') /\
      (j' < length tb)%nat /\ nth j' tb 0 <> 0 /\ (mf <= j')%nat
  end /\
  (forall x : word, ~ (six <= bv_unsigned x < six + Z.of_nat mf + 1) -> ~ (spE - 64 <= bv_unsigned x < spE) ->
     ms_mem ms' x = m0 x) /\
  mem_grows (mrestrict (w_H W) m0) (mrestrict (w_H W) (ms_mem ms')) /\
  caw_memf (ms_mem ms') /\
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms')) mdc' k /\
  ARU tfibsegs B lyc Sc Up W (ms_mem ms') mdc'.
(* the loop from the head at text index j *)
Definition caw_loop_at (j : nat) : Prop :=
  (j < length tb)%nat ->
  forall sx pad E ms mdc (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E (caw_ss1 1 255) (restrict (w_H W) ms) ->
  caw_atoms E j (length sx) pad ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  Forall (fun v => 0 <= v < 64) sx ->
  caw_memf (ms_mem ms) -> caw_six (ms_mem ms) sx ->
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  (forall ms' mdc', caw_post E (ms_mem ms) j sx pad ms' mdc' -> SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.

(* ---- the memory facts across one iteration ---- *)
Lemma caw_memf_frame : forall (m m' : word -> option byte),
  caw_static -> caw_memf m ->
  (forall x : word, ~ (six <= bv_unsigned x < six + size) -> ~ (spE - 64 <= bv_unsigned x < spE) -> m' x = m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> caw_memf m'.
Proof.
intros m m' HST (Hg & Hrt & Hrs & Hw) Hk Hgr.
destruct HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hk' : forall x : word, ~ ((six <= bv_unsigned x < six + size) \/ (spE - 64 <= bv_unsigned x < spE)) ->
  m' x = m x) by (intros x Hx; apply Hk; intros Hc; apply Hx; [left | right]; exact Hc).
(* a shadow byte of an address below 2^47 is neither in six nor in the stack *)
assert (SH : forall x, 0 <= x < 2 ^ 47 ->
  aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. unfold aview.
  assert (Hy : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 17592186044416)
    by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  rewrite (caw_mbyte_keep (w_H W) m m' (fun a => (six <= a < six + size) \/ (spE - 64 <= a < spE)) _ Hk');
    [reflexivity | unfold SHADOW_OFF in *; lia |].
  intros [Hc|Hc].
  - exact (Hssh _ Hc Hy).
  - unfold SHADOW_OFF in *; lia. }
split; [|split; [|split]].
- apply (garr8_frame tfibsegs _ _ t (tb ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (caw_mbyte_keep (w_H W) m m' (fun a => (six <= a < six + size) \/ (spE - 64 <= a < spE))); [exact Hk' | lia | lia].
- intros x Hx. destruct (Hrt x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite SH; [exact Hs | lia].
- intros x Hx. destruct (Hrs x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite SH; [exact Hs | lia].
- intros a Ha. apply (writable_at_grows _ _ _ _ Hgr). apply Hw. exact Ha.
Qed.
Lemma caw_six_frame : forall (m m' : word -> option byte) sx q,
  caw_static -> caw_six m sx -> six + Z.of_nat (length sx) <= q < six + size ->
  (forall x : word, ~ (spE - 64 <= bv_unsigned x < spE) -> ~ (q <= bv_unsigned x < q + 1) -> m' x = m x) ->
  caw_six m' sx.
Proof.
intros m m' sx q HST H6 Hq Hk i Hi.
destruct HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
intros kk Hkk. assert (kk = 0%nat) as -> by lia. pose proof (H6 i Hi 0%nat ltac:(lia)) as Hv.
rewrite <- Hv. apply (caw_mbyte_keep (w_H W) m m' (fun a => (spE - 64 <= a < spE) \/ (q <= a < q + 1))).
- intros x Hx. apply Hk; intros Hc; apply Hx; [left | right]; exact Hc.
- cbv beta. lia.
- cbv beta. lia.
Qed.
Lemma caw_shok : forall E (m : word -> option byte) j q,
  caw_static -> caw_memf m -> (j < length tb)%nat ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> bv_unsigned (ew E 35) = t + Z.of_nat j ->
  bv_unsigned (ew E 36) = t + Z.of_nat j + 1 -> bv_unsigned (ew E 40) = q -> six <= q < six + size ->
  sh_ok tfibsegs caw_Bx caw_SHs E (mrestrict (w_H W) m).
Proof.
intros E m j q HST (Hg & Hrt & Hrs & Hw) Hj H32 H35 H36 H40 Hq.
destruct HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
assert (HB : U E caw_Bx = SHADOW_OFF) by (unfold caw_Bx; apply U_atom; [exact H32 | unfold SHADOW_OFF; lia]).
unfold sh_ok, caw_SHs. constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (shent_ok_of_range tfibsegs (w_H W) m E caw_Bx 35 t (Z.of_nat (length tb) + 1) (t + Z.of_nat j) 1 2 Hrt HB);
    [apply caw_U0; exact H35 | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. apply Htsh. lia.
- eapply (shent_ok_of_range tfibsegs (w_H W) m E caw_Bx 40 six size q 0 1 Hrs HB);
    [apply caw_U0; exact H40 | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. apply Hssh. lia.
- eapply (shent_ok_of_range tfibsegs (w_H W) m E caw_Bx 36 t (Z.of_nat (length tb) + 1) (t + Z.of_nat j + 1) 0 1 Hrt HB);
    [apply caw_U0; exact H36 | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. apply Htsh. lia.
Qed.
Lemma caw_awr : forall E rs q,
  caw_static -> skeleton rs = skeleton caw_mem1 ->
  bv_unsigned (ew E 2) = spE -> bv_unsigned (ew E 40) = q -> six <= q < six + size ->
  awr_ok tfibsegs B E rs STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc) lyc own (frames SA).
Proof.
intros E rs q HST Hsk H2 H40 Hq a Hin.
destruct HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
apply (caw_in_wrange_skel E rs caw_mem1 _ Hsk) in Hin. apply caw_in_wrange1 in Hin.
destruct Hin as [Ha|Ha]; [left; unfold awr_byte0; left; lia | apply Hawr; lia].
Qed.

(* the head state with the class of the current character narrowed *)
Lemma caw_narrow : forall E lo hi lo' hi' ms, st_ok tfibsegs E (caw_ss1 lo hi) ms ->
  lo' <= bv_unsigned (ew E 37) <= hi' -> st_ok tfibsegs E (caw_ss1 lo' hi') ms.
Proof.
intros E lo hi lo' hi' ms HS H37.
assert (HF' : facts_ok E (caw_facts1 lo' hi')).
{ pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  unfold caw_ss1 in HF. cbn [ss_facts] in HF. unfold caw_facts1 in HF |- *.
  destruct HF as (HA & HC & HL). split; [|split; [exact HC | exact HL]].
  cbn [f_atoms atoms_ok] in HA |- *.
  destruct HA as (A2 & A30 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & _).
  refine (conj A2 (conj A30 (conj A32 (conj A33 (conj A34 (conj A35 (conj A36 (conj _ (conj A38 (conj A39 (conj A40
    (conj A41 I)))))))))))).
  unfold afact_ok in *. cbn [af_lo af_hi af_al2] in *. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
exact (st_ok_facts tfibsegs E (caw_ss1 lo hi) ms (caw_facts1 lo' hi') HS HF').
Qed.
(* ---- re-keying the state at the next loop head (0x8170c) ---- *)
Ltac caw_obls_tac tac :=
  apply Forall_forall; let nf := fresh "nf" in let Hin := fresh "Hin" in intros nf Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin]; [subst nf; cbn [fst snd]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite Z.pow_0_r, Z.mod_1_r; tac|]); destruct Hin.
Lemma caw_head_ok : forall E2 ss2 ms2 j m pad,
  caw_static -> caw_memf (ms_mem ms2) ->
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) ->
  ss_pc ss2 = 0x8170c ->
  reabs_check caw_P ss2 caw_regs1 caw_facts1n = true ->
  nth_error (ss_mem ss2) 0 = Some caw_stk ->
  ew E2 2 = Z_to_bv 64 spE -> ew E2 33 = Z_to_bv 64 six ->
  (S j < length tb)%nat ->
  bv_unsigned (getr (ms_regs ms2) 19%bv) = t + Z.of_nat (S j) ->
  bv_unsigned (getr (ms_regs ms2) 11%bv) = t + Z.of_nat (S j) + 1 ->
  bv_unsigned (getr (ms_regs ms2) 12%bv) = nth (S j) tb 0 ->
  bv_unsigned (getr (ms_regs ms2) 14%bv) = Z.of_nat m ->
  bv_unsigned (getr (ms_regs ms2) 28%bv) = pad ->
  (m <= S j)%nat -> 0 <= pad <= Z.of_nat (S j) ->
  st_ok tfibsegs (caw_reenv E2 (ms_regs ms2) (Z_to_bv 64 (six + Z.of_nat m)) (Z_to_bv 64 (nth (S (S j)) (tb ++ [0]) 0)))
    (caw_ss1 1 255) (restrict (w_H W) ms2) /\
  caw_atoms (caw_reenv E2 (ms_regs ms2) (Z_to_bv 64 (six + Z.of_nat m)) (Z_to_bv 64 (nth (S (S j)) (tb ++ [0]) 0)))
    (S j) m pad.
Proof.
intros E2 ss2 ms2 j m pad HST HM HS2 Hpc Hck Hstk H2 H33 Hj R19 R11 R12 R14 R28 Hm Hpad.
pose proof HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
pose proof HM as (Hg & Hrt & Hrs & Hw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (N2 := nth (S (S j)) (tb ++ [0]) 0).
set (E' := caw_reenv E2 (ms_regs ms2) (Z_to_bv 64 (six + Z.of_nat m)) (Z_to_bv 64 N2)).
assert (Hlen1 : length (tb ++ [0]) = S (length tb)) by (rewrite length_app; cbn [length]; lia).
destruct (Hg (S (S j)) ltac:(lia)) as [VN2 RN2]. fold N2 in VN2, RN2.
assert (Hc : nth (S j) tb 0 <> 0 /\ 0 <= nth (S j) tb 0 < 256).
{ split.
  - apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. exact Hj.
  - destruct (Hg (S j) ltac:(lia)) as [_ R]. rewrite app_nth1 in R by exact Hj. exact R. }
assert (E2' : ew E' 2 = Z_to_bv 64 spE) by (unfold E'; rewrite caw_reenv_old by lia; exact H2).
assert (E33' : ew E' 33 = Z_to_bv 64 six) by (unfold E'; rewrite caw_reenv_old by lia; exact H33).
assert (E35' : ew E' 35 = Z_to_bv 64 (t + Z.of_nat (S j))) by (unfold E'; rewrite caw_reenv_35; apply caw_w_of_u; exact R19).
assert (E36' : ew E' 36 = Z_to_bv 64 (t + Z.of_nat (S j) + 1))
  by (unfold E'; rewrite caw_reenv_36; apply caw_w_of_u; exact R11).
assert (E37' : ew E' 37 = Z_to_bv 64 (nth (S j) tb 0)) by (unfold E'; rewrite caw_reenv_37; apply caw_w_of_u; exact R12).
assert (E38' : ew E' 38 = Z_to_bv 64 (Z.of_nat m)) by (unfold E'; rewrite caw_reenv_38; apply caw_w_of_u; exact R14).
assert (E39' : ew E' 39 = Z_to_bv 64 pad) by (unfold E'; rewrite caw_reenv_39; apply caw_w_of_u; exact R28).
assert (E40' : ew E' 40 = Z_to_bv 64 (six + Z.of_nat m)) by reflexivity.
assert (E41' : ew E' 41 = Z_to_bv 64 N2) by reflexivity.
assert (HN2 : nth (S (S j)) (tb ++ [0]) 0 = N2) by reflexivity.
split; [|unfold caw_atoms; rewrite HN2; repeat split; assumption].
assert (HM' : mem_ok tfibsegs E' (ms_mem (restrict (w_H W) ms2)) caw_mem1).
{ cbn [ms_mem restrict]. split; [vm_compute; reflexivity|]. split.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + pose proof (fsw_region_nth E2 ss2 (restrict (w_H W) ms2) 0 caw_stk HS2 Hstk) as R0. cbn [ms_mem restrict] in R0.
      exact (region_ok_agree tfibsegs 35 E2 E' _ caw_stk (caw_reenv_agree35 _ _ _ _) ltac:(vm_compute; reflexivity) R0).
    + unfold region_ok, caw_txt1. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E35', unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E' _ _ 1 1%N (SOff 41 0) N2);
        [apply caw_den0; rewrite E41'; apply unsigned_lit_small; lia | cbn; lia | cbn; lia |].
      replace (t + Z.of_nat (S j) + 1) with (t + Z.of_nat (S (S j))) by lia. exact VN2.
    + unfold region_ok, caw_six1. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E40', unsigned_lit_small by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hw; lia | constructor].
  - unfold caw_mem1, caw_stk, caw_txt1, caw_six1. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2', E35', E40', !unsigned_lit_small by lia.
    repeat split; lia. }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E' (fst nf) (snd nf)) (fact_obls caw_P caw_facts1n)).
{ caw_obls_tac ltac:(rewrite ?E35', ?E36', ?E37', ?E38', ?E39', ?E40', ?E41';
    rewrite unsigned_lit_small by (unfold CAW_CEIL; lia); unfold CAW_CEIL; lia). }
pose proof (st_ok_reabs tfibsegs caw_P E2 E' ss2 (restrict (w_H W) ms2) caw_regs1 caw_mem1 caw_facts1n HS2
  (caw_reenv_agree _ _ _ _) Hck (caw_reenv_obl _ _ _ _) HFO HM') as HS'.
rewrite Hpc in HS'.
pose proof HS' as (_ & _ & _ & _ & _ & _ & _ & _ & HF').
assert (HF : facts_ok E' (caw_facts1 1 255)).
{ split; [exact (proj1 HF')|]. split; [exact I|]. cbn [caw_facts1 f_alias alias_ok]. split; [|exact I].
  cbn [sv_denot]. rewrite E33', E38', E40', !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  apply alu_add_small; unfold M64; lia. }
exact (st_ok_facts tfibsegs E' _ _ (caw_facts1 1 255) HS' HF).
Qed.
(* ---- re-keying the state at a loop exit (0x81804 or 0x81a78) ---- *)
Lemma caw_exit_ok : forall E2 ss2 ms2 j' mf pad',
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) ->
  reabs_check caw_P ss2 caw_regs1 caw_factsX = true ->
  nth_error (ss_mem ss2) 0 = Some caw_stk ->
  bv_unsigned (getr (ms_regs ms2) 19%bv) = t + Z.of_nat j' ->
  bv_unsigned (getr (ms_regs ms2) 14%bv) = Z.of_nat mf ->
  bv_unsigned (getr (ms_regs ms2) 28%bv) = pad' ->
  4096 <= t + Z.of_nat j' <= CAW_CEIL -> Z.of_nat mf <= 3145728 -> 0 <= pad' <= 3145728 ->
  st_ok tfibsegs (caw_reenv E2 (ms_regs ms2) (ew E2 40) (ew E2 41)) (caw_ssXp (ss_pc ss2)) (restrict (w_H W) ms2).
Proof.
intros E2 ss2 ms2 j' mf pad' HS2 Hck Hstk R19 R14 R28 Hj' Hmf Hpad.
set (E' := caw_reenv E2 (ms_regs ms2) (ew E2 40) (ew E2 41)).
assert (E35' : ew E' 35 = Z_to_bv 64 (t + Z.of_nat j')) by (unfold E'; rewrite caw_reenv_35; apply caw_w_of_u; exact R19).
assert (E38' : ew E' 38 = Z_to_bv 64 (Z.of_nat mf)) by (unfold E'; rewrite caw_reenv_38; apply caw_w_of_u; exact R14).
assert (E39' : ew E' 39 = Z_to_bv 64 pad') by (unfold E'; rewrite caw_reenv_39; apply caw_w_of_u; exact R28).
assert (HM' : mem_ok tfibsegs E' (ms_mem (restrict (w_H W) ms2)) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  pose proof (fsw_region_nth E2 ss2 (restrict (w_H W) ms2) 0 caw_stk HS2 Hstk) as R0.
  exact (region_ok_agree tfibsegs 35 E2 E' _ caw_stk (caw_reenv_agree35 _ _ _ _) ltac:(vm_compute; reflexivity) R0). }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E' (fst nf) (snd nf)) (fact_obls caw_P caw_factsX)).
{ caw_obls_tac ltac:(rewrite ?E35', ?E38', ?E39';
    rewrite unsigned_lit_small by (unfold CAW_CEIL in *; lia); unfold CAW_CEIL in *; lia). }
exact (st_ok_reabs tfibsegs caw_P E2 E' ss2 (restrict (w_H W) ms2) caw_regs1 [caw_stk] caw_factsX HS2
  (caw_reenv_agree _ _ _ _) Hck (caw_reenv_obl _ _ _ _) HFO HM').
Qed.
(* ---- the register values a run leaves ---- *)
Lemma caw_regv_lit : forall EN ssN (msN : machine_state) (r : bv 5) z,
  st_ok tfibsegs EN ssN (restrict (w_H W) msN) -> sr_get (ss_regs ssN) r = SLit z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (getr (ms_regs msN) r) = z.
Proof.
intros EN ssN msN r z HS Hr Hz. rewrite (fsw_reg_lit (w_H W) EN ssN msN r z HS Hr Hz). apply unsigned_lit_small. exact Hz.
Qed.

(* ---- the continuation through one iteration ---- *)
Lemma caw_post_step : forall E E' (m m2 : word -> option byte) j sx pad sx' pad' ms' mdc',
  caw_static -> (j < length tb)%nat ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  WriterSpec.b64_scan pad sx [nth j tb 0] = Some (sx', pad') ->
  (forall n, (n < 35)%nat -> ew E' n = ew E n) ->
  (forall x : word, ~ (spE - 64 <= bv_unsigned x < spE) ->
     ~ (six + Z.of_nat (length sx) <= bv_unsigned x < six + Z.of_nat (length sx) + 1) -> m2 x = m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m2) ->
  caw_post E' m2 (S j) sx' pad' ms' mdc' -> caw_post E m j sx pad ms' mdc'.
Proof.
intros E E' m m2 j sx pad sx' pad' ms' mdc' HST Hj Hscan Hstep HAg Hfr Hgr
  (E'' & j'' & mf & pad'' & HAg'' & H35 & H38 & H39 & Hjj & Hmf & Hfin & Hfr'' & Hgr'' & HM'' & HJ'' & HARU'').
destruct (caw_scan_step tb j sx pad sx' pad' Hj Hscan Hstep) as [Hscan' Hrest].
pose proof (caw_scan_bound [nth j tb 0] pad sx sx' pad' Hstep) as (Hl & _ & _).
exists E'', j'', mf, pad''.
split; [intros n Hn; rewrite HAg'' by exact Hn; apply HAg; exact Hn|].
split; [exact H35|]. split; [exact H38|]. split; [exact H39|]. split; [lia|]. split; [lia|].
split; [rewrite Hrest; exact Hfin|].
split; [intros x Hx1 Hx2; rewrite (Hfr'' x Hx1 Hx2); apply Hfr; [exact Hx2 | lia]|].
split; [exact (mem_grows_trans _ _ _ Hgr Hgr'')|].
split; [exact HM''|]. split; [exact HJ'' | exact HARU''].
Qed.
(* the exit by a refused character (a character that is no whitespace, '=', or sextet; a sextet after '='):
   straight to 0x81a78 *)
Lemma caw_exit_break : forall j sx pad E (ms ms2 : machine_state) mdc2 E2 ss2,
  caw_static -> (j < length tb)%nat ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  WriterSpec.b64_scan pad sx [nth j tb 0] = None ->
  caw_memf (ms_mem ms) ->
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) -> ss_pc ss2 = 0x81a78 ->
  reabs_check caw_P ss2 caw_regs1 caw_factsX = true -> nth_error (ss_mem ss2) 0 = Some caw_stk ->
  (forall n, (n < 45)%nat -> ew E2 n = ew E n) ->
  bv_unsigned (getr (ms_regs ms2) 19%bv) = t + Z.of_nat j ->
  bv_unsigned (getr (ms_regs ms2) 14%bv) = Z.of_nat (length sx) ->
  bv_unsigned (getr (ms_regs ms2) 28%bv) = pad ->
  (forall x : word, ~ (spE - 64 <= bv_unsigned x < spE) ->
     ~ (six + Z.of_nat (length sx) <= bv_unsigned x < six + Z.of_nat (length sx) + 1) -> ms_mem ms2 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 k ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
  caw_post E (ms_mem ms) j sx pad ms2 mdc2.
Proof.
intros j sx pad E ms ms2 mdc2 E2 ss2 HST Hj Hscan Hstop HM HS2 Hpc Hck Hstk HAg R19 R14 R28 Hfr Hgr HJ HARU.
pose proof HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (caw_scan_bound _ 0 [] sx pad Hscan) as (_ & Hp0 & Hsb).
rewrite firstn_length_le in Hsb by lia. cbn [length] in Hsb.
exists (caw_reenv E2 (ms_regs ms2) (ew E2 40) (ew E2 41)), j, (length sx), pad.
split; [intros n Hn; rewrite caw_reenv_old by exact Hn; apply HAg; lia|].
split; [rewrite caw_reenv_35; apply caw_w_of_u; exact R19|].
split; [rewrite caw_reenv_38; apply caw_w_of_u; exact R14|].
split; [rewrite caw_reenv_39; apply caw_w_of_u; exact R28|].
split; [lia|]. split; [lia|].
split; [rewrite (caw_scan_stop tb j pad sx Hj Hstop); split;
  [unfold caw_ssB; rewrite <- Hpc;
   apply (caw_exit_ok E2 ss2 ms2 j (length sx) pad HS2 Hck Hstk R19 R14 R28); unfold CAW_CEIL; lia
  | split; [exact Hj | split; [apply (proj1 (Forall_forall _ _) Hnz); apply nth_In; exact Hj | lia]]]|].
split; [intros x Hx1 Hx2; apply Hfr; [exact Hx2 | lia]|].
split; [exact Hgr|].
split; [apply (caw_memf_frame (ms_mem ms) (ms_mem ms2) HST HM); [intros x Hx1 Hx2; apply Hfr; [exact Hx2 | lia] | exact Hgr]|].
split; [exact HJ | exact HARU].
Qed.
(* the exit at the NUL after the last character (0x81804) *)
Lemma caw_exit_end : forall j sx pad sx' pad' E (ms ms2 : machine_state) mdc2 E2 ss2,
  caw_static -> (j < length tb)%nat -> (S j = length tb)%nat ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  WriterSpec.b64_scan pad sx [nth j tb 0] = Some (sx', pad') ->
  caw_memf (ms_mem ms) ->
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) -> ss_pc ss2 = 0x81804 ->
  reabs_check caw_P ss2 caw_regs1 caw_factsX = true -> nth_error (ss_mem ss2) 0 = Some caw_stk ->
  (forall n, (n < 45)%nat -> ew E2 n = ew E n) ->
  bv_unsigned (getr (ms_regs ms2) 19%bv) = t + Z.of_nat (S j) ->
  bv_unsigned (getr (ms_regs ms2) 14%bv) = Z.of_nat (length sx') ->
  bv_unsigned (getr (ms_regs ms2) 28%bv) = pad' ->
  (forall x : word, ~ (spE - 64 <= bv_unsigned x < spE) ->
     ~ (six + Z.of_nat (length sx) <= bv_unsigned x < six + Z.of_nat (length sx) + 1) -> ms_mem ms2 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
  caw_six (ms_mem ms2) sx' ->
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 k ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
  caw_post E (ms_mem ms) j sx pad ms2 mdc2.
Proof.
intros j sx pad sx' pad' E ms ms2 mdc2 E2 ss2 HST Hj Hend Hscan Hstep HM HS2 Hpc Hck Hstk HAg R19 R14 R28 Hfr Hgr H6 HJ HARU.
pose proof HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (caw_scan_step tb j sx pad sx' pad' Hj Hscan Hstep) as [Hscan' Hrest].
pose proof (caw_scan_bound _ 0 [] sx' pad' Hscan') as (_ & Hp0 & Hsb).
rewrite firstn_length_le in Hsb by lia. cbn [length] in Hsb.
pose proof (caw_scan_bound [nth j tb 0] pad sx sx' pad' Hstep) as (Hl & _ & _).
pose proof (caw_scan_bound _ 0 [] sx pad Hscan) as (_ & Hp00 & Hsb0).
rewrite firstn_length_le in Hsb0 by lia. cbn [length] in Hsb0.
exists (caw_reenv E2 (ms_regs ms2) (ew E2 40) (ew E2 41)), (S j), (length sx'), pad'.
split; [intros n Hn; rewrite caw_reenv_old by exact Hn; apply HAg; lia|].
split; [rewrite caw_reenv_35; apply caw_w_of_u; exact R19|].
split; [rewrite caw_reenv_38; apply caw_w_of_u; exact R14|].
split; [rewrite caw_reenv_39; apply caw_w_of_u; exact R28|].
split; [lia|]. split; [lia|].
split; [rewrite Hrest, (caw_skipn_end tb j Hend); cbn [WriterSpec.b64_scan];
  split; [unfold caw_ssX; rewrite <- Hpc;
          apply (caw_exit_ok E2 ss2 ms2 (S j) (length sx') pad' HS2 Hck Hstk R19 R14 R28); unfold CAW_CEIL; lia|];
  split; [lia|]; split; [reflexivity|]; split; [reflexivity|];
  split; [exact (caw_scan_six _ 0 [] sx' pad' Hscan' (Forall_nil _)) | exact H6]|].
split; [intros x Hx1 Hx2; apply Hfr; [exact Hx2 | lia]|].
split; [exact Hgr|].
split; [apply (caw_memf_frame (ms_mem ms) (ms_mem ms2) HST HM); [intros x Hx1 Hx2; apply Hfr; [exact Hx2 | lia] | exact Hgr]|].
split; [exact HJ | exact HARU].
Qed.
(* back at the head with the next character *)
Lemma caw_next : forall j sx pad sx' pad' E (ms : machine_state) (Q : world tfibsegs -> config -> Prop) E2 ss2
  (ms2 : machine_state) mdc2,
  caw_static -> caw_loop_at (S j) -> (j < length tb)%nat -> (S j < length tb)%nat ->
  caw_atoms E j (length sx) pad ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  WriterSpec.b64_scan pad sx [nth j tb 0] = Some (sx', pad') ->
  caw_memf (ms_mem ms) ->
  (forall ms' mdc', caw_post E (ms_mem ms) j sx pad ms' mdc' -> SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) -> ss_pc ss2 = 0x8170c ->
  reabs_check caw_P ss2 caw_regs1 caw_facts1n = true -> nth_error (ss_mem ss2) 0 = Some caw_stk ->
  (forall n, (n < 45)%nat -> ew E2 n = ew E n) ->
  bv_unsigned (getr (ms_regs ms2) 19%bv) = t + Z.of_nat (S j) ->
  bv_unsigned (getr (ms_regs ms2) 11%bv) = t + Z.of_nat (S j) + 1 ->
  bv_unsigned (getr (ms_regs ms2) 12%bv) = nth (S j) tb 0 ->
  bv_unsigned (getr (ms_regs ms2) 14%bv) = Z.of_nat (length sx') ->
  bv_unsigned (getr (ms_regs ms2) 28%bv) = pad' ->
  (forall x : word, ~ (spE - 64 <= bv_unsigned x < spE) ->
     ~ (six + Z.of_nat (length sx) <= bv_unsigned x < six + Z.of_nat (length sx) + 1) -> ms_mem ms2 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
  caw_six (ms_mem ms2) sx' ->
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 k ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
  SRr tfibsegs W (mkCfg ms2 mdc2) Q.
Proof.
intros j sx pad sx' pad' E ms Q E2 ss2 ms2 mdc2 HST IH Hj Hj1 HA Hscan Hstep HM Hk HS2 Hpc Hck Hstk HAg
  R19 R11 R12 R14 R28 Hfr Hgr H6 HJ HARU.
pose proof HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr).
destruct HA as (A2 & A33 & _).
destruct (caw_scan_step tb j sx pad sx' pad' Hj Hscan Hstep) as [Hscan' Hrest].
pose proof (caw_scan_bound _ 0 [] sx' pad' Hscan') as (_ & Hp0 & Hsb).
rewrite firstn_length_le in Hsb by lia. cbn [length] in Hsb.
pose proof (caw_scan_bound _ 0 [] sx pad Hscan) as (_ & Hp00 & Hsb0).
rewrite firstn_length_le in Hsb0 by lia. cbn [length] in Hsb0.
assert (HM2 : caw_memf (ms_mem ms2)).
{ apply (caw_memf_frame (ms_mem ms) (ms_mem ms2) HST HM); [|exact Hgr].
  intros x Hx1 Hx2. apply Hfr; [exact Hx2 | lia]. }
destruct (caw_head_ok E2 ss2 ms2 j (length sx') pad' HST HM2 HS2 Hpc Hck Hstk
  ltac:(rewrite HAg by lia; exact A2) ltac:(rewrite HAg by lia; exact A33) Hj1 R19 R11 R12 R14 R28
  ltac:(lia) ltac:(lia)) as [HS' HA'].
apply (IH Hj1 sx' pad' _ ms2 mdc2 Q HS' HA' Hscan' (caw_scan_six _ 0 [] sx' pad' Hscan' (Forall_nil _)) HM2 H6 HJ HARU).
intros ms' mdc' Hpost. apply Hk.
exact (caw_post_step E _ (ms_mem ms) (ms_mem ms2) j sx pad sx' pad' ms' mdc' HST Hj Hscan Hstep
  ltac:(intros n Hn; rewrite caw_reenv_old by exact Hn; apply HAg; lia) Hfr Hgr Hpost).
Qed.

(* ---- the walk of one character class: the tactics ---- *)
Lemma caw_ss1_32 : forall E lo hi ms, st_ok tfibsegs E (caw_ss1 lo hi) ms -> ew E 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
intros E lo hi ms HS. pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & _ & _)).
unfold caw_ss1, caw_facts1 in HA. cbn [ss_facts f_atoms atoms_ok] in HA.
destruct HA as (_ & _ & A32 & _). unfold afact_ok in A32. cbn [af_lo af_hi] in A32.
apply caw_w_of_u. lia.
Qed.
Lemma caw_regv_off : forall EN ssN (msN : machine_state) (r : bv 5) n z v,
  st_ok tfibsegs EN ssN (restrict (w_H W) msN) -> sr_get (ss_regs ssN) r = SOff n z ->
  bv_unsigned (ew EN n) + z = v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr (ms_regs msN) r) = v.
Proof.
intros EN ssN msN r n z v HS Hr Hv Hb. rewrite (st_ok_restrict_reg tfibsegs (w_H W) EN ssN msN r HS), Hr, denot_SOff, Hv.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma caw_regv_lit' : forall EN ssN (msN : machine_state) (r : bv 5) z v,
  st_ok tfibsegs EN ssN (restrict (w_H W) msN) -> sr_get (ss_regs ssN) r = SLit z -> z = v -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (getr (ms_regs msN) r) = v.
Proof. intros EN ssN msN r z v HS Hr <- Hz. exact (caw_regv_lit EN ssN msN r z HS Hr Hz). Qed.
Lemma caw_six_snoc : forall (m : word -> option byte) sx v, caw_six m sx ->
  val_mem tfibsegs (mrestrict (w_H W) m) (six + Z.of_nat (length sx)) 1 v -> caw_six m (sx ++ [v]).
Proof.
intros m sx v H Hv i Hi. rewrite length_app in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i (length sx)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. exact (H i Hl).
- assert (i = length sx) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hv.
Qed.
Lemma caw_store_byte : forall EN ssN (msN : machine_state) e v q,
  st_ok tfibsegs EN ssN (restrict (w_H W) msN) ->
  nth_error (ss_mem ssN) 2 = Some (YP09.mkRegion (Some 40%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 e)]) ->
  bv_unsigned (ew EN 40) = q -> sv_denot EN e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 v.
Proof.
intros EN ssN msN e v q HS Hn Hq He Hv.
pose proof (fsw_region_nth EN ssN (restrict (w_H W) msN) 2 _ HS Hn) as R. cbn [ms_mem restrict] in R.
pose proof (fsw_field EN _ 40 q [YP09.mkChunk 0 (CVal 1 e)] 0 1 0 1 0 1%N e v R Hq ltac:(left; reflexivity) He
  ltac:(cbn; lia) ltac:(cbn; lia)) as Hm.
rewrite Z.add_0_r in Hm. exact Hm.
Qed.
(* the next character: a NUL exactly at the end of the text *)
Lemma caw_next_char : forall j, caw_static -> (j < length tb)%nat ->
  ((S j < length tb)%nat /\ nth (S j) (tb ++ [0]) 0 = nth (S j) tb 0 /\ nth (S j) tb 0 <> 0) \/
  ((S j = length tb)%nat /\ nth (S j) (tb ++ [0]) 0 = 0).
Proof.
intros j HST Hj. pose proof HST as (Hnz & _).
destruct (Nat.lt_ge_cases (S j) (length tb)) as [H|H].
- left. split; [exact H|]. split; [apply app_nth1; exact H|].
  apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. exact H.
- right. assert (S j = length tb) as E by lia. split; [exact E|].
  rewrite app_nth2 by lia. rewrite E, Nat.sub_diag. reflexivity.
Qed.

(* the run tactics; HS / HJ / HARU / SHOK the run's state, journal, ARU and shadow entries. The agreement of the
   run's env with the head env (atoms below 45: the token atoms of a run start at run_K = 45, past
   the state's last atom 44) and the head's atom values are found by their form. *)
Ltac caw_uval :=
  repeat match goal with H : bv_unsigned (ew ?E0 ?n) = _ |- context [bv_unsigned (ew ?E0 ?n)] => rewrite H end.
Ltac caw_awr_tac :=
  lazymatch goal with
  | HSTx : caw_static, HAgx : forall n, (n < 45)%nat -> ew ?Er n = ew ?E0 n,
    U2x : bv_unsigned (ew ?E0 2) = _, U40x : bv_unsigned (ew ?E0 40) = _ |- awr_ok _ _ ?Er _ _ _ _ _ _ _ _ _ =>
    eapply (caw_awr _ _ _ HSTx); [vm_compute; reflexivity | try (rewrite HAgx by lia); exact U2x
      | try (rewrite HAgx by lia); exact U40x | lia]
  end.
Ltac caw_post_run :=
  lazymatch goal with
  | HSn : st_ok _ ?En _ (restrict _ ?msn), HFn : frame_of ?Er ?rs (ms_mem ?msa) (ms_mem ?msn),
    HFrn : frame_of _ _ (mrestrict _ (ms_mem ?msa)) _,
    HAg0 : forall n, (n < 45)%nat -> ew ?Er n = ew ?E0 n,
    U2x : bv_unsigned (ew ?E0 2) = ?spx, U40x : bv_unsigned (ew ?E0 40) = ?qx |- _ =>
    let HAg' := fresh "HAg" in
    assert (HAg' : forall n, (n < 45)%nat -> ew En n = ew E0 n)
      by (let n := fresh "n" in let Hn := fresh "Hn" in
          intros n Hn; try (rewrite <- (HAg0 n Hn)); rewrite ?caw_ew_ewset by lia; reflexivity);
    let Fr := fresh "Fr" in
    pose proof (caw_frame_run Er rs (ms_mem msa) (ms_mem msn) spx qx
      ltac:(vm_compute; reflexivity) HFn ltac:(try (rewrite HAg0 by lia); exact U2x) ltac:(try (rewrite HAg0 by lia); exact U40x)) as Fr;
    clear HFn HFrn HAg0
  end.
Ltac caw_run stop :=
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ _), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HARUx : ARU _ _ _ _ _ _ _ _, SHOKx : sh_ok _ _ _ _ _ |- _ =>
    fsw_aj_run_to_tokU caw_tbl_ok HSx HJx HARUx SHOKx caw_Bspan stop; [caw_awr_tac | caw_post_run]
  end.
Ltac caw_rv :=
  lazymatch goal with
  | HSN : st_ok _ ?EN ?ssN (restrict _ ?msN), HAgx : forall n, (n < 45)%nat -> ew ?EN n = ew ?E0 n
    |- bv_unsigned (getr (ms_regs ?msN) ?r) = ?v =>
    let e := eval vm_compute in (sr_get (ss_regs ssN) r) in
    lazymatch e with
    | SOff ?n ?z => apply (caw_regv_off EN ssN msN r n z v HSN ltac:(vm_compute; reflexivity));
        [try (rewrite HAgx by lia); caw_uval; rewrite ?length_app; cbn [length]; lia
        | rewrite ?length_app; cbn [length]; lia]
    | SLit ?z => apply (caw_regv_lit' EN ssN msN r z v HSN ltac:(vm_compute; reflexivity)); lia
    end
  end.
Ltac caw_fr :=
  let x := fresh "x" in let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros x H1 H2;
  repeat match goal with Fr : forall y : word, _ -> _ -> ms_mem ?b y = ms_mem ?a y |- ms_mem ?b x = _ =>
    rewrite (Fr x H1 H2) end;
  reflexivity.
Ltac caw_gr :=
  repeat match goal with H1 : mem_grows ?a ?b, H2 : mem_grows ?b ?c |- _ =>
    let H := fresh "HG" in pose proof (mem_grows_trans _ _ _ H1 H2) as H; clear H1 H2 end;
  assumption.
Ltac caw_cont :=
  lazymatch goal with Hkx : forall ms' mdc', caw_post _ _ _ _ _ ms' mdc' -> _ |- _ => apply Hkx end.
(* the refusal exit (0x81a78) *)
Ltac caw_break Hstop :=
  caw_cont; eapply caw_exit_break;
  [ eassumption | eassumption | eassumption | Hstop | eassumption | eassumption
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | eassumption
  | caw_rv | caw_rv | caw_rv | caw_fr | caw_gr | eassumption | eassumption ].
(* the head of an iteration: the atoms' values, the shadow entries, the class of the character *)
Ltac caw_intro lo hi :=
  intros j HST IH Hc Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk;
  pose proof HST as (Hnz & Hlen & Ht0 & Ht1 & Htsh & Hs0 & Hs1 & Hsz & Hssh & Hdis & Hce & Hsp1 & Hsp2 & Hsp3 & Hawr);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  pose proof (caw_scan_bound _ 0 [] sx pad Hscan) as (_ & Hp0 & Hsb);
  rewrite firstn_length_le in Hsb by lia; cbn [length] in Hsb;
  pose proof HA as (A2 & A33 & A35 & A36 & A37 & A38 & A39 & A40 & A41);
  assert (Hlen1 : length (tb ++ [0]) = S (length tb)) by (rewrite length_app; cbn [length]; lia);
  destruct (proj1 HM (S j) ltac:(lia)) as [_ RN];
  destruct (proj1 HM j ltac:(lia)) as [_ RC]; rewrite app_nth1 in RC by exact Hj;
  assert (U2 : bv_unsigned (ew E 2) = spE) by (apply caw_ew_lit; [exact A2 | lia]);
  assert (U33 : bv_unsigned (ew E 33) = six) by (apply caw_ew_lit; [exact A33 | lia]);
  assert (U35 : bv_unsigned (ew E 35) = t + Z.of_nat j) by (apply caw_ew_lit; [exact A35 | lia]);
  assert (U36 : bv_unsigned (ew E 36) = t + Z.of_nat j + 1) by (apply caw_ew_lit; [exact A36 | lia]);
  assert (U37 : bv_unsigned (ew E 37) = nth j tb 0) by (apply caw_ew_lit; [exact A37 | lia]);
  assert (U38 : bv_unsigned (ew E 38) = Z.of_nat (length sx)) by (apply caw_ew_lit; [exact A38 | lia]);
  assert (U39 : bv_unsigned (ew E 39) = pad) by (apply caw_ew_lit; [exact A39 | lia]);
  assert (U40 : bv_unsigned (ew E 40) = six + Z.of_nat (length sx)) by (apply caw_ew_lit; [exact A40 | lia]);
  assert (U41 : bv_unsigned (ew E 41) = nth (S j) (tb ++ [0]) 0) by (apply caw_ew_lit; [exact A41 | lia]);
  pose proof (caw_ss1_32 E 1 255 _ HS) as A32;
  pose proof (caw_shok E (ms_mem ms) j (six + Z.of_nat (length sx)) HST HM Hj A32 U35 U36 U40 ltac:(lia)) as SHOK;
  apply (caw_narrow E 1 255 lo hi) in HS; [|rewrite U37; lia];
  assert (HAg : forall n, (n < 45)%nat -> ew E n = ew E n) by (intros; reflexivity).
(* add the classification conditions the engine cannot decide from the class (c - 'A', c - 'a', c - '0' wrap) *)
Ltac caw_cond C bf :=
  lazymatch goal with HSx : st_ok _ ?E0 _ _, A37x : ew ?E0 37 = Z_to_bv 64 ?c |- _ =>
    apply (st_ok_add_cond tfibsegs _ _ _ (ac_c C) (ac_a C) (ac_b C)) in HSx;
    [|rewrite (caw_br37 E0 c (ac_c C) (ac_a C) (ac_b C) A37x eq_refl eq_refl); apply bf; lia]
  end.

(* ---- the classes that refuse at once ---- *)
Lemma caw_cls_hi : forall j, caw_static -> caw_loop_at (S j) -> 123 <= nth j tb 0 <= 255 -> caw_loop_at j.
Proof.
caw_intro 123 255.
caw_run 0x81a78.
caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_bad _ 123 255 ltac:(vm_compute; reflexivity) Hc))).
Qed.
Lemma caw_cls_91 : forall j, caw_static -> caw_loop_at (S j) -> 91 <= nth j tb 0 <= 96 -> caw_loop_at j.
Proof.
caw_intro 91 96. caw_cond caw_C2 caw_bf_C2.
caw_run 0x81a78.
caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_bad _ 91 96 ltac:(vm_compute; reflexivity) Hc))).
Qed.
Lemma caw_cls_62 : forall j, caw_static -> caw_loop_at (S j) -> 62 <= nth j tb 0 <= 64 -> caw_loop_at j.
Proof.
caw_intro 62 64. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2.
caw_run 0x81a78.
caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_bad _ 62 64 ltac:(vm_compute; reflexivity) Hc))).
Qed.
(* ---- the branches the engine leaves to the walk ---- *)
Lemma caw_Uag : forall En E0 n v, (forall m, (m < 45)%nat -> ew En m = ew E0 m) -> (n < 45)%nat ->
  bv_unsigned (ew E0 n) = v -> U En (SOff n 0) = v.
Proof. intros En E0 n v HA Hn Hv. apply caw_U0. rewrite HA by exact Hn. exact Hv. Qed.
(* `beqz a2` at 0x8179c on the next character: not taken -> the next head, taken -> the end of the text *)
Lemma caw_N_more : forall j, caw_static -> (j < length tb)%nat ->
  (nth (S j) (tb ++ [0]) 0 =? 0) = false ->
  (S j < length tb)%nat /\ nth (S j) (tb ++ [0]) 0 = nth (S j) tb 0.
Proof.
intros j HST Hj Hb. destruct (caw_next_char j HST Hj) as [(H1 & H2 & H3)|(H1 & H2)]; [split; assumption|].
rewrite H2 in Hb. discriminate Hb.
Qed.
Lemma caw_N_end : forall j, caw_static -> (j < length tb)%nat ->
  (nth (S j) (tb ++ [0]) 0 =? 0) = true -> (S j = length tb)%nat.
Proof.
intros j HST Hj Hb. destruct (caw_next_char j HST Hj) as [(H1 & H2 & H3)|(H1 & H2)]; [|exact H1].
apply Z.eqb_eq in Hb. rewrite H2 in Hb. contradiction.
Qed.
Lemma caw_bf_wsbad : forall c lo hi, forallb (fun c => WriterSpec.b64_ws c || caw_bad c) (zrange lo hi) = true ->
  lo <= c <= hi -> WriterSpec.b64_ws c = false -> caw_bad c = true.
Proof.
intros c lo hi H Hc Hw. pose proof (zrange_all _ lo hi H c Hc) as Hx. cbv beta in Hx. rewrite Hw in Hx. exact Hx.
Qed.
Lemma caw_bf_nows : forall c lo hi, forallb (fun c => negb (WriterSpec.b64_ws c)) (zrange lo hi) = true ->
  lo <= c <= hi -> WriterSpec.b64_ws c = false.
Proof.
intros c lo hi H Hc. pose proof (zrange_all _ lo hi H c Hc) as Hx. cbv beta in Hx. apply negb_true_iff in Hx. exact Hx.
Qed.
Ltac caw_br cn av bv :=
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ _) |- SRr _ _ _ _ =>
    eapply SRr_sym_branch with (c := cn) (a := av) (b := bv);
    [exact HSx | clear HSx; let Hb := fresh "Hb" in intros Hb HSx | clear HSx; let Hb := fresh "Hb" in intros Hb HSx]
  end.
Ltac caw_hb37 :=
  lazymatch goal with Hb : branch_taken ?cnd (sv_denot ?En ?a) (sv_denot ?En ?b) = _,
    HAgx : forall n, (n < 45)%nat -> ew ?En n = ew ?E0 n, A37x : ew ?E0 37 = Z_to_bv 64 ?c |- _ =>
    rewrite (caw_br37 En c cnd a b ltac:(try (rewrite HAgx by lia); exact A37x) eq_refl eq_refl) in Hb
  end.
Ltac caw_hbU :=
  lazymatch goal with Hb : branch_taken BC_NE (sv_denot ?En (SOff ?n 0)) (sv_denot ?En (SLit _)) = _,
    HAgx : forall m, (m < 45)%nat -> ew ?En m = ew ?E0 m, Ux : bv_unsigned (ew ?E0 ?n) = ?v |- _ =>
    rewrite branch_ne_U, (caw_Uag En E0 n v HAgx ltac:(lia) Ux), U_lit in Hb by lia
  end.
Ltac caw_hbUe :=
  lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?En (SOff ?n 0)) (sv_denot ?En (SLit _)) = _,
    HAgx : forall m, (m < 45)%nat -> ew ?En m = ew ?E0 m, Ux : bv_unsigned (ew ?E0 ?n) = ?v |- _ =>
    rewrite branch_eq_U, (caw_Uag En E0 n v HAgx ltac:(lia) Ux), U_lit in Hb by lia
  end.
Ltac caw_six_keep :=
  lazymatch goal with HSTx : caw_static, H6x : caw_six (ms_mem ?ms0) ?sx0 |- caw_six (ms_mem ?msN) ?sx0 =>
    apply (caw_six_frame (ms_mem ms0) (ms_mem msN) sx0 (six + Z.of_nat (length sx0)) HSTx H6x ltac:(lia)); caw_fr
  end.
Ltac caw_six_store den :=
  lazymatch goal with |- caw_six (ms_mem ?msN) (?sx0 ++ [?v]) =>
    apply caw_six_snoc; [caw_six_keep |
      lazymatch goal with HSx : st_ok _ ?EN ?ssN (restrict _ msN), HAgx : forall n, (n < 45)%nat -> ew ?EN n = ew ?E0 n,
        U40x : bv_unsigned (ew ?E0 40) = _ |- _ =>
      let r := eval vm_compute in (nth_error (ss_mem ssN) 2) in
      lazymatch r with Some (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?e)]) =>
        apply (caw_store_byte EN ssN msN e v (six + Z.of_nat (length sx0)) HSx ltac:(vm_compute; reflexivity));
        [try (rewrite HAgx by lia); exact U40x | den | lia]
      end end ]
  end.
(* the next head, the end of the text *)
Ltac caw_next_tac Hstep H6tac :=
  eapply caw_next;
  [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | exact Hstep | eassumption
  | eassumption | eassumption | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | eassumption | caw_rv | caw_rv | caw_rv | caw_rv | caw_rv | caw_fr | caw_gr | H6tac | eassumption | eassumption ].
Ltac caw_end_tac Hstep H6tac :=
  caw_cont; eapply caw_exit_end;
  [ eassumption | eassumption | eassumption | eassumption | exact Hstep | eassumption | eassumption
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | eassumption
  | caw_rv | caw_rv | caw_rv | caw_fr | caw_gr | H6tac | eassumption | eassumption ].
(* after the advance (0x8177c-0x817a0: the UBSan test of s3 + 1, decided; the shadow check of a1; s3++; the next
   character): `beqz a2` at 0x8179c decides the next head or the end *)
Ltac caw_adv Hstep H6tac :=
  caw_run 0x81804;
  caw_br BC_EQ (SOff 41 0) (SLit 0);
  [ caw_hbUe;
    lazymatch goal with HSTx : caw_static, Hjx : (?j0 < length _)%nat, Hb : (_ =? 0) = true |- _ =>
      pose proof (caw_N_end j0 HSTx Hjx Hb) as Hend end;
    caw_run 0x81804; caw_end_tac Hstep H6tac
  | caw_hbUe;
    lazymatch goal with HSTx : caw_static, Hjx : (?j0 < length _)%nat, Hb : (_ =? 0) = false |- _ =>
      destruct (caw_N_more j0 HSTx Hjx Hb) as [Hj1 HN1] end;
    caw_run 0x8170c; caw_next_tac Hstep H6tac ].
(* a sextet value c + d at the '=' test 0x817bc (bnez t3): with '=' seen the text is refused (0x81a78), else it is
   stored (the UBSan test `bltu a3, a4` at 0x817c0 is decided by the engine) *)
Lemma caw_val_scan_pad : forall c v pad sx, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  pad <> 0 -> WriterSpec.b64_scan pad sx [c] = None.
Proof.
intros c v pad sx H1 H2 H3 H4. rewrite (caw_val_scan c v pad sx H1 H2 H3).
replace (pad =? 0) with false by (symmetry; apply Z.eqb_neq; exact H4). reflexivity.
Qed.
Lemma caw_val_scan_0 : forall c v sx, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  WriterSpec.b64_scan 0 sx [c] = Some (sx ++ [v], 0).
Proof. intros c v sx H1 H2 H3. rewrite (caw_val_scan c v 0 sx H1 H2 H3). reflexivity. Qed.
Ltac caw_value Hv den :=
  destruct Hv as (Hv1 & Hv2 & Hv3);
  caw_br BC_NE (SOff 39 0) (SLit 0);
  [ caw_hbU;
    lazymatch goal with Hbx : negb (_ =? 0) = true |- _ => apply negb_true_iff, Z.eqb_neq in Hbx end;
    caw_run 0x81a78;
    caw_break ltac:(eapply caw_val_scan_pad; eassumption)
  | caw_hbU;
    lazymatch goal with Hbx : negb (?p =? 0) = false |- _ => apply negb_false_iff, Z.eqb_eq in Hbx; rewrite Hbx in * end;
    lazymatch goal with H6x : caw_six (ms_mem _) ?sx0 |- _ =>
      caw_adv (caw_val_scan_0 _ _ sx0 ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
        ltac:(idtac; caw_six_store den) end ].

(* ---- the classes below '0' with whitespace: 1 .. 42 ---- *)
Lemma caw_cls_lo : forall j, caw_static -> caw_loop_at (S j) -> 1 <= nth j tb 0 <= 42 -> caw_loop_at j.
Proof.
caw_intro 1 42. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2. caw_cond caw_C3 caw_bf_C3.
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- (* t5 = 0: no whitespace, the value -1 *)
  caw_hb37. rewrite caw_bf_ws in Hb by lia. apply negb_true_iff in Hb. rename Hb into Hnws.
  caw_run 0x81a78.
  caw_br BC_LT caw_slx (SLit 0).
  + caw_run 0x81a78.
    caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_wsbad _ 1 42 ltac:(vm_compute; reflexivity) Hc Hnws))).
  + exfalso. caw_hb37. rewrite caw_bf_sl in Hb by lia. discriminate Hb.
- (* whitespace *)
  caw_hb37. rewrite caw_bf_ws in Hb by lia. apply negb_false_iff in Hb.
  caw_adv (caw_ws_scan (nth j tb 0) pad sx Hb) ltac:(idtac; caw_six_keep).
Qed.
Lemma caw_bf_AZv : forall c, 65 <= c <= 90 -> sv_denot (Ec c) (caw_azx (-65)) = Z_to_bv 64 (c - 65).
Proof. intros c Hc. exact (proj2 (caw_bf_AZ c Hc)). Qed.
Lemma caw_bf_azv : forall c, 97 <= c <= 122 -> sv_denot (Ec c) (caw_azx (-71)) = Z_to_bv 64 (c - 71).
Proof. intros c Hc. exact (proj2 (caw_bf_az c Hc)). Qed.
Ltac caw_den bf :=
  lazymatch goal with HAgx : forall n, (n < 45)%nat -> ew ?EN n = ew ?E0 n, A37x : ew ?E0 37 = Z_to_bv 64 ?c
    |- sv_denot ?EN ?e = Z_to_bv 64 ?v =>
    rewrite (caw_den37 EN c e ltac:(try (rewrite HAgx by lia); exact A37x) eq_refl);
    etransitivity; [exact (bf c ltac:(lia)) | f_equal; lia]
  end.

(* ---- the other refused classes ---- *)
Lemma caw_cls_44 : forall j, caw_static -> caw_loop_at (S j) -> 44 <= nth j tb 0 <= 46 -> caw_loop_at j.
Proof.
caw_intro 44 46. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2. caw_cond caw_C3 caw_bf_C3.
pose proof (caw_bf_nows _ 44 46 ltac:(vm_compute; reflexivity) Hc) as Hnws.
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- caw_run 0x81a78.
  caw_br BC_LT caw_slx (SLit 0).
  + caw_run 0x81a78.
    caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_bad _ 44 46 ltac:(vm_compute; reflexivity) Hc))).
  + exfalso. caw_hb37. rewrite caw_bf_sl in Hb0 by lia. discriminate Hb0.
- exfalso. caw_hb37. rewrite caw_bf_ws, Hnws in Hb by lia. discriminate Hb.
Qed.
Lemma caw_cls_58 : forall j, caw_static -> caw_loop_at (S j) -> 58 <= nth j tb 0 <= 60 -> caw_loop_at j.
Proof.
caw_intro 58 60. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2.
pose proof (caw_bf_nows _ 58 60 ltac:(vm_compute; reflexivity) Hc) as Hnws.
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- caw_run 0x81a78.
  caw_break ltac:(exact (caw_bad_scan (nth j tb 0) pad sx (caw_bf_bad _ 58 60 ltac:(vm_compute; reflexivity) Hc))).
- exfalso. caw_hb37. rewrite caw_bf_ws, Hnws in Hb by lia. discriminate Hb.
Qed.

(* ---- '=' (the UBSan test of `pad++` at 0x817ac is decided by the engine: `addiw a2, t3, 1` is t3 + 1) ---- *)
Lemma caw_cls_61 : forall j, caw_static -> caw_loop_at (S j) -> 61 <= nth j tb 0 <= 61 -> caw_loop_at j.
Proof.
caw_intro 61 61. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2.
assert (H61 : nth j tb 0 = 61) by lia.
assert (Hstep : WriterSpec.b64_scan pad sx [nth j tb 0] = Some (sx, pad + 1)) by (rewrite H61; reflexivity).
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- caw_run 0x81a78.
  caw_br BC_NE (SOff 37 0) (SLit 61).
  + exfalso. caw_hbU. rewrite H61 in Hb0. discriminate Hb0.
  + caw_adv Hstep ltac:(idtac; caw_six_keep).
- exfalso. caw_hb37. rewrite caw_bf_ws, H61 in Hb by lia. discriminate Hb.
Qed.

(* ---- the sextet classes ---- *)
Lemma caw_cls_AZ : forall j, caw_static -> caw_loop_at (S j) -> 65 <= nth j tb 0 <= 90 -> caw_loop_at j.
Proof.
caw_intro 65 90.
pose proof (caw_vcls_ok 65 90 (-65) _ ltac:(vm_compute; reflexivity) Hc) as Hv.
caw_run 0x81a78.
caw_br BC_LT (caw_azx (-65)) (SLit 0).
- exfalso. caw_hb37. rewrite (proj1 (caw_bf_AZ _ Hc)) in Hb. discriminate Hb.
- caw_run 0x81a78.
  caw_value Hv ltac:(idtac; caw_den caw_bf_AZv).
Qed.
Lemma caw_cls_az : forall j, caw_static -> caw_loop_at (S j) -> 97 <= nth j tb 0 <= 122 -> caw_loop_at j.
Proof.
caw_intro 97 122.
pose proof (caw_vcls_ok 97 122 (-71) _ ltac:(vm_compute; reflexivity) Hc) as Hv.
caw_run 0x81a78.
caw_br BC_LT (caw_azx (-71)) (SLit 0).
- exfalso. caw_hb37. rewrite (proj1 (caw_bf_az _ Hc)) in Hb. discriminate Hb.
- caw_run 0x81a78.
  caw_value Hv ltac:(idtac; caw_den caw_bf_azv).
Qed.
Lemma caw_cls_09 : forall j, caw_static -> caw_loop_at (S j) -> 48 <= nth j tb 0 <= 57 -> caw_loop_at j.
Proof.
caw_intro 48 57. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2.
pose proof (caw_vcls_ok 48 57 4 _ ltac:(vm_compute; reflexivity) Hc) as Hv.
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- caw_run 0x81a78.
  caw_value Hv ltac:(idtac; caw_den caw_bf_09).
- exfalso. caw_hb37. rewrite caw_bf_ws, (proj1 Hv) in Hb by lia. discriminate Hb.
Qed.
Lemma caw_cls_43 : forall j, caw_static -> caw_loop_at (S j) -> 43 <= nth j tb 0 <= 43 -> caw_loop_at j.
Proof.
caw_intro 43 43. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2. caw_cond caw_C3 caw_bf_C3.
pose proof (caw_vcls_ok 43 43 19 _ ltac:(vm_compute; reflexivity) Hc) as Hv.
caw_run 0x81a78.
caw_br BC_NE (SOff 37 0) (SLit 43).
- exfalso. caw_hbU. replace (nth j tb 0) with 43 in Hb by lia. discriminate Hb.
- caw_run 0x81a78.
  caw_br BC_EQ caw_wsx (SLit 0).
  + caw_run 0x81a78.
    caw_value Hv ltac:(idtac; cbn [sv_denot]; f_equal; lia).
  + exfalso. caw_hb37. rewrite caw_bf_ws, (proj1 Hv) in Hb0 by lia. discriminate Hb0.
Qed.
Lemma caw_cls_47 : forall j, caw_static -> caw_loop_at (S j) -> 47 <= nth j tb 0 <= 47 -> caw_loop_at j.
Proof.
caw_intro 47 47. caw_cond caw_C1 caw_bf_C1. caw_cond caw_C2 caw_bf_C2. caw_cond caw_C3 caw_bf_C3.
pose proof (caw_vcls_ok 47 47 16 _ ltac:(vm_compute; reflexivity) Hc) as Hv.
caw_run 0x81a78.
caw_br BC_EQ caw_wsx (SLit 0).
- caw_run 0x81a78.
  caw_value Hv ltac:(idtac; cbn [sv_denot]; f_equal; lia).
- exfalso. caw_hb37. rewrite caw_bf_ws, (proj1 Hv) in Hb by lia. discriminate Hb.
Qed.
(* ---- the loop ---- *)
Lemma caw_class_split : forall c, 1 <= c <= 255 ->
  (1 <= c <= 42) \/ (43 <= c <= 43) \/ (44 <= c <= 46) \/ (47 <= c <= 47) \/ (48 <= c <= 57) \/ (58 <= c <= 60) \/
  (61 <= c <= 61) \/ (62 <= c <= 64) \/ (65 <= c <= 90) \/ (91 <= c <= 96) \/ (97 <= c <= 122) \/ (123 <= c <= 255).
Proof. intros c Hc. lia. Qed.
Lemma caw_loop_step : forall j, caw_static -> caw_loop_at (S j) -> caw_loop_at j.
Proof.
intros j HST IH Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk.
assert (Hc : 1 <= nth j tb 0 <= 255).
{ pose proof HST as (Hnz & _).
  destruct (proj1 HM j ltac:(rewrite length_app; cbn [length]; lia)) as [_ R]. rewrite app_nth1 in R by exact Hj.
  pose proof (proj1 (Forall_forall _ _) Hnz (nth j tb 0) (nth_In _ _ Hj)) as Hn0. cbv beta in Hn0. lia. }
destruct (caw_class_split _ Hc) as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]].
- exact (caw_cls_lo j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_43 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_44 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_47 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_09 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_58 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_61 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_62 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_AZ j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_91 j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_az j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
- exact (caw_cls_hi j HST IH H Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
Qed.
Lemma caw_loop_all : caw_static -> forall d j, (length tb - j = d)%nat -> caw_loop_at j.
Proof.
intros HST d. induction d as [|d IH]; intros j Hd.
- intros Hj. lia.
- apply caw_loop_step; [exact HST|]. apply IH. lia.
Qed.

(* THE LEMMA. From the loop head 0x8170c at text index j (the state caw_ss1 with the atoms caw_atoms: s3 = t + j,
   a1 = t + j + 1, a2 = c = tb[j], a4 = m = |sx|, t3 = pad, six + m, the next character), the sextets sx and pad that
   b64_scan gives for tb[0, j) written at six[0, m), the text, its shadow, six's shadow and writability (caw_memf) and
   what does not change (caw_static), the machine reaches a loop exit, and the goal Q holds if the continuation
   discharges it there from caw_post: the atoms (s3 = t + j', a4 = m', t3 = pad'), what b64_scan pad sx tb[j ..]
   gives (Some (sx', pad'): the state caw_ssX at 0x81804, j' = |tb|, m' = |sx'|, six[0, m') holds sx'; None: the
   state caw_ssB at 0x81a78, tb[j'] is the refused character), memory outside [six, six + m' + 1) and the stack
   window [spE - 64, spE) unchanged, the journal and ARU at the exit memory. *)
Theorem caw_scan_loop : forall j sx pad E ms mdc (Q : world tfibsegs -> config -> Prop),
  caw_static ->
  (j < length tb)%nat ->
  st_ok tfibsegs E (caw_ss1 1 255) (restrict (w_H W) ms) ->
  caw_atoms E j (length sx) pad ->
  WriterSpec.b64_scan 0 [] (firstn j tb) = Some (sx, pad) ->
  Forall (fun v => 0 <= v < 64) sx ->
  caw_memf (ms_mem ms) -> caw_six (ms_mem ms) sx ->
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  (forall ms' mdc', caw_post E (ms_mem ms) j sx pad ms' mdc' -> SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros j sx pad E ms mdc Q HST Hj HS HA Hscan Hsx HM H6 HJ HARU Hk.
exact (caw_loop_all HST (length tb - j) j eq_refl Hj sx pad E ms mdc Q HS HA Hscan Hsx HM H6 HJ HARU Hk).
Qed.
End scan.
