(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v; 402 of its 445 lines of code are new or changed and 971 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the piece "one turn of the
   inner scan" of the walk of LLVMFuzzerTestOneInput, lib/A/RPgSeg.v rs_piece_W11a_inner_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (I 0x821e0 .. 0x822a4, pod_next_pair's inner loop with pod_string inlined, pod.h:90-96 and :134-142)
     0x821e0 .. 0x821f0  add a0,a4,a6; the instrumented 1-byte check of &ent[m].type (slow block 0x8227c)
     0x821f4 .. 0x821fc  a0 := a5 + a4; lw t0,0(a0); bne t0,s10 (s10 = 8): not a String, to 0x82250
     0x82200 .. 0x82210  t0 := a4 + a2; the check of &ent[m].size (slow block 0x8228c)
     0x82214 .. 0x82218  lw a0,4(a0); beqz a0: size 0, to 0x82250
     0x8221c .. 0x8223c  a0 := a4 + a3 + zext32 (size - 1); the check of &ent[m].body[size - 1] (slow block 0x8229c)
     0x82240 .. 0x8224c  a0 := a7 + a4 (the body); lbu of body[size - 1]; beqz: a key, to 0x82254
     0x82250             mv a0,zero: not a key
     0x82254             beq s4,s5 (s4 = n_ent - 1, s5 = m): the last entry starts no pair, to ABS 0x82380
     0x82258 .. 0x82270  s5 := m + 1; addiw s9 := m + 2; the five bases a6, a7, a3, a2, a5 advance by 104
     0x82274             beqz a0: not a key, back to I 0x821e0 with m + 1
     0x82278             j 0x822a8: a key, to KM
   with a4 = 104 at0, a5 = a6 = &ent[0] + 104 (m - at0), a2 = that + 4, a3 = a7 = that + 8, so that a4 + a6 is
   &ent[m] (Layout.ent_mem: type at +0, size at +4, body at +8). No store and no call: the turn writes no byte and
   changes no float register.

   HOW. si_blk is the turn as a block lemma over the machine state at I (lib/Reusable: the token engine YCbn.v, the
   journal YCbq.v), stated for any float state. Its entry state has the registers as atoms and six more atoms: A =
   &ent[m] (32), the type t (33), the size z (34), D = (z - 1) mod 2^32 (35), P = A + 8 + max (z - 1, 0) (36) and
   the byte lb at P (37). Alias facts make every address the code computes an atom plus a constant: a4 + a6 and
   a5 + a4 are A, a4 + a2 is A + 4, a4 + a3 and a7 + a4 are A + 8, the zero extension of size - 1 is D, and (added
   once size <> 0 is known, when D = z - 1) A + D is P - 8. Two read-only regions hold the two words at A and the
   byte at P. The shadow base is s7 itself (atom 23, SHADOW_OFF), and the two shadow entries [A - 4, A + 108) and
   [P, P + 8) cover the 8 bytes from each check's address, so the engine reads each shadow byte as 0 and decides
   each `bnez` not taken (the entries are paid from the first block's shadow, RPgMem.rm_blk_ra). The engine splits
   the four branches it cannot decide (the type, the size, the last byte, m = n_ent - 1) and runs each arm to its
   end pc. The post is RPgScanOuter.ro_post (the journal, the memory and the 19 registers of ro_kept as at I).
   rk_inner_A reads I's cut, reads the three fields out of the first block's image (RPgMem.rm_pp_ent), runs si_blk
   at the run's own float state, and rebuilds the cut of the arm: ABS (the entry is the last one: the answer is
   (None, 0) by RPgScanF.rk_inv_last), I at m + 1 (the entry is not a key) or KM (the entry is a key: the three
   tests are Accessors.key_of's three conjuncts). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgMem RPgScanF.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgScanOuter.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table and the entry state ================================ *)
(* the 50 words 0x821e0 .. 0x822a4 (the three slow blocks included); the end pcs I 0x821e0 is its first word, KM
   0x822a8 and ABS 0x82380 lie outside it *)
Definition si_tbl : ctable := build_table rsegs RS_I 50 TEmpty.
Lemma si_tbl_ok : table_ok rsegs si_tbl.
Proof. apply build_table_ok0. unfold RS_I. lia. Qed.

(* the shadow base: register s7 (atom 23) holds SHADOW_OFF *)
Definition SISB : Z := 0x7fff8000.
Definition SIBx : sv := SOff 23 0.
Definition SIBspan : Z * Z := (SISB, SISB + 2 ^ 44 - 1).

(* the two read-only regions: the type and size words at A (atom 32), the byte at P (atom 36) *)
Definition si_R1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition si_R2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
(* the zero extension of size - 1, in the form the engine builds for 0x8221c .. 0x82224 *)
Definition si_zx : sv :=
  SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit (-4294967296))) (SLit 32).
Definition si_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 14 0) (SOff 16 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 15 0) (SOff 14 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 14 0) (SOff 12 0), SOff 32 4);
    (SAlu ALU_ADD (SOff 14 0) (SOff 13 0), SOff 32 8);
    (SAlu ALU_ADD (SOff 17 0) (SOff 14 0), SOff 32 8);
    (si_zx, SOff 35 0) ].
(* added once size <> 0 is known *)
Definition si_aP : sv := SAlu ALU_ADD (SOff 32 0) (SOff 35 0).
Definition si_aP' : sv := SOff 36 (-8).
Definition si_facts : facts :=
  mkFacts [ (23%nat, mkAF SISB SISB 0); (32%nat, mkAF 0x4014 (2 ^ 47 - 0x200) 0);
            (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 45 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
            (36%nat, mkAF 0x401c (2 ^ 47 - 0x100) 0); (37%nat, mkAF 0 255 0); (25%nat, mkAF 1 32 0) ]
          [] si_alias.
Definition si_ss0 : sstate := mkSS RS_I sr_atoms [si_R1; si_R2] None si_facts.
Definition si_SH : list shent := [mkSHE 32 (-4) 108; mkSHE 36 0 8].
(* the six atoms after the registers *)
Definition si_D (z : Z) : Z := (z - 1) mod 2 ^ 32.
Definition si_P (A z : Z) : Z := A + 8 + Z.of_nat (Z.to_nat (z - 1)).
Definition si_extra (A t z lb : Z) : list word :=
  [w64 A; w64 t; w64 z; w64 (si_D z); w64 (si_P A z); w64 lb].
(* the three tests of pod_string *)
Definition si_key (t z lb : Z) : bool := (t =? 8) && (1 <=? z) && (lb =? 0).

(* ================================ arithmetic ================================ *)
Lemma si_zx_U : forall E z, ew E 34 = Z_to_bv 64 z -> 0 <= z <= 45 -> U E si_zx = si_D z.
Proof.
intros E z H Hz. unfold si_zx, si_D.
rewrite !U_SAlu, !U_SLit, (U_atom E 34 z H) by lia. cbn [zalu_raw].
rewrite (zcanon_id 32) by (unfold M64; lia). change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (-4294967296 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32).
rewrite (Z.mod_small (z * 2 ^ 32)) by lia.
destruct (Z.eq_dec z 0) as [->|Hz0]; [reflexivity|].
replace (z * 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with ((z - 1) * 2 ^ 32 + 1 * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite (Z.mod_small ((z - 1) * 2 ^ 32)) by lia. rewrite Z.div_mul by lia.
rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. apply Z.mod_small. lia.
Qed.

Lemma si_sext_U : forall E t, ew E 33 = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
(U E (SExt true 32 (SOff 33 0)) =? 8) = (t =? 8).
Proof.
intros E t H Ht. rewrite U_SExt, (U_atom E 33 t H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small t) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
unfold zcanon, M64.
destruct (Z.ltb_spec t (2 ^ 31)) as [Hl|Hg].
- rewrite (Z.mod_small (t + 2 ^ 31)) by lia. replace (t + 2 ^ 31 - 2 ^ 31) with t by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (t + 2 ^ 31) with ((t + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (t + 2 ^ 31 - 2 ^ 32)) by lia.
  replace (t + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((t + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (t + 2 ^ 64 - 2 ^ 32) 8); [lia|]. destruct (Z.eqb_spec t 8); [lia | reflexivity].
Qed.

Lemma si_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.

(* ================================ the entry's bytes ================================ *)
Lemma si_firstn4 : forall (a b : list byte), length a = 4%nat -> firstn 4 (a ++ b) = a.
Proof. intros a b H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. Qed.
Lemma si_slice_type : forall e, rm_slice (ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof. intros e. unfold rm_slice, ent_mem. cbn [skipn]. apply si_firstn4. apply length_le32. Qed.
Lemma si_slice_size : forall e, rm_slice (ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold rm_slice, ent_mem. rewrite skipn_app, length_le32, Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite length_le32; lia). cbn [app]. apply si_firstn4. apply length_le32.
Qed.
Lemma si_nth_zeros : forall (l : list byte) n k, nth k (l ++ zeros n) NUL = nth k l NUL.
Proof.
intros l n k. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- apply app_nth1. exact Hk.
- rewrite app_nth2 by exact Hk. rewrite (nth_overflow l) by exact Hk. unfold zeros. apply nth_repeat.
Qed.
Lemma si_nth_body : forall e k, nth (8 + k) (ent_mem e) (Z_to_bv 8 0) = nth k (e_body e) NUL.
Proof.
intros e k. change (Z_to_bv 8 0) with NUL. unfold ent_mem.
rewrite app_nth2 by (rewrite length_le32; lia). rewrite length_le32.
rewrite app_nth2 by (rewrite length_le32; lia). rewrite length_le32.
replace (8 + k - 4 - 4)%nat with k by lia. apply si_nth_zeros.
Qed.

(* membership in the kept registers, and the post's register facts *)
Ltac si_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
Ltac si_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio.
(* the memory after a run over the read-only regions is the memory at I *)
Ltac si_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac si_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok si_tbl_ok HS HJ SHOK SIBspan; [awr_ok_tac | ] end.
Ltac si_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok si_tbl_ok HS HJ SHOK SIBspan pc; [awr_ok_tac | ] end.
Ltac si_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok si_tbl_ok HS SHOK SIBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* what the back edge computes *)
Definition si_I_R (regs : bvmap 5 word) (A x j : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 14) = getr regs (Z_to_bv 5 14) /\
getr regs2 (Z_to_bv 5 21) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 25) = w64 (j + 2) /\
getr regs2 (Z_to_bv 5 16) = w64 (A - x + 104) /\ getr regs2 (Z_to_bv 5 15) = w64 (A - x + 104) /\
getr regs2 (Z_to_bv 5 12) = w64 (A + 4 - x + 104) /\ getr regs2 (Z_to_bv 5 13) = w64 (A + 8 - x + 104) /\
getr regs2 (Z_to_bv 5 17) = w64 (A + 8 - x + 104).
(* what the exit to KM computes *)
Definition si_KM_R (A j : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 (A + 8) /\ getr regs2 (Z_to_bv 5 21) = w64 (j + 1) /\
getr regs2 (Z_to_bv 5 25) = w64 (j + 2).

(* the leaves of the run tree (used inside si_blk only: they name its hypotheses) *)
(* a register the arm advanced: SOff n c over the atom n, whose value En gives *)
Ltac si_adv :=
si_sv;
lazymatch goal with |- sv_denot _ (SOff ?n ?c) = w64 ?v =>
  lazymatch goal with En : ew _ n = Z_to_bv 64 ?v0 |- _ =>
    rewrite (si_soff _ n v0 c En) by lia; unfold w64; f_equal; lia end end.
Ltac si_kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 ro_kept HS HAE
    ltac:(vm_compute; reflexivity) r Hr) end.
Ltac si_post_intro :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (ro_post_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | si_io | si_kept | ] end.
(* the `beq s4,s5` at 0x82254, then the arm's end *)
Ltac si_abs Hl :=
si_run_to RS_ABS; si_mem; apply SRr_ret; left;
split; [apply Z.eqb_eq in Hl; exact Hl|];
si_post_intro; exact I.
Ltac si_Ileaf Hk Hl :=
si_run_to RS_I; si_mem; apply SRr_ret; right; left;
split; [apply Z.eqb_neq in Hl; exact Hl|];
split; [exact Hk|];
si_post_intro;
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  unfold si_I_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end;
split; [si_sv; rewrite ro_denot0; lazymatch goal with E14 : ew _ 14 = _, H14 : getr _ (Z_to_bv 5 14) = _ |- _ =>
  rewrite E14, H14; reflexivity end|];
repeat split; si_adv.
Ltac si_KMleaf Hk Hl :=
si_run_to RS_KM; si_mem; apply SRr_ret; right; right;
split; [apply Z.eqb_neq in Hl; exact Hl|];
split; [exact Hk|];
si_post_intro;
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  unfold si_KM_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end;
repeat split; si_adv.
Ltac si_last Hl :=
si_branch Hl;
lazymatch goal with E20 : ew ?E 20 = Z_to_bv 64 ?n, E21 : ew ?E 21 = Z_to_bv 64 ?j |- _ =>
  rewrite branch_eq_U, (U_atom E 20 n E20), (U_atom E 21 j E21) in Hl by lia end.
(* an entry that is not a key: 0x82250 a0 := 0, then the `beq` *)
Ltac si_nk Hk := si_run; si_mem; let Hl := fresh "Hl" in si_last Hl; [si_abs Hl | si_Ileaf Hk Hl].

Lemma si_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(x A t z lb j nm1 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 14) = w64 x ->
getr regs (Z_to_bv 5 16) = w64 (A - x) -> getr regs (Z_to_bv 5 15) = w64 (A - x) ->
getr regs (Z_to_bv 5 12) = w64 (A + 4 - x) ->
getr regs (Z_to_bv 5 13) = w64 (A + 8 - x) -> getr regs (Z_to_bv 5 17) = w64 (A + 8 - x) ->
getr regs (Z_to_bv 5 21) = w64 j -> getr regs (Z_to_bv 5 25) = w64 (j + 1) ->
getr regs (Z_to_bv 5 20) = w64 nm1 -> getr regs (Z_to_bv 5 26) = w64 8 ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
0 <= x <= A -> 0x4014 <= A <= 2 ^ 47 - 0x200 -> 0 <= t < 2 ^ 32 -> 0 <= z <= 45 -> 0 <= lb < 256 ->
0 <= j <= 31 -> 0 <= nm1 <= 31 ->
val_mem rsegs (mrestrict (w_H W) memc) A 4 t ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 z ->
val_mem rsegs (mrestrict (w_H W) memc) (si_P A z) 1 lb ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A - 4) 112 ->
(forall a, A - 4 <= a < A + 108 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs RS_I regs memc mdc)
(fun W2 c2 =>
 (nm1 = j /\ ro_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_ABS (fun _ => True) W2 c2) \/
 (nm1 <> j /\ si_key t z lb = false /\
  ro_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_I (si_I_R regs A x j) W2 c2) \/
 (nm1 <> j /\ si_key t z lb = true /\
  ro_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs RS_KM (si_KM_R A j) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x A t z lb j nm1 HJ
  H14 H16 H15 H12 H13 H17 H21 H25 H20 H26 H23 Hx HA Ht Hz Hlb Hj Hn Vt Vz Vb HRA Happ.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (si_extra A t z lb) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E14 : ew (Ereg regs ex) 14 = Z_to_bv 64 x) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 (A - x)) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 (A - x)) by (rewrite (EA 15%nat (Z_to_bv 5 15) eq_refl); exact H15).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 (A + 4 - x)) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 (A + 8 - x)) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 (A + 8 - x)) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E21 : ew (Ereg regs ex) 21 = Z_to_bv 64 j) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E25 : ew (Ereg regs ex) 25 = Z_to_bv 64 (j + 1)) by (rewrite (EA 25%nat (Z_to_bv 5 25) eq_refl); exact H25).
assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 nm1) by (rewrite (EA 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (E26 : ew (Ereg regs ex) 26 = Z_to_bv 64 8) by (rewrite (EA 26%nat (Z_to_bv 5 26) eq_refl); exact H26).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 A) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 t) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 z) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 (si_D z)) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 (si_P A z)) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 lb) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HD : 0 <= si_D z < 2 ^ 32) by (unfold si_D; apply Z.mod_pos_bound; lia).
assert (HP : A + 8 <= si_P A z <= A + 52) by (unfold si_P; lia).
assert (HS : st_ok rsegs (Ereg regs ex) si_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 RS_I) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold si_ss0. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold si_R1, si_R2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ A 0 4 (SOff 33 0) t); [rewrite ro_denot0; exact E33 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vt.
      * apply (chunk_ok_val rsegs _ _ A 4 4 (SOff 34 0) z); [rewrite ro_denot0; exact E34 | cbn; lia | cbn; lia |].
        exact Vz.
    + rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (si_P A z) 0 1 (SOff 37 0) lb); [rewrite ro_denot0; exact E37 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, si_R1, si_R2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E32, E36, !unsigned_lit_small by lia. left. lia.
  - split; [|split; [exact I|]].
    + cbn [si_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E32, E33, E34, E35, E36, E37, E25, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SISB, SHADOW_OFF. repeat split; lia.
    + cbn [si_facts f_alias alias_ok si_alias]. unfold si_zx.
      repeat split; apply U_inj.
      * rewrite U_SAlu, (U_atom _ 14 x E14), (U_atom _ 16 (A - x) E16), (U_atom _ 32 A E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 14 x E14), (U_atom _ 15 (A - x) E15), (U_atom _ 32 A E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 14 x E14), (U_atom _ 12 (A + 4 - x) E12), (U_atom_off _ 32 A 4 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 14 x E14), (U_atom _ 13 (A + 8 - x) E13), (U_atom_off _ 32 A 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 14 x E14), (U_atom _ 17 (A + 8 - x) E17), (U_atom_off _ 32 A 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * fold si_zx. rewrite (si_zx_U _ z E34 Hz), (U_atom _ 35 (si_D z) E35) by lia. reflexivity. }
assert (U23 : U (Ereg regs ex) SIBx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs SIBx si_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, si_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H W) memc _ SIBx 32 (A - 4) 112 A (-4) 108 HRA U23); [| lia | lia |].
    + apply U_atom; [exact E32 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia.
  - apply (shent_ok_of_range rsegs (w_H W) memc _ SIBx 36 (A - 4) 112 (si_P A z) 0 8 HRA U23); [| lia | lia |].
    + apply U_atom; [exact E36 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 RS_I) with (Z_to_bv 64 RS_I).
(* 0x821e0 .. 0x821f8: the type's check and load; stop at 0x821fc bne t0,s10 *)
si_run. si_mem.
si_branch Hty; rewrite branch_ne_U, (U_atom E 26 8 E26), (si_sext_U E t E33 Ht) in Hty by lia.
- (* taken: not a String *)
  apply negb_true_iff in Hty.
  assert (Hk : si_key t z lb = false) by (unfold si_key; rewrite Hty; reflexivity).
  si_nk Hk.
- (* the type is 8: 0x82200 .. 0x82214, the size's check and load; stop at 0x82218 beqz a0 *)
  apply negb_false_iff in Hty.
  si_run. si_mem.
  si_branch Hsz; rewrite branch_eq_U, (U_atom E 34 z E34), (U_lit E 0) in Hsz by lia.
  + (* size 0: not a key *)
    assert (Hk : si_key t z lb = false).
    { unfold si_key. replace (1 <=? z) with false by (symmetry; apply Z.leb_gt; apply Z.eqb_eq in Hsz; lia).
      rewrite andb_false_r. reflexivity. }
    si_nk Hk.
  + (* size >= 1: A + D is P - 8; 0x8221c .. 0x82248, the last byte's check and load; stop at 0x8224c beqz t0 *)
    apply Z.eqb_neq in Hsz.
    assert (HaP : sv_denot E si_aP = sv_denot E si_aP').
    { apply U_inj. unfold si_aP, si_aP'.
      rewrite U_SAlu, (U_atom E 32 A E32), (U_atom E 35 (si_D z) E35), (U_atom_off E 36 (si_P A z) (-8) E36) by lia.
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia).
      unfold si_D, si_P. rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ si_aP si_aP' HS HaP) as HS'. clear HS. rename HS' into HS.
    si_run. si_mem.
    si_branch Hb; rewrite branch_eq_U, (U_atom E 37 lb E37), (U_lit E 0) in Hb by lia.
    * (* the byte is NUL: a key; 0x82254 beq s4,s5 *)
      assert (Hk : si_key t z lb = true).
      { unfold si_key. rewrite Hty, Hb. replace (1 <=? z) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      si_run. si_mem.
      let Hl := fresh "Hl" in si_last Hl; [si_abs Hl | si_KMleaf Hk Hl].
    * (* not a key *)
      assert (Hk : si_key t z lb = false) by (unfold si_key; rewrite Hb, andb_false_r; reflexivity).
      si_nk Hk.
Qed.

End d.
End b.

(* ================================ the cuts ================================ *)
Lemma si_key_of : forall e, key_of e = if si_key (e_type e) (e_size e) (last_body_byte e) then Some (cstr (e_body e)) else None.
Proof. intros e. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem rk_inner_A : rs_piece_W11a_inner_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_inner_stmt. intros cx POST inp at0 m Hst HI HKM HA.
unfold rs_from_I. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec Hcut.
pose proof Hcut as (Hbase & Hat & Hrole & Hinv & Hrec & [Hat0 Hm] & Hrun).
pose proof Hbase as (Hcore & _ & _ & _ & Hpp & Hwf & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof Hst as (Hpre & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
(* the first block at the cut: its place and its shadow *)
pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hin2.
pose proof HJ as (HAR & _).
pose proof (al_blocks rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hin2) as (_ & Hp4k & Hpc & Happ & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hpc, Happ.
pose proof (@ASAN_CEIL_range rc) as [[_ Hceil] _]. unfold ASAN_CEIL in Hceil.
unfold Layout.PP_SIZE in Hpc.
(* entry m of the record *)
pose proof (rk_nent_le rec Hwf) as Hn32.
pose proof (rk_ent_wf_nth rec m Hwf Hm) as (Htw & Hbl & Hzw).
unfold rk_d in Htw, Hbl, Hzw.
assert (Hb : Z.of_nat (length (buf rec)) <= POD_BUF_MAX)
  by (pose proof (buf_header rec Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents rec)).
{ eapply Forall_impl; [|exact (rk_ents_wf rec Hwf)]. intros e (_ & He & Hz). lia. }
pose proof (rm_pp_ent rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp (x_e cx)) m Hpp Hm) as Hent.
pose proof (length_ent_mem (nth m (ents rec) (Ent 0 0 [])) ltac:(lia)) as HL104.
pose proof (rm_bytes_field rsegs _ _ _ _ 0 4 _ Hent (si_slice_type _) ltac:(lia)) as Vt.
pose proof (rm_bytes_field rsegs _ _ _ _ 4 4 _ Hent (si_slice_size _) ltac:(lia)) as Vz.
pose proof (rm_bytes_byte rsegs _ _ _ _ (8 + Z.to_nat (e_size (nth m (ents rec) (Ent 0 0 [])) - 1)) Hent
  ltac:(lia)) as Vb.
rewrite si_nth_body in Vb.
set (A := e_pp (x_e cx) + 0x4014 + 104 * Z.of_nat m).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 0) with A in Vt
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 4) with (A + 4) in Vz
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + Z.to_nat (e_size (nth m (ents rec) (Ent 0 0 [])) - 1)))
  with (si_P A (e_size (nth m (ents rec) (Ent 0 0 [])))) in Vb by (unfold A, si_P, OFF_ENT, ENT_SIZE; lia).
assert (HRA : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (A - 4) 112).
{ apply (rm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp (x_e cx)) Layout.PP_SIZE (A - 4) 112 HAR Hin2);
  [| rewrite Hrq]; unfold A, Layout.PP_SIZE; lia. }
(* the registers at I *)
unfold rs_at_cx in Hat.
pose proof (ro_at_get _ _ _ _ _ 14 (104 * Z.of_nat at0) Hat ltac:(ro_in)) as R14.
pose proof (ro_at_get _ _ _ _ _ 16 (e_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(ro_in)) as R16.
pose proof (ro_at_get _ _ _ _ _ 15 (e_pp (x_e cx) + 0x4014 + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(ro_in)) as R15.
pose proof (ro_at_get _ _ _ _ _ 12 (e_pp (x_e cx) + 0x4018 + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(ro_in)) as R12.
pose proof (ro_at_get _ _ _ _ _ 13 (e_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(ro_in)) as R13.
pose proof (ro_at_get _ _ _ _ _ 17 (e_pp (x_e cx) + 0x401c + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(ro_in)) as R17.
pose proof (ro_at_get _ _ _ _ _ 21 (Z.of_nat m) Hat ltac:(ro_in)) as R21.
pose proof (ro_at_get _ _ _ _ _ 25 (Z.of_nat m + 1) Hat ltac:(ro_in)) as R25.
pose proof (ro_at_get _ _ _ _ _ 20 (Z.of_nat (length (ents rec)) - 1) Hat ltac:(ro_in)) as R20.
pose proof (ro_at_get _ _ _ _ _ 26 8 Hat ltac:(ro_in)) as R26.
pose proof (ro_at_get _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(ro_in)) as R23.
unfold rs_at in Hat. apply Forall_app in Hat as [Hscan _].
fold (rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (rs_L_scan rsegs cx rec)) in Hscan.
(* the turn *)
eapply SRr_bind.
{ apply (si_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (104 * Z.of_nat at0) A
    (e_type (nth m (ents rec) (Ent 0 0 []))) (e_size (nth m (ents rec) (Ent 0 0 [])))
    (last_body_byte (nth m (ents rec) (Ent 0 0 []))) (Z.of_nat m) (Z.of_nat (length (ents rec)) - 1) HJ R14);
  try (rewrite ?R16, ?R15, ?R12, ?R13, ?R17; unfold w64, A; f_equal; lia);
  try assumption; try (unfold A; lia).
  - apply rm_byte_range.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, Layout.PP_SIZE, A in *. lia. }
intros W3 c3 _ [(Hl & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
  | [(Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR) | (Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR)]].
- (* ABS: entry m is the last one, the answer is (None, 0) *)
  assert (Hlen : (length (ents rec) <= S m)%nat) by lia.
  assert (HE0 : rs_E0 rec = (None, 0)) by exact (rk_inv_last rec at0 m Hinv Hat0 Hm Hlen Hrun).
  pose proof Hrec as (_ & _ & _ & Hsnd & Hfst).
  rewrite HE0 in Hsnd, Hfst. cbn [fst snd] in Hsnd, Hfst.
  pose proof (ro_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk3 ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HA fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (ro_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3 Hk3)|].
  split.
  { unfold rs_at_cx. unfold rs_L_scan in Hscan3. rewrite Hsnd in Hscan3.
    apply (ro_at_sub _ _ _ _ _ _ Hscan3). intros y Hy. unfold rs_L_chk in Hy |- *. cbn [In app] in Hy |- *.
    repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy. }
  split; [exact Hrole|]. split; assumption.
- (* I at m + 1: entry m is not a key *)
  destruct HR as (Q14 & Q21 & Q25 & Q16 & Q15 & Q12 & Q13 & Q17).
  assert (Hk : key_of (nth m (ents rec) (Ent 0 0 [])) = None) by (rewrite si_key_of, Hkey; reflexivity).
  pose proof (ro_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk3 ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HI fx2 ly2 S2 W2 regs3 mem2 md3 rec).
  split; [exact (ro_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3 Hk3)|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
    - rewrite Q14. exact R14.
    - rewrite Q21. unfold w64. f_equal. lia.
    - rewrite Q25. unfold w64. f_equal. lia.
    - rewrite Q16. unfold w64, A. f_equal. lia.
    - rewrite Q15. unfold w64, A. f_equal. lia.
    - rewrite Q12. unfold w64, A. f_equal. lia.
    - rewrite Q13. unfold w64, A. f_equal. lia.
    - rewrite Q17. unfold w64, A. f_equal. lia. }
  split; [exact Hrole|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|].
  intros q Hq. destruct (Nat.eq_dec q m) as [->|Hqm]; [exact Hk | apply Hrun; lia].
- (* KM: entry m is a key, entry m + 1 its value *)
  destruct HR as (Q10 & Q21 & Q25).
  assert (Hk : key_of (nth m (ents rec) (Ent 0 0 [])) = Some (cstr (e_body (nth m (ents rec) (Ent 0 0 [])))))
    by (rewrite si_key_of, Hkey; reflexivity).
  pose proof (ro_at_keep _ _ regs2 regs3 _ (rs_L_scan rsegs cx rec) ro_kept Hk3 ltac:(vm_compute; reflexivity) Hscan) as Hscan3.
  apply (HKM fx2 ly2 S2 W2 regs3 mem2 md3 rec (cstr (e_body (nth m (ents rec) (Ent 0 0 []))))).
  split; [exact (ro_chk_base B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hbase HJ3 Hio3 Hk3)|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact Hscan3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd].
    - rewrite Q10. unfold w64, A. f_equal. lia.
    - exact Q21.
    - rewrite Q25; unfold w64; f_equal; lia. }
  split; [exact Hrole|]. split; [exact Hinv|]. split; [exact Hrec|].
  split; [lia|]. split; [lia|]. split; [exact Hrun | exact Hk].
Qed.
End c.

Print Assumptions rk_inner_A.
