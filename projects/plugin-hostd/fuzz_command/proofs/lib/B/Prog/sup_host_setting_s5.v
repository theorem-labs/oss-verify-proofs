(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the steps of a program walk through a runtime entry whose contract is art_post (lib/A/Rt/RtDefs.v) and whose writes leave the errno cell, after PaArt.v's aj_art_at and cgif_file_fuzzer's aj_intrin_atS: aj_art_own_at, for an entry that writes bytes the caller's journal may write (its side-stack frame, its footprint, a block made in the call), is the sup_resp walk's lemma (an earlier version of lib/A/Prog/sup_resp_s0.v); aj_art_blk_at, for an entry that writes inside one live heap block, and awrite_ok_of_block, the entry's write premise on a range of such a block, are the sup_host_setting walk's lemmas hs5_art_wr_at and hs6_wr_block (lib/A/Prog/sup_host_setting_s5.v and sup_host_setting_s6.v), stated over any segments and symbols. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaArtOwn.v, with its module paths and module names changed; 1176 of its 1235 lines of code are new or changed and 72 lines of the source are left out. *)
(* Three segment lemmas of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan),
   on the points and statements of sup_host_setting_s0.v; the B twin of the ASan walk's lib/A/Prog/sup_host_setting_s5.v
   (a working branch e323bbe76d2):
   - hs_seg_l1h: from L1H n (0x8b6bc) the three UBSan checks of &tok[n] (0x8b6bc `bltu s6,s8`, 0x8b6c8 `beqz a0`,
     0x8b6cc `beqz s7`, all to the `unimp` 0x8b8c0), the load8 shadow check of &tok[n] (report edge 0x8b6dc), a0 :=
     tok[n] and the call of the strlen wrapper (0x4517c, at 0x8b6e4), back at L1R n (0x8b6e8);
   - hs_seg_l1r: from L1R n the loop's increments and the back edge 0x8b6fc to L1H (S n), and on the exit the call of
     xmalloc(len + 1) (0x899b4, at 0x8b704) through cl_callS and xmalloc_c, back at XM (0x8b708);
   - hs_seg_xm: from XM the store1 shadow check of words[0] (0x8b718 / 0x8b8c8), words[0] := 0, the join loop's entry
     (0x8b738 `beqz s11` taken), the UBSan check 0x8b774 `bltu s5,s7`, the load8 shadow check of tok[0] (0x8b788) and the
     call of the strcat wrapper (0x45220, at 0x8b794), back at L2C 0 (0x8b798).
   Every call is made at the realigned sp1 = hs_sp1 sp0 (offset hs_sp1 sp0 - sp0, -160 or -176, hs3_sp1). The shared
   helpers of the walk are sup_host_setting_s3.v's hs3_*. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_s0 sup_host_setting_s1 sup_host_setting_aux sup_host_setting_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic seeds (the runs measured by vm_compute on the listing, 2026-10-29) ---- *)
Definition hsb5_Bx : sv := SOff 26 0.
Definition hsb5_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
Definition hsb5_PTRF : afact := mkAF 4096 0x7fffff800000 3.
Definition hsb5_SBF : afact := mkAF HS_SB HS_SB 0.
(* L1H 0x8b6bc: s2 = s7 = 1 (hs_regsL1), s3 = s6 = &tok[n] (atom 22, at or above 4096, 8-aligned), the word at
   &tok[n] the token pointer (atom 32). The run stops at 0x8b6bc `bltu s6,s8` (two atoms); with its fall-through
   condition it decides 0x8b6c8 (seqz of atom 22 is 0 by its fact, 1 xor 0 = 1) and 0x8b6cc (s7 = 1), the token
   executor decides the load8 check, and it stops at the call of the strlen wrapper. *)
Definition hsb5_fH : facts := mkFacts [(22%nat, hsb5_PTRF); (26%nat, hsb5_SBF)] [] [].
Definition hsb5_ssH : sstate := mkSS HS_L1H (sr_set (sr_set (sr_set sr_atoms 18 (SLit 1)) 23 (SLit 1)) 19 (SOff 22 0))
  [YP09.mkRegion (Some 22%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None hsb5_fH.
Definition hsb5_SHH : list shent := [mkSHE 22 0 8].
(* L1R 0x8b6e8: the loop's tail, no memory touched; it stops at the back edge 0x8b6fc `bnez s11` *)
Definition hsb5_ssR : sstate := mkSS HS_L1R sr_atoms [] None (mkFacts [] [] []).
(* XM 0x8b708: a0 = the word list (atom 10, 16-aligned), s5 = ntok (atom 21), s8 = tok (atom 24), the word at tok
   the token pointer (atom 32). The run stops at 0x8b774 `bltu s5,s7` (not tok against 0); with its fall-through
   condition it stops at the call of the strcat wrapper. *)
Definition hsb5_fM : facts := mkFacts [(10%nat, mkAF 4096 0x7fffff800000 4); (21%nat, mkAF 1 64 0);
  (24%nat, hsb5_PTRF); (26%nat, hsb5_SBF)] [] [].
Definition hsb5_ssM : sstate := mkSS HS_XM sr_atoms
  [YP09.mkRegion (Some 10%nat) 0 1 0 1 []; YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]]
  None hsb5_fM.
Definition hsb5_SHM : list shent := [mkSHE 10 0 1; mkSHE 24 0 8].

(* ---- arithmetic and list facts (A_hs_s5.v's hs5_words lemmas) ---- *)
Lemma hsb5_words_nil : hs_words_len [] = 0.
Proof. reflexivity. Qed.
Lemma hsb5_words_cons : forall w l, hs_words_len (w :: l) = Z.of_nat (length w) + 1 + hs_words_len l.
Proof. reflexivity. Qed.
Lemma hsb5_words_app : forall l1 l2, hs_words_len (l1 ++ l2) = hs_words_len l1 + hs_words_len l2.
Proof.
induction l1 as [|w l1 IH]; intros l2; [rewrite hsb5_words_nil; reflexivity|].
cbn [app]. rewrite !hsb5_words_cons, IH. lia.
Qed.
Lemma hsb5_firstn_S : forall n (l : list (list byte)), (n < length l)%nat ->
firstn (S n) l = firstn n l ++ [nth n l []].
Proof.
induction n as [|n IH]; intros [|w l] Hn; cbn [length] in Hn; try lia.
- reflexivity.
- cbn [firstn nth app]. rewrite (IH l ltac:(cbn in Hn; lia)). reflexivity.
Qed.
Lemma hsb5_words_firstn_S : forall n (l : list (list byte)), (n < length l)%nat ->
hs_words_len (firstn (S n) l) = hs_words_len (firstn n l) + Z.of_nat (length (nth n l [])) + 1.
Proof.
intros n l Hn. rewrite (hsb5_firstn_S n l Hn), hsb5_words_app, hsb5_words_cons, hsb5_words_nil. lia.
Qed.
Lemma hsb5_words_firstn_le : forall n (l : list (list byte)), hs_words_len (firstn n l) <= hs_words_len l.
Proof.
intros n l. pose proof (hsb5_words_app (firstn n l) (skipn n l)) as E. rewrite (firstn_skipn n l) in E.
pose proof (hs3_wl_nonneg (skipn n l)). lia.
Qed.
Lemma hsb5_words_tok_le : forall n (l : list (list byte)), (n < length l)%nat ->
Z.of_nat (length (nth n l [])) + 1 <= hs_words_len l.
Proof.
intros n l Hn. pose proof (hsb5_words_firstn_S n l Hn) as E.
pose proof (hsb5_words_firstn_le (S n) l). pose proof (hs3_wl_nonneg (firstn n l)). lia.
Qed.
Lemma hsb5_join_one : forall (l : list (list byte)), (0 < length l)%nat -> join_sp (firstn 1 l) = nth 0 l [].
Proof. intros [|w l] H; [cbn in H; lia | reflexivity]. Qed.
Lemma hsb5_forall2_nth : forall {A C} (R : A -> C -> Prop) l1 l2 i a c,
Forall2 R l1 l2 -> nth_error l1 i = Some a -> nth_error l2 i = Some c -> R a c.
Proof.
intros A C R l1 l2 i. revert l1 l2.
induction i as [|i IH]; intros [|u l1] [|v l2] a c HF H1 H2; cbn in H1, H2; try discriminate;
  inversion HF as [|u' v' l1' l2' Huv HF' E1 E2]; subst.
- injection H1 as <-. injection H2 as <-. exact Huv.
- exact (IH l1 l2 a c HF' H1 H2).
Qed.

(* 0x8b72c `not s5,s8` (`xori s5,s8,-1`): s5 = 2^64 - 1 - tok *)
Lemma hsb5_not : forall t, 0 <= t < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 t) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - t).
Proof.
intros t Ht. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small t) by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite hsb_lxor_ones by lia. rewrite (unsigned_lit_small (2 ^ 64 - 1 - t)) by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* the n-wide field read over aview is the executor's val_mem (B_socket_send.v's aval_mem_view / val_mem_view) *)
Lemma hsb5_aval_mem_view : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma hsb5_val_mem_view : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate]. cbn [option_map] in Hb.
injection Hb as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. rewrite Hb. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition hsb5_E (regs1 : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs1 extra).

Lemma hsb5_E_img : forall regs1 extra, img_env VAL A_LIM (hsb5_E regs1 extra).
Proof. intros regs1 extra. unfold hsb5_E. apply Eimg_env. Qed.
Lemma hsb5_E_reg : forall regs1 extra k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (hsb5_E regs1 extra) k = getr regs1 r.
Proof. intros regs1 extra k r Hk. unfold hsb5_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma hsb5_E_x32 : forall regs1 v l, ew (hsb5_E regs1 (v :: l)) 32 = v.
Proof.
intros regs1 v l. unfold hsb5_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs1 (v :: l) 0).
Qed.
Lemma hsb5_U_off0 : forall E m v, bv_unsigned (ew E m) = v -> 0 <= v < M64 -> U E (SOff m 0) = v.
Proof. intros E m v Hm Hv. rewrite U_SOff, Hm, Z.add_0_r. apply zcanon_id. exact Hv. Qed.
Lemma hsb5_U_add2 : forall E m1 z1 m2 z2 v1 v2,
bv_unsigned (ew E m1) = v1 -> bv_unsigned (ew E m2) = v2 ->
0 <= v1 + z1 < M64 -> 0 <= v2 + z2 < M64 -> 0 <= v1 + z1 + (v2 + z2) < M64 ->
U E (SAlu ALU_ADD (SOff m1 z1) (SOff m2 z2)) = v1 + z1 + (v2 + z2).
Proof.
intros E m1 z1 m2 z2 v1 v2 H1 H2 R1 R2 R3. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, H1, H2, (zcanon_id (v1 + z1)) by lia. rewrite (zcanon_id (v2 + z2)) by lia.
apply zcanon_id. lia.
Qed.

(* ---- the entry state of the run at L1H ---- *)
Lemma hsb5_seed_H : forall (W : world SEGS) (regs1 : bvmap 5 word) mem q p,
getr regs1 26 = w64 HS_SB -> getr regs1 22 = w64 q -> getr regs1 19 = w64 q ->
getr regs1 18 = w64 1 -> getr regs1 23 = w64 1 ->
4096 <= q -> q + 8 <= 0x7fffff800000 -> q mod 8 = 0 -> 0 <= p < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
st_ok_pi SEGS VAL (hsb5_E regs1 [Z_to_bv 64 p]) hsb5_ssH
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_L1H)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem q p H26 H22 H19 H18 H23 Hq1 Hq2 Hq8 Hp Hv.
rewrite restrict_mkst_fx. unfold hsb5_ssH.
set (E := hsb5_E regs1 [Z_to_bv 64 p]).
assert (E26 : ew E 26 = w64 HS_SB) by (unfold E; rewrite (hsb5_E_reg regs1 _ 26%nat 26%bv eq_refl); exact H26).
assert (E22 : ew E 22 = w64 q) by (unfold E; rewrite (hsb5_E_reg regs1 _ 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (unfold E; exact (hsb5_E_x32 regs1 _ [])).
assert (U26 : bv_unsigned (ew E 26) = HS_SB) by (rewrite E26; apply unsigned_lit_small; unfold HS_SB; lia).
assert (U22 : bv_unsigned (ew E 22) = q) by (rewrite E22; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- apply YI04.regs_ok_pin; [apply YI04.regs_ok_pin; [apply YI04.regs_ok_pin; [unfold E, hsb5_E; apply regs_ok_Eimg_Ereg | |] | |] | |].
  + intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  + rewrite H18. reflexivity.
  + intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  + rewrite H23. reflexivity.
  + intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  + rewrite H19, denot_lit_U, (hsb5_U_off0 E 22%nat q U22 ltac:(unfold M64; lia)). reflexivity.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [hsb5_fH f_atoms atoms_ok]. unfold afact_ok, hsb5_PTRF, hsb5_SBF. cbn [af_lo af_hi af_al2].
  rewrite U26, U22.
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I
          | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
          | (change (2 ^ 3) with 8; exact Hq8)
          | (unfold HS_SB; lia) ].
Qed.

(* ---- the entry state of the run at L1R ---- *)
Lemma hsb5_seed_R : forall (W : world SEGS) (regs1 : bvmap 5 word) mem,
st_ok_pi SEGS VAL (hsb5_E regs1 []) hsb5_ssR
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_L1R)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem. rewrite restrict_mkst_fx. unfold hsb5_ssR.
apply pa_entry_st_ok_full.
- unfold hsb5_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

(* ---- the entry state of the run at XM ---- *)
Lemma hsb5_seed_M : forall (W : world SEGS) (regs1 : bvmap 5 word) mem w ntok q p,
getr regs1 26 = w64 HS_SB -> getr regs1 21 = w64 ntok -> getr regs1 10 = w64 w -> getr regs1 24 = w64 q ->
1 <= ntok <= 64 -> 4096 <= w -> w + 1 <= 0x7fffff800000 -> w mod 16 = 0 ->
4096 <= q -> q + 8 <= 0x7fffff800000 -> q mod 8 = 0 -> 0 <= p < 2 ^ 64 ->
(w + 1 <= q \/ q + 8 <= w) ->
(forall o, 0 <= o < 1 -> YP09.writable_at SEGS (mrestrict (w_H W) mem) (w + o)) ->
val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
st_ok_pi SEGS VAL (hsb5_E regs1 [Z_to_bv 64 p]) hsb5_ssM
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_XM)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem w ntok q p H26 H21 H10 H24 Hnt Hw1 Hw2 Hw16 Hq1 Hq2 Hq8 Hp Hdisj Hwr Hv.
rewrite restrict_mkst_fx. unfold hsb5_ssM.
set (E := hsb5_E regs1 [Z_to_bv 64 p]).
assert (E26 : ew E 26 = w64 HS_SB) by (unfold E; rewrite (hsb5_E_reg regs1 _ 26%nat 26%bv eq_refl); exact H26).
assert (E21 : ew E 21 = w64 ntok) by (unfold E; rewrite (hsb5_E_reg regs1 _ 21%nat 21%bv eq_refl); exact H21).
assert (E10 : ew E 10 = w64 w) by (unfold E; rewrite (hsb5_E_reg regs1 _ 10%nat 10%bv eq_refl); exact H10).
assert (E24 : ew E 24 = w64 q) by (unfold E; rewrite (hsb5_E_reg regs1 _ 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (unfold E; exact (hsb5_E_x32 regs1 _ [])).
assert (U26 : bv_unsigned (ew E 26) = HS_SB) by (rewrite E26; apply unsigned_lit_small; unfold HS_SB; lia).
assert (U21 : bv_unsigned (ew E 21) = ntok) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = w) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = q) by (rewrite E24; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- unfold E, hsb5_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U10. split; [lia|]. split; [lia|]. split; [exact Hwr | apply Forall_nil].
  + rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U24.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [hsb5_fM f_atoms atoms_ok]. unfold afact_ok, hsb5_PTRF, hsb5_SBF. cbn [af_lo af_hi af_al2].
  rewrite U26, U21, U10, U24.
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I
          | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
          | (change (2 ^ 3) with 8; exact Hq8)
          | (change (2 ^ 4) with 16; exact Hw16)
          | (unfold HS_SB; lia) ].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- what a journal of the call keeps (A_hs_s5.v's hs5_j lemmas) ---- *)
Lemma hsb5_j_frames : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> frames Sc = own ++ frames S.
Proof. intros * HJ. destruct HJ as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma hsb5_j_lay : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k cid pos,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
frame_addr lyc cid pos = frame_addr ly cid pos.
Proof.
intros * HJ. destruct HJ as (_ & Hly & _). unfold frame_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma hsb5_j_blk : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k p n i,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
rdW Wc memc (p + i) = rdW W mem (p + i).
Proof.
intros * HJ H1 H2 H3 H4. destruct HJ as (_&_&_&_&_&_&_&_&_& F2 &_). exact (F2 p n i H1 H2 H3 H4).
Qed.
Lemma hsb5_j_frm : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k cid pos a,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> rdW Wc memc a = rdW W mem a.
Proof.
intros * HJ H1 H2 H3. destruct HJ as (_&_&_&_&_&_&_&_&_&_&_& F4 &_). exact (F4 cid pos a H1 H2 H3).
Qed.

(* a byte of a live frame, and a shadow byte of one, is outside the footprint (A_hs_s5.v's hs5_frm_outFP,
   hs5_frmsh_outFP) *)
Lemma hsb5_frm_outFP : forall ly S (W : world SEGS) mem md O cid pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O cid pos a HAR HO Hin Ha Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (frm_img SEGS B LAWS ly S W mem md cid pos a HAR Hin Ha (hh_prog_img B MT HH a (hs3_grec_in a ltac:(lia)))). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (frm_img SEGS B LAWS ly S W mem md cid pos a HAR Hin Ha (hh_prog_img B MT HH a (hs3_spill_in a ltac:(lia)))). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md q m cid pos HAR (HO (q, m) Hqm) Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma hsb5_frmsh_outFP : forall ly S (W : world SEGS) mem md O cid pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (cid, pos) (frames S) ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O cid pos a HAR HO Hin Ha Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Happ).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
assert (Hlo : SHADOW_OFF <= a).
{ unfold shadow_addr in Ha. assert (0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia). lia. }
assert (Hhi : a < kHighMemBeg).
{ pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfb) as Hre.
  assert (Hle : shadow_addr (frame_addr ly cid pos + fs_frame_bytes cid) <= shadow_addr alloc_ceiling)
    by (apply shadow_mono; lia).
  assert (Hc8 : alloc_ceiling / 8 <= 17592184995840)
    by (replace 17592184995840 with (140737479966720 / 8) by (vm_compute; reflexivity); apply Z.div_le_mono; lia).
  unfold shadow_addr in *. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ cbn in Hg. unfold A_G_REC, REC_SIZE, SHADOW_OFF in *. lia. }
apply inFP_cons in Hfp as [Hs | Hfp].
{ cbn in Hs. unfold A_REC_SPILL, SC_SIZE, SHADOW_OFF in *. lia. }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR (HO (q, m) Hqm)) as (_ & _ & _ & Hqapp & _).
destruct Hqapp as (_ & [Hq | [Hq1 Hq2]]); unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* the eight bytes of one slot of the token array, at a state of the call (A_hs_s5.v's hs5_arr_now, with the
   frame the journal owns) *)
Lemma hsb5_arr_now : forall STK sp0 ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k O ptok N j,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (hs_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(afobj SEGS B ly S W mem ptok N \/
 (in_blockA (ablocks B ly S) ptok N /\ Forall (fun qk => iv_apart ptok N (fst qk) (snd qk)) O)) ->
0 <= j -> j + 8 <= N ->
4096 <= ptok + j /\ ptok + j + 8 <= alloc_ceiling /\ in_app (ptok + j) 8 /\
(forall i, 0 <= i < 8 -> rdW Wc memc (ptok + j + i) = rdW W mem (ptok + j + i)) /\
range_addressable (rdW Wc memc) SHADOW_OFF (ptok + j) 8.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k O ptok N j HARe HJ HO Hlive HARR Hj0 HjN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
destruct HARR as [((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hp8 & HRA) | [HBLK HAP]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HARe Hin) as (Hb1 & Hb2 & Happ).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hdiv : forall x, frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
    shadow_addr (frame_addr ly cid pos) <= shadow_addr x < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8).
  { intros x Hx. split; [apply shadow_mono; lia|].
    assert (Hlt : x / 8 < frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
    { apply Z.div_lt_upper_bound; [lia|].
      pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as D1.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2. rewrite Hal in D1. rewrite Hb8 in D2. lia. }
    unfold shadow_addr. lia. }
  split; [lia|]. split; [lia|].
  split; [apply (in_app_sub (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia]|].
  split.
  { intros i Hi.
    apply (hsb5_j_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (ptok + j + i) HJ Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - exact (hsb5_frm_outFP ly S W mem md O cid pos (ptok + j + i) HARe HO Hin ltac:(lia)). }
  intros x Hx. destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs.
  apply (hsb5_j_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (shadow_of_addr SHADOW_OFF x) HJ Hin).
  + right. unfold in_zr. cbn [fst snd].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) by reflexivity.
    exact (Hdiv x ltac:(lia)).
  + replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) by reflexivity.
    exact (hsb5_frmsh_outFP ly S W mem md O cid pos (shadow_addr x) HARe HO Hin (Hdiv x ltac:(lia))).
- destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
  assert (Hno : ~ In (q, m) O).
  { intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  pose proof (Hlive (q, m) Hqm Hno) as Hqc.
  destruct (al_blocks _ _ LAWS ly S W mem md q m HARe Hqm) as (_ & Hq4096 & Hqceil & Happ & _ & _ & Hmr).
  pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
  split; [lia|]. split; [lia|].
  split; [apply (in_app_sub q (req_size m)); [exact Happ | lia | lia | lia]|].
  split.
  { intros i Hi. replace (ptok + j + i) with (q + (ptok + j + i - q)) by lia.
    apply (hsb5_j_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m (ptok + j + i - q) HJ Hqm Hqc ltac:(lia)).
    exact (hs3_blk_outFP B MT HH ly S W mem md O q m (q + (ptok + j + i - q)) HARe HO Hqm Hno ltac:(lia)). }
  exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc q m (ptok + j) 8 HARc Hqc ltac:(lia) ltac:(lia)).
Qed.

(* what the walk needs of a string argument at a state of the call *)
Definition hsb5_argok (Wc : world SEGS) (memc : word -> option byte) (p : Z) (s : list byte) : Prop :=
4096 <= p /\ p + Z.of_nat (length s) + 1 <= alloc_ceiling /\ Z.of_nat (length s) + 1 <= LMAX + 1 /\
astr_atR (rdW Wc memc) p s /\ atail_vis SEGS Wc memc (p + Z.of_nat (length s)) /\
amem_range p (Z.of_nat (length s) + 1) /\
range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
shadow_hull_vis (rdW Wc memc) p (Z.of_nat (length s) + 1).

(* a token of the entry at a state of the call: hs3_str_now, and its tail by the heap-tail fact *)
Lemma hsb5_arg_now : forall x fpos lyc Sc (Wc : world SEGS) memc mdc k O1 Nw Rest p s, hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  hs_ba B x lyc Sc O1 Nw Rest ->
  hs_str B (i_ly x) (i_S x) (rdW (i_W x) (i_mem x)) (i_O x) p s ->
  hsb5_argok Wc memc p s.
Proof.
intros x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s CX HJ HBA HARG.
destruct (hs3_str_now B MT HH x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s CX HJ HBA HARG)
  as (_ & HSTR & Hnle & Hp0 & q & m & Hqc & Hq1 & Hq2 & _).
pose proof (proj1 HJ) as HARc.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc Hqc) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hmr).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
split; [lia|]. split; [lia|]. split; [exact Hnle|]. split; [exact HSTR|].
split; [exact (hh_heap_tail B MT HH lyc Sc Wc memc mdc q m (p + Z.of_nat (length s)) HARc Hqc ltac:(lia))|].
split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia))|].
exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* a string argument is a range the runtime entries may read *)
Lemma hsb5_read_of_arg : forall stk (Wc : world SEGS) memc (regs : bvmap 5 word) p s,
hsb5_argok Wc memc p s -> alloc_ceiling <= spZ regs - stk -> 0 <= stk ->
aread_ok SEGS stk Wc regs memc p (astr_len s + 1).
Proof.
intros stk Wc memc regs p s (H1 & H2 & H3 & HSTR & HTl & HMR & HRA & HHU) Hsp Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold aread_ok, astr_len. split; [lia|]. split; [lia|]. split; [unfold LMAX in H3; lia|].
split.
- intros a Ha. split.
  + destruct HSTR as [HB _].
    replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (HB (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
  + unfold ascratch_stk. lia.
- split; [exact HMR|]. split; [exact HRA | intros _; exact HHU].
Qed.

(* the runtime entries' read-only view (in_rom is in_roP's first arm) *)
Lemma hsb5_rom_view : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem H a Hrom Ho He. apply H; [left; exact Hrom | exact Ho | exact He]. Qed.

(* the recorder's bytes lie below the allocator's ceiling *)
Lemma hsb5_rec_low : forall ly S (W : world SEGS) mem md rd R O a,
  AR SEGS B ly S W mem md -> rec_repA B ly S rd R O -> hs_in_rec a \/ hs_in_own O a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O a HAR HR [Ha | (pn & Hpn & Ha)].
- pose proof asan_consts as (C1 & _). unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
- destruct pn as [q m]. cbn [fst snd] in Ha.
  destruct (hs_rec_own B _ _ _ _ _ HR (q, m) Hpn) as [Hin _].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hin) as (_ & Hq4 & Hqc & _ & _ & _ & Hmr).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr2]. lia.
Qed.

(* what a point carries, through a step that keeps the saved registers and the frame's flag pointer *)
Lemma hsb5_mid_keep : forall x fpos lyc Sc (Wc : world SEGS) memc mdc memc' mdc' k kb ma lb O1 Nw Rest,
  hs_mid B MT x fpos lyc Sc Wc memc mdc k kb ma lb O1 Nw Rest ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc' mdc' k ->
  (forall a, spZ (i_regs x) - 104 <= a < spZ (i_regs x) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, hs_F x fpos + 56 <= a < hs_F x fpos + 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  hs_mid B MT x fpos lyc Sc Wc memc' mdc' k kb ma lb O1 Nw Rest.
Proof.
intros x fpos lyc Sc Wc memc mdc memc' mdc' k kb ma lb O1 Nw Rest (HJ & Hk & HM & HBB & HFR & HFL & HBA) HJ' K1 K2.
refine (conj HJ' (conj Hk (conj HM (conj HBB (conj _ (conj _ HBA)))))).
- exact (hs3_frame_kept_on (rdW Wc memc) (rdW Wc memc') (spZ (i_regs x)) (i_regs x) K1 HFR).
- apply (hs3_aval_on (rdW Wc memc)); [|exact HFL]. intros b Hb. apply K2. change (Z.of_nat 8) with 8 in Hb. lia.
Qed.

Lemma hsb5_spill_keep : forall x fpos (rd rd' : reader), hs_spill x fpos rd ->
  (forall a, hs_sp1 (spZ (i_regs x)) + 8 <= a < hs_sp1 (spZ (i_regs x)) + 32 -> rd' a = rd a) -> hs_spill x fpos rd'.
Proof.
intros x fpos rd rd' (V1 & V2 & V3) K. unfold hs_spill. cbv zeta.
split; [|split]; (apply (hs3_aval_on rd); [intros b Hb; apply K; change (Z.of_nat 8) with 8 in Hb; lia | assumption]).
Qed.

Lemma hsb5_regsK_pres : forall x fpos (rA rB : bvmap 5 word),
  hs_regsK x fpos rA -> aregs_preserved rA rB -> hs_regsK x fpos rB.
Proof.
intros x fpos rA rB (K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) HP.
split; [transitivity (getr rA 2); [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact K2]|].
split; [transitivity (getr rA 9); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact K9]|].
split; [transitivity (getr rA 8); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact K8]|].
split; [transitivity (getr rA 3); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact K3]|].
split; [transitivity (getr rA 4); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact K4]|].
split; [transitivity (getr rA 24); [exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact K24]|].
split; [transitivity (getr rA 25); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact K25]|].
transitivity (getr rA 26); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact K26].
Qed.

Lemma hsb5_regsL1_pres : forall x fpos n (rA rB : bvmap 5 word),
  hs_regsL1 x fpos n rA -> aregs_preserved rA rB -> hs_regsL1 x fpos n rB.
Proof.
intros x fpos n rA rB (HK & R18 & R23 & R21 & R19 & R22 & R20 & R27) HP.
split; [exact (hsb5_regsK_pres x fpos rA rB HK HP)|].
split; [transitivity (getr rA 18); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
split; [transitivity (getr rA 23); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact R23]|].
split; [transitivity (getr rA 21); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
split; [transitivity (getr rA 19); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
split; [transitivity (getr rA 22); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
split; [transitivity (getr rA 20); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
transitivity (getr rA 27); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact R27].
Qed.

Lemma hsb5_regsL2_pres : forall x fpos n w (rA rB : bvmap 5 word),
  hs_regsL2 x fpos n w rA -> aregs_preserved rA rB -> hs_regsL2 x fpos n w rB.
Proof.
intros x fpos n w rA rB (HK & R22 & R23 & R27 & R21 & R18 & R20) HP.
split; [exact (hsb5_regsK_pres x fpos rA rB HK HP)|].
split; [transitivity (getr rA 22); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
split; [transitivity (getr rA 23); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact R23]|].
split; [transitivity (getr rA 27); [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact R27]|].
split; [transitivity (getr rA 21); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
split; [transitivity (getr rA 18); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
transitivity (getr rA 20); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact R20].
Qed.

(* ---- L1H n: the UBSan checks and the load8 check of &tok[n], the strlen wrapper ---- *)
Lemma hs_seg_l1h : forall x n, ST_L1R B MT x n -> ST_L1H B MT x n.
Proof.
intros x n HR. unfold ST_L1H.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 Hn CX FXR MID REP SPL RG.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R23 & R21 & R19 & R22 & R20 & R27).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof HBA as (BA1 & BA2 & BA3 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HARc.
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn Hno; exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hpn Hno))))).
(* token n: its pointer and its string *)
assert (Hnp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply nth_error_nth'; lia).
assert (Hnt : nth_error (i_toks x) n = Some (hs_tok x n)) by (apply nth_error_nth'; lia).
destruct (HPS n _ Hnp) as (Hp64 & HVAL).
pose proof (hsb5_forall2_nth _ _ _ n _ _ HTOKS Hnp Hnt) as HARG.
destruct (hsb5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)]
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) (8 * Z.of_nat n)
  HAR0 HJ HO Hlive HTA ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & Hkeptarr & HRAarr).
assert (HVALc : val_mem SEGS (mrestrict (w_H Wc) memc) (i_ptok x + 8 * Z.of_nat n) 8 (hs_ptr x n)).
{ apply hsb5_val_mem_view. intros kk Hkk. rewrite (Hkeptarr (Z.of_nat kk) ltac:(lia)). exact (HVAL kk Hkk). }
assert (Hm8 : (i_ptok x + 8 * Z.of_nat n) mod 8 = 0).
{ rewrite Z.add_mod by lia. rewrite Hp8.
  replace (8 * Z.of_nat n) with (Z.of_nat n * 8) by lia. rewrite Z.mod_mul by lia. reflexivity. }
pose proof (hsb5_seed_H Wc regs1 memc (i_ptok x + 8 * Z.of_nat n) (hs_ptr x n) K26 R22 R19 R18 R23
  ltac:(lia) ltac:(lia) Hm8 Hp64 HVALc) as HS.
set (E := hsb5_E regs1 [Z_to_bv 64 (hs_ptr x n)]) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hsb5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hsb5_E_img).
assert (E32 : ew E 32 = Z_to_bv 64 (hs_ptr x n)) by (unfold E; apply hsb5_E_x32).
assert (UBx : U E hsb5_Bx = SHADOW_OFF).
{ unfold hsb5_Bx. rewrite U_SOff, (EE 26%nat 26%bv eq_refl), K26, Z.add_0_r.
  unfold w64, HS_SB, SHADOW_OFF. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U22 : U E (SOff 22 0) = i_ptok x + 8 * Z.of_nat n).
{ apply hsb5_U_off0; [rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (U24 : U E (SOff 24 0) = i_ptok x).
{ apply hsb5_U_off0; [rewrite (EE 24%nat 24%bv eq_refl), K24; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (SHOK : sh_ok SEGS hsb5_Bx hsb5_SHH E (mrestrict (w_H Wc) memc)).
{ unfold hsb5_SHH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS); [exact HRAarr | exact UBx | exact U22 | lia | lia |].
  cbn [Z.min Z.max]. intros z Hz. destruct Happ as (_ & [Hk1 | [Hk1 Hk2]]);
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
clearbody E.
unfold hs_at.
(* 0x8b6bc: the executor stops at `bltu s6,s8` *)
paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
rename HFr into HFr1. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK hsb5_Bspan.
{ (* 0x8b6bc: refuted by hsb_ub_6bc at sup_host_setting_aux.v:94, from i_ptok x + 8 * n + 8 <= alloc_ceiling
     (hsb5_arr_now on hs_cx's token-array premise): s6 = tok + 8n does not wrap below s8 = tok *)
  exfalso. rewrite !denot_lit_U, U22, U24 in Hc.
  rewrite (hsb_ub_6bc (i_ptok x) (8 * Z.of_nat n)) in Hc by lia. discriminate Hc. }
(* 0x8b6c0 .. 0x8b6e4 with `bgeu s6,s8`, a0 := tok[n], the call of the strlen wrapper. The executor decides the
   other checks:
   0x8b6c8: refuted by hsb5_seed_H at sup_host_setting_s5.v:175, from hs_regsL1's s2 = 1 and the seed fact
     4096 <= tok + 8n (hsb5_PTRF on atom 22): seqz s6 = 0, 1 xor 0 = 1, `beqz a0` not taken.
   0x8b6cc: refuted by hsb5_seed_H at sup_host_setting_s5.v:175, from hs_regsL1's s7 = 1: `beqz s7` not taken.
   0x8b6dc: refuted by shent_ok_of_range at sup_host_setting_s5.v:605, from range_addressable of &tok[n] (hsb5_arr_now
     on hs_cx's token-array premise): the token executor decides the load8 check, report 0x8b8e8 not reached. *)
paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. rewrite <- (KEEP1 a Ha).
  apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9. rewrite E32 in P10.
rewrite (EE 22%nat 22%bv eq_refl), R22 in P19. rewrite (EE 20%nat 20%bv eq_refl), R20 in P20.
rewrite (EE 21%nat 21%bv eq_refl), R21 in P21. rewrite (EE 22%nat 22%bv eq_refl), R22 in P22.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (RGm : hs_regsL1 x fpos n (ms_regs ms)).
{ split; [|split; [exact P18|split; [exact P23|split; [exact P21|split; [exact P19|split; [exact P22|split; [exact P20|exact P27]]]]]]].
  split; [exact P2|]. split; [exact P9|]. split; [exact P8|]. split; [exact P3|]. split; [exact P4|].
  split; [exact P24|]. split; [exact P25 | exact P26]. }
destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms) mdw k CX HJ) as [HRODc _].
pose proof (hsb5_arg_now x fpos lyc Sc Wc (ms_mem ms) mdw k O1 _ Rest (hs_ptr x n) (hs_tok x n) CX HJ HBA HARG) as HAOK.
pose proof HAOK as (G1 & G2 & G3 & GSTR & GTl & GMR & GRA & GHU).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B (hh_TL B MT HH)) ESTACK (fun _ => False)
    (SIG CS___interceptor_trampoline_strlen) Wc (ms_regs ms) (ms_mem ms) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc _ k
    (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (Z_to_bv 64 (BASE + HS_L1R)) _ HJ Qsp S1b ltac:(lia) ltac:(lia)
    ltac:(lia) P1 (fun a (H : False) => False_ind _ H)).
  apply (hh_strlen B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw (hs_ptr x n) (hs_tok x n)).
  - eapply (ecall_pre_stk_at SEGS B ESTACK SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x)
      (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc Wc (ms_mem ms) mdw k (ms_regs ms)
      (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) HJ Qsp S1b ltac:(lia) ltac:(lia) ltac:(lia) HraT);
      [rewrite P3; exact Hgp | rewrite P4; exact Htp].
  - rewrite P10. reflexivity.
  - lia.
  - apply (astr_atR_view SEGS). exact GSTR.
  - exact (hsb5_read_of_arg ESTACK Wc (ms_mem ms) (ms_regs ms) (hs_ptr x n) (hs_tok x n) HAOK
      ltac:(rewrite Qsp; lia) ltac:(lia)).
  - unfold astr_len. exact GTl.
  - exact (hsb5_rom_view Wc (ms_mem ms) HRODc). }
(* back at 0x8b6e8 with a0 = |tok[n]| *)
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (hs_sp1 (spZ (i_regs x)) - 4096 <= a < hs_sp1 (spZ (i_regs x))) ->
  rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw. rewrite (HK2 a Ha ltac:(lia) ltac:(intros [])). apply KEEP2. exact Ha. }
apply (HR fpos lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 b1 Hn CX FXR).
- apply (hsb5_mid_keep x fpos lyc Sc Wc memc mdc mem2 md2 k _ _ _ O1 _ Rest MID HJ2);
    intros a Ha; apply KEEPA; lia.
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ REP).
  + intros a Ha. destruct (hsb5_rec_low lyc Sc Wc memc mdc _ _ _ a HARc REP Ha) as [Hl0 Hl1]. apply KEEPA; lia.
  + intros pn H. exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H)).
- apply (hsb5_spill_keep x fpos (rdW Wc memc)); [exact SPL|]. intros a Ha. apply KEEPA; lia.
- exact (hsb5_regsL1_pres x fpos n (ms_regs ms) regs2 RGm HP2).
- rewrite HQ2. reflexivity.
Qed.

(* ---- L1R n: the loop's tail, the back edge, and on the exit xmalloc(len + 1) ---- *)
Lemma hs_seg_l1r : forall x n,
((S n < length (i_toks x))%nat -> ST_L1H B MT x (S n)) ->
(S n = length (i_toks x) -> ST_XM B MT x) ->
ST_L1R B MT x n.
Proof.
intros x n HNX HXM. unfold ST_L1R.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 Hn CX FXR MID REP SPL RG H10.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10e & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R23 & R21 & R19 & R22 & R20 & R27).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
pose proof (proj1 HJ) as HARc.
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn Hno; exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hpn Hno))))).
(* the bytes of the tokens so far *)
assert (Htokn : Z.of_nat (length (hs_tok x n)) + 1 <= hs_words_len (i_toks x)) by (apply hsb5_words_tok_le; lia).
pose proof (hsb5_words_firstn_le n (i_toks x)) as Hfle.
pose proof (hs3_wl_nonneg (firstn n (i_toks x))) as Hfnn.
pose proof (hs3_wl_nonneg (i_toks x)) as Hwnn.
pose proof (hsb5_words_firstn_S n (i_toks x) ltac:(lia)) as HfS.
change (nth n (i_toks x) []) with (hs_tok x n) in HfS.
destruct (hsb5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)]
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) (8 * Z.of_nat n)
  HAR0 HJ HO Hlive HTA ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & _ & _).
pose proof (hsb5_seed_R Wc regs1 memc) as HS.
set (E := hsb5_E regs1 []) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hsb5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hsb5_E_img).
assert (SHOK : sh_ok SEGS hsb5_Bx (@nil shent) E (mrestrict (w_H Wc) memc)) by apply Forall_nil.
clearbody E.
unfold hs_at.
(* 0x8b6e8 .. 0x8b6fc: the loop's increments, then the back edge `bnez s11` *)
paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
rename HFr into HFRa. rename ms into msa.
psrr_branch_tok RUN BR HS SHOK hsb5_Bspan.
- (* taken: tokens are left, back to 0x8b6bc *)
  assert (HSn : (S n < length (i_toks x))%nat).
  { rewrite branch_ne_U in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27, U_SLit in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite (zcanon_id (Z.of_nat (length (i_toks x) - n) + -1)) in Hc by (unfold M64; lia).
    rewrite (zcanon_id 0) in Hc by (unfold M64; lia). lia. }
  paj_run_to_tok RUNTO HS HJ SHOK hsb5_Bspan HS_L1H.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
    apply (awr_ok_nil SEGS B). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  apply (HNX HSn fpos lyc Sc Wc (ms_mem ms) mdw (ms_regs ms) k O1 Rest b0 b1 HSn CX FXR).
  + apply (hsb5_mid_keep x fpos lyc Sc Wc memc mdc (ms_mem ms) mdw k _ _ _ O1 _ Rest MID HJ);
      intros a Ha; apply KEEP2; lia.
  + apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP).
    * intros a Ha. destruct (hsb5_rec_low lyc Sc Wc memc mdc _ _ _ a HARc REP Ha) as [Hl0 Hl1]. apply KEEP2; lia.
    * intros pn H. exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H)).
  + apply (hsb5_spill_keep x fpos (rdW Wc memc)); [exact SPL|]. intros a Ha. apply KEEP2; lia.
  + split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    * split; [rewrite P2, (EE 2%nat 2%bv eq_refl); exact K2|].
      split; [rewrite P9, (EE 9%nat 9%bv eq_refl); exact K9|].
      split; [rewrite P8, (EE 8%nat 8%bv eq_refl); exact K8|].
      split; [rewrite P3, (EE 3%nat 3%bv eq_refl); exact K3|].
      split; [rewrite P4, (EE 4%nat 4%bv eq_refl); exact K4|].
      split; [rewrite P24, (EE 24%nat 24%bv eq_refl); exact K24|].
      split; [rewrite P25, (EE 25%nat 25%bv eq_refl); exact K25|].
      rewrite P26, (EE 26%nat 26%bv eq_refl); exact K26.
    * rewrite P18, (EE 18%nat 18%bv eq_refl). exact R18.
    * rewrite P23, (EE 23%nat 23%bv eq_refl). exact R23.
    * rewrite P21, (EE 21%nat 21%bv eq_refl). exact R21.
    * rewrite P19, (EE 19%nat 19%bv eq_refl), R19. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. lia.
    * rewrite P22, (EE 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. lia.
    * rewrite P20. transitivity (sv_denot E (SAlu ALU_ADD (SOff 10 1) (SOff 20 0))).
      { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
      rewrite denot_lit_U, (hsb5_U_add2 E 10%nat 1 20%nat 0
        (Z.of_nat (length (hs_tok x n))) (hs_words_len (firstn n (i_toks x))));
        [ unfold w64; f_equal; lia
        | rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
        | rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
        | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia ].
    * rewrite P27, (EE 27%nat 27%bv eq_refl), R27. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. lia.
- (* the exit: the last token was read; xmalloc(len + 1) *)
  assert (HSn : S n = length (i_toks x)).
  { rewrite branch_ne_U in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rewrite U_SOff, (EE 27%nat 27%bv eq_refl), R27, U_SLit in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite (zcanon_id (Z.of_nat (length (i_toks x) - n) + -1)) in Hc by (unfold M64; lia).
    rewrite (zcanon_id 0) in Hc by (unfold M64; lia). lia. }
  assert (HWSZ : hs_wsz x = Z.of_nat (length (hs_tok x n)) + 2 + hs_words_len (firstn n (i_toks x))).
  { assert (Hall : firstn (S n) (i_toks x) = i_toks x) by (rewrite HSn; apply firstn_all).
    rewrite Hall in HfS. unfold hs_wsz. lia. }
  paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
    apply (awr_ok_nil SEGS B). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS.
  assert (SIGXM : SIG CS_xmalloc = BASE + AF_xmalloc).
  { rewrite (hh_sigp B MT HH CS_xmalloc ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
    try (f_equal; vm_compute; reflexivity). }
  rewrite SIGXM.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (21%bv : bv 5) P21. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3.
  rewrite (EE 4%nat 4%bv eq_refl), K4 in P4. rewrite (EE 8%nat 8%bv eq_refl), K8 in P8.
  rewrite (EE 9%nat 9%bv eq_refl), K9 in P9. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
  rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
  rewrite (EE 26%nat 26%bv eq_refl), K26 in P26.
  assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
  { unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (HA0 : getr (ms_regs ms) 10 = w64 (hs_wsz x)).
  { rewrite P10. transitivity (sv_denot E (SAlu ALU_ADD (SOff 10 2) (SOff 20 0))).
    { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
    rewrite denot_lit_U, (hsb5_U_add2 E 10%nat 2 20%nat 0
      (Z.of_nat (length (hs_tok x n))) (hs_words_len (firstn n (i_toks x))));
      [ unfold w64; f_equal; lia
      | rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia ]. }
  (* xmalloc's premises at the call *)
  pose proof HJ as (_ & _ & _ & _ & _ & HFRSc & HNEVc & _).
  assert (HFRc : hs_frame (rdW Wc (ms_mem ms)) (spZ (i_regs x)) (i_regs x)).
  { apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR]. intros b Hb. apply KEEP2.
    pose proof CX as (HPRE' & _). pose proof HPRE' as (_ & _ & _ & _ & _ & (_ & Hs0' & Hc' & Hl' & Hh' & H47' & _) & _).
    pose proof (@ASAN_CEIL_range rc) as [C1' _]. unfold ASAN_CEIL in C1'. clear - Hb Hs0' Hc' Hl' Hh' H47' C1'. lia. }
  destruct (hs3_achain B MT x fpos lyc Sc Wc (ms_mem ms) mdw k (ms_regs ms) CX HJ HFRc ltac:(rewrite Qsp; lia) P8)
    as (ch1 & HCH).
  assert (HXSv : XMALLOC_STK = 16400) by (vm_compute; reflexivity).
  assert (HNEVx : st_nev Sc + EV_XMALLOC <= EV_MAX).
  { unfold EV_SUP_HOST_SETTING, hs_k2, hs_k1, hs_k0 in *. unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC in *.
    lia. }
  assert (HLIVEx : blocks_bytes Sc + LIVE_XMALLOC (hs_wsz x) <= LIVE_MAX).
  { unfold hs_l2, hs_l1 in HBB. unfold LIVE_SUP_HOST_SETTING in HLIVE.
    assert (0 <= LIVE_ARG_S (Some (join_sp (i_toks x)))) by (unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
    unfold hs_wsz. lia. }
  assert (HMOx : mo_ok MT Sc (XM_XMALLOC MT (hs_wsz x))).
  { pose proof (hh_MTL B MT HH) as ML.
    apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m2 MT x) _ ML HMO HMLE).
    - exact (hs3_xx_nonneg B MT HH (hs_wsz x)).
    - unfold XM_SUP_HOST_SETTING, hs_m2, hs_m1, hs_m0, hs_wsz.
      pose proof (hs3_xs_nonneg B MT HH (Some (join_sp (i_toks x)))).
      pose proof (mo_free_nonneg MT ML). lia. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) _ SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x))
      (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc _ k
      XMALLOC_STK [] EV_XMALLOC (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms) 1) ch1
      (fun ly' S' W' regs' mem' md' => exists p : Z,
         getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly' S') ((p, LIVE_XMALLOC (hs_wsz x)) :: ablocks B lyc Sc) /\
         Forall (fun qk => iv_apart p (LIVE_XMALLOC (hs_wsz x)) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
         in_blockA (ablocks B ly' S') p (LIVE_XMALLOC (hs_wsz x)) /\
         blocks_bytes S' <= blocks_bytes Sc + LIVE_XMALLOC (hs_wsz x) /\
         mo_le MT Sc S' (XM_XMALLOC MT (hs_wsz x)))
      HJ Qsp S1b ltac:(lia) ltac:(rewrite HXSv; lia) ltac:(rewrite HXSv, FS; lia)).
    - rewrite P3. exact Hgp.
    - rewrite P4. exact Htp.
    - reflexivity.
    - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite P1, unsigned_lit_small by lia. lia.
    - replace (spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))) with (spZ (ms_regs ms)) by lia. exact HCH.
    - intros HPREx. eapply SRr_mono.
      + apply (hh_xmalloc B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ ch1 (hs_wsz x) HPREx HA0).
        * unfold hs_wsz, MALLOC_MAX, LMAX in *. lia.
        * exact HNEVx.
        * exact HLIVEx.
        * exact HMOx.
      + cbv beta. unfold apost_base. intros W3' c3' _ (ly3 & S3 & regs3' & mem3' & md3' & -> & HJx & HPx & HKx).
        exists ly3, S3, regs3', mem3', md3'. split; [reflexivity | split; [exact HJx | split; [exact HPx | exact HKx]]].
    - intros a (r & Hr & _). destruct Hr. }
  (* back at 0x8b708 with the word list *)
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJi & HP4 &
    (res & Ha04 & Hres & Hperm4 & Hap4 & Hblk4 & Hbb4 & MLE4)).
  pose proof HJi as (HAR4 & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
  assert (HL : LIVE_XMALLOC (hs_wsz x) = hs_wsz x) by (unfold LIVE_XMALLOC, hs_wsz; lia).
  assert (KST : forall a, alloc_ceiling <= a < 2 ^ 64 -> hs_sp1 (spZ (i_regs x)) <= a ->
    rdW W4 mem4 a = rdW Wc memc a).
  { intros a Ha Ha'. rewrite (J1 a Ha ltac:(rewrite HXSv; lia) ltac:(intros (r & Hr & _); destruct Hr)).
    apply KEEP2. lia. }
  assert (KBL : forall q m i, In (q, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
    rdW W4 mem4 (q + i) = rdW Wc memc (q + i)).
  { intros q m i Hin Hi. rewrite (J2 q m i Hin ltac:(apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hin)
      Hi ltac:(intros (r & Hr & _); destruct Hr)).
    apply KEEP2. destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hin) as (_ & Hq4 & Hqc & _). lia. }
  assert (KPG : forall a, Exists (in_zr a) recb_PG -> rdW W4 mem4 a = rdW Wc memc a).
  { intros a Hpg. destruct (RecBLemmas.recb_prog_unowned_m B (hh_HB B MT HH) (hh_prog_img B MT HH) a Hpg) as (G1 & G2 & G3).
    rewrite (J3 a G1 G2 G3 (fp_spares_closed [] a sink_closed_nil ltac:(intros (r & Hr & _); destruct Hr))).
    apply KEEP2. pose proof (pa_img_range a G1). lia. }
  rewrite P1.
  refine (HXM HSn fpos ly4 S4 W4 mem4 md4 regs4 (k + EV_XMALLOC) O1 Rest b0 b1 res CX FXR _ _ _ _ _ _ _).
  + refine (conj HJ4 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * unfold hs_k3. unfold EV_XMALLOC. lia.
    * exact (mle_station MT (i_S x) Sc S4 (hs_m2 MT x) (XM_XMALLOC MT (hs_wsz x)) (hh_MTL B MT HH) HMLE MLE4).
    * unfold hs_l3. lia.
    * apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
      intros b Hb. apply KST; [lia | lia].
    * apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
      intros b Hb. change (Z.of_nat 8) with 8 in Hb. rewrite <- (KEEP2 b ltac:(lia)). apply (J4 0 fpos b HFin).
      -- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. lia.
      -- intros (r & Hr & _). destruct Hr.
    * split; [|split; [exact BA2|split; [exact BA3|split; [exact BA4|split; [exact BA5|split; [|exact BA7]]]]]].
      -- eapply Permutation_trans; [exact Hperm4|]. eapply Permutation_trans; [apply perm_skip; exact BA1|].
         exact (Permutation_middle [(b0, hs_b0 x); (b1, hs_b1 x)] Rest (res, LIVE_XMALLOC (hs_wsz x))).
      -- intros pn Hpn Hin. cbn [In] in Hpn.
         destruct Hpn as [Hb | [Hb | [Hb | []]]].
         ++ apply (BA6 pn); [cbn [In]; left; exact Hb | exact Hin].
         ++ apply (BA6 pn); [cbn [In]; right; left; exact Hb | exact Hin].
         ++ subst pn.
            destruct (in_dec hs3_pair_dec (res, LIVE_XMALLOC (hs_wsz x)) (i_O x)) as [Ho | Ho]; [exact Ho|].
            exfalso. pose proof (proj1 (Forall_forall _ _) Hap4 _ (Hlive _ Hin Ho)) as Hd.
            rewrite HL in Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. unfold hs_wsz in Hd. lia.
  + apply (hs_rec_kept B lyc Sc ly4 S4 (rdW Wc memc) (rdW W4 mem4) _ _ REP).
    * intros a [Hrec | (pn & Hpn & Ha)].
      -- apply KPG. unfold hs_in_rec in Hrec. destruct Hrec as [Hg | Hs]; [apply hs3_grec_in | apply hs3_spill_in]; lia.
      -- destruct pn as [q m]. cbn [fst snd] in Ha.
         pose proof (proj1 (hs_rec_own B _ _ _ _ _ REP (q, m) Hpn)) as Hqm.
         destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hqm) as (_ & _ & _ & _ & _ & _ & Hmr).
         pose proof (req_size_pos m ltac:(lia)) as [_ Hr2].
         replace a with (q + (a - q)) by lia. apply (KBL q m (a - q) Hqm). lia.
    * intros pn H. apply (Permutation_in _ (Permutation_sym Hperm4)). right.
      exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H)).
  + apply (hsb5_spill_keep x fpos (rdW Wc memc)); [exact SPL|]. intros a Ha. apply KST; lia.
  + apply (hsb5_regsK_pres x fpos (ms_regs ms) regs4); [|exact HP4].
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|]. split; [exact P3|]. split; [exact P4|].
    split; [exact P24|]. split; [exact P25 | exact P26].
  + transitivity (getr (ms_regs ms) 21); [exact (HP4 21 ltac:(unfold acallee_saved; lia)) | exact P21].
  + exact Ha04.
  + lia.
Qed.

(* ---- XM: the store1 check, words[0] := 0, the join loop's entry and the strcat wrapper on token 0 ---- *)
(* The step through a runtime entry (art_post) that writes inside one live block [bq, bq + req_size nq), a block
   the call may write (A_hs_s5.v's hs5_art_wr_at) *)
Lemma hsb5_art_wr_at : forall stk (Eb : Z -> Prop) pc (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k (o : Z) raw bq nq (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
In (bq, nq) (ablocks B lyc Sc) -> (forall a, Eb a -> bq <= a < bq + req_size nq) ->
(forall a, bq <= a < bq + req_size nq ->
  (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
   rdW W mem2 a = rdW W memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw bq nq Qr
  HJ Hsp Hal Hneg Hstk Hbud Hraw Hbq HEb Hcov HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal SEGS B stk (spZ regsT) (ablocks_fp [(bq, nq)]) lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
  { eapply (call_effect_journal SEGS B LAWS pa_segs_low (pal_env B (hh_TL B MT HH)) stk lyc Sc W regsT memT mdc lyc Sc W
      mem2 md2 Eb (ablocks_fp [(bq, nq)]) [] 0);
    [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr
    | exact HAR | | reflexivity | lia | lia | lia | | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
    - intros a H0 _ _ H3 H4. apply (Hfr a H0); [intros Hs; apply H3; left; exact Hs | exact H4].
    - unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
      repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia].
    - intros a Ha. exists bq, nq. split; [left; exact Hbq|]. split; [exact (HEb a Ha)|].
      left. pose proof (HEb a Ha) as Hr. replace a with (bq + (a - bq)) by lia.
      apply (inFP_ablocks_fp [(bq, nq)] bq nq (a - bq)); [left; reflexivity | lia]. }
  pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT)
    (ablocks_fp [(bq, nq)]) [] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)) as HJ2.
  rewrite app_nil_l, Z.add_0_r in HJ2. apply HJ2.
  intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p' & n' & Hpn & Hr).
  destruct Hpn as [Hpn | []]. injection Hpn as <- <-. exact (Hcov a Hr). }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.

(* a string argument is apart from a live block that is the recorder's or was made in the call *)
Lemma hsb5_arg_apart : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O p s q m,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc ->
hs_str B ly S (rdW W mem) O p s ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
In (q, m) (ablocks B lyc Sc) -> (In (q, m) O \/ ~ In (q, m) (ablocks B ly S)) ->
q + req_size m <= p \/ p + Z.of_nat (length s) + 1 <= q.
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O p s q m HARe HARc HARG Hlive Hqm HqO.
unfold hs_str in HARG. destruct HARG as (Hp0 & HSTR & Hnle & HBLK & HAP).
destruct HBLK as (q0 & m0 & Hq0 & Hq1 & Hq2).
assert (Hno : ~ In (q0, m0) O).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q0, m0) Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hne : (q0, m0) <> (q, m)).
{ intros E. rewrite E in Hno, Hq0. destruct HqO as [H | H]; [exact (Hno H) | exact (H Hq0)]. }
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q0 m0 q m HARc (Hlive (q0, m0) Hq0 Hno) Hqm Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md q0 m0 HARe Hq0) as (_ & _ & _ & _ & _ & _ & Hmr).
pose proof (req_size_pos m0 ltac:(lia)) as [_ Hr0].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the allocator's live blocks are pairwise distinct *)
Lemma hs_seg_xm : forall x, ST_L2C B MT x 0 -> ST_XM B MT x.
Proof.
intros x HL2. unfold ST_XM.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 wl CX FXR MID REP SPL RGK R21 R10 Hw4096.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10e & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RGK as (K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJ) as HARc.
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn Hno; exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hpn Hno))))).
assert (HNWL : forall pn, In pn [(b0, hs_b0 x); (b1, hs_b1 x); (wl, LIVE_XMALLOC (hs_wsz x))] ->
  In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_introl Hpn)))).
(* the word list's block *)
pose proof (hs3_wl_nonneg (i_toks x)) as Hwnn.
assert (HL : LIVE_XMALLOC (hs_wsz x) = hs_wsz x) by (unfold LIVE_XMALLOC, hs_wsz; lia).
assert (Hwin : In (wl, LIVE_XMALLOC (hs_wsz x)) (ablocks B lyc Sc)) by (apply HNWL; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wl _ HARc Hwin) as (Hw16 & _ & Hwceil & Hwapp & Hwpres & _ & Hwmr).
assert (Hrw : req_size (LIVE_XMALLOC (hs_wsz x)) = hs_wsz x).
{ rewrite HL. unfold req_size, hs_wsz. destruct (_ =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
assert (Hwsz1 : 1 <= hs_wsz x) by (unfold hs_wsz; lia).
assert (Hwszd : hs_wsz x = hs_words_len (i_toks x) + 1) by reflexivity.
assert (HwO : In (wl, LIVE_XMALLOC (hs_wsz x)) (i_O x) \/ ~ In (wl, LIVE_XMALLOC (hs_wsz x)) (ablocks B (i_ly x) (i_S x))).
{ destruct (in_dec hs3_pair_dec (wl, LIVE_XMALLOC (hs_wsz x)) (i_O x)) as [Ho | Ho];
    [left; exact Ho | right; intros Hin; apply Ho; apply (BA6 _ ltac:(right; right; left; reflexivity) Hin)]. }
assert (Hwcov : forall a, wl <= a < wl + req_size (LIVE_XMALLOC (hs_wsz x)) ->
  (inFP (hs_FP (i_O x)) a /\ exists bb nn, In (bb, nn) (ablocks B lyc Sc) /\ bb <= a < bb + req_size nn) \/
  in_tmp_block (ablocks B (i_ly x) (i_S x)) (ablocks B lyc Sc) a).
{ intros a Ha. destruct HwO as [Ho | Hno].
  - left. split; [|exists wl, (LIVE_XMALLOC (hs_wsz x)); split; [exact Hwin | exact Ha]].
    unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
    replace a with (wl + (a - wl)) by lia.
    apply (inFP_ablocks_fp (i_O x) wl (LIVE_XMALLOC (hs_wsz x)) (a - wl)); [exact Ho | lia].
  - right. exists wl, (LIVE_XMALLOC (hs_wsz x)). split; [exact Hwin|]. split; [exact Hno | exact Ha]. }
(* token 0 *)
assert (Hn0 : (0 < length (i_toks x))%nat) by lia.
assert (Hnp : nth_error (i_ps x) 0 = Some (hs_ptr x 0)) by (apply nth_error_nth'; lia).
assert (Hnt : nth_error (i_toks x) 0 = Some (hs_tok x 0)) by (apply nth_error_nth'; lia).
destruct (HPS 0%nat _ Hnp) as (Hp64 & HVAL).
pose proof (hsb5_forall2_nth _ _ _ 0%nat _ _ HTOKS Hnp Hnt) as HARG.
assert (Htok0 : Z.of_nat (length (hs_tok x 0)) + 1 <= hs_words_len (i_toks x)) by (apply hsb5_words_tok_le; lia).
pose proof (hsb5_arg_apart (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) lyc Sc Wc memc mdc (i_O x)
  (hs_ptr x 0) (hs_tok x 0) wl _ HAR0 HARc HARG Hlive Hwin HwO) as Hapart.
destruct (hsb5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)]
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) 0
  HAR0 HJ HO Hlive HTA ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & Hkeptarr & HRAarr).
rewrite Z.add_0_r in Ha1, Ha2, Happ, Hkeptarr, HRAarr.
assert (HVALc : val_mem SEGS (mrestrict (w_H Wc) memc) (i_ptok x) 8 (hs_ptr x 0)).
{ apply hsb5_val_mem_view. intros kk Hkk. rewrite (Hkeptarr (Z.of_nat kk) ltac:(lia)).
  pose proof (HVAL kk Hkk) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
(* the token array is apart from the word list's block *)
assert (Hdisj : wl + 1 <= i_ptok x \/ i_ptok x + 8 <= wl).
{ destruct HTA as [((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & _ & _) | [(q & m & Hqm & Hq1 & Hq2) HAP]].
  - assert (Hfc : In (cid, pos) (frames Sc))
      by (rewrite (hsb5_j_frames _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); apply in_or_app; right; exact Hin).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc wl _ cid pos HARc Hwin Hfc) as Hd.
    rewrite (hsb5_j_lay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos HJ) in Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - assert (Hno : ~ In (q, m) (i_O x)).
    { intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
      unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
    assert (Hne : (q, m) <> (wl, LIVE_XMALLOC (hs_wsz x))).
    { intros E. rewrite E in Hno, Hqm. destruct HwO as [H | H]; [exact (Hno H) | exact (H Hqm)]. }
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m wl _ HARc (Hlive (q, m) Hqm Hno) Hwin Hne) as Hd.
    destruct (al_blocks _ _ LAWS (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) q m HAR0 Hqm) as (_ & _ & _ & _ & _ & _ & Hmr).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr0].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the seed at 0x8b708 *)
pose proof (hsb5_seed_M Wc regs1 memc wl (Z.of_nat (length (i_toks x))) (i_ptok x) (hs_ptr x 0)
  K26 R21 R10 K24 ltac:(lia) Hw4096 ltac:(lia) Hw16 ltac:(lia) ltac:(lia) Hp8 Hp64 Hdisj
  ltac:(intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hwpres (wl + o) ltac:(lia))))
  HVALc) as HS.
set (E := hsb5_E regs1 [Z_to_bv 64 (hs_ptr x 0)]) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hsb5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hsb5_E_img).
assert (E32 : ew E 32 = Z_to_bv 64 (hs_ptr x 0)) by (unfold E; apply hsb5_E_x32).
assert (UBx : U E hsb5_Bx = SHADOW_OFF).
{ unfold hsb5_Bx. rewrite U_SOff, (EE 26%nat 26%bv eq_refl), K26, Z.add_0_r.
  unfold w64, HS_SB, SHADOW_OFF. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U10 : U E (SOff 10 0) = wl).
{ apply hsb5_U_off0; [rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (U24 : U E (SOff 24 0) = i_ptok x).
{ apply hsb5_U_off0; [rewrite (EE 24%nat 24%bv eq_refl), K24; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (SHOK : sh_ok SEGS hsb5_Bx hsb5_SHM E (mrestrict (w_H Wc) memc)).
{ unfold hsb5_SHM. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E hsb5_Bx 10%nat wl _ 0 1 HARc Hwin UBx U10); lia.
  - eapply (shent_ok_of_range SEGS); [exact HRAarr | exact UBx | exact U24 | lia | lia |].
    cbn [Z.min Z.max]. intros z Hz. destruct Happ as (_ & [Hk1 | [Hk1 Hk2]]);
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
clearbody E.
unfold hs_at.
(* 0x8b708 .. 0x8b774: s6 := w, the store1 check of words[0], words[0] := 0, the join loop's set-up, `beqz s11` taken
   (s11 = 0); the run stops at 0x8b774 `bltu s5,s7`.
   0x8b718/0x8b8c8: refuted by shent_ok_of_block at sup_host_setting_s5.v:1137, from the word list's live block
     (w, LIVE_XMALLOC (hs_wsz x)) in hs_mid's Nw: the token executor decides the store1 check and its slow path
     0x8b8c4 .. 0x8b8c8, report 0x8b8d0 not reached. *)
paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64;
    apply unsigned_lit_small; lia | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    destruct (Hwcov a ltac:(lia)) as [(Hfp & Hbl) | Htmp].
    + right; left. split; [exact Hfp | exact Hbl].
    + right; right; left. exact Htmp.
  - apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
(* the run wrote words[0] only *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wl + 1) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => wl <= a < wl + 1) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite (EE 10%nat 10%bv eq_refl), R10 in Hrr || idtac; unfold w64 in Hrr;
      first [rewrite unsigned_lit_small in Hrr by lia; lia | lia]
    | exact Ha | exact Hn ]. }
rename HFr into HFRa. rename ms into msa.
psrr_branch_tok RUN BR HS SHOK hsb5_Bspan.
{ (* 0x8b774 (first pass, s7 = 0): refuted by hsb_ub_774 at sup_host_setting_aux.v:126, from i_ptok x + 0 < 2 ^ 64
     (hsb5_arr_now on the token-array premise of hs_cx) *)
  exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite (EE 24%nat 24%bv eq_refl), K24 in Hc.
  unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by lia.
  rewrite (hsb_ub_774 (i_ptok x) 0) in Hc by lia. discriminate Hc. }
(* 0x8b778 .. 0x8b794: a0 := tok + 0, the load8 check of tok[0], a1 := tok[0], a0 := w, the call of the strcat wrapper.
   0x8b788 (first pass): refuted by shent_ok_of_range at sup_host_setting_s5.v:1138, from range_addressable of tok[0]
     (hsb5_arr_now on hs_cx's token-array premise): the token executor decides the load8 check, report 0x8b8ec not
     reached. *)
paj_run_tok RUN HS HJ SHOK hsb5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64;
    apply unsigned_lit_small; lia | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    destruct (Hwcov a ltac:(lia)) as [(Hfp & Hbl) | Htmp].
    + right; left. split; [exact Hfp | exact Hbl].
    + right; right; left. exact Htmp.
  - apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wl + 1) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. rewrite <- (KEEP1 a Ha Hn).
  apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => wl <= a < wl + 1) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr;
      rewrite (EE 10%nat 10%bv eq_refl), R10 in Hrr || idtac; unfold w64 in Hrr;
      first [rewrite unsigned_lit_small in Hrr by lia; lia | lia]
    | exact Ha | exact Hn ]. }
(* words[0] = 0, from the region of the state at the call *)
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HRg.
pose proof (field_of_region_any _ _ _ wl _ _ _ _ _ 0 1 (SLit 0) HRg) as Hw0.
assert (Hw0'' : rdW Wc (ms_mem ms) wl = Some 0).
{ match type of Hw0 with ?A -> _ => assert (HA : A) end.
  { cbn [ew ewset Nat.eqb]. rewrite (EE 10%nat 10%bv eq_refl), R10. unfold w64. apply unsigned_lit_small. lia. }
  specialize (Hw0 HA (or_introl eq_refl) ltac:(cbn; lia)).
  cbn [ms_mem restrict] in Hw0. rewrite Z.add_0_r in Hw0.
  pose proof (hsb5_aval_mem_view SEGS (w_H Wc) (ms_mem ms) wl 1 _ Hw0 0%nat ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. rewrite Hb. reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 10%nat 10%bv eq_refl), R10 in P10. rewrite E32 in P11.
rewrite (EE 21%nat 21%bv eq_refl), R21 in P18. rewrite (EE 10%nat 10%bv eq_refl), R10 in P22.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P21. unfold w64 in P21. rewrite (hsb5_not (i_ptok x)) in P21 by lia.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (RGm : hs_regsL2 x fpos 0 wl (ms_regs ms)).
{ split; [|split; [exact P22|split; [exact P23|split; [exact P27|split; [exact P21|split; [exact P18|exact P20]]]]]].
  split; [exact P2|]. split; [exact P9|]. split; [exact P8|]. split; [exact P3|]. split; [exact P4|].
  split; [exact P24|]. split; [exact P25 | exact P26]. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* token 0 at the state of the call *)
destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms) mdw k CX HJ) as [HRODc _].
pose proof (hsb5_arg_now x fpos lyc Sc Wc (ms_mem ms) mdw k O1 _ Rest (hs_ptr x 0) (hs_tok x 0) CX HJ HBA HARG) as HAOK.
pose proof HAOK as (G1 & G2 & G3 & GSTR & GTl & GMR & GRA & GHU).
pose proof (proj1 HJ) as HARm.
(* token 0's live block (none of this call's), for strcat's band and word-separation premises (RtString.v
   astrcat_realizes, B BASE 2) *)
destruct (hs3_tok_blk B MT x fpos lyc Sc Wc (ms_mem ms) mdw k O1 _ Rest (hs_ptr x 0) (hs_tok x 0) CX HJ HBA HARG)
  as (tq & tm & Htq & Htq1 & Htq2 & HtNw).
assert (Htne : (tq, tm) <> (wl, LIVE_XMALLOC (hs_wsz x)))
  by (intros Etq; apply HtNw; rewrite Etq; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdw tq tm HARm Htq) as (_ & _ & _ & _ & _ & _ & Htm).
pose proof (req_size_pos tm ltac:(lia)) as [_ Htmr].
eapply SRr_bind.
{ eapply (hsb5_art_wr_at (2 * ESTACK)
    (fun a => wl + astr_len [] <= a < wl + astr_len [] + astr_len (hs_tok x 0) + 1)
    (SIG CS___interceptor_trampoline_strcat) Wc (ms_regs ms) (ms_mem ms) SUP_HOST_SETTING_STK (spZ (i_regs x))
    (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc mdw k
    (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (Z_to_bv 64 (BASE + HS_L2C)) wl _ _ HJ Qsp S1b ltac:(lia) ltac:(lia)
    ltac:(lia) P1 Hwin ltac:(intros a Ha; unfold astr_len in Ha; cbn [length] in Ha; lia) Hwcov).
  apply (hh_strcat B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw wl (hs_ptr x 0) [] (hs_tok x 0)).
  - eapply (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_HOST_SETTING_STK
      (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc Wc (ms_mem ms) mdw k
      (ms_regs ms) (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) HJ Qsp S1b ltac:(lia) ltac:(lia) ltac:(lia) HraT);
      [rewrite P3; exact Hgp | rewrite P4; exact Htp].
  - exact P10.
  - rewrite P11. reflexivity.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS). split; [|intros []].
    intros i Hi. cbn [length app] in Hi. assert (i = 0%nat) as -> by lia. rewrite Z.add_0_r, Hw0''. reflexivity.
  - apply (astr_atR_view SEGS). exact GSTR.
  - unfold astr_len. cbn [length]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [replace a with wl by lia; rewrite Hw0''; discriminate | unfold ascratch_stk; lia]. }
    split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl 1 HARm Hwin ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl 1 HARm Hwin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl 1 HARm Hwin ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* the destination string's band: wl's block *)
    apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl (astr_len []) HARm Hwin);
      unfold astr_len; cbn [length]; lia.
  - exact (hsb5_read_of_arg (2 * ESTACK) Wc (ms_mem ms) (ms_regs ms) (hs_ptr x 0) (hs_tok x 0) HAOK
      ltac:(rewrite Qsp; lia) ltac:(lia)).
  - (* the source string's band: token 0's block *)
    apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw tq tm (hs_ptr x 0) (astr_len (hs_tok x 0)) HARm Htq);
      unfold astr_len; lia.
  - unfold astr_len. cbn [length]. rewrite Z.add_0_r.
    split; [lia|]. split; [lia|]. split; [unfold LMAX in *; lia|]. split.
    { intros a Ha.
      destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdw wl _ HARm Hwin) as (_ & _ & _ & _ & Hpm & _).
      split; [|split].
      - apply (apresent_writable SEGS). exact (proj1 (Hpm a ltac:(lia))).
      - exact (proj2 (Hpm a ltac:(lia))).
      - unfold ascratch_stk. lia. }
    split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ wl (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* the written range's band: wl's block *)
    apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdw wl _ (wl + astr_len []) (astr_len (hs_tok x 0)) HARm Hwin);
      unfold astr_len; cbn [length]; lia.
  - (* the written range holds no read-only image byte: it is wl's heap block *)
    intros a Ha _. apply (hs3_heap_norom B lyc Sc Wc (ms_mem ms) mdw wl _ a HARm Hwin).
    unfold astr_len in Ha; cbn [length] in Ha; lia.
  - unfold astr_len. cbn [length]. rewrite Z.add_0_r.
    exact (hh_heap_tail B MT HH lyc Sc Wc (ms_mem ms) mdw wl _ wl HARm Hwin ltac:(lia)).
  - unfold astr_len. exact GTl.
  - unfold astr_len. cbn [length]. lia.
  - (* the destination tail does not start inside the token's last word: two live blocks, 16-aligned *)
    apply (hs3_word_sep B lyc Sc Wc (ms_mem ms) mdw tq tm wl _ (hs_ptr x 0) (astr_len (hs_tok x 0)) (wl + astr_len [])
      HARm Htq Hwin Htne); unfold astr_len in *; cbn [length] in *; lia.
  - exact (hsb5_rom_view Wc (ms_mem ms) HRODc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & HQb) & HK2).
(* back at 0x8b798: the word list holds token 0 *)
assert (HNDc : List.NoDup ([(b0, hs_b0 x); (b1, hs_b1 x); (wl, LIVE_XMALLOC (hs_wsz x))] ++ Rest))
  by exact (Permutation_NoDup BA1 (RecBLemmas.recb_ablocks_nodup_m B lyc Sc Wc memc mdc HARc)).
cbn [app] in HNDc.
apply List.NoDup_cons_iff in HNDc as [Hb0n HNDc].
apply List.NoDup_cons_iff in HNDc as [Hb1n HNDc].
apply List.NoDup_cons_iff in HNDc as [Hwn _].
assert (HNOTW : forall pn, In pn ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) -> pn <> (wl, LIVE_XMALLOC (hs_wsz x))).
{ intros pn Hpn E0. subst pn. destruct Hpn as [Hq | [Hq | Hpn]].
  - apply Hb1n. rewrite Hq. left. reflexivity.
  - apply Hb0n. rewrite Hq. right. left. reflexivity.
  - exact (Hwn (BA7 _ Hpn)). }
assert (KEEPW : forall a, 0 <= a < 2 ^ 64 -> ~ (hs_sp1 (spZ (i_regs x)) - 8192 <= a < hs_sp1 (spZ (i_regs x))) ->
  ~ (wl <= a < wl + hs_wsz x) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw Hwl. rewrite (HK2 a Ha ltac:(lia) ltac:(cbv beta; unfold astr_len; cbn [length]; lia)).
  apply KEEP2; lia. }
assert (KEEPR : forall a, hs_in_rec a \/ hs_in_own ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) a ->
  rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. destruct (hsb5_rec_low lyc Sc Wc memc mdc _ _ _ a HARc REP Ha) as [Hl0 Hl1].
  apply KEEPW; [lia | lia |]. intros Hw.
  destruct Ha as [Hrec | (pn & Hpn & Hr)].
  - assert (Hpg : Exists (in_zr a) recb_PG).
    { unfold hs_in_rec in Hrec. destruct Hrec as [Hg | Hs]; [apply hs3_grec_in | apply hs3_spill_in]; lia. }
    exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc wl _ a HARc Hwin ltac:(lia) (hh_prog_img B MT HH a Hpg)).
  - destruct pn as [q m]. cbn [fst snd] in Hr.
    pose proof (proj1 (hs_rec_own B _ _ _ _ _ REP (q, m) Hpn)) as Hqm.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc Hqm) as (_ & _ & _ & _ & _ & _ & Hmr).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr2].
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m wl _ HARc Hqm Hwin (HNOTW (q, m) Hpn)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Hfw : hs_F x fpos + 64 <= wl \/ wl + hs_wsz x <= hs_F x fpos).
{ pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc wl _ 0 fpos HARc Hwin HFin) as Hd.
  rewrite EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
apply (HL2 fpos lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 b1 wl ltac:(lia) CX FXR).
- apply (hsb5_mid_keep x fpos lyc Sc Wc memc mdc mem2 md2 k _ _ _ O1 _ Rest MID HJ2);
    intros a Ha; (apply KEEPW; [lia | lia | lia]).
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ REP); [exact KEEPR|].
  intros pn H. exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H)).
- apply (hsb5_spill_keep x fpos (rdW Wc memc)); [exact SPL|]. intros a Ha. apply KEEPW; lia.
- rewrite (hsb5_join_one (i_toks x) ltac:(lia)). change (nth 0 (i_toks x) []) with (hs_tok x 0).
  split; [|exact (proj2 GSTR)].
  apply (abytes_atR_view SEGS). rewrite app_nil_l in HQb. exact HQb.
- exact Hw4096.
- exact (hsb5_regsL2_pres x fpos 0 wl (ms_regs ms) regs2 RGm HP2).
Qed.
End e.
End f.
End d.
