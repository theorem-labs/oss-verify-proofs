(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 1261 of its 1318 lines of code are new or changed and 684 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): _s19 of the walk of the test
   harness's entry function LLVMFuzzerTestOneInput (0x84d34): segment S10, K8559c -> K856bc (lt_seg_S10_stmt of
   LLVMFuzzerTestOneInput_defs.v).
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep, output in the walk's shared brief; checker (fresh, read-only): CONFIRM; none:
   written new); this file is one segment lemma of its walk.
   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s lines 540-611, 1048-1052, 1120-1123; listing
   SegList.v lines 587-658):
   - 0x8559c sd s11,152(s1) (SH(m + 0x2000)); a0 = c, a1 = m; jal check_refusals (0x855a8).
   - 0x855ac s3 = m + 0x23ac (&m->n_kept), s2 = SH(s3); check 21 (lb 0(s2), its 4-byte slow block 0x85d8c); a0 =
     n_kept; a4 = m; blez a0 -> 0x856bc.
   - 0x855d4 .. 0x8562c: s4 = 0, s6 = c + 0x34c8 (&c->n_refusals), s9 = c->refusal[0], s10 = m->kept[0], s7 = s8 =
     &m->kept_knock[0], s11 = SH(s6), s5 / 136(s1) the slow blocks' bounds.
   - head 0x85630: check 22 (lb 0(s11)); bge s4, n_refusals -> 0x856bc; check_address(s9, s10) (0x85648); check 23
     (SH(s7)); check_knock_refused(s9, kept_knock[i]) (0x85668); check 24 (lb 0(s2)); i += 1; the four pointers
     step; blt i, n_kept -> head; j 0x856bc.
   Every check's byte lies in c or m: a shadow entry of the block covers it, so the runner reads 0 and the slow
   blocks and the error calls (0x85d9c, 0x85eb0, 0x85eb8, 0x856b8) are never reached. n_refusals = n_kept (the
   model's check_refusals), so the head's bge falls through on every turn the latch took. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegObj SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
check_refusals_c check_address_c check_knock_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s19k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the points of the segment (offsets from BASE = 0x84d34) ---- *)
Definition LO_CRRA : Z := 0x878.   (* 0x855ac: check_refusals returned *)
Definition LO_CARA : Z := 0x918.   (* 0x8564c: check_address returned *)
Definition LO_CKRA : Z := 0x938.   (* 0x8566c: check_knock_refused returned *)

(* ---- the symbolic states ----
   Atom 32 is the shadow base (the word at 176(s1)); the other extra atoms are named per state. *)
Definition S19x : sv := SOff 32 0.
Definition S19span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow byte's address of atom a, as the code forms it: (a >> 3) + the base *)
Definition s19_shx (a : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff a 0) (SLit 3)) (SOff 32 0).
(* A, at 0x8559c: atoms 33 = c, 34 = m; the frame's slots 152 (written) and 160, 168 (c, m) *)
Definition s19_rgA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 176 152 160
    [YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0))].
Definition s19_factsA : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_A : sstate := mkSS LO_K8559c sr_atoms [s19_rgA] None s19_factsA.
(* B, at 0x855ac (check_refusals returned): atoms 33 = c, 34 = m, 35 = n (n_kept = n_refusals); the frame's slots
   136 (written), 160 c, 168 m, 176 the shadow base, 184 &m->n; m->n_kept and c->n_refusals; the shadow entries of
   the 8 bytes from each (checks 21, 22); n in [nlo, nhi] *)
Definition s19_rgBf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 192 136 144
    [YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0));
     YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 34 0x2000))].
Definition s19_rgBm : YP09.region := YP09.mkRegion (Some 34%nat) 0x23ac 0x23b0 0 0 [YP09.mkChunk 0x23ac (CVal 4 (SOff 35 0))].
Definition s19_rgBc : YP09.region := YP09.mkRegion (Some 33%nat) 0x34c8 0x34cc 0 0 [YP09.mkChunk 0x34c8 (CVal 4 (SOff 35 0))].
Definition s19_factsB (nlo nhi : Z) : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (33%nat, mkAF 4096 0x7fffff800000 0); (34%nat, mkAF 4096 0x7fffff800000 0); (35%nat, mkAF nlo nhi 0)] [] [].
Definition ss_B (nlo nhi : Z) : sstate :=
  mkSS LO_CRRA sr_atoms [s19_rgBf; s19_rgBm; s19_rgBc] None (s19_factsB nlo nhi).
Definition s19_SHB : list shent := [mkSHE 34 0x23ac 0x23b4; mkSHE 33 0x34c8 0x34d0].
(* L, at 0x8564c and 0x8566c (the two returns of the loop body): every register its own atom but s2 = SH(s3) and
   s11 = SH(s6) as the code formed them; atoms 33 = n, 34 = kept_knock[i]; the shadow base at 176(s1),
   kept_knock[i] at s8, m->n_kept at s3, c->n_refusals at s6; the shadow entries of the 8 bytes from s3, s6 and
   s7 (checks 24, 22, 23); i = s4 in [0, 7], n in [1, 8] *)
Definition s19_rgLf : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition s19_rgLk : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition s19_rgLn : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition s19_rgLr : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition s19_factsL : facts :=
  mkFacts [(19%nat, mkAF 4096 0x7fffff800000 0); (22%nat, mkAF 4096 0x7fffff800000 0);
    (23%nat, mkAF 4096 0x7fffff800000 0); (20%nat, mkAF 0 7 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (33%nat, mkAF 1 8 0); (34%nat, mkAF 0 1 0)] [] [].
Definition s19_srL : list sv := sr_set (sr_set sr_atoms 18%bv (s19_shx 19)) 27%bv (s19_shx 22).
Definition ss_L (pc : Z) : sstate := mkSS pc s19_srL [s19_rgLf; s19_rgLk; s19_rgLn; s19_rgLr] None s19_factsL.
Definition s19_SHL : list shent := [mkSHE 19 0 8; mkSHE 22 0 8; mkSHE 23 0 8].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s19_E (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).

Lemma s19_E_reg : forall regs xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s19_E regs xs) n = getr regs r.
Proof.
intros regs xs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s19_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma s19_E_extra : forall regs xs j, (j < length xs)%nat -> (32 + j < A_TEXT)%nat ->
  ew (s19_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j Hj Hj2. unfold s19_E. rewrite Eimg_low by exact Hj2.
rewrite ew_Ereg_extra. apply map_nth.
Qed.

(* a word read through the reader is a 64-bit value *)
Lemma s19_rdword_rng : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v E. unfold rdword in E.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng _ _ _ _ _ E0). pose proof (sa_aview_rng _ _ _ _ _ E1).
pose proof (sa_aview_rng _ _ _ _ _ E2). pose proof (sa_aview_rng _ _ _ _ _ E3).
pose proof (sa_aview_rng _ _ _ _ _ E4). pose proof (sa_aview_rng _ _ _ _ _ E5).
pose proof (sa_aview_rng _ _ _ _ _ E6). pose proof (sa_aview_rng _ _ _ _ _ E7).
lia.
Qed.

(* an 8-byte chunk of a region, from the word the reader holds there *)
Lemma s19_chunk8 : forall (W : world SEGS) mem E base off (n : nat) d x v,
  ew E n = Z_to_bv 64 x -> v = x + d -> rdword (rdW W mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n d))).
Proof.
intros W mem E base off n d x v En Hv Hrd.
pose proof (s19_rdword_rng _ _ _ _ Hrd) as R.
apply (chunk_ok_val SEGS E _ base off 8 _ v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R | zside |].
- cbn [sv_denot]. rewrite En. subst v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hrd).
Qed.

(* ---- seed A: the state at 0x8559c is an instance of ss_A ---- *)
Lemma s19_seedA : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 c m,
  getr regs 9 = w64 s1 -> 0x7fff7f800000 <= s1 -> s1 + 192 <= 2 ^ 47 ->
  (forall a, s1 + 152 <= a < s1 + 160 -> apresent (w_H W) mem a) ->
  rdword (rdW W mem) (s1 + 160) = Some c -> rdword (rdW W mem) (s1 + 168) = Some m ->
  st_ok_pi SEGS VAL (s19_E regs [SHADOW_OFF; c; m]) ss_A
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K8559c)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S19x [] (s19_E regs [SHADOW_OFF; c; m]) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s1 c m R9 Hs1 Hs1' Hpres Hc Hm.
set (E := s19_E regs [SHADOW_OFF; c; m]).
assert (E9 : ew E 9 = w64 s1) by exact (eq_trans (s19_E_reg regs _ 9 9%bv eq_refl) R9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by exact (s19_E_extra regs [SHADOW_OFF; c; m] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by exact (s19_E_extra regs [SHADOW_OFF; c; m] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by exact (s19_E_extra regs [SHADOW_OFF; c; m] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
unfold ss_A. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, s19_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, s19_rgA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (s19_chunk8 W mem E s1 160 33 0 c c E33 ltac:(lia) Hc).
  + apply (s19_chunk8 W mem E s1 168 34 0 m m E34 ltac:(lia) Hm).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [s19_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* a 4-byte value read through the reader is a value of the restricted memory *)
Lemma s19_val_mem : forall H mem a n v, sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
      | change (YG0f.le_byte v n k) with (YO0f.le_byte v n k) in *; rewrite <- Hv
      | change (YO0f.le_byte v n k) with (YG0f.le_byte v n k) in *; rewrite <- Hv
      | unfold YG0f.le_byte, YO0f.le_byte in *; rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma s19_chunk4 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sa_val (rdW W mem) (base + off) 4 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 4 _ v); [| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hv | zside |].
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (s19_val_mem _ _ _ 4 _ Hrd).
Qed.
Lemma s19_regs_ok_set : forall E sr regs (r : bv 5) e, regs_ok E sr regs -> bv_eqb r 0 = false ->
  getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'. specialize (Hr r'). unfold sr_set. rewrite Hr0.
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
Qed.
Lemma s19_shx_denot : forall E (a : nat) x, ew E a = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> sv_denot E (s19_shx a) = Z_to_bv 64 (shadow_addr x).
Proof.
intros E a x Ea Hx E32. apply bv_eq.
change (bv_unsigned (sv_denot E (s19_shx a))) with (U E (s19_shx a)). unfold s19_shx.
rewrite U_SAlu, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a x Ea) by lia. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia).
rewrite U_lit by lia. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold shadow_addr, SHADOW_OFF, zcanon, M64.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small (x / 8)) by lia. rewrite Z.mod_small by lia.
rewrite unsigned_lit_small by lia. lia.
Qed.
(* the shadow entry of [p + lo, p + hi), inside a live heap block whose shadow is addressable *)
Lemma s19_shent : forall (W : world SEGS) mem E (mt : nat) b n p lo hi,
  range_addressable (rdW W mem) SHADOW_OFF b n -> in_app b n ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E mt = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  b <= p + lo -> p + hi <= b + n -> lo < hi ->
  shent_ok SEGS S19x E (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros W mem E mt b n p lo hi Hra Happ E32 Em Hp Hlo Hhi Hlh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (shent_ok_of_range SEGS (w_H W) mem E S19x mt b n p lo hi Hra).
- unfold S19x. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
- apply (U_atom E mt p Em Hp).
- exact Hlo.
- exact Hhi.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ.
  unfold SHADOW_OFF. lia.
Qed.
(* the shadow byte's address the code forms from atom a + d *)
Lemma s19_shxd_denot : forall E (a : nat) d x, ew E a = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + d < 2 ^ 47 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a d) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (shadow_addr (x + d)).
Proof.
intros E a d x Ea Hx Hxd E32. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a d) (SLit 3)) (SOff 32 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a d) (SLit 3)) (SOff 32 0))).
rewrite U_SAlu, U_SAlu. cbn [zalu_raw].
rewrite U_SOff, Ea, unsigned_lit_small by lia.
rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia).
rewrite U_lit by lia. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold shadow_addr, SHADOW_OFF, zcanon, M64.
rewrite (Z.mod_small (x + d)) by lia.
pose proof (Z.div_pos (x + d) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (x + d) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small ((x + d) / 8)) by lia. rewrite Z.mod_small by lia.
rewrite unsigned_lit_small by lia. lia.
Qed.
(* a register of a symbolic state, its value as the run left it (prreg without its normalisation) *)
Ltac s19_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.


(* ---- seed B: the state at 0x855ac is an instance of ss_B nlo nhi ---- *)
Lemma s19_seedB : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 c m n nlo nhi,
  getr regs 9 = w64 s1 -> alloc_ceiling <= s1 -> s1 + 192 <= 2 ^ 47 ->
  (forall a, s1 + 136 <= a < s1 + 144 -> apresent (w_H W) mem a) ->
  rdword (rdW W mem) (s1 + 160) = Some c -> rdword (rdW W mem) (s1 + 168) = Some m ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF -> rdword (rdW W mem) (s1 + 184) = Some (m + seg_spec.MC_N) ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= alloc_ceiling -> 4096 <= m -> m + seg_spec.SEG_M_SIZE <= alloc_ceiling ->
  c + seg_spec.SEG_C_SIZE <= m \/ m + seg_spec.SEG_M_SIZE <= c ->
  range_addressable (rdW W mem) SHADOW_OFF c seg_spec.SEG_C_SIZE -> in_app c seg_spec.SEG_C_SIZE ->
  range_addressable (rdW W mem) SHADOW_OFF m seg_spec.SEG_M_SIZE -> in_app m seg_spec.SEG_M_SIZE ->
  sa_val (rdW W mem) (m + seg_spec.MC_NKEPT) 4 n -> sa_val (rdW W mem) (c + seg_spec.RC_NREF) 4 n ->
  0 <= nlo -> nlo <= n <= nhi -> nhi < 2 ^ 31 ->
  st_ok_pi SEGS VAL (s19_E regs [SHADOW_OFF; c; m; n]) (ss_B nlo nhi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_CRRA)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S19x s19_SHB (s19_E regs [SHADOW_OFF; c; m; n]) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s1 c m n nlo nhi R9 Hs1 Hs1' Hpres Hc Hm Hsb Hmn Hc4 Hcc Hm4 Hmc Hcm Hrc Hac Hrm Ham Hnm Hnc Hnlo Hn Hnhi.
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, seg_spec.MC_N, seg_spec.MC_NKEPT, seg_spec.RC_NREF in *.
set (E := s19_E regs [SHADOW_OFF; c; m; n]).
assert (E9 : ew E 9 = w64 s1) by exact (eq_trans (s19_E_reg regs _ 9 9%bv eq_refl) R9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by exact (s19_E_extra regs [SHADOW_OFF; c; m; n] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by exact (s19_E_extra regs [SHADOW_OFF; c; m; n] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by exact (s19_E_extra regs [SHADOW_OFF; c; m; n] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by exact (s19_E_extra regs [SHADOW_OFF; c; m; n] 3 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = m) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = n) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- unfold ss_B. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, s19_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold YP09.region_ok, s19_rgBf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- exact (s19_chunk8 W mem E s1 160 33 0 c c E33 ltac:(lia) Hc).
      -- exact (s19_chunk8 W mem E s1 168 34 0 m m E34 ltac:(lia) Hm).
      -- exact (s19_chunk8 W mem E s1 176 32 0 SHADOW_OFF SHADOW_OFF E32 ltac:(lia) Hsb).
      -- exact (s19_chunk8 W mem E s1 184 34 0x2000 m (m + 8192) E34 ltac:(lia) Hmn).
    * unfold YP09.region_ok, s19_rgBm. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. exact (s19_chunk4 W mem E m 0x23ac 35 n E35 ltac:(lia) Hnm).
    * unfold YP09.region_ok, s19_rgBc. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. exact (s19_chunk4 W mem E c 0x34c8 35 n E35 ltac:(lia) Hnc).
  + apply pairwise_disjoint_of_extents. unfold s19_rgBf, s19_rgBm, s19_rgBc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U34.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
  + split; [|split; [exact I | exact I]].
    cbn [s19_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U33, U34, U35, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, s19_SHB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (s19_shent W mem E 34 m 9236 m 0x23ac 0x23b4 Hrm Ham E32 E34); lia.
  + apply (s19_shent W mem E 33 c 16616 c 0x34c8 0x34d0 Hrc Hac E32 E33); lia.
Qed.

(* ---- seed L: the state at a return point of the loop body (pc) is an instance of ss_L pc ---- *)
Lemma s19_seedL : forall (W : world SEGS) (regs : bvmap 5 word) mem pc s1 c m n i kn,
  getr regs 9 = w64 s1 -> alloc_ceiling <= s1 -> s1 + 192 <= 2 ^ 47 ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_NKEPT)) -> getr regs 19 = w64 (m + seg_spec.MC_NKEPT) ->
  getr regs 20 = w64 (Z.of_nat i) -> getr regs 22 = w64 (c + seg_spec.RC_NREF) ->
  getr regs 23 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) ->
  getr regs 24 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) ->
  getr regs 27 = w64 (shadow_addr (c + seg_spec.RC_NREF)) ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= alloc_ceiling -> 4096 <= m -> m + seg_spec.SEG_M_SIZE <= alloc_ceiling ->
  c + seg_spec.SEG_C_SIZE <= m \/ m + seg_spec.SEG_M_SIZE <= c ->
  range_addressable (rdW W mem) SHADOW_OFF c seg_spec.SEG_C_SIZE -> in_app c seg_spec.SEG_C_SIZE ->
  range_addressable (rdW W mem) SHADOW_OFF m seg_spec.SEG_M_SIZE -> in_app m seg_spec.SEG_M_SIZE ->
  sa_val (rdW W mem) (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) 4 kn ->
  sa_val (rdW W mem) (m + seg_spec.MC_NKEPT) 4 n -> sa_val (rdW W mem) (c + seg_spec.RC_NREF) 4 n ->
  (i < 8)%nat -> 1 <= n <= 8 -> 0 <= kn <= 1 ->
  st_ok_pi SEGS VAL (s19_E regs [SHADOW_OFF; n; kn]) (ss_L pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S19x s19_SHL (s19_E regs [SHADOW_OFF; n; kn]) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc s1 c m n i kn R9 Hs1 Hs1' Hsb R18 R19 R20 R22 R23 R24 R27 Hc4 Hcc Hm4 Hmc Hcm Hrc Hac Hrm Ham
  Hkn Hnm Hnc Hi Hn Hk.
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.RC_NREF in *.
set (E := s19_E regs [SHADOW_OFF; n; kn]).
assert (EE : forall k (r : bv 5) v, Z.of_nat k = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  ew E k = Z_to_bv 64 v /\ bv_unsigned (ew E k) = v).
{ intros k r v Hk0 Hr Hv. assert (Ek : ew E k = getr regs r) by exact (s19_E_reg regs _ k r Hk0).
  rewrite Ek, Hr. split; [reflexivity|]. apply unsigned_lit_small. exact Hv. }
destruct (EE 9%nat 9%bv s1 eq_refl R9 ltac:(lia)) as [E9 U9].
destruct (EE 19%nat 19%bv _ eq_refl R19 ltac:(lia)) as [E19 U19].
destruct (EE 20%nat 20%bv _ eq_refl R20 ltac:(lia)) as [E20 U20].
destruct (EE 22%nat 22%bv _ eq_refl R22 ltac:(lia)) as [E22 U22].
destruct (EE 23%nat 23%bv _ eq_refl R23 ltac:(lia)) as [E23 U23].
destruct (EE 24%nat 24%bv _ eq_refl R24 ltac:(lia)) as [E24 U24].
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by exact (s19_E_extra regs [SHADOW_OFF; n; kn] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by exact (s19_E_extra regs [SHADOW_OFF; n; kn] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 kn) by exact (s19_E_extra regs [SHADOW_OFF; n; kn] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = kn) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- unfold ss_L. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold s19_srL. apply s19_regs_ok_set; [apply s19_regs_ok_set; [unfold E, s19_E; apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
    * rewrite R18. symmetry. exact (s19_shx_denot E 19 _ E19 ltac:(lia) E32).
    * rewrite R27. symmetry. exact (s19_shx_denot E 22 _ E22 ltac:(lia) E32).
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil;
      unfold YP09.region_ok, s19_rgLf, s19_rgLk, s19_rgLn, s19_rgLr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. exact (s19_chunk8 W mem E s1 176 32 0 SHADOW_OFF SHADOW_OFF E32 ltac:(lia) Hsb).
    * rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (s19_chunk4 W mem E _ 0 34 kn E34 ltac:(lia)). rewrite Z.add_0_r. exact Hkn.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (s19_chunk4 W mem E _ 0 33 n E33 ltac:(lia)). rewrite Z.add_0_r. exact Hnm.
    * rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (s19_chunk4 W mem E _ 0 33 n E33 ltac:(lia)). rewrite Z.add_0_r. exact Hnc.
  + apply pairwise_disjoint_of_extents. unfold s19_rgLf, s19_rgLk, s19_rgLn, s19_rgLr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U22, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
  + split; [|split; [exact I | exact I]].
    cbn [s19_factsL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U22, U23, U20, U33, U34, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, s19_SHL. repeat apply Forall_cons; try apply Forall_nil.
  + apply (s19_shent W mem E 19 m 9236 (m + 9132) 0 8 Hrm Ham E32 E19); lia.
  + apply (s19_shent W mem E 22 c 16616 (c + 13512) 0 8 Hrc Hac E32 E22); lia.
  + apply (s19_shent W mem E 23 m 9236 (m + 9100 + 4 * Z.of_nat i) 0 8 Hrm Ham E32 E23); lia.
Qed.

(* ---- what a state change of the segment keeps: every byte below the allocation ceiling (the image, the heap
   blocks, the side-stack frames and every shadow byte of them) reads the same ---- *)
Definition s19_low (rd rd' : reader) : Prop := forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.

Lemma s19_rdword_kept : forall (rd rd' : reader) a v, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a HK). exact H. Qed.
Lemma s19_val_kept : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite (HK k Hk). exact (H k Hk). Qed.
Lemma s19_bytes_kept : forall (rd rd' : reader) a bs,
  (forall i, (i < length bs)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite (HK i Hi). exact (H i Hi). Qed.
Lemma s19_strz_kept : forall (rd rd' : reader) p s,
  (forall i, (i <= length s)%nat -> rd' (p + Z.of_nat i) = rd (p + Z.of_nat i)) -> sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' p s HK [Hz Hn]. split; [|exact Hn]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (HK i ltac:(lia)). apply Hz. rewrite length_app. cbn [length]. lia.
Qed.
Lemma s19_str_low : forall (rd rd' : reader) p s, s19_low rd rd' -> 0 <= p ->
  p + Z.of_nat (length s) + 8 <= alloc_ceiling -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HL Hp Hb [Hz Ht]. split.
- apply (s19_strz_kept rd); [|exact Hz]. intros i Hi. apply HL. lia.
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite (HL x) by lia. exact (Ht x Hx).
Qed.
(* every byte of an image object lies below the low memory's end *)
Lemma s19_img_lo : forall (B : asyms) q n x, sa_img SEGS B q n -> q <= x < q + n -> 0 <= x < kLowMemEnd.
Proof. intros B q n x H Hx. destruct (H x Hx) as (Hi & _ & _). exact (pa_segs_low x Hi). Qed.
Lemma s19_lit_low : forall (B : asyms) (rd rd' : reader) a s, s19_low rd rd' ->
  sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros B rd rd' a s HL (H0 & Hs & Hp & Hr & Hi).
pose proof (s19_img_lo B a (Z.of_nat (length s) + 1) (a + Z.of_nat (length s)) Hi ltac:(lia)) as Hlo.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [exact H0|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (s19_str_low rd); [exact HL | lia | rewrite C5 in Hlo; lia | exact Hs].
Qed.
Lemma s19_addr_low : forall (rd rd' : reader) q n, s19_low rd rd' -> 0 <= q -> q + n <= 2 ^ 47 ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HL Hq Hn (H0 & H63 & Hm & Hra & Hv).
pose proof asan_consts as (C1 & _).
split; [exact H0|]. split; [exact H63|]. split; [exact Hm|]. split.
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
  rewrite (HL (shadow_of_addr SHADOW_OFF x)); [exact Hs|].
  unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
- intros Hn0 s Hs. rewrite (HL s); [exact (Hv Hn0 s Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (q + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
(* the image facts of a point carry over to any reader that agrees below the allocation ceiling *)
Lemma s19_img_low : forall (B : asyms) cx (rd rd' : reader), s19_low rd rd' -> lt_img B cx rd -> lt_img B cx rd'.
Proof.
intros B cx rd rd' HL (Haro & Hh & Hgi).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [|split].
- intros a Hro Ho He. rewrite (HL a); [exact (Haro a Hro Ho He)|].
  destruct Hro as [(sg & Hsg & _ & Ha) | Ha].
  + pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Ha))) as Hl. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
- destruct Hh as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  refine (conj _ (conj H2 (conj _ (conj _ (conj _ (conj H6 (conj _ (conj _ (conj _ H10))))))))).
  + apply (s19_val_kept rd); [|exact H1]. intros k Hk. apply HL. unfold mod40A. lia.
  + intros s Hs. destruct (H3 s Hs) as [Hl Ha]. exact (conj (s19_lit_low B rd rd' _ s HL Hl) Ha).
  + intros s Hs. destruct (H4 s Hs) as [Hl Ha]. exact (conj (s19_lit_low B rd rd' _ s HL Hl) Ha).
  + destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi'. destruct (Hr i Hi') as (tp & Ht & Hl). exists tp. split; [|exact (s19_lit_low B rd rd' _ _ HL Hl)].
    apply (s19_rdword_kept rd); [|exact Ht]. intros k Hk. apply HL.
    unfold pin_spec.CAT_N in Hi'. unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA. lia.
  + destruct H7 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi'. destruct (Hr i Hi') as (wp & Ht & Hl). exists wp. split; [|exact (s19_lit_low B rd rd' _ _ HL Hl)].
    apply (s19_rdword_kept rd); [|exact Ht]. intros k Hk. apply HL. unfold wordsA. lia.
  + destruct H8 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hi'. apply (s19_val_kept rd); [|exact (Hr i Hi')]. intros k Hk. apply HL. unfold rolesA. lia.
  + destruct H9 as (Hg & g & Hg2). split.
    * apply (s19_rdword_kept rd); [|exact Hg]. intros k Hk. apply HL. unfold gotwA. lia.
    * exists g. apply (s19_rdword_kept rd); [|exact Hg2]. intros k Hk. apply HL. unfold guardA. lia.
- intros i Hi. rewrite (HL (longlA + LONGL_W + i)) by (unfold longlA, A_LONGL, LONGL_W; lia). exact (Hgi i Hi).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws are a theorem (lib/Reusable/YG0q.v) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the walk's hypotheses: the meter's law for a side-stack frame's state change, the listing's program call targets
   (closed at image A by SegRecRest.seg_sig_prog_PB), and the three callees' contracts at every FP state *)
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HCR : forall fx0 : YK11.FPState,
  check_refusals_contract (fx := fx0) SEGS B (BASE + AF_check_refusals) STK_check_refusals.
Hypothesis HCA : forall fx0 : YK11.FPState,
  check_address_contract (fx := fx0) SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Hypothesis HCK : forall fx0 : YK11.FPState,
  check_knock_refused_contract (fx := fx0) SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the entry's sp and the base register s1 *)
Lemma s19_bounds : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold STK_LLVMFuzzerTestOneInput in Hslo.
unfold x_s1, x_sp0, LT_FRAME. set (s := spZ (x_regs cx)) in *.
pose proof (Z.div_mod s 16 ltac:(lia)) as D1. pose proof (Z.div_mod (s - 320) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (s - 320) 32 ltac:(lia)) as M2.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (s - 320 - (s - 320) mod 32) with ((s - 320) / 32 * 32) by lia. apply Z.mod_mul. lia.
- lia.
Qed.

(* what every point of the segment holds: the cut's core with c and m the live harness blocks, the slots of
   the file loop's list, and c and m holding SegModel.run of the payload (LT_K8559c_stmt's premises but s11) *)
Definition s19_inv (cx : lcx) ly S (W : world SEGS) regs mem md k acc (c m : Z) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem) (LT_L cx c m) /\ lt_cm (rdW W mem) c m (x_run cx).

Lemma s19_LT_L_offs : forall cx c m o v, In (o, v) (LT_L cx c m) ->
  In o [8; 16; 24; 32; 40; 48; 56; 64; 72; 80; 88; 96; 104; 144; 160; 168; 184].
Proof.
intros cx c m o v Hin. change [8; 16; 24; 32; 40; 48; 56; 64; 72; 80; 88; 96; 104; 144; 160; 168; 184]
  with (map fst (LT_L cx c m)). exact (in_map fst _ (o, v) Hin).
Qed.

(* a state the segment reaches keeps the invariant: same journal from the entry, sp / gp / tp / s0 / s1, the same
   live blocks, the meter, and every byte outside the callees' windows below s1 and the two slots the code writes
   (136, 152) *)
Lemma s19_keep : forall cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2,
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ASTACK <= a < x_s1 cx) -> ~ (x_s1 cx + 136 <= a < x_s1 cx + 144) ->
     ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W2 mem2 a = rdW W mem a) ->
  s19_inv cx ly2 S2 W2 regs2 mem2 md2 k acc c m.
Proof.
intros cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2 HBASE HINV HJ2 R2 R3 R4 R8 R9 HPERM HMO HK.
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
destruct HINV as (HCORE & HC & HM & HSL & HCM).
destruct HCORE as (HFR & HIMG & HBL & HBUD).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & FSV & FH0 & FH8 & FH16 & FFL & F176 & FSH).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR.
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)).
{ destruct HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. left. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HFin) as (Hf4 & Hfc & _).
change (fs_frame_bytes LT_FCLS) with 512 in Hfc.
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold x_fr, frame_addr. rewrite HF. reflexivity. }
rewrite HFA in Hf4, Hfc.
assert (HL : s19_low (rdW W mem) (rdW W2 mem2)).
{ intros a Ha. apply HK; unfold ASTACK in *; lia. }
assert (HS1 : forall a, x_s1 cx <= a < 2 ^ 64 -> ~ (x_s1 cx + 136 <= a < x_s1 cx + 144) ->
  ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha H1 H2. apply HK; [lia | lia | exact H1 | exact H2]. }
assert (HBLK : forall p n, In (p, n) (ablocks B ly S) -> 0 <= p /\ p + n <= alloc_ceiling).
{ intros p n Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
  unfold req_size in Hc. destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En|]; lia. }
assert (HCb := HBLK c seg_spec.SEG_C_SIZE (proj1 HC)). assert (HMb := HBLK m seg_spec.SEG_M_SIZE (proj1 HM)).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in HCb, HMb.
assert (HPin : forall p n, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2))
  by (intros p n Hin; exact (Permutation_in _ (Permutation_sym HPERM) Hin)).
split; [split; [|split; [|split]]|split; [|split; [|split]]].
- (* lt_frame *)
  split; [exact HJ2|]. split; [rewrite R2; exact F2|]. split; [rewrite R3; exact F3|]. split; [rewrite R4; exact F4|].
  split; [rewrite R8; exact F8|]. split; [rewrite R9; exact F9|].
  split.
  { intros i r Hi. apply (s19_rdword_kept (rdW W mem)); [|exact (FSV i r Hi)].
    assert (Hi13 : (i < length LT_SAVED)%nat)
      by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
    change (length LT_SAVED) with 13%nat in Hi13.
    intros kk Hk. apply HS1; lia. }
  split; [apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HL; lia | exact FH0]|].
  split; [apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HL; lia | exact FH8]|].
  split; [apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HL; lia | exact FH16]|].
  split; [apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HL; unfold LT_FLAGW; lia | exact FFL]|].
  split; [apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HS1; lia | exact F176]|].
  intros i Hi. rewrite lt_fsh_len in Hi. rewrite (HL (x_sh cx + Z.of_nat i)); [exact (FSH i ltac:(rewrite lt_fsh_len; exact Hi))|].
  unfold x_sh, shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_lt_upper_bound (x_fr cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)). lia.
- exact (s19_img_low B cx _ _ HL HIMG).
- unfold lt_blocks in *. exact (Permutation_trans HPERM HBL).
- destruct HBUD as (Hk0 & Hr0 & Hkr & _ & Hacc & Hxm). unfold lt_bud. repeat (split; [assumption|]). exact Hxm.
- destruct HC as (Hin & H4 & H16 & Ha). split; [exact (HPin _ _ Hin)|]. split; [exact H4|]. split; [exact H16|].
  apply (s19_addr_low (rdW W mem)); [exact HL | lia | unfold seg_spec.SEG_C_SIZE; lia | exact Ha].
- destruct HM as (Hin & H4 & H16 & Ha). split; [exact (HPin _ _ Hin)|]. split; [exact H4|]. split; [exact H16|].
  apply (s19_addr_low (rdW W mem)); [exact HL | lia | unfold seg_spec.SEG_M_SIZE; lia | exact Ha].
- intros o v Hin. apply (s19_rdword_kept (rdW W mem)); [|exact (HSL o v Hin)].
  pose proof (s19_LT_L_offs cx c m o v Hin) as Ho. intros kk Hk.
  apply HS1; cbn [In] in Ho; repeat (destruct Ho as [<- | Ho]; [lia|]); destruct Ho.
- destruct HCM as [(bs & Hb & He) (bm & Hbm & Hem)]. split.
  + exists bs. split; [|exact He]. apply (s19_bytes_kept (rdW W mem)); [|exact Hb]. intros i Hi.
    destruct He as (Hl & _). apply HL. unfold seg_spec.SEG_C_SIZE in Hl. lia.
  + exists bm. split; [|exact Hem]. apply (s19_bytes_kept (rdW W mem)); [|exact Hbm]. intros i Hi.
    destruct Hem as (Hl & _). apply HL. unfold seg_spec.SEG_M_SIZE in Hl. lia.
Qed.

(* a program call from a point of the segment (sp = s1), to a callee with no footprint and no allocator event
   whose post keeps every byte outside its window (check_refusals, check_address, check_knock_refused: their
   contracts' sa_kept / sa_noalloc), through cl_callS; back at ra the walk's journal holds again *)
Lemma s19_call : forall cx ly S W regs mem md k o (STKF AF ret : Z) Q,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 0 <= STKF <= ASTACK ->
  getr regs 1 = w64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall ch, afn_pre SEGS B STKF ly S W regs mem md ch ->
     SRr SEGS W (cfg_at SEGS AF regs mem md)
       (apost_base SEGS B STKF [] regs ly S W mem md 0
          (fun ly' S' W' regs' mem' md' =>
             sa_kept SEGS W mem W' mem' regs STKF (fun _ => False) /\ sa_noalloc B ly S ly' S'))) ->
  (forall ly2 S2 W2 regs2 mem2 md2, wle W W2 ->
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
       (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
     aregs_preserved regs regs2 ->
     sa_kept SEGS W mem W2 mem2 regs STKF (fun _ => False) -> sa_noalloc B ly S ly2 S2 ->
     SRr SEGS W2 (cfg_at SEGS (BASE + ret) regs2 mem2 md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 AF) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k o STKF AF ret Q HBASE HFR HSTK R1 Hret Hret2 HCALLEE HK.
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof HBASE as (HPRE0 & HPRES0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0 : s0Z regs = x_sp0 cx).
{ unfold s0Z. rewrite F8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* the frame chain at the call: the stack from s1 up is readable (the entry's astack_pres, kept by the journal) *)
assert (HRD : astack_rd ly (rdW W mem) (x_s1 cx)).
{ apply (astack_rd_of_pres SEGS). apply (astack_pres_mono _ _ _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
  - unfold STK_LLVMFuzzerTestOneInput. lia.
  - eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HPRES0 |].
    intros a (r & Hr & Ha) Ha2. exfalso. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch & Hch).
eapply SRr_bind.
{ apply (cl_callS B LAWS W regs mem (Z_to_bv 64 AF) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STKF [] 0
    (x_s1 cx - x_sp0 cx) (getr regs 1) ch
    (fun ly2 S2 W2 regs2 mem2 md2 => sa_kept SEGS W mem W2 mem2 regs STKF (fun _ => False) /\ sa_noalloc B ly S ly2 S2)
    HJ Hsp).
  - pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D1.
    replace (x_s1 cx - x_sp0 cx) with ((x_s1 cx / 32 * 2 - x_sp0 cx / 16) * 16).
    + apply Z.mod_mul. lia.
    + pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D2. lia.
  - lia.
  - lia.
  - unfold STK_LLVMFuzzerTestOneInput, ASTACK in *. lia.
  - rewrite F3. exact Hgp0.
  - rewrite F4. exact Htp0.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia. rewrite Hs0. exact Hch.
  - intros HPRE. exact (HCALLEE ch HPRE).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & Hkp & Hna).
rewrite Z.add_0_r in HJ2. rewrite R1.
exact (HK ly2 S2 W2 regs2 mem2 md2 Hle HJ2 HP Hkp Hna).
Qed.

(* a callee-saved register is what it was at the call *)
Lemma s19_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac s19_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* the events spent so far leave room for a callee that spends none *)
Lemma s19_nev : forall cx ly S W regs mem md k acc rem o O, lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc rem o O -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W regs mem md k acc rem o O HB HC.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
destruct HC as ((HJ & _) & _ & _ & (Hk0 & Hr0 & Hkr & _)).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
Qed.

(* back from a callee of the segment: the invariant, every byte outside its window below s1, the callee-saved
   registers *)
Lemma s19_after_call : forall cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2 STKF,
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m -> 0 <= STKF <= ASTACK ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved regs regs2 ->
  sa_kept SEGS W mem W2 mem2 regs STKF (fun _ => False) -> sa_noalloc B ly S ly2 S2 ->
  s19_inv cx ly2 S2 W2 regs2 mem2 md2 k acc c m /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ASTACK <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a).
Proof.
intros cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2 STKF HB HI HS HJ2 HP Hkp (Hperm & -> & f & ->).
pose proof HI as ((HFR & _ & _ & HBUD) & _).
pose proof HFR as (_ & F2 & _).
destruct (s19_bounds cx HB) as (_ & Bac & B47 & _ & Bs1).
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ regs = x_s1 cx) by (unfold spZ; rewrite F2; unfold w64; apply unsigned_lit_small; lia).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ASTACK <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha Hn. apply Hkp; [exact Ha | rewrite Hsp; lia | tauto]. }
split; [|exact HK].
apply (s19_keep cx ly S W regs mem md k acc c m ly (set_fs f S) W2 regs2 mem2 md2 HB HI HJ2);
  try (apply s19_pres; [exact HP | s19_cs]).
- exact Hperm.
- destruct HBUD as (_ & _ & _ & Hmo & _). exact (mo_le_set_fs_r MT MTFL _ _ f _ Hmo).
- intros a Ha H1 _ _. exact (HK a Ha H1).
Qed.

(* the model's two refusal checks on the payload's run, and n_refusals = n_kept *)
Lemma s19_model : forall cx,
  SegModel.check_refusals (x_rcF cx) (x_mcF cx) = true /\
  SegModel.check_kept_all (SegModel.rc_refusal (x_rcF cx)) (SegModel.mc_kept (x_mcF cx)) = true /\
  length (SegModel.rc_refusal (x_rcF cx)) = length (SegModel.mc_kept (x_mcF cx)).
Proof.
intros cx. destruct (sk_harness_checks (x_pl cx)) as [H1 H2]. unfold x_rcF, x_mcF, x_run.
split; [exact H1|]. split; [exact H2|]. exact (sk_refusals_len _ _ H1).
Qed.

(* a range inside an addressable range is addressable *)
Lemma s19_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
  sa_addr rd q' n'.
Proof.
intros rd q n q' n' (H0 & H63 & Hm & Hra & Hv) H1 H2 H3.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
- exact (range_addressable_sub _ _ q n q' n' Hra H1 H2).
- intros _ s Hs. apply (Hv ltac:(lia) s). split.
  + pose proof (shadow_mono q q' H1) as M. pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M) as M2. lia.
  + pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) M) as M2. lia.
Qed.

(* check_refusals' pre at a point of the segment *)
Lemma s19_pre_cr : forall cx ly S W regs mem md k acc c m, s19_inv cx ly S W regs mem md k acc c m ->
  check_refusals_pre B ly S (rdW W mem) c m (x_rcF cx) (x_mcF cx).
Proof.
intros cx ly S W regs mem md k acc c m (_ & (HinC & Hc4 & Hc16 & HaC) & (HinM & Hm4 & Hm16 & HaM) & _ & Hrc & Hmc).
unfold check_refusals_pre.
split; [lia|]. split; [exact Hc16|]. split; [exact Hrc|]. split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HinC | lia]|].
split; [exact HaC|].
split; [lia|]. split; [exact Hm16|]. split; [exact Hmc|]. split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HinM | lia]|].
split; [exact HaM|]. exact (proj1 (s19_model cx)).
Qed.

(* check_address's pre at turn i of the loop: refusal[i] of c, kept[i] of m *)
Lemma s19_pre_ca : forall cx ly S W regs mem md k acc c m i, s19_inv cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  check_address_pre B ly S (rdW W mem) (seg_spec.refusal_addr c i) (seg_spec.kept_addr m i)
    (nth i (SegModel.rc_refusal (x_rcF cx)) []) (fst (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))).
Proof.
intros cx ly S W regs mem md k acc c m i (_ & (HinC & Hc4 & Hc16 & HaC) & (HinM & Hm4 & Hm16 & HaM) & _ & Hrc & Hmc) Hi.
change (sa_rconf (rdW W mem) c (x_rcF cx)) in Hrc. change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (s19_model cx) as (_ & Mka & Mlen).
assert (Hir : (i < length (SegModel.rc_refusal (x_rcF cx)))%nat) by lia.
destruct (sk_rconf_refusal _ c _ i Hrc Hir) as [Hgs Hgl].
destruct (sk_mconf_kept _ m _ i Hmc Hi) as (Hws & Hwl & _).
destruct (sk_mconf_nkept _ m _ Hmc) as [_ H8].
pose proof (sk_kept_nth _ _ i Mka Hir Hi) as CK. unfold SegModel.check_kept in CK.
apply andb_prop in CK as [CK1 _]. apply Z.eqb_eq in CK1.
pose proof HaC as (_ & _ & HmC & _). pose proof HaM as (_ & _ & HmM & _).
set (gs := nth i (SegModel.rc_refusal (x_rcF cx)) []) in *.
set (ws := fst (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
unfold check_address_pre, seg_spec.refusal_addr, seg_spec.kept_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
  seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN in *.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
split; [lia|]. split.
{ apply (sk_str_of_strz _ _ _ c (c + 16616) Hgs); [intros x Hx; exact (sk_rconf_mapped _ c _ x Hrc Hx) | lia | lia]. }
split; [lia|]. split; [exists c, 16616; split; [exact HinC | lia]|].
split; [apply (s19_addr_sub _ c 16616); [exact HaC | lia | lia | lia]|].
split; [unfold amem_range in *; lia|].
split; [lia|]. split.
{ apply (sk_str_of_strz _ _ _ m (m + 9236) Hws); [intros x Hx; exact (sk_mconf_mapped _ m _ x Hmc Hx) | lia | lia]. }
split; [lia|]. split; [exists m, 9236; split; [exact HinM | lia]|].
split; [apply (s19_addr_sub _ m 9236); [exact HaM | lia | lia | lia]|].
split; [unfold amem_range in *; lia|].
exact CK1.
Qed.

(* check_knock_refused's pre at turn i: refusal[i] of c and kept_knock[i] of m *)
Lemma s19_pre_ck : forall cx ly S W regs mem md k acc c m i, s19_inv cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  check_knock_refused_pre SEGS B ly S (rdW W mem) seg_litA_fz (seg_spec.refusal_addr c i)
    (seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))) gotwA guardA
    (nth i (SegModel.rc_refusal (x_rcF cx)) []) (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))).
Proof.
intros cx ly S W regs mem md k acc c m i ((_ & HIMG & _) & (HinC & Hc4 & Hc16 & HaC) & _ & _ & Hrc & Hmc) Hi.
change (sa_rconf (rdW W mem) c (x_rcF cx)) in Hrc. change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (s19_model cx) as (_ & Mka & Mlen).
assert (Hir : (i < length (SegModel.rc_refusal (x_rcF cx)))%nat) by lia.
destruct (sk_rconf_refusal _ c _ i Hrc Hir) as [Hgs Hgl].
destruct (sk_mconf_nkept _ m _ Hmc) as [_ H8].
pose proof (sk_kept_nth _ _ i Mka Hir Hi) as CK. unfold SegModel.check_kept in CK.
apply andb_prop in CK as [_ CK2].
destruct HIMG as (_ & (_ & _ & HFZ & _ & _ & _ & _ & _ & HSSP & _) & _).
unfold check_knock_refused_pre, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN in *.
unfold seg_spec.SEG_C_SIZE in *.
split; [lia|]. split.
{ apply (sk_str_of_strz _ _ _ c (c + 16616) Hgs); [intros x Hx; exact (sk_rconf_mapped _ c _ x Hrc Hx) | lia | lia]. }
split; [lia|]. split; [exists c, 16616; split; [exact HinC | lia]|].
split; [apply (s19_addr_sub _ c 16616); [exact HaC | lia | lia | lia]|].
split; [reflexivity|]. split; [exact CK2|]. split; [|exact HSSP].
intros s Hs. apply (HFZ s). unfold LTOI_FZ_LITS. apply in_or_app. right. apply in_or_app. left. exact Hs.
Qed.

(* ---- the point after check_refusals (0x855ac): the invariant and slot 152 = SH(m + 0x2000) ---- *)
Definition s19_PCR : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> s19_inv cx ly S W regs mem md k acc c m ->
  rdword (rdW W mem) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_CRRA) regs mem md) (lt_post B MT cx).

(* 0x8559c .. 0x855a8: sd s11,152(s1), a0 = c, a1 = m, jal check_refusals, and the call *)
Lemma s19_stepA : s19_PCR -> LT_K8559c_stmt B MT.
Proof.
intros HP. unfold LT_K8559c_stmt.
intros cx ly S W regs mem md k acc c m HBASE HFRM HCORE HC HM H27 HSL HCM.
assert (HINV : s19_inv cx ly S W regs mem md k acc c m) by exact (conj HCORE (conj HC (conj HM (conj HSL HCM)))).
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
pose proof HCORE as ((HJ & F2 & F3 & F4 & F8 & F9 & _) & _ & _ & (_ & _ & _ & HMO & _)).
assert (Hpres : forall a, x_s1 cx + 152 <= a < x_s1 cx + 160 -> apresent (w_H W) mem a).
{ intros a Ha. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). apply Hpr.
  unfold STK_LLVMFuzzerTestOneInput. lia. }
assert (Hc160 : rdword (rdW W mem) (x_s1 cx + 160) = Some c)
  by (apply HSL; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
assert (Hm168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m)
  by (apply HSL; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])).
destruct (s19_seedA W regs mem (x_s1 cx) c m F9 ltac:(lia) ltac:(lia) Hpres Hc160 Hm168) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (s19_E regs [SHADOW_OFF; c; m])) by (unfold s19_E; apply Eimg_env).
pose proof (fun n (r : bv 5) H => s19_E_reg regs [SHADOW_OFF; c; m] n r H) as EEo.
assert (E33 : ew (s19_E regs [SHADOW_OFF; c; m]) 33 = Z_to_bv 64 c)
  by exact (s19_E_extra regs [SHADOW_OFF; c; m] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew (s19_E regs [SHADOW_OFF; c; m]) 34 = Z_to_bv 64 m)
  by exact (s19_E_extra regs [SHADOW_OFF; c; m] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
remember (s19_E regs [SHADOW_OFF; c; m]) as E eqn:HE. clear HE.
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), F9. unfold w64. apply unsigned_lit_small. lia. }
unfold cfg_at, w64.
(* 0x8559c .. 0x855a8 *)
paj_run_tok RUN HS HJ SHOK S19span.
{ unfold ss_A. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
    [reflexivity | rewrite U9; lia | unfold s19_rgA; cbn [YP09.r_wlo]; unfold STK_LLVMFuzzerTestOneInput; lia
    | unfold s19_rgA; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn.
  apply (PaDenot.kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms)
    (fun a => x_s1 cx + 152 <= a < x_s1 cx + 160) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq | []].
  injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U9 in Hrr. lia. }
(* slot 152 holds s11 = SH(m + 0x2000), read back from the run's chunk *)
assert (H152 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N))).
{ lazymatch type of HS with st_ok _ _ ?ss1 _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss1) 0) in
    lazymatch l with Some ?rg => assert (HRG : nth_error (ss_mem ss1) 0 = Some rg) by reflexivity end end.
  assert (R27 : 0 <= shadow_addr (m + seg_spec.MC_N) < 2 ^ 64).
  { pose proof HC as (_ & _ & _ & (Hm0 & _)). destruct HM as (_ & _ & _ & (Hm0' & Hm63 & _)).
    unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N, seg_spec.SEG_M_SIZE in *.
    pose proof (Z.div_pos (m + 8192) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (m + 8192) 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
  pose proof (YI67.st_chunk_val SEGS E _ _ 0 _ 9 152 8 (SOff 27 0) (x_s1 cx) (shadow_addr (m + seg_spec.MC_N))
    HS HRG eq_refl ltac:(cbn; left; reflexivity) U9) as Hv.
  cbn [ms_mem restrict] in Hv.
  apply (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact R27].
  apply Hv; [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R27 | lia].
  cbn [sv_denot]. rewrite (EEo 27%nat 27%bv eq_refl), H27. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
rewrite (SIGP SS_check_refusals ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_refusals) with AF_check_refusals by (vm_compute; reflexivity).
assert (INV1 : s19_inv cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m).
{ apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv HBASE HINV HJ).
  - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
  - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
  - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
  - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
  - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
  - apply Permutation_refl.
  - exact HMO.
  - intros a Ha _ _ H2. exact (KEEP a Ha H2). }
assert (HEV : st_nev S + EV_check_refusals <= EV_MAX).
{ unfold EV_check_refusals. pose proof (s19_nev _ _ _ _ _ _ _ _ _ _ _ _ HBASE (proj1 INV1)). lia. }
apply (s19_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k LFO0 STK_check_refusals (BASE + AF_check_refusals) LO_CRRA
  (lt_post B MT cx) HBASE (proj1 (proj1 INV1))).
- unfold STK_check_refusals, ASTACK. lia.
- rewrite P1. reflexivity.
- unfold LO_CRRA. lia.
- reflexivity.
- intros ch HPRE.
  assert (Rc : 0 <= c < 2 ^ 64).
  { pose proof HC as (_ & _ & _ & (Hc0 & Hc63 & _)). unfold seg_spec.SEG_C_SIZE in Hc63. lia. }
  assert (Rm : 0 <= m < 2 ^ 64).
  { pose proof HM as (_ & _ & _ & (Hm0 & Hm63 & _)). unfold seg_spec.SEG_M_SIZE in Hm63. lia. }
  exact (HCR fx ly S W (ms_regs ms) (ms_mem ms) mdv ch c m (x_rcF cx) (x_mcF cx) HPRE
    ltac:(rewrite P10, E33; reflexivity) Rc ltac:(rewrite P11, E34; reflexivity) Rm
    (s19_pre_cr _ _ _ _ _ _ _ _ _ _ _ INV1) HEV).
- intros ly2 S2 W2 regs2 mem2 md2 Hle HJ2 HPr Hkp Hna.
  destruct (s19_after_call cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m ly2 S2 W2 regs2 mem2 md2
    STK_check_refusals HBASE INV1 ltac:(unfold STK_check_refusals, ASTACK; lia) HJ2 HPr Hkp Hna) as [INV2 HK2].
  apply (HP cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM INV2).
  apply (s19_rdword_kept (rdW W (ms_mem ms))); [intros kk Hk; apply HK2; lia | exact H152].
Qed.

(* the two harness blocks at a point of the segment: where they lie, apart, their shadow *)
Lemma s19_blocks : forall cx ly S W regs mem md k acc c m, s19_inv cx ly S W regs mem md k acc c m ->
  4096 <= c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ 4096 <= m /\ m + seg_spec.SEG_M_SIZE <= alloc_ceiling /\
  (c + seg_spec.SEG_C_SIZE <= m \/ m + seg_spec.SEG_M_SIZE <= c) /\
  range_addressable (rdW W mem) SHADOW_OFF c seg_spec.SEG_C_SIZE /\ in_app c seg_spec.SEG_C_SIZE /\
  range_addressable (rdW W mem) SHADOW_OFF m seg_spec.SEG_M_SIZE /\ in_app m seg_spec.SEG_M_SIZE.
Proof.
intros cx ly S W regs mem md k acc c m
  (((HJ & _) & _ & HBL & _) & (HinC & _ & _ & (_ & _ & _ & HraC & _)) & (HinM & _ & _ & (_ & _ & _ & HraM & _)) & _).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ HAR HinC) as (_ & Hc4 & Hcc & Hca & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ HAR HinM) as (_ & Hm4 & Hmc & Hma & _).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HBL) as Hd.
unfold block_rng, zdisjoint in Hd. cbn [fst snd] in Hd.
change (req_size seg_spec.SEG_C_SIZE) with 16616 in *. change (req_size seg_spec.SEG_M_SIZE) with 9236 in *.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj HraC (conj Hca (conj HraM Hma)))))))); lia.
Qed.

(* ---- the loop's turn i at check_address's entry (the jal 0x85648): s2 = SH(&m->n_kept), s3 = &m->n_kept, s4 = i,
   s6 = &c->n_refusals, s7 = s8 = &m->kept_knock[i], s9 = a0 = c->refusal[i], s10 = a1 = m->kept[i],
   s11 = SH(&c->n_refusals), ra = 0x8564c ---- *)
Definition s19_LCA (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv cx ly S W regs mem md k acc c m ->
  rdword (rdW W mem) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs 1 = w64 (BASE + LO_CARA) ->
  getr regs 10 = w64 (seg_spec.refusal_addr c i) -> getr regs 11 = w64 (seg_spec.kept_addr m i) ->
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_NKEPT)) -> getr regs 19 = w64 (m + seg_spec.MC_NKEPT) ->
  getr regs 20 = w64 (Z.of_nat i) -> getr regs 22 = w64 (c + seg_spec.RC_NREF) ->
  getr regs 23 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) ->
  getr regs 24 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) ->
  getr regs 25 = w64 (seg_spec.refusal_addr c i) -> getr regs 26 = w64 (seg_spec.kept_addr m i) ->
  getr regs 27 = w64 (shadow_addr (c + seg_spec.RC_NREF)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_address)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* the facts every run of the segment starts from *)
Lemma s19_start : forall cx ly S W regs mem md k acc c m, lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m ->
  getr regs 9 = w64 (x_s1 cx) /\ rdword (rdW W mem) (x_s1 cx + 176) = Some SHADOW_OFF /\
  (forall a, x_s1 cx + 136 <= a < x_s1 cx + 144 -> apresent (w_H W) mem a) /\
  rdword (rdW W mem) (x_s1 cx + 160) = Some c /\ rdword (rdW W mem) (x_s1 cx + 168) = Some m /\
  rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N) /\
  sa_rconf (rdW W mem) c (x_rcF cx) /\ sa_mconf (rdW W mem) m (x_mcF cx).
Proof.
intros cx ly S W regs mem md k acc c m HBASE ((HFR & _) & _ & _ & HSL & Hrc & Hmc).
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
destruct HFR as (HJ & _ & _ & _ & _ & F9 & _ & _ & _ & _ & _ & F176 & _).
split; [exact F9|]. split; [exact F176|]. split.
{ intros a Ha. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _). apply Hpr.
  unfold STK_LLVMFuzzerTestOneInput. lia. }
split; [apply HSL; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])|].
split; [apply HSL; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])|].
split; [apply HSL; unfold LT_L; cbn [In]; repeat (first [left; reflexivity | right])|].
split; [exact Hrc | exact Hmc].
Qed.

(* the run's write window of seed B, slot 136, is the walk's to write *)
Ltac s19_awrB cx U9 :=
  unfold ss_B; cbn [ss_mem];
  eapply (awr_ok_cons_stack_off SEGS _) with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
    [reflexivity | rewrite U9; lia | unfold s19_rgBf; cbn [YP09.r_wlo]; unfold STK_LLVMFuzzerTestOneInput; lia
    | unfold s19_rgBf; cbn [YP09.r_whi]; lia
    | apply awr_ok_cons_ro; [unfold s19_rgBm; cbn; lia|]; apply awr_ok_cons_ro; [unfold s19_rgBc; cbn; lia|];
      apply awr_ok_nil ].

(* 0x855ac .. : n_kept (check 21), blez to 0x856bc when n = 0; else the loop's set-up (slot 136), the head's check 22,
   bge (n_refusals = n > 0), a0 = refusal[0], a1 = kept[0], jal check_address *)
Lemma s19_stepB : LTA_K856bc B MT -> s19_LCA 0 -> s19_PCR.
Proof.
intros HK0 HL0. unfold s19_PCR.
intros cx ly S W regs mem md k acc c m HBASE HFRM HINV H152.
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
pose proof asan_consts as (C1 & _).
destruct (s19_blocks _ _ _ _ _ _ _ _ _ _ _ HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & Hrc & Hac & Hrm & Ham).
destruct (s19_start _ _ _ _ _ _ _ _ _ _ _ HBASE HINV) as (F9 & F176 & Hpres & Hc160 & Hm168 & Hm184 & Hrcf & Hmcf).
pose proof HINV as ((HFR & _ & _ & (_ & _ & _ & HMO & _)) & _).
pose proof HFR as (HJ & _).
destruct (s19_model cx) as (_ & _ & Mlen).
destruct (sk_mconf_nkept _ m _ Hmcf) as [Hnm Hn8].
destruct (sk_rconf_nref _ c _ Hrcf) as [Hnc _]. rewrite Mlen in Hnc.
set (n := length (SegModel.mc_kept (x_mcF cx))) in *.
assert (HKEEPB : forall E ms, bv_unsigned (ew E 9) = x_s1 cx ->
  frame_of E [s19_rgBf; s19_rgBm; s19_rgBc] (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 136 <= a < x_s1 cx + 144) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros E ms U9 HFr a Ha Hn.
  apply (PaDenot.kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms)
    (fun a => x_s1 cx + 136 <= a < x_s1 cx + 144) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; [rewrite U9 in Hrr|..]; lia. }
destruct (Nat.eq_dec n 0) as [N0 | N0].
- (* n = 0: the blez is taken, to 0x856bc *)
  destruct (s19_seedB W regs mem (x_s1 cx) c m (Z.of_nat n) 0 0 F9 ltac:(lia) ltac:(lia) Hpres Hc160 Hm168 F176 Hm184
    Hc4 Hcc Hm4 Hmc Hcm Hrc Hac Hrm Ham Hnm Hnc ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n])) by (unfold s19_E; apply Eimg_env).
  pose proof (fun n0 (r : bv 5) H => s19_E_reg regs [SHADOW_OFF; c; m; Z.of_nat n] n0 r H) as EEo.
  remember (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n]) as E eqn:HE. clear HE.
  assert (U9 : bv_unsigned (ew E 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), F9. unfold w64. apply unsigned_lit_small. lia. }
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK S19span LO_K856bc.
  { s19_awrB cx U9. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (HKEEPB E ms U9 HFr) as KEEP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  assert (INV1 : s19_inv cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m).
  { apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv HBASE HINV HJ).
    - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
    - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
    - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
    - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
    - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
    - apply Permutation_refl.
    - exact HMO.
    - intros a Ha _ H1 _. exact (KEEP a Ha H1). }
  destruct INV1 as (HCORE1 & HC1 & HM1 & HSL1 & HCM1).
  apply (HK0 fx cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HBASE HFRM HCORE1 HC1 HM1); [|exact HCM1].
  intros o v Hin. apply in_app_or in Hin as [Hin | [Heq | []]]; [exact (HSL1 o v Hin)|].
  injection Heq as <- <-. apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply KEEP; lia | exact H152].
- (* n >= 1: the set-up, the head, the jal of check_address *)
  destruct (s19_seedB W regs mem (x_s1 cx) c m (Z.of_nat n) 1 8 F9 ltac:(lia) ltac:(lia) Hpres Hc160 Hm168 F176 Hm184
    Hc4 Hcc Hm4 Hmc Hcm Hrc Hac Hrm Ham Hnm Hnc ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n])) by (unfold s19_E; apply Eimg_env).
  pose proof (fun n0 (r : bv 5) H => s19_E_reg regs [SHADOW_OFF; c; m; Z.of_nat n] n0 r H) as EEo.
  assert (E32 : ew (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n]) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (s19_E_extra regs [SHADOW_OFF; c; m; Z.of_nat n] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
  assert (E33 : ew (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n]) 33 = Z_to_bv 64 c)
    by exact (s19_E_extra regs [SHADOW_OFF; c; m; Z.of_nat n] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
  assert (E34 : ew (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n]) 34 = Z_to_bv 64 m)
    by exact (s19_E_extra regs [SHADOW_OFF; c; m; Z.of_nat n] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
  remember (s19_E regs [SHADOW_OFF; c; m; Z.of_nat n]) as E eqn:HE. clear HE.
  assert (U9 : bv_unsigned (ew E 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), F9. unfold w64. apply unsigned_lit_small. lia. }
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK S19span.
  { s19_awrB cx U9. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pose proof (HKEEPB E ms U9 HFr) as KEEP.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26.
  s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (27%bv : bv 5) P27.
  rewrite (SIGP SS_check_address ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_check_address) with AF_check_address by (vm_compute; reflexivity).
  assert (INV1 : s19_inv cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m).
  { apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms) (ms_mem ms) mdv HBASE HINV HJ).
    - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
    - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
    - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
    - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
    - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
    - apply Permutation_refl.
    - exact HMO.
    - intros a Ha _ H1 _. exact (KEEP a Ha H1). }
  unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
  assert (VC : forall d, 0 <= d < 16616 -> Z_to_bv 64 (bv_unsigned (ew E 33) + d) = w64 (c + d)).
  { intros d Hd. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (VM : forall d, 0 <= d < 9236 -> Z_to_bv 64 (bv_unsigned (ew E 34) + d) = w64 (m + d)).
  { intros d Hd. rewrite E34. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  apply (HL0 cx ly S W (ms_regs ms) (ms_mem ms) mdv k acc c m HBASE HFRM ltac:(lia) INV1);
    unfold seg_spec.refusal_addr, seg_spec.kept_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
      seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.RC_NREF.
  + apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply KEEP; lia | exact H152].
  + rewrite P1. reflexivity.
  + rewrite P10, (VC 11912) by lia. unfold w64. f_equal. lia.
  + rewrite P11, (VM 8204) by lia. unfold w64. f_equal. lia.
  + rewrite P18. rewrite (s19_shxd_denot E 34 9132 m E34 ltac:(lia) ltac:(lia) E32). reflexivity.
  + rewrite P19, (VM 9132) by lia. reflexivity.
  + rewrite P20. reflexivity.
  + rewrite P22, (VC 13512) by lia. reflexivity.
  + rewrite P23, (VM 9100) by lia. unfold w64. f_equal. lia.
  + rewrite P24, (VM 9100) by lia. unfold w64. f_equal. lia.
  + rewrite P25, (VC 11912) by lia. unfold w64. f_equal. lia.
  + rewrite P26, (VM 8204) by lia. unfold w64. f_equal. lia.
  + rewrite P27. rewrite (s19_shxd_denot E 33 13512 c E33 ltac:(lia) ltac:(lia) E32). reflexivity.
Qed.

(* ---- the loop body ---- *)
(* the registers the body keeps across its two calls (all callee-saved), at turn i *)
Definition s19_lregs (regs : bvmap 5 word) (c m : Z) (i : nat) : Prop :=
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_NKEPT)) /\ getr regs 19 = w64 (m + seg_spec.MC_NKEPT) /\
  getr regs 20 = w64 (Z.of_nat i) /\ getr regs 22 = w64 (c + seg_spec.RC_NREF) /\
  getr regs 23 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) /\
  getr regs 24 = w64 (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) /\
  getr regs 25 = w64 (seg_spec.refusal_addr c i) /\ getr regs 26 = w64 (seg_spec.kept_addr m i) /\
  getr regs 27 = w64 (shadow_addr (c + seg_spec.RC_NREF)).
Lemma s19_lregs_ext : forall regs regs' c m i,
  (forall r : bv 5, In (bv_unsigned r) [18; 19; 20; 22; 23; 24; 25; 26; 27] -> getr regs' r = getr regs r) ->
  s19_lregs regs c m i -> s19_lregs regs' c m i.
Proof.
intros regs regs' c m i HR (R18 & R19 & R20 & R22 & R23 & R24 & R25 & R26 & R27).
repeat split; rewrite HR by (cbn; tauto); assumption.
Qed.
Lemma s19_lregs_pres : forall regs regs' c m i, aregs_preserved regs regs' ->
  s19_lregs regs c m i -> s19_lregs regs' c m i.
Proof.
intros regs regs' c m i HP. apply s19_lregs_ext. intros r Hr. apply (s19_pres _ _ r HP).
unfold acallee_saved. cbn [In] in Hr. lia.
Qed.

(* the loop's seed from the invariant: the state at a return point of the body *)
Lemma s19_seedL_inv : forall cx ly S W regs mem md k acc c m i pc,
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m ->
  (i < length (SegModel.mc_kept (x_mcF cx)))%nat -> s19_lregs regs c m i ->
  st_ok_pi SEGS VAL
    (s19_E regs [SHADOW_OFF; Z.of_nat (length (SegModel.mc_kept (x_mcF cx)));
                 seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))]) (ss_L pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S19x s19_SHL
    (s19_E regs [SHADOW_OFF; Z.of_nat (length (SegModel.mc_kept (x_mcF cx)));
                 seg_spec.b2z (snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false)))]) (mrestrict (w_H W) mem).
Proof.
intros cx ly S W regs mem md k acc c m i pc HBASE HINV Hi (R18 & R19 & R20 & R22 & R23 & R24 & _ & _ & R27).
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
destruct (s19_blocks _ _ _ _ _ _ _ _ _ _ _ HINV) as (Hc4 & Hcc & Hm4 & Hmc & Hcm & Hrc & Hac & Hrm & Ham).
destruct (s19_start _ _ _ _ _ _ _ _ _ _ _ HBASE HINV) as (F9 & F176 & _ & _ & _ & _ & Hrcf & Hmcf).
destruct (s19_model cx) as (_ & _ & Mlen).
destruct (sk_mconf_nkept _ m _ Hmcf) as [Hnm Hn8].
destruct (sk_rconf_nref _ c _ Hrcf) as [Hnc _]. rewrite Mlen in Hnc.
destruct (sk_mconf_kept _ m _ i Hmcf Hi) as (_ & _ & Hkn).
assert (Hb : forall b, 0 <= seg_spec.b2z b <= 1) by (intros []; cbn; lia).
apply (s19_seedL W regs mem pc (x_s1 cx) c m _ i _ F9 ltac:(lia) ltac:(lia) F176 R18 R19 R20 R22 R23 R24 R27
  Hc4 Hcc Hm4 Hmc Hcm Hrc Hac Hrm Ham Hkn Hnm Hnc ltac:(lia) ltac:(lia) (Hb _)).
Qed.

(* every region of the loop's states is read-only: the runs write nothing *)
Ltac s19_awr_ro :=
  unfold awr_ok; intros ?a (?r & ?Hin & ?Hr); exfalso; vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.

(* a signed compare of two small values *)
Lemma s19_lt : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite !YK11.bv_signed_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* the body's two return points: after check_address (0x8564c) and after check_knock_refused (0x8566c) *)
Definition s19_PA (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv cx ly S W regs mem md k acc c m ->
  rdword (rdW W mem) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)) -> s19_lregs regs c m i ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_CARA) regs mem md) (lt_post B MT cx).
Definition s19_PK (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc c m,
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv cx ly S W regs mem md k acc c m ->
  rdword (rdW W mem) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N)) -> s19_lregs regs c m i ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_CKRA) regs mem md) (lt_post B MT cx).

(* the call of check_address (refusal[i], kept[i]) *)
Lemma s19_stepCA : forall i, s19_PA i -> s19_LCA i.
Proof.
intros i HPA. unfold s19_LCA.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV H152 R1 R10 R11 R18 R19 R20 R22 R23 R24 R25 R26 R27.
destruct (s19_blocks _ _ _ _ _ _ _ _ _ _ _ HINV) as (Hc4 & Hcc & Hm4 & Hmc & _).
destruct (s19_start _ _ _ _ _ _ _ _ _ _ _ HBASE HINV) as (_ & _ & _ & _ & _ & _ & _ & Hmcf).
destruct (sk_mconf_nkept _ m _ Hmcf) as [_ Hn8].
pose proof asan_consts as (C1 & _).
pose proof HINV as ((HFR & (HARO & _) & _) & _).
apply (s19_call cx ly S W regs mem md k LFO0 STK_check_address (BASE + AF_check_address) LO_CARA (lt_post B MT cx)
  HBASE HFR).
- unfold STK_check_address, ESTACK, ASTACK. lia.
- exact R1.
- unfold LO_CARA. lia.
- reflexivity.
- intros ch HPRE.
  assert (HEV : st_nev S + EV_check_address <= EV_MAX).
  { unfold EV_check_address. pose proof (s19_nev _ _ _ _ _ _ _ _ _ _ _ _ HBASE (proj1 HINV)). lia. }
  unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
  exact (HCA fx ly S W regs mem md ch _ _ _ _ HPRE HARO R10
    ltac:(unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN; lia) R11
    ltac:(unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; lia)
    (s19_pre_ca _ _ _ _ _ _ _ _ _ _ _ i HINV Hi) HEV).
- intros ly2 S2 W2 regs2 mem2 md2 Hle HJ2 HPr Hkp Hna.
  destruct (s19_after_call cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2 STK_check_address HBASE HINV
    ltac:(unfold STK_check_address, ESTACK, ASTACK; lia) HJ2 HPr Hkp Hna) as [INV2 HK2].
  destruct (s19_bounds cx HBASE) as (_ & Bac & B47 & _ & Bs1).
  apply (HPA cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi INV2).
  + apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HK2; lia | exact H152].
  + apply (s19_lregs_pres regs); [exact HPr|]. repeat split; assumption.
Qed.

(* 0x8564c .. 0x85668: check 23 (kept_knock[i]'s shadow), a1 = kept_knock[i], a0 = refusal[i], jal
   check_knock_refused, and the call *)
Lemma s19_stepC : forall i, s19_PK i -> s19_PA i.
Proof.
intros i HPK. unfold s19_PA.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV H152 HLR.
destruct (s19_seedL_inv cx ly S W regs mem md k acc c m i LO_CARA HBASE HINV Hi HLR) as [HS SHOK].
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
destruct (s19_blocks _ _ _ _ _ _ _ _ _ _ _ HINV) as (Hc4 & Hcc & Hm4 & Hmc & _).
destruct (s19_start _ _ _ _ _ _ _ _ _ _ _ HBASE HINV) as (_ & _ & _ & _ & _ & _ & _ & Hmcf).
destruct (sk_mconf_nkept _ m _ Hmcf) as [_ Hn8].
pose proof asan_consts as (C1 & _).
pose proof HINV as ((HFR & _ & _ & (_ & _ & _ & HMO & _)) & _).
pose proof HFR as (HJ & _).
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
set (n := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
assert (HEI : img_env VAL A_LIM (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb])) by (unfold s19_E; apply Eimg_env).
pose proof (fun n0 (r : bv 5) H => s19_E_reg regs [SHADOW_OFF; n; seg_spec.b2z kb] n0 r H) as EEo.
assert (E32 : ew (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) 32 = Z_to_bv 64 SHADOW_OFF)
  by exact (s19_E_extra regs [SHADOW_OFF; n; seg_spec.b2z kb] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) 34 = Z_to_bv 64 (seg_spec.b2z kb))
  by exact (s19_E_extra regs [SHADOW_OFF; n; seg_spec.b2z kb] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
remember (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x8564c .. 0x85668 *)
paj_run_tok RUN HS HJ SHOK S19span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (frame_of_read_only E (ss_mem (ss_L LO_CARA)) mem (ms_mem ms) eq_refl HF) as Hmem.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22.
prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26.
s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (27%bv : bv 5) P27.
change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0)) with (s19_shx 19) in P18.
change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 32 0)) with (s19_shx 22) in P27.
rewrite (SIGP SS_check_knock_refused ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_knock_refused) with AF_check_knock_refused by (vm_compute; reflexivity).
rewrite Hmem in HJ |- *.
pose proof HLR as (R18 & R19 & R20 & R22 & R23 & R24 & R25 & R26 & R27).
(* the registers the body keeps are as the seed had them *)
assert (HLR1 : s19_lregs (ms_regs ms) c m i).
{ unfold s19_lregs.
  rewrite P18, (s19_shx_denot E 19 (m + seg_spec.MC_NKEPT) (eq_trans (EEo 19%nat 19%bv eq_refl) R19)
    ltac:(unfold seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *; lia) E32).
  rewrite P27, (s19_shx_denot E 22 (c + seg_spec.RC_NREF) (eq_trans (EEo 22%nat 22%bv eq_refl) R22)
    ltac:(unfold seg_spec.RC_NREF, seg_spec.SEG_C_SIZE in *; lia) E32).
  rewrite P19, P20, P22, P23, P24, P25, P26.
  rewrite (EEo 19%nat 19%bv eq_refl), (EEo 20%nat 20%bv eq_refl), (EEo 22%nat 22%bv eq_refl),
    (EEo 23%nat 23%bv eq_refl), (EEo 24%nat 24%bv eq_refl), (EEo 25%nat 25%bv eq_refl), (EEo 26%nat 26%bv eq_refl).
  repeat split; first [assumption | reflexivity]. }
assert (INV1 : s19_inv cx ly S W (ms_regs ms) mem mdv k acc c m).
{ apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms) mem mdv HBASE HINV HJ).
  - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
  - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
  - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
  - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
  - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
  - apply Permutation_refl.
  - exact HMO.
  - intros a _ _ _ _. reflexivity. }
assert (HEV : st_nev S + EV_check_knock_refused <= EV_MAX).
{ unfold EV_check_knock_refused. pose proof (s19_nev _ _ _ _ _ _ _ _ _ _ _ _ HBASE (proj1 INV1)). lia. }
apply (s19_call cx ly S W (ms_regs ms) mem mdv k LFO0 STK_check_knock_refused (BASE + AF_check_knock_refused) LO_CKRA
  (lt_post B MT cx) HBASE (proj1 (proj1 INV1))).
- unfold STK_check_knock_refused, ESTACK, ASTACK. lia.
- rewrite P1. reflexivity.
- unfold LO_CKRA. lia.
- reflexivity.
- intros ch HPRE.
  pose proof INV1 as ((_ & (HARO & _) & _) & _).
  assert (Hb : 0 <= seg_spec.b2z kb < 2 ^ 64) by (destruct kb; cbn; lia).
  exact (HCK fx ly S W (ms_regs ms) mem mdv ch _ _ _ _ HPRE HARO
    ltac:(rewrite P10, (EEo 25%nat 25%bv eq_refl); exact R25)
    ltac:(unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia)
    ltac:(rewrite P11, E34; reflexivity) Hb
    (s19_pre_ck _ _ _ _ _ _ _ _ _ _ _ i INV1 Hi) HEV).
- intros ly2 S2 W2 regs2 mem2 md2 Hle HJ2 HPr Hkp Hna.
  destruct (s19_after_call cx ly S W (ms_regs ms) mem mdv k acc c m ly2 S2 W2 regs2 mem2 md2 STK_check_knock_refused
    HBASE INV1 ltac:(unfold STK_check_knock_refused, ESTACK, ASTACK; lia) HJ2 HPr Hkp Hna) as [INV2 HK2].
  apply (HPK cx ly2 S2 W2 regs2 mem2 md2 k acc c m HBASE HFRM Hi INV2).
  + apply (s19_rdword_kept (rdW W mem)); [intros kk Hk; apply HK2; lia | exact H152].
  + exact (s19_lregs_pres _ _ _ _ _ HPr HLR1).
Qed.

(* 0x8566c .. 0x8568c: check 24 (n_kept's shadow), i += 1, n_kept, the four pointers step, blt i, n_kept: to the
   head (check 22, bge decided by the latch's condition, the next jal of check_address) or out to 0x856bc *)
Lemma s19_stepK : LTA_K856bc B MT -> forall i, s19_LCA (Datatypes.S i) -> s19_PK i.
Proof.
intros HK0 i HIH. unfold s19_PK.
intros cx ly S W regs mem md k acc c m HBASE HFRM Hi HINV H152 HLR.
destruct (s19_seedL_inv cx ly S W regs mem md k acc c m i LO_CKRA HBASE HINV Hi HLR) as [HS SHOK].
destruct (s19_bounds cx HBASE) as (B16 & Bac & B47 & B32 & Bs1).
destruct (s19_blocks _ _ _ _ _ _ _ _ _ _ _ HINV) as (Hc4 & Hcc & Hm4 & Hmc & _).
destruct (s19_start _ _ _ _ _ _ _ _ _ _ _ HBASE HINV) as (_ & _ & _ & _ & _ & _ & _ & Hmcf).
destruct (sk_mconf_nkept _ m _ Hmcf) as [_ Hn8].
pose proof asan_consts as (C1 & _).
pose proof HINV as ((HFR & _ & _ & (_ & _ & _ & HMO & _)) & _).
pose proof HFR as (HJ & _).
pose proof HLR as (R18 & R19 & R20 & R22 & R23 & R24 & R25 & R26 & R27).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
set (kb := snd (nth i (SegModel.mc_kept (x_mcF cx)) ([], false))) in *.
set (n := Z.of_nat (length (SegModel.mc_kept (x_mcF cx)))) in *.
assert (HEI : img_env VAL A_LIM (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb])) by (unfold s19_E; apply Eimg_env).
pose proof (fun n0 (r : bv 5) H => s19_E_reg regs [SHADOW_OFF; n; seg_spec.b2z kb] n0 r H) as EEo.
assert (E32 : ew (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) 32 = Z_to_bv 64 SHADOW_OFF)
  by exact (s19_E_extra regs [SHADOW_OFF; n; seg_spec.b2z kb] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) 33 = Z_to_bv 64 n)
  by exact (s19_E_extra regs [SHADOW_OFF; n; seg_spec.b2z kb] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
remember (s19_E regs [SHADOW_OFF; n; seg_spec.b2z kb]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x8566c .. 0x8568c, to the blt *)
paj_run_tok RUN HS HJ SHOK S19span.
{ s19_awr_ro. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pose proof (frame_of_read_only E (ss_mem (ss_L LO_CKRA)) mem (ms_mem ms) eq_refl HF) as Hmem.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK S19span.
- (* i + 1 < n: the head and the next turn's jal of check_address *)
  assert (Hlt : (Datatypes.S i < length (SegModel.mc_kept (x_mcF cx)))%nat).
  { rewrite (s19_lt E (SOff 20 1) (SOff 33 0) (Z.of_nat i + 1) n) in Hc; [apply Z.ltb_lt in Hc; lia | | | lia | lia].
    - cbn [sv_denot]. rewrite (EEo 20%nat 20%bv eq_refl), R20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK S19span.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  pose proof (fun H => frame_of_read_only E _ _ _ H HF) as Hmem2. specialize (Hmem2 ltac:(vm_compute; reflexivity)).
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22.
  prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  prreg HS (26%bv : bv 5) P26.
  s19_rreg HS (18%bv : bv 5) P18. s19_rreg HS (27%bv : bv 5) P27.
  change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0)) with (s19_shx 19) in P18.
  change (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 32 0)) with (s19_shx 22) in P27.
  rewrite (SIGP SS_check_address ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_check_address) with AF_check_address by (vm_compute; reflexivity).
  assert (Hm2 : ms_mem ms0 = mem) by (rewrite Hmem2; exact Hmem).
  rewrite Hm2 in HJ |- *.
  assert (INV2 : s19_inv cx ly S W (ms_regs ms0) mem mdv2 k acc c m).
  { apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms0) mem mdv2 HBASE HINV HJ).
    - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
    - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
    - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
    - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
    - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
    - apply Permutation_refl.
    - exact HMO.
    - intros a _ _ _ _. reflexivity. }
  assert (VS : forall (rr : nat) (r : bv 5) v d, Z.of_nat rr = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
    Z_to_bv 64 (bv_unsigned (ew E rr) + d) = w64 (v + d)).
  { intros rr r v d Hr Hv Hv64. rewrite (EEo rr r Hr), Hv. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  unfold seg_spec.refusal_addr, seg_spec.kept_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.RC_NREF in *.
  apply (HIH cx ly S W (ms_regs ms0) mem mdv2 k acc c m HBASE HFRM Hlt INV2 H152);
    unfold seg_spec.refusal_addr, seg_spec.kept_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
      seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.RC_NREF.
  + rewrite P1. reflexivity.
  + rewrite P10, (VS 25%nat 25%bv _ 200 eq_refl R25) by lia. unfold w64. f_equal. lia.
  + rewrite P11, (VS 26%nat 26%bv _ 112 eq_refl R26) by lia. unfold w64. f_equal. lia.
  + rewrite P18, (s19_shx_denot E 19 (m + 9132) (eq_trans (EEo 19%nat 19%bv eq_refl) R19) ltac:(lia) E32).
    reflexivity.
  + rewrite P19, (EEo 19%nat 19%bv eq_refl). exact R19.
  + rewrite P20, (VS 20%nat 20%bv _ 1 eq_refl R20) by lia. unfold w64. f_equal. lia.
  + rewrite P22, (EEo 22%nat 22%bv eq_refl). exact R22.
  + rewrite P23, (VS 23%nat 23%bv _ 4 eq_refl R23) by lia. unfold w64. f_equal. lia.
  + rewrite P24, (VS 24%nat 24%bv _ 4 eq_refl R24) by lia. unfold w64. f_equal. lia.
  + rewrite P25, (VS 25%nat 25%bv _ 200 eq_refl R25) by lia. unfold w64. f_equal. lia.
  + rewrite P26, (VS 26%nat 26%bv _ 112 eq_refl R26) by lia. unfold w64. f_equal. lia.
  + rewrite P27, (s19_shx_denot E 22 (c + 13512) (eq_trans (EEo 22%nat 22%bv eq_refl) R22) ltac:(lia) E32).
    reflexivity.
- (* i + 1 = n: j 0x856bc *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK S19span LO_K856bc.
  { s19_awr_ro. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv2 := d) in *; clearbody mdv2 end.
  pose proof (fun H => frame_of_read_only E _ _ _ H HF) as Hmem2. specialize (Hmem2 ltac:(vm_compute; reflexivity)).
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  assert (Hm2 : ms_mem ms0 = mem) by (rewrite Hmem2; exact Hmem).
  rewrite Hm2 in HJ |- *.
  assert (INV2 : s19_inv cx ly S W (ms_regs ms0) mem mdv2 k acc c m).
  { apply (s19_keep cx ly S W regs mem md k acc c m ly S W (ms_regs ms0) mem mdv2 HBASE HINV HJ).
    - rewrite P2. exact (EEo 2%nat 2%bv eq_refl).
    - rewrite P3. exact (EEo 3%nat 3%bv eq_refl).
    - rewrite P4. exact (EEo 4%nat 4%bv eq_refl).
    - rewrite P8. exact (EEo 8%nat 8%bv eq_refl).
    - rewrite P9. exact (EEo 9%nat 9%bv eq_refl).
    - apply Permutation_refl.
    - exact HMO.
    - intros a _ _ _ _. reflexivity. }
  destruct INV2 as (HCORE2 & HC2 & HM2 & HSL2 & HCM2).
  apply (HK0 fx cx ly S W (ms_regs ms0) mem mdv2 k acc c m HBASE HFRM HCORE2 HC2 HM2); [|exact HCM2].
  intros o v Hin. apply in_app_or in Hin as [Hin | [Heq | []]]; [exact (HSL2 o v Hin)|].
  injection Heq as <- <-. exact H152.
Qed.

(* no turn i >= 8 is reached: n_kept <= 8 *)
Lemma s19_LCA_vac : forall i, (8 <= i)%nat -> s19_LCA i.
Proof.
intros i Hi. unfold s19_LCA. intros cx ly S W regs mem md k acc c m _ _ Hn (_ & _ & _ & _ & _ & Hmc). exfalso.
change (sa_mconf (rdW W mem) m (x_mcF cx)) in Hmc.
destruct (sk_mconf_nkept _ m _ Hmc) as [_ H8]. lia.
Qed.

(* the loop, turn by turn from the last *)
Lemma s19_loop : LTA_K856bc B MT -> forall j i, (i + j = 8)%nat -> s19_LCA i.
Proof.
intros HK0 j. induction j as [|j IH]; intros i Hij.
- apply s19_LCA_vac. lia.
- apply s19_stepCA, s19_stepC, (s19_stepK HK0). apply IH. lia.
Qed.

(* ---- the segment ---- *)
Theorem lt_seg_S10 : lt_seg_S10_stmt B MT.
Proof.
unfold lt_seg_S10_stmt. intros HK0.
apply s19_stepA. apply (s19_stepB HK0). exact (s19_loop HK0 8 0 eq_refl).
Qed.
End e.
End f.
End d.
