(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan) and the two arms of the inlined record(), from 0x8d10c to the join at 0x8d180, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement) with the shared seed pieces of lib/A/Prog/RecBTemplate.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s7.v, with its module paths and module names changed; 762 of its 820 lines of code are new or changed and 839 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan): sub-walk NEW of segment A8b of reac_segconf_parse_file's
   walk (segment A8b's proof, by the G3 walk owner, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk); the lane's rule-24 record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md (reuse
   verdict: none, written new).

   pfa8b_new : forall n, HA_A8B_JOIN B n -> H_NEW B n
   (H_NEW / INV_NEW are lib/A/Prog/pf_pieces.v; HA_A8B_JOIN / INV_A8B_JOIN are lib/A/Prog/pf_a8b_d.v).

   THE CODE (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x8890c ld a0,0xb0(s1); lb a0,0(a0); bnez a0,0x88b64       check #35 (store4 of c->n): the slot holds
                                                                 sh(&c->n) as the term (x >> 3) + s6
     0x88918 addi a0,s3,1; addi a1,zero,0x164; mul a1,s3,a1
     0x88924 ld a2,0x80(s1); sw a0,0(a2)                         c->n = n + 1
     0x8892c ld s8,0x90(s1); add s4,s8,a1                        s4 = &c->seg[n]
     0x88934 addi a2,zero,0x164; mv a0,s4; mv a1,zero
     0x88940 jal checked_memset                                  memset(&seg[n], 0, 356)       (PaCall.aj_intrin_atS)
     0x88944 auipc/addi a2 = "%s"; addi a1,zero,0x10; mv a0,s4; mv a3,s9
     0x88958 jal wrapper_snprintf                                snprintf(seg[n].name, 16, "%s", np)
                                                                 (pf_a8b_t.pfa8b_aj_snprintf_atSF)
     0x8895c ld s3,0x98(s1); j 0x889b0; 0x889b0 ld a3,0x38(s1)   then JOIN (0x889b4)

   THE WALK. Three symbolic runs, each from a seed of its own: run A (pn_ssA, the token executor: the s1 region
   with the slots 0x80 = c + RC_N, 0x90 = c, 0xb0 = the shadow term on atom 32 with Bx = s6's atom 22, and the
   written region c->n, whose 8-byte granule is the one shadow entry, so check #35 is decided with no
   obligation) to the memset; run B (pf_a8b_d.pfa8b_seed, no region) to the snprintf; run C (pn_ssC, the slots
   0x38 and 0x98) to JOIN, at the FP state snprintf returns. The cut's facts are carried across each step by
   the step's own keep clause (pf_a8b_k.pfk_*, and pn_base_move below); the block's shadow is re-derived from
   AR at the new state (pf_a6_k.a6_heap_addr); the new entry and n + 1 go into c's model by
   pf_a8b_m.pfa8b_rconf_newseg, whose keep premise asks only the block's bytes.

   Section hypotheses: AMSET (the checked memset, aintrin_realizes OSet at pa_sigma SS___asan_memset), ASNP
   (RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf), OBJ (seg_val_objs: the "%s"
   literal's atom A_OBJ 35). No SSPX, no VRO, no ROMV: sa_ssp, arodata_okP and rt_rom_view come from the cut's
   pf_obj and pf_a5_k.a5_rom, carried by the steps' keep clauses. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_d pf_a8b_k pf_a8b_m pf_a8b_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_d pf_a5_k pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* the register literals of the listing's decoder, as Z_to_bv 5 r (the form pf_rg states) *)
Lemma pn_r1 : Z_to_bv 5 1 = (1%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r2 : Z_to_bv 5 2 = (2%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r3 : Z_to_bv 5 3 = (3%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r4 : Z_to_bv 5 4 = (4%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r8 : Z_to_bv 5 8 = (8%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r9 : Z_to_bv 5 9 = (9%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r10 : Z_to_bv 5 10 = (10%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r11 : Z_to_bv 5 11 = (11%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r12 : Z_to_bv 5 12 = (12%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r13 : Z_to_bv 5 13 = (13%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r18 : Z_to_bv 5 18 = (18%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r19 : Z_to_bv 5 19 = (19%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r20 : Z_to_bv 5 20 = (20%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r21 : Z_to_bv 5 21 = (21%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r22 : Z_to_bv 5 22 = (22%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r24 : Z_to_bv 5 24 = (24%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r25 : Z_to_bv 5 25 = (25%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r26 : Z_to_bv 5 26 = (26%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Lemma pn_r27 : Z_to_bv 5 27 = (27%bv : bv 5). Proof. apply bv_eq; reflexivity. Qed.
Ltac pn_lit H := rewrite ?pn_r1, ?pn_r2, ?pn_r3, ?pn_r4, ?pn_r8, ?pn_r9, ?pn_r10, ?pn_r11, ?pn_r12, ?pn_r13, ?pn_r18, ?pn_r19, ?pn_r20, ?pn_r21, ?pn_r22, ?pn_r24, ?pn_r25, ?pn_r26, ?pn_r27 in H.
Ltac pn_unlit := rewrite <- ?pn_r1, <- ?pn_r2, <- ?pn_r3, <- ?pn_r4, <- ?pn_r8, <- ?pn_r9, <- ?pn_r10, <- ?pn_r11, <- ?pn_r12, <- ?pn_r13, <- ?pn_r18, <- ?pn_r19, <- ?pn_r20, <- ?pn_r21, <- ?pn_r22, <- ?pn_r24, <- ?pn_r25, <- ?pn_r26, <- ?pn_r27.

(** ** The seeds' symbolic states *)
(* run A (PF_NEW): the s1 region (atom 9) with the slots 0x80 = c + RC_N (atom 32), 0x90 = c (atom 33) and 0xb0 =
   sh(c + RC_N) as the term (atom 32 >> 3) + s6, read only; the written region c->n on atom 32, [0, 4); the shadow
   base s6 (atom 22) pinned to SB, atom 32 a pointer 8-aligned; the one shadow entry: atom 32's granule *)
Definition pn_Bx : sv := SOff 22 0.
Definition pn_SH : list shent := [mkSHE 32 0 8].
Definition pn_regA : smem :=
[ YP09.mkRegion (Some 9%nat) 0x80 0xb8 0 0
    [YP09.mkChunk 0x80 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0xb0 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0) (SLit 3)) (SOff 22 0)))];
  YP09.mkRegion (Some 32%nat) 0 4 0 4 [] ].
Definition pn_factsA : facts := mkFacts [ (22%nat, mkAF SB SB 0); (32%nat, PTR 3) ] [] [].
Definition pn_ssA : sstate := mkSS PF_NEW sr_atoms pn_regA None pn_factsA.
(* run C (0x8895c, after the snprintf): the s1 region with the slots 0x38 (atom 32) and 0x98 (atom 33) *)
Definition pn_regC : smem :=
[ YP09.mkRegion (Some 9%nat) 0x38 0xa0 0 0
    [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 33 0))] ].
Definition pn_ssC : sstate := mkSS PF_A8B_RET_SNPN sr_atoms pn_regC None (mkFacts [] [] []).

(** ** Pure helpers *)
Lemma pn_denot : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pn_bv8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
(* the check's address term: (x >> 3) + SHADOW_OFF is sh(x) *)
Lemma pn_U_shadow : forall E (m : nat) x, U E (SOff m 0) = x -> U E (SOff 22 0) = SHADOW_OFF -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 22 0)) = shadow_addr x.
Proof.
intros E m x Hx HB Hr. rewrite !U_SAlu, U_SLit, Hx, HB. cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 /\ 8 * (x / 8) <= x) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
unfold zcanon, shadow_addr, SHADOW_OFF in *. change M64 with 18446744073709551616 in *.
generalize dependent (x / 8). intros q Hd. assert (Hq : q < 18446744073709551616) by lia.
rewrite (Z.mod_small q) by (split; [apply Hd | exact Hq]).
rewrite (Z.mod_small (q + 2147450880)) by (split; [lia | lia]). lia.
Qed.
(* s4 = s8 + s3 * 356 *)
Lemma pn_U_seg : forall E c nn, U E (SOff 33 0) = c -> U E (SOff 19 0) = nn -> 0 <= nn < 32 -> 0 <= c ->
  c + 356 * 32 < 2 ^ 64 -> U E (SAlu ALU_ADD (SMd M_MUL (SOff 19 0) (SLit 356)) (SOff 33 0)) = c + 356 * nn.
Proof.
intros E c nn Hc Hn Hnr Hc0 Hlt. rewrite U_SAlu, U_SMd, U_SLit, Hc, Hn. cbn [zalu_raw zmd_raw].
unfold zcanon. change M64 with 18446744073709551616.
assert (E1 : 356 mod 18446744073709551616 = 356) by reflexivity. rewrite E1.
assert (E2 : (nn * 356) mod 18446744073709551616 = nn * 356) by (apply Z.mod_small; lia). rewrite E2.
assert (E3 : (nn * 356 + c) mod 18446744073709551616 = nn * 356 + c) by (apply Z.mod_small; lia). rewrite E3.
lia.
Qed.
(* the 4 little-endian bytes of a u32 *)
Lemma pn_u32 : forall v, 0 <= v < 2 ^ 32 -> seg_spec.u32_enc v (Z_to_le_bytes 4 v).
Proof. intros v Hv. split; [exact Hv|]. unfold Mem.le4. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Lemma pn_le4 : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes 4 v) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold le_byte.
replace (v mod 2 ^ (8 * Z.of_nat 4)) with v by (symmetry; apply Z.mod_small; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
(* snprintf(d, 16, "%s", name) with |name| <= 15 writes name and its NUL *)
Lemma pn_snlen : forall name : list Z, (length name <= 15)%nat ->
  RtPFShared.sn_len (16 - 1) name = Z.of_nat (length name) + 1 /\ RtPFShared.sn_bytes (16 - 1) name = name ++ [0].
Proof.
intros name H. unfold RtPFShared.sn_len, RtPFShared.sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
rewrite firstn_all2 by exact H. rewrite length_app. cbn [length]. split; [lia | reflexivity].
Qed.
(* a register list after a run that left those registers as their own atoms *)
Lemma pn_rg_kept : forall (rX rX' : bvmap 5 word) (L : list (Z * Z)) (l : list Z),
  (forall r, In r (map (Z_to_bv 5) l) -> getr rX' r = getr rX r) -> Forall (fun rv => In (fst rv) l) L ->
  pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L l HK HL H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK (Z_to_bv 5 (fst rv))) by (apply in_map; exact (HL rv Hin)). exact (H rv Hin).
Qed.
Lemma pn_sl_get : forall (rd : reader) b L o x, pf_sl rd b L -> In (o, x) L -> rdword rd (b + o) = Some x.
Proof. intros rd b L o x H Hin. exact (proj1 (Forall_forall _ _) H (o, x) Hin). Qed.
(* a string's bytes, NUL and slack lie in [p, p + cstr_span p s) *)
Lemma pn_sa_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall x, p <= x < p + seg_spec.cstr_span p s -> rd' x = rd x) -> sa_str rd' p s.
Proof.
intros rd rd' p s ((Hz & Hn) & Ht) K. unfold seg_spec.cstr_span in K.
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D2.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite K by lia. exact (Hz i Hi).
- intros x Hx. rewrite K; [exact (Ht x Hx)|]. lia.
Qed.
(* a sub-range of an addressable range *)
Lemma pn_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
  sa_addr rd q' n'.
Proof.
intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) H1 H2 H3.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
split; [exact (range_addressable_sub rd SHADOW_OFF q n q' n' A3 H1 H2)|].
intros _ s Hs. apply (A4 ltac:(lia)). unfold shadow_addr in *.
assert (D1 : (SHADOW_OFF + q / 8) / 8 <= (SHADOW_OFF + q' / 8) / 8)
  by (apply Z.div_le_mono; [lia | apply Z.add_le_mono_l, Z.div_le_mono; lia]).
assert (D2 : (SHADOW_OFF + (q' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia | apply Z.add_le_mono_l, Z.div_le_mono; lia]).
lia.
Qed.
Ltac pn_in := cbn [In]; repeat first [left; reflexivity | right].
Ltac pn_inmap := apply in_map; pn_in.
Ltac pn_reg HS r Hr :=
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

(* a callee-saved register from the end of run C back to the cut: run C kept it (HKC), snprintf preserved it
   (HP3), run B kept it (HKB), the memset preserved it (HP2) *)
Ltac pn_chain4 HKC HP3 HKB HP2 k :=
  rewrite (HKC (Z_to_bv 5 k)) by pn_inmap; rewrite (HP3 k) by (unfold acallee_saved; lia);
  rewrite (HKB (Z_to_bv 5 k)) by pn_inmap; rewrite (HP2 k) by (unfold acallee_saved; lia).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* buf's bytes are addressable: their 64 shadow cells are 0 in a scope with buf in (pf_fsh) *)
Lemma pn_buf_addr : forall (rd : reader) (sh F p len : Z) (sc : pf_scope),
  pf_fsh rd sh sc -> sc_buf sc = true -> sh = SHADOW_OFF + F / 8 -> F mod 8 = 0 ->
  in_app F 2048 -> F + 0x40 <= p -> p + len <= F + 0x240 -> 0 < len -> sa_addr rd p len.
Proof.
intros rd sh F p len sc HF Hb Hsh HF8 Happ H1 H2 H3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hac.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
unfold in_app, ASAN_CEIL, kLowShadowBeg in Happ.
assert (HC : forall i, 8 <= i < 72 -> rd (sh + i) = Some 0).
{ intros i Hi. rewrite (HF i) by lia. rewrite a5_shb_in by exact Hi. rewrite Hb. reflexivity. }
assert (HV : forall s, sh <= s < sh + 144 -> rd s <> None).
{ intros s Hs. replace s with (sh + (s - sh)) by lia. rewrite (HF (s - sh)) by lia. discriminate. }
split; [lia|]. split; [lia|]. split; [unfold amem_range; lia|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  replace (SHADOW_OFF + x / 8) with (sh + (x / 8 - F / 8)) by lia. apply HC. lia.
- intros _ s Hs. apply HV. unfold shadow_addr in Hs.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
  pose proof (Z.div_mod (p + len - 1) 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound (p + len - 1) 8 ltac:(lia)) as Me.
  pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as Dq.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as Mq.
  pose proof (Z.div_mod (SHADOW_OFF + (p + len - 1) / 8) 8 ltac:(lia)) as Dr.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + len - 1) / 8) 8 ltac:(lia)) as Mr.
  lia.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition pn_EA (rX : bvmap 5 word) (c : Z) : env := Eimg (Ereg rX [w64 (c + seg_spec.RC_N); w64 c]).
Definition pn_EC (rX : bvmap 5 word) (g h : Z) : env := Eimg (Ereg rX [w64 g; w64 h]).
Lemma pn_den_reg : forall regs extra (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs extra)) (SOff k 0) = getr regs r.
Proof.
intros regs extra k r H. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regs extra k r H), Z.add_0_r.
apply Z_to_bv_bv_unsigned.
Qed.

Section s. Context {fx : YK11.FPState}.
Lemma pn_seedA : forall (Wc : world SEGS) (rX : bvmap 5 word) memc c s1,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF ->
  0 <= c -> 4096 <= c + seg_spec.RC_N <= 140737479966720 -> (c + seg_spec.RC_N) mod 8 = 0 ->
  c + seg_spec.RC_N + 4 <= s1 + 0x80 -> s1 + 0xb8 <= 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0x80) = Some (c + seg_spec.RC_N) ->
  rdword (rdW Wc memc) (s1 + 0x90) = Some c ->
  rdword (rdW Wc memc) (s1 + 0xb0) = Some (shadow_addr (c + seg_spec.RC_N)) ->
  (forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H Wc) memc) (c + seg_spec.RC_N + o)) ->
  st_ok_pi SEGS VAL (pn_EA rX c) pn_ssA
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_NEW)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc c s1 R9 R22 Hc0 Hn1 Hn8 Hlt Hs1 K80 K90 KB0 Hw.
assert (HRN : seg_spec.RC_N = 11392) by reflexivity.
assert (E9 : ew (pn_EA rX c) 9 = w64 s1)
  by (unfold pn_EA; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl); exact R9).
assert (E22 : ew (pn_EA rX c) 22 = w64 SHADOW_OFF)
  by (unfold pn_EA; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact R22).
assert (E32 : ew (pn_EA rX c) 32 = w64 (c + seg_spec.RC_N))
  by (unfold pn_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (pn_EA rX c) 33 = w64 c)
  by (unfold pn_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (Hs0 : 0 <= s1) by (unfold seg_spec.RC_N in *; lia).
assert (Hc64 : c + seg_spec.RC_N < 2 ^ 64) by lia.
assert (Hsh : 0 <= shadow_addr (c + seg_spec.RC_N) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF.
  assert (0 <= (c + seg_spec.RC_N) / 8 <= c + seg_spec.RC_N)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
set (E := pn_EA rX c) in *.
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = c + seg_spec.RC_N) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold pn_ssA. apply pa_entry_st_ok_full.
- subst E. unfold pn_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pn_regA. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ s1 0x80 8 (SOff 32 0) (c + seg_spec.RC_N));
        [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K80) ].
      apply pn_denot. apply U_atom; [exact E32 | lia].
    * apply (chunk_ok_val SEGS E _ s1 0x90 8 (SOff 33 0) c);
        [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K90) ].
      apply pn_denot. apply U_atom; [exact E33 | lia].
    * apply (chunk_ok_val SEGS E _ s1 0xb0 8 _ (shadow_addr (c + seg_spec.RC_N)));
        [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ KB0) ].
      apply pn_denot. apply pn_U_shadow; [apply U_atom; [exact E32 | lia] | apply U_atom; [exact E22 | unfold SHADOW_OFF; lia] | lia].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Hw o Ho)|]. constructor.
- unfold pn_regA. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U32. repeat split; lia.
- split; [|split; exact I]. cbn [pn_factsA f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E22, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 3) with 8. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

Lemma pn_seedC : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 g h,
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0xa0 <= 2 ^ 64 -> 0 <= g < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0x38) = Some g -> rdword (rdW Wc memc) (s1 + 0x98) = Some h ->
  st_ok_pi SEGS VAL (pn_EC rX g h) pn_ssC
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_A8B_RET_SNPN)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 g h R9 Hs0 Hs1 Hg Hh K38 K98.
assert (E9 : ew (pn_EC rX g h) 9 = w64 s1)
  by (unfold pn_EC; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl); exact R9).
assert (E32 : ew (pn_EC rX g h) 32 = w64 g)
  by (unfold pn_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (pn_EC rX g h) 33 = w64 h)
  by (unfold pn_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
set (E := pn_EC rX g h) in *.
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold pn_ssC. apply pa_entry_st_ok_full.
- subst E. unfold pn_EC. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pn_regC. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS E _ s1 0x38 8 (SOff 32 0) g);
      [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K38) ].
    apply pn_denot. apply U_atom; [exact E32 | lia].
  + apply (chunk_ok_val SEGS E _ s1 0x98 8 (SOff 33 0) h);
      [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
        | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ K98) ].
    apply pn_denot. apply U_atom; [exact E33 | lia].
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.
End s.

Section e.
Variable B : asyms.
(* the callee texts of NEW (pf_pieces.v's per-segment list), at listing terms *)
Hypothesis AMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
(* the listing's objects over the walk's abstract instance (SegObj.v): the "%s" literal is object 35 *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma pn_fs_atom : forall E, img_env VAL A_LIM E -> ew E 276%nat = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E 276%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section c. Context {fx : YK11.FPState}.

(* pf_base at the state after NEW's calls, at the FP state fx1 snprintf returned: the journal again (the same
   layout and state), and the reader kept outside the block's write range [c, c + RC_N + 4) and the deepest
   callee window [s1 - CMD_SNP_K, s1) *)
Lemma pn_base_move : forall (fx1 : YK11.FPState) v pos Sc Wc rX memc mdc rX' mem' md',
  pf_base (fx := fx) B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc Wc mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v <= a < p_c v + seg_spec.RC_N + 4) ->
     ~ (pf_s1 v - 8192 <= a < pf_s1 v) -> rdW Wc mem' a = rdW Wc memc a) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base (fx := fx1) B v pos (p_ly v) Sc Wc rX' mem' md' PF_SC_LINE.
Proof.
intros fx1 v pos Sc Wc rX memc mdc rX' mem' md' HB Hfx HJ' K HRG'.
pose proof (a5_geo B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & _ & Hin5 & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (HJ & Hly & HSf & HPerm & HSAV & HFLG & HFRM & HRGF).
destruct HOBJ as (OSTR & OAT & OHT & OAC & OHC & OCAT & OLITS & OROD & OSSP).
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_heap_bounds B (p_ly v) Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR OHC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hbc1 & Hbc2 & Hbc3 & Hbc4 & Hbcapp).
destruct (a6_heap_bounds B (p_ly v) Sc Wc memc mdc (p_t v) (pf_len v) HAR OHT ltac:(unfold pf_len; lia))
  as (bt & mt & Hint & Hbt1 & Hbt2 & Hbt3 & Hbt4 & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc 5 pos HAR Hinc Hin5) as HBF.
unfold zdisjoint in HBF. cbn [fst snd] in HBF.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in HBF. change (fs_frame_bytes 5) with 2048 in HBF.
pose proof (blk_off_imgP B (p_ly v) Sc Wc memc mdc bc mc HAR Hinc) as HOFF. unfold off_img in HOFF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hac.
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
unfold in_app, ASAN_CEIL in Hbcapp.
assert (N1 : seg_spec.RC_N = 11392) by reflexivity. assert (N2 : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (N3 : kLowShadowBeg = 2147446784) by reflexivity. assert (N4 : kImgEnd = 6295552) by reflexivity.
pose proof (proj1 HJ') as HAR'.
assert (KP : pfk_keep (rdW Wc memc) (rdW Wc mem') (p_c v) (seg_spec.RC_N + 4) (pf_s1 v - 8192) (pf_s1 v)).
{ intros a Ha H1 H2. apply K; [exact Ha | intros ?; apply H1; lia | exact H2]. }
assert (KIMG : forall x, in_img SEGS x -> rdW Wc mem' x = rdW Wc memc x).
{ intros x Hx. pose proof (pa_img_range x Hx). apply K; [lia | | lia].
  intros Hb. exact (blk_img SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc x HAR Hinc ltac:(lia) Hx). }
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSf|]. split; [exact HPerm|].
  split; [apply (pfk_pf_saved _ _ _ _ _ _ _ _ KP HSAV); [lia | lia | unfold pfk_apart; lia]|].
  split.
  { change (fs_frame_bytes 5) with 2048 in *.
    rewrite (pfk_rdword _ _ _ _ _ _ _ KP); [exact HFLG | lia | lia | unfold pfk_apart; lia]. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|]. exact HRG'. }
split.
{ split.
  { apply (pn_sa_str_keep _ _ _ _ OSTR). intros x Hx.
    unfold sa_disj, seg_spec.cstr_span in HDJ. unfold seg_spec.cstr_span in Hx.
    pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as M.
    unfold pf_len in *. apply K; lia. }
  split; [exact (a6_heap_addr B (p_ly v) Sc Wc mem' md' _ _ HAR' OHT ltac:(unfold pf_len; lia))|].
  split; [exact OHT|].
  split; [exact (a6_heap_addr B (p_ly v) Sc Wc mem' md' _ _ HAR' OHC ltac:(lia))|].
  split; [exact OHC|].
  split; [exact (a6_cat_move B _ Wc mem' OCAT (fun x Hx _ _ => KIMG x Hx))|].
  split; [intros x Hx; exact (a6_lit_move B _ Wc mem' _ _ (OLITS x Hx) (fun y Hy _ _ => KIMG y Hy))|].
  split.
  { intros a Hro Ho He. destruct Hro as [(sg & Hsg & Hw & Hr) | Hr].
    - rewrite KIMG by (exists sg; split; [exact Hsg | exact Hr]).
      exact (OROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
    - assert (Hl : 0x10000 <= a < kImgEnd) by (unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr; lia).
      rewrite K by lia. exact (OROD a (or_intror Hr) Ho He). }
  apply (pfk_sa_ssp _ _ _ _ _ _ _ _ KP OSSP); unfold gotwA, guardA, pfk_apart; lia. }
split.
{ apply (pfk_pf_sl _ _ _ _ _ _ _ _ KP HSL). apply Forall_forall. intros ov Hov. unfold PF_SL in Hov.
  cbn [In] in Hov. repeat (destruct Hov as [<- | Hov]; [cbn [fst]; unfold pfk_apart; lia|]). destruct Hov. }
apply (pfk_pf_fsh _ _ _ _ _ _ _ _ KP HFSH); [lia | lia | unfold pfk_apart; lia].
Qed.

Lemma pfa8b_new : forall n : nat, HA_A8B_JOIN B n -> H_NEW (fx := fx) B n.
Proof.
intros n HJN. unfold H_NEW.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI.
destruct HI as (HB & HMID & HST & HSTR & HINB & HLEN & HFIND & HN32 & HSLB & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin5 & G & HFpre & HSHpre).
subst lyc.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & HSAV & HFLG & HFRM & HRGF).
pose proof HOBJ as (OSTR & OAT & OHT & OAC & OHC & OCAT & OLITS & OROD & OSSP).
pose proof HST as (HRC & HNM & HCNT).
pose proof HMID as (Holt & _ & _).
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_heap_bounds B (p_ly v) Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR OHC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hbc1 & Hbc2 & Hbc3 & Hbc4 & Hbcapp).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc 5 pos HAR Hinc Hin5) as HBF.
unfold zdisjoint in HBF. cbn [fst snd] in HBF.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in HBF. change (fs_frame_bytes 5) with 2048 in HBF.
pose proof (blk_off_imgP B (p_ly v) Sc Wc memc mdc bc mc HAR Hinc) as HOFF. unfold off_img in HOFF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hac.
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12). rewrite SPF in G1.
pose proof (pfa8b_o_ok v Hsp16) as (Ho16 & Ho0 & Ho336).
unfold in_app, ASAN_CEIL in Hbcapp.
assert (N1 : seg_spec.RC_N = 11392) by reflexivity. assert (N2 : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (N3 : kLowShadowBeg = 2147446784) by reflexivity. assert (N4 : kImgEnd = 6295552) by reflexivity.
assert (N5 : seg_spec.RC_GEN = 16608) by reflexivity. assert (N6 : ESTACK = 4096) by reflexivity.
assert (N7 : RtPFCmd.CMD_SNP_K = 8192) by reflexivity. assert (N8 : seg_litA_rc F_s = 136000) by (vm_compute; reflexivity).
pose proof HSTR as ((HZS & HNZ) & HTL).
pose proof (pfa8b_bytes_range_aview SEGS (w_H Wc) memc np name HSTR) as HNR.
rewrite (pfa8b_step_new cf nm name (ln + 1) HFIND HN32).
set (c := p_c v) in *. set (sp0 := pf_sp0 v) in *. set (s1 := pf_s1 v) in *.
set (SH := pf_SH v pos) in *. set (F := pf_F v pos) in *.
set (nn := length (rc_seg cf)) in *.
set (dn := seg_spec.rseg_addr c nn).
assert (Edn : dn = c + 356 * Z.of_nat nn) by reflexivity.
unfold pf_inb, PF_O_BUF in HINB.
(* the registers of the cut *)
assert (R2 : getr rX (Z_to_bv 5 2) = w64 s1) by (eapply a5_rg_get; [exact HRGF | pn_in]).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (eapply a5_rg_get; [exact HRGF | pn_in]).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (eapply a5_rg_get; [exact HRGF | pn_in]).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 s1) by (eapply a5_rg_get; [exact HRGF | pn_in]).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF) by (eapply a5_rg_get; [exact HRGF | pn_in]).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (Z.of_nat nn))
  by (eapply a5_rg_get; [exact HRG | apply in_or_app; left; pn_in]).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 np)
  by (eapply a5_rg_get; [exact HRG | apply in_or_app; left; pn_in]).
(* the block bytes this sub-walk writes: c->n and the new entry, both in the block and in parse_file's
   footprint *)
assert (HAWR : forall a, c <= a < c + seg_spec.RC_N + 4 ->
  awr_byte SEGS B STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) (ablocks B (p_ly v) (p_S v))
    (ablocks B (p_ly v) Sc) (frames (p_S v)) (p_ly v) [(5, pos)] a).
{ intros a Ha. right; left. split; [apply pfa8b_fp_block; lia|]. exists bc, mc. split; [exact Hinc | lia]. }
assert (HVAC : forall (M : word -> option byte) a, c <= a < c + seg_spec.RC_N + 4 ->
  inFP (seg_spec.RC_PARSE_W c) a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ sp0 <= a < ly_top (p_ly v) ->
  writable_at SEGS (mrestrict (w_H Wc) M) a).
{ intros M a Ha _ [[_ Hi] | Hs]; exfalso; [|lia].
  exact (blk_img SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc a HAR Hinc ltac:(lia) Hi). }
(* ======== run A: 0x8890c .. 0x88940, check #35, c->n = n + 1, s4 = &seg[n], to the memset ======== *)
assert (K80 : rdword (rdW Wc memc) (s1 + 0x80) = Some (c + seg_spec.RC_N))
  by (apply (pn_sl_get _ _ _ _ _ HSL); unfold PF_SL; pn_in).
assert (K90 : rdword (rdW Wc memc) (s1 + 0x90) = Some c) by (apply (pn_sl_get _ _ _ _ _ HSL); unfold PF_SL; pn_in).
assert (KB0 : rdword (rdW Wc memc) (s1 + 0xb0) = Some (shadow_addr (c + seg_spec.RC_N)))
  by (apply (pn_sl_get _ _ _ _ _ HSLB); pn_in).
assert (HWA : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H Wc) memc) (c + seg_spec.RC_N + o)).
{ intros o' Ho'.
  exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
    (HAWR (c + seg_spec.RC_N + o') ltac:(lia)) (HVAC memc (c + seg_spec.RC_N + o') ltac:(lia)))). }
assert (Hc8 : (c + seg_spec.RC_N) mod 8 = 0).
{ rewrite N1. pose proof (Z.div_mod c 16 ltac:(lia)) as D. rewrite Hc16, Z.add_0_r in D. rewrite D.
  replace (16 * (c / 16) + 11392) with ((2 * (c / 16) + 1424) * 8) by lia. apply Z_mod_mult. }
pose proof (pn_seedA (fx := fx) Wc rX memc c s1 R9 R22 ltac:(lia) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)
  K80 K90 KB0 HWA) as HS.
assert (HEI : img_env VAL A_LIM (pn_EA rX c)) by (unfold pn_EA; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [w64 (c + seg_spec.RC_N); w64 c]) (pn_EA rX c))
  by (split; [intros k Hk; unfold pn_EA; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EA : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (pn_EA rX c) k = getr rX r)
  by (intros k r Hk; unfold pn_EA; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EA32 : ew (pn_EA rX c) 32 = w64 (c + seg_spec.RC_N))
  by (unfold pn_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (EA33 : ew (pn_EA rX c) 33 = w64 c)
  by (unfold pn_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
revert HS HEI HA0 EA EA32 EA33. generalize (pn_EA rX c) as E. intros E HS HEI HA0 EA EA32 EA33.
assert (U22 : U E (SOff 22 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EA 22%nat (Z_to_bv 5 22) eq_refl); exact R22 | unfold SHADOW_OFF; lia]).
assert (U19 : U E (SOff 19 0) = Z.of_nat nn)
  by (apply U_atom; [rewrite (EA 19%nat (Z_to_bv 5 19) eq_refl); exact R19 | lia]).
assert (U32 : U E (SOff 32 0) = c + seg_spec.RC_N) by (apply U_atom; [exact EA32 | lia]).
assert (U33 : U E (SOff 33 0) = c) by (apply U_atom; [exact EA33 | lia]).
assert (B32 : bv_unsigned (ew E 32) = c + seg_spec.RC_N) by (rewrite EA32; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS pn_Bx pn_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pn_SH. apply Forall_cons; [|apply Forall_nil].
  pose proof OAC as (_ & _ & _ & HRAc & _).
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E pn_Bx 32%nat c seg_spec.SEG_C_SIZE (c + seg_spec.RC_N) 0 8
    HRAc U22 U32); [lia | lia |].
  intros x Hx. change (Z.min 0 8) with 0 in Hx. change (Z.max 0 8) with 8 in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + PF_NEW)) with (Z_to_bv 64 (BASE + PF_NEW)).
pose proof (paj_run (fx := fx) B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := c + seg_spec.RC_N); [reflexivity | exact B32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HAWR. lia. }
set (mdA := with_vm_backing _ _ _) in *; clearbody mdA.
rename ms into msA.
assert (KMA : forall a, 0 <= a < 2 ^ 64 -> ~ (c + seg_spec.RC_N <= a < c + seg_spec.RC_N + 4) ->
  rdW Wc (ms_mem msA) a = rdW Wc memc a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem msA)
    (fun a' => c + seg_spec.RC_N <= a' < c + seg_spec.RC_N + 4) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; [lia | rewrite B32 in Hrr; lia]. }
(* the 4 bytes the `sw` wrote at c + RC_N: n + 1 *)
assert (HSTB : forall k, (k < 4)%nat ->
  rdW Wc (ms_mem msA) (c + seg_spec.RC_N + Z.of_nat k) = Some (le_byte (Z.of_nat nn + 1) 4 k)).
{ intros k Hk.
  pose proof (st_ok_region_nth E _ _ 1
    (YP09.mkRegion (Some 32%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 19 1))]) HS ltac:(vm_compute; reflexivity)) as Hr.
  pose proof (field_of_region_any E _ 32 (c + seg_spec.RC_N) _ 0 4 0 4 0 4 (SOff 19 1) Hr B32 (or_introl eq_refl)
    ltac:(lia)) as V.
  cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V.
  assert (U19' : bv_unsigned (sv_denot E (SOff 19 1)) = Z.of_nat nn + 1).
  { change (bv_unsigned (sv_denot E (SOff 19 1))) with (U E (SOff 19 1)).
    apply U_atom_off; [rewrite (EA 19%nat (Z_to_bv 5 19) eq_refl); exact R19 | lia | lia]. }
  rewrite U19' in V. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V.
  rewrite (Z.mod_small (Z.of_nat nn + 1)) in V by lia.
  unfold aview. rewrite (V k Hk). cbn [option_map]. f_equal. apply pn_bv8.
  unfold le_byte. apply Z.mod_pos_bound. lia. }
(* the registers after run A *)
pose proof (regs_kept_of_st_ok SEGS E _ _ rX [w64 (c + seg_spec.RC_N); w64 c]
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 21; 22; 25; 26; 27]) HS HA0 ltac:(vm_compute; reflexivity)) as HKA.
cbn [ms_regs restrict] in HKA.
pn_reg HS (Z_to_bv 5 10) RA10. pn_reg HS (Z_to_bv 5 20) RA20. pn_reg HS (Z_to_bv 5 24) RA24.
pn_reg HS (Z_to_bv 5 11) RA11. pn_reg HS (Z_to_bv 5 12) RA12.
prreg HS (1%bv : bv 5) RA1.
assert (Udn : U E (SAlu ALU_ADD (SMd M_MUL (SOff 19 0) (SLit 356)) (SOff 33 0)) = dn)
  by (rewrite Edn; apply pn_U_seg; [exact U33 | exact U19 | lia | lia | lia]).
rewrite (pn_denot _ _ _ Udn) in RA10, RA20.
rewrite (pn_denot _ _ _ U33) in RA24.
cbn [sv_denot] in RA11, RA12.
clear HF HFr HG.
pmkst HS.
set (oo := s1 - sp0) in *. assert (Eoo : oo = s1 - sp0) by reflexivity.
assert (Hsp : spZ (ms_regs msA) = sp0 + oo).
{ unfold spZ. pn_unlit. rewrite (HKA (Z_to_bv 5 2)) by pn_inmap. rewrite R2.
  unfold w64. rewrite unsigned_lit_small by lia. unfold oo. lia. }
change 15376 with PF_A8B_RET_MEMSET in RA1.
(* ======== the checked memset of the new entry (0x88940) ======== *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) (AMSET fx) Wc (ms_regs msA) (ms_mem msA)
    STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)]
    (p_ly v) Sc mdA 0 dn 0 356 oo (Z_to_bv 64 (BASE + PF_A8B_RET_MEMSET)) HJ).
  - pn_unlit. exact RA10.
  - pn_unlit. exact RA11.
  - pn_unlit. exact RA12.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact Ho16.
  - exact Ho0.
  - lia.
  - pn_unlit. rewrite (HKA (Z_to_bv 5 3)) by pn_inmap. exact R3.
  - pn_unlit. rewrite (HKA (Z_to_bv 5 4)) by pn_inmap. exact R4.
  - exact RA1.
  - apply ret_ok_codeptr_v; [unfold PF_A8B_RET_MEMSET, AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split; [apply HAWR; lia | lia].
  - intros a Ha. apply HVAC. lia.
  - pose proof OAC as (_ & _ & HAM & _). unfold amem_range in *. lia.
  - pose proof (a6_heap_addr B (p_ly v) Sc Wc (ms_mem msA) mdA c seg_spec.SEG_C_SIZE (proj1 HJ) OHC ltac:(lia)) as HA.
    exact (proj1 (proj2 (proj2 (proj2 (pn_addr_sub _ _ _ dn 356 HA ltac:(lia) ltac:(lia) ltac:(lia)))))).
  - intros _.
    pose proof (a6_heap_addr B (p_ly v) Sc Wc (ms_mem msA) mdA c seg_spec.SEG_C_SIZE (proj1 HJ) OHC ltac:(lia)) as HA.
    exact (proj2 (proj2 (proj2 (proj2 (pn_addr_sub _ _ _ dn 356 HA ltac:(lia) ltac:(lia) ltac:(lia))))) ltac:(lia)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR2a & HSET & HK2 & HPR2 & HSM2).
cbn iota in HSET.
(* ======== run B: 0x88944 .. 0x88958, the snprintf's arguments ======== *)
pose proof (pfa8b_seed (fx := fx) PF_A8B_RET_MEMSET Wc regs2 mem2) as HSB.
assert (HEIB : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HAB : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HSB HJ2.
{ apply awr_ok_nil. }
set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
rename ms into msB.
assert (KMB : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msB) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) mem2 (ms_mem msB) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 []
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]) HSB HAB ltac:(vm_compute; reflexivity)) as HKB.
cbn [ms_regs restrict] in HKB.
pn_reg HSB (Z_to_bv 5 10) RB10. pn_reg HSB (Z_to_bv 5 11) RB11. pn_reg HSB (Z_to_bv 5 12) RB12.
pn_reg HSB (Z_to_bv 5 13) RB13.
pn_reg HSB (1%bv : bv 5) RB1. change (SOff 240 15400) with (SOff A_TEXT 15400) in RB1.
rewrite (codeptr_val _ 15400 HEIB) in RB1.
clear HF HFr HG.
(* the registers at the snprintf call, against the cut's *)
assert (QB2 : getr (ms_regs msB) (Z_to_bv 5 2) = w64 s1).
{ rewrite (HKB (Z_to_bv 5 2)) by pn_inmap. rewrite (HP2 2) by (unfold acallee_saved; lia).
  rewrite (HKA (Z_to_bv 5 2)) by pn_inmap. exact R2. }
assert (QB3 : getr (ms_regs msB) (Z_to_bv 5 3) = w64 (as_gp B)).
{ rewrite (HKB (Z_to_bv 5 3)) by pn_inmap. rewrite (HP2 3) by (unfold acallee_saved; lia).
  rewrite (HKA (Z_to_bv 5 3)) by pn_inmap. exact R3. }
assert (QB4 : getr (ms_regs msB) (Z_to_bv 5 4) = w64 (as_tp B)).
{ rewrite (HKB (Z_to_bv 5 4)) by pn_inmap. rewrite (HP2 4) by (unfold acallee_saved; lia).
  rewrite (HKA (Z_to_bv 5 4)) by pn_inmap. exact R4. }
assert (QB10 : getr (ms_regs msB) (Z_to_bv 5 10) = w64 dn).
{ rewrite RB10, (pn_den_reg regs2 [] 20 (Z_to_bv 5 20) eq_refl). rewrite (HP2 20) by (unfold acallee_saved; lia).
  exact RA20. }
assert (QB11 : getr (ms_regs msB) (Z_to_bv 5 11) = w64 16) by (rewrite RB11; reflexivity).
assert (QB12 : getr (ms_regs msB) (Z_to_bv 5 12) = w64 (seg_litA_rc F_s)).
{ rewrite RB12. cbn [sv_denot]. rewrite (pn_fs_atom _ HEIB). unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity. }
assert (QB13 : getr (ms_regs msB) (Z_to_bv 5 13) = w64 np).
{ rewrite RB13, (pn_den_reg regs2 [] 25 (Z_to_bv 5 25) eq_refl). rewrite (HP2 25) by (unfold acallee_saved; lia).
  rewrite (HKA (Z_to_bv 5 25)) by pn_inmap. exact R25. }
pmkst HSB.
change 15400 with PF_A8B_RET_SNPN in RB1.
assert (HspB : spZ (ms_regs msB) = sp0 + oo).
{ unfold spZ. pn_unlit. rewrite QB2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* what the reader at the snprintf call keeps of the cut's: everything off the block's writes and the windows *)
assert (KT : pfk_keep (rdW Wc memc) (rdW Wc (ms_mem msB)) c (seg_spec.RC_N + 4) (s1 - 8192) s1).
{ intros a Ha H1 H2. rewrite KMB by exact Ha. rewrite HK2 by lia. apply KMA; lia. }
assert (KIMG_T : forall x, in_img SEGS x -> rdW Wc (ms_mem msB) x = rdW Wc memc x).
{ intros x Hx. pose proof (pa_img_range x Hx). apply KT; [lia | | lia].
  intros Hb. exact (blk_img SEGS B LAWS (p_ly v) Sc Wc memc mdc bc mc x HAR Hinc ltac:(lia) Hx). }
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite G8, Z.add_0_r in D. rewrite D.
  replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
assert (HFSH_T : pf_fsh (rdW Wc (ms_mem msB)) SH PF_SC_LINE).
{ apply (pfk_pf_fsh _ _ _ _ _ _ _ _ KT HFSH); [lia | lia | unfold pfk_apart; lia]. }
assert (HSTR_T : sa_str (rdW Wc (ms_mem msB)) np name).
{ apply (pfk_sa_str _ _ _ _ _ _ _ _ KT HSTR); [lia | lia | unfold pfk_apart, PF_O_BUF in *; lia]. }
assert (HinFs : In F_s PARSE_FILE_LITS) by (unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity).
pose proof (a6_lit_move B _ Wc (ms_mem msB) _ _ (OLITS F_s HinFs) (fun y Hy _ _ => KIMG_T y Hy)) as LITT.
pose proof LITT as (_ & HSFs & HPFs & _ & _).
pose proof (HPFs (p_ly v) Sc Wc (ms_mem msB) mdB (proj1 HJ2)) as HAFs.
change (Z.of_nat (length F_s) + 1) with 3 in HAFs.
destruct (pn_snlen name ltac:(lia)) as (HSL15 & HSB15).
pose proof (Z.mod_pos_bound (- (np + Z.of_nat (length name) + 1)) 8 ltac:(lia)) as Hspan.
(* ======== snprintf(&seg[n], 16, "%s", np) (0x88958) ======== *)
eapply SRr_bind.
{ apply (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (SIGMA SS___interceptor_trampoline_snprintf)
    (ASNP fx) Wc (ms_regs msB) (ms_mem msB) STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc mdB 0 dn 16 (seg_litA_rc F_s) name oo
    (Z_to_bv 64 (BASE + PF_A8B_RET_SNPN)) HJ2).
  - pn_unlit. exact QB10.
  - pn_unlit. exact QB11.
  - pn_unlit. exact QB12.
  - lia.
  - lia.
  - lia.
  - exact HspB.
  - exact Ho16.
  - exact Ho0.
  - lia.
  - pn_unlit. exact QB3.
  - pn_unlit. exact QB4.
  - exact RB1.
  - apply ret_ok_codeptr_v; [unfold PF_A8B_RET_SNPN, AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split; [apply HAWR; lia | lia].
  - intros a Ha. apply HVAC. lia.
  - pose proof OAC as (_ & _ & HAM & _). unfold amem_range in *. lia.
  - pose proof (a6_heap_addr B (p_ly v) Sc Wc (ms_mem msB) mdB c seg_spec.SEG_C_SIZE (proj1 HJ2) OHC ltac:(lia)) as HA.
    exact (proj1 (proj2 (proj2 (proj2 (pn_addr_sub _ _ _ dn 16 HA ltac:(lia) ltac:(lia) ltac:(lia)))))).
  - pose proof (a6_heap_addr B (p_ly v) Sc Wc (ms_mem msB) mdB c seg_spec.SEG_C_SIZE (proj1 HJ2) OHC ltac:(lia)) as HA.
    exact (proj2 (proj2 (proj2 (proj2 (pn_addr_sub _ _ _ dn 16 HA ltac:(lia) ltac:(lia) ltac:(lia))))) ltac:(lia)).
  - unfold off_img. rewrite HSL15. lia.
  - unfold RtPFCmd.CMD_IMG_HI. lia.
  - unfold aguard_ok. exact (pfk_sa_ssp _ _ _ _ _ _ _ _ KT OSSP ltac:(unfold gotwA; lia) ltac:(unfold gotwA; lia)
      ltac:(unfold guardA; lia) ltac:(unfold guardA; lia) ltac:(unfold gotwA, pfk_apart; lia)
      ltac:(unfold guardA, pfk_apart; lia)).
  - unfold gotwA. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_HI. lia.
  - unfold guardA. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_HI. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_LO. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_LO. lia.
  - apply (pfa8b_FR_s_regs _ _ _ np).
    + unfold argZ. change (10 + 3) with 13. pn_unlit. rewrite QB13. unfold w64. apply unsigned_lit_small. lia.
    + lia.
    + unfold RtPFCmd.CMD_IMG_LO. lia.
    + unfold RtPFCmd.CMD_GOTW. lia.
    + exact HSFs.
    + exact HAFs.
    + unfold RtPFShared.snp_out. rewrite HspB, HSL15.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
    + lia.
    + exact HNR.
    + lia.
    + exact HSTR_T.
    + apply (pn_buf_addr _ SH F np _ PF_SC_LINE HFSH_T eq_refl G10 HF8 G9); unfold PF_O_BUF in *; lia.
    + unfold in_app, ASAN_CEIL, amem_range in *. lia.
    + unfold RtPFShared.snp_out, seg_spec.cstr_span. rewrite HspB, HSL15.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold PF_O_BUF in *; lia|].
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold PF_O_BUF in *; lia | apply Forall_nil].
  - lia.
  - intros a Hrom Ho He. rewrite KIMG_T by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; assumption).
    exact (a5_rom B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_LINE HB a Hrom Ho He).
  - exact HFRM. }
cbv beta. intros W3 c3 _ (-> & fx1 & regs3 & mem3 & md3 & Hfx1 & -> & HJ3 & HP3 & HR3a & HSNB & HK3 & HPR3 & HSM3).
rewrite HSL15 in HK3, HSNB. rewrite HSB15 in HSNB.
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
(* the reader after the snprintf against the cut's: off the new entry, c->n and the deepest window *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (dn <= a < dn + 356) -> ~ (c + seg_spec.RC_N <= a < c + seg_spec.RC_N + 4) ->
  ~ (s1 - 8192 <= a < s1) -> rdW Wc mem3 a = rdW Wc memc a).
{ intros a Ha H1 H2 H3. rewrite HK3 by lia. rewrite KMB by exact Ha. rewrite HK2 by lia. apply KMA; lia. }
(* ======== run C: 0x8895c .. 0x889b4, s3 and a3 reloaded, at the FP state snprintf returned ======== *)
assert (Q39 : getr regs3 (Z_to_bv 5 9) = w64 s1).
{ rewrite (HP3 9) by (unfold acallee_saved; lia). rewrite (HKB (Z_to_bv 5 9)) by pn_inmap.
  rewrite (HP2 9) by (unfold acallee_saved; lia). rewrite (HKA (Z_to_bv 5 9)) by pn_inmap. exact R9. }
assert (K38 : rdword (rdW Wc mem3) (s1 + 0x38) = Some (shadow_addr (c + seg_spec.RC_GEN))).
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem3) (s1 + 0x38)) by (intros k Hk; apply K3; lia).
  apply (pn_sl_get _ _ _ _ _ HSL). unfold PF_SL. pn_in. }
assert (K98 : rdword (rdW Wc mem3) (s1 + 0x98) = Some (SH + 8)).
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem3) (s1 + 0x98)) by (intros k Hk; apply K3; lia).
  apply (pn_sl_get _ _ _ _ _ HSL). unfold PF_SL. pn_in. }
assert (Hg : 0 <= shadow_addr (c + seg_spec.RC_GEN) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (c + seg_spec.RC_GEN) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (c + seg_spec.RC_GEN) 8 ltac:(lia)). lia. }
pose proof (pn_seedC (fx := fx1) Wc regs3 mem3 s1 (shadow_addr (c + seg_spec.RC_GEN)) (SH + 8) Q39 ltac:(lia)
  ltac:(lia) Hg ltac:(lia) K38 K98) as HSC.
assert (HEIC : img_env VAL A_LIM (pn_EC regs3 (shadow_addr (c + seg_spec.RC_GEN)) (SH + 8)))
  by (unfold pn_EC; apply Eimg_env).
assert (HAC : env_agree 32 (Ereg regs3 [w64 (shadow_addr (c + seg_spec.RC_GEN)); w64 (SH + 8)])
  (pn_EC regs3 (shadow_addr (c + seg_spec.RC_GEN)) (SH + 8)))
  by (split; [intros k Hk; unfold pn_EC; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HSC HJ3 PF_A8B_JOIN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
set (mdC := with_vm_backing _ _ _) in *; clearbody mdC.
rename ms into msC.
assert (KMC : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msC) a = rdW Wc mem3 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) mem3 (ms_mem msC) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-. lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 [w64 (shadow_addr (c + seg_spec.RC_GEN)); w64 (SH + 8)]
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]) HSC HAC ltac:(vm_compute; reflexivity)) as HKC.
cbn [ms_regs restrict] in HKC.
pn_reg HSC (Z_to_bv 5 19) RC19. pn_reg HSC (Z_to_bv 5 13) RC13.
rewrite (pn_denot _ _ (SH + 8)) in RC19
  by (apply U_atom; [unfold pn_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1) | lia]).
rewrite (pn_denot _ _ (shadow_addr (c + seg_spec.RC_GEN))) in RC13
  by (apply U_atom; [unfold pn_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0) | lia]).
clear HF HFr HG.
pmkst HSC.
(* the registers JOIN asks for, and pf_fi's *)
assert (F2 : getr (ms_regs msC) (Z_to_bv 5 2) = w64 s1)
  by (pn_chain4 HKC HP3 HKB HP2 2; rewrite (HKA (Z_to_bv 5 2)) by pn_inmap; exact R2).
assert (F3 : getr (ms_regs msC) (Z_to_bv 5 3) = w64 (as_gp B))
  by (pn_chain4 HKC HP3 HKB HP2 3; rewrite (HKA (Z_to_bv 5 3)) by pn_inmap; exact R3).
assert (F4 : getr (ms_regs msC) (Z_to_bv 5 4) = w64 (as_tp B))
  by (pn_chain4 HKC HP3 HKB HP2 4; rewrite (HKA (Z_to_bv 5 4)) by pn_inmap; exact R4).
assert (F8 : getr (ms_regs msC) (Z_to_bv 5 8) = w64 sp0)
  by (pn_chain4 HKC HP3 HKB HP2 8; rewrite (HKA (Z_to_bv 5 8)) by pn_inmap; eapply a5_rg_get; [exact HRGF | pn_in]).
assert (F9 : getr (ms_regs msC) (Z_to_bv 5 9) = w64 s1)
  by (pn_chain4 HKC HP3 HKB HP2 9; rewrite (HKA (Z_to_bv 5 9)) by pn_inmap; exact R9).
assert (F22 : getr (ms_regs msC) (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (pn_chain4 HKC HP3 HKB HP2 22; rewrite (HKA (Z_to_bv 5 22)) by pn_inmap; exact R22).
assert (F18 : getr (ms_regs msC) (Z_to_bv 5 18) = w64 0x23)
  by (pn_chain4 HKC HP3 HKB HP2 18; rewrite (HKA (Z_to_bv 5 18)) by pn_inmap;
      eapply a5_rg_get; [exact HRG | apply in_or_app; left; pn_in]).
assert (F27 : getr (ms_regs msC) (Z_to_bv 5 27) = w64 SH)
  by (pn_chain4 HKC HP3 HKB HP2 27; rewrite (HKA (Z_to_bv 5 27)) by pn_inmap;
      eapply a5_rg_get; [exact HRG | apply in_or_app; left; pn_in]).
assert (F25 : getr (ms_regs msC) (Z_to_bv 5 25) = w64 np)
  by (pn_chain4 HKC HP3 HKB HP2 25; rewrite (HKA (Z_to_bv 5 25)) by pn_inmap; exact R25).
assert (F21 : getr (ms_regs msC) (Z_to_bv 5 21) = w64 (p_t v + Z.of_nat (pf_next (p_s v) o)))
  by (pn_chain4 HKC HP3 HKB HP2 21; rewrite (HKA (Z_to_bv 5 21)) by pn_inmap;
      eapply a5_rg_get; [exact HRG | apply in_or_app; right; unfold PF_RM; pn_in]).
assert (F26 : getr (ms_regs msC) (Z_to_bv 5 26) = w64 (ln + 1))
  by (pn_chain4 HKC HP3 HKB HP2 26; rewrite (HKA (Z_to_bv 5 26)) by pn_inmap;
      eapply a5_rg_get; [exact HRG | apply in_or_app; right; unfold PF_RM; pn_in]).
assert (F24 : getr (ms_regs msC) (Z_to_bv 5 24) = w64 c) by (pn_chain4 HKC HP3 HKB HP2 24; exact RA24).
assert (F20 : getr (ms_regs msC) (Z_to_bv 5 20) = w64 dn) by (pn_chain4 HKC HP3 HKB HP2 20; exact RA20).
assert (HRGFI : pf_rg (ms_regs msC) (a5_FI B v)).
{ unfold a5_FI, pf_rg. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil. }
(* the reader at JOIN against the cut's *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (dn <= a < dn + 356) -> ~ (c + seg_spec.RC_N <= a < c + seg_spec.RC_N + 4) ->
  ~ (s1 - 8192 <= a < s1) -> rdW Wc (ms_mem msC) a = rdW Wc memc a).
{ intros a Ha H1 H2 H3. rewrite KMC by exact Ha. exact (K3 a Ha H1 H2 H3). }
assert (KPF : pfk_keep (rdW Wc memc) (rdW Wc (ms_mem msC)) c (seg_spec.RC_N + 4) (s1 - 8192) s1).
{ intros a Ha H1 H2. apply KF; lia. }
assert (Ern : seg_spec.rseg_addr c nn = dn) by reflexivity.
(* the new entry's 356 bytes: name, its NUL, zeros *)
set (nw := seg_spec.zb (name ++ [0])).
assert (Lnw : length nw = S (length name)) by (unfold nw, seg_spec.zb; rewrite length_map, length_app; cbn [length]; lia).
set (f := pfa8b_splice 0 nw (repeat seg_spec.ZERO 356)).
assert (Lf : length f = 356%nat) by (unfold f; rewrite pfa8b_splice_len by (rewrite repeat_length; lia); apply repeat_length).
assert (HR0 : Forall (fun z => 0 <= z < 256) (name ++ [0])).
{ apply Forall_app. split; [|constructor; [lia | constructor]].
  eapply Forall_impl; [|exact HNR]. intros z Hz. cbv beta in *. lia. }
assert (HGF : seg_spec.rseg_enc (rseg0 (snprintf_s 16 F_s [AS name])) f).
{ rewrite (pfa8b_snprintf_name16 name HNZ ltac:(lia)). apply pfa8b_rseg0_enc.
  - exact Lf.
  - intros k Hk. unfold f. rewrite pfa8b_splice_nth_out by (rewrite ?repeat_length; lia).
    apply nth_repeat.
  - unfold f. rewrite (pfa8b_fld_splice_in 0 16 0 0) by (rewrite ?repeat_length; lia).
    apply pfa8b_cstr_splice0; [unfold seg_spec.fld; rewrite length_firstn, length_skipn, repeat_length; lia
      | lia | exact HNZ | eapply Forall_impl; [|exact HNR]; intros z Hz; cbv beta in *; lia]. }
assert (HBf : sa_bytes (rdW Wc (ms_mem msC)) dn f).
{ intros i Hi. rewrite Lf in Hi. rewrite KMC by lia.
  destruct (Nat.lt_ge_cases i (S (length name))) as [Hin | Hout].
  - rewrite (HSNB (Z.of_nat i)) by lia. rewrite Nat2Z.id. unfold f.
    rewrite pfa8b_splice_nth_in by (rewrite ?repeat_length; lia). rewrite Nat.sub_0_r. unfold nw, seg_spec.zb.
    change ZB0 with (Z_to_bv 8 0). rewrite map_nth. f_equal. symmetry. apply pn_bv8.
    apply (proj1 (Forall_nth _ _) HR0). rewrite length_app. cbn [length]. lia.
  - rewrite HK3 by lia. rewrite KMB by lia. rewrite (HSET (Z.of_nat i)) by lia. unfold f.
    rewrite pfa8b_splice_nth_out by (rewrite ?repeat_length; lia). change ZB0 with seg_spec.ZERO.
    rewrite nth_repeat. reflexivity. }
assert (HBn : sa_bytes (rdW Wc (ms_mem msC)) (c + seg_spec.RC_N) (Z_to_le_bytes 4 (Z.of_nat nn + 1))).
{ intros k Hk. change (length (Z_to_le_bytes 4 (Z.of_nat nn + 1))) with 4%nat in Hk.
  rewrite KMC by lia. rewrite HK3 by lia. rewrite KMB by lia. rewrite HK2 by lia.
  rewrite (HSTB k Hk). rewrite (pn_le4 (Z.of_nat nn + 1) k ltac:(lia) Hk). reflexivity. }
(* ======== JOIN (0x889b4), at the FP state fx1 ======== *)
apply (HJN fx1 v pos (p_ly v) Sc Wc (ms_regs msC) (ms_mem msC) mdC
  (r_set_segs cf (rc_seg cf ++ [rseg0 (snprintf_s 16 F_s [AS name])])) nm o ln d np name nn).
unfold INV_A8B_JOIN.
unfold dn, c, sp0, s1, SH, F in *.
split.
{ apply (pn_base_move fx1 v pos Sc Wc rX memc mdc (ms_regs msC) (ms_mem msC) mdC HB Hfx1 HJ3).
  - intros a Ha H1 H2. apply KF; lia.
  - exact HRGFI. }
split; [exact HMID|].
split.
{ split.
  { apply (pfa8b_rconf_newseg (rdW Wc memc) (rdW Wc (ms_mem msC)) (p_c v) cf _ f (Z_to_le_bytes 4 (Z.of_nat nn + 1))
      HRC HN32 ltac:(lia) HGF (pn_u32 (Z.of_nat nn + 1) ltac:(lia))); [|exact HBf | exact HBn].
    intros x Hx H1 H2. change (length (rc_seg cf)) with nn in H1. apply KF; lia. }
  split.
  { apply (pfk_pf_nm _ _ _ _ _ _ _ _ KPF HNM); unfold pfk_apart, PF_O_CN; lia. }
  apply (pf_cnt_mono _ (length (skipn o (p_s v)))); [|exact HCNT].
  pose proof (pf_next_skipn_lt (p_s v) o Holt). lia. }
split.
{ apply (pfk_sa_str _ _ _ _ _ _ _ _ KPF HSTR); [lia | lia | unfold pfk_apart; lia]. }
split; [exact HINB|].
split; [exact HLEN|].
split; [cbn [r_set_segs rc_seg]; rewrite length_app; cbn [length]; lia|].
unfold pf_rg. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
- unfold PF_RM. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
Qed.


End c.
End e.
End f.
End d.
