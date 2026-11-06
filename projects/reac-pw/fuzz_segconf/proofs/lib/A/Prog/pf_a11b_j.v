(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of check_reply_answer's ASan walk (plugin-hostd/fuzz_command), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the walk's kit: regions, facts, register files, seed lemma cl_seed) over fuzz_command's listing (lib/A/Prog/CmdList.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_answer_k.v, with its module paths and module names changed; 883 of its 932 lines of code are new or changed and 380 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_chain_s3.v, with its module paths and module names changed; 657 of its 738 lines of code are new or changed and 851 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the JOIN LOOP of segment A11b of reac_segconf_parse_file's
   walk (0x87a78), part of segment A11b's proof, by the G3 walk owner, 2026-10-30.

   proves function reac_segconf_parse_file (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates,
   origin/release/pau-projects-recipes, the unreleased proof delivery, cold/* heads, image-A address 0x87a78 /
   the released-proof index's query for reac_segconf_parse_file): this file proves one internal cut of
   that walk; the lookup is CONFIRMed (the rule-24 check 2026-10-30T15:42:08Z, the unit's internal record,
   commit dfb49d6ad789, path records/segp/g3-lookup.md), reuse
   verdict none: written new.

   Theorem pfj_kloop_ok : forall n, HA_KEXIT B n -> forall ti, ti < 11 -> H_KLOOP B n ti
   (lib/A/Prog/pf_a11b_d.v's cuts KLOOP 0x8865c and KEXIT 0x886c8).

   The code (the excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s, 27 instructions 0x8865c .. 0x886c4, eleven passes):
     0x8865c addi a0,zero,1 ; beq s3,a0 (s3 = ti + 1)         the separator: 0x88670 a3 = 0x21860 "" at pass 0,
                                                               0x88664 a3 = 0x21840 "|" after (auipc / addi, listing
                                                               objects 63 / 62, SegObj.seg_val_objs)
     0x88678 lbu a0,0(s4) ; bnez a0                           check 28: the shadow byte of row ti's 8-aligned token
                                                               word, a read-only region of its own on the s4 atom
                                                               (CVal 1 (SLit 0)); it is 0 because the table is pinned
                                                               (sa_cat's sa_pinned at the journal's AR)
     0x88680 ld a4,0(s7) ; a0 = known + kn ; a1 = 240 - kn ; a2 = "%s%s" (0x21820, object 64)
     0x88698 jal the snprintf trampoline                       pf_a8b_t.v's pfa8b_aj_snprintf_atSF under SNP, its
                                                               premises from pf_a11b_jsite.v's closed site lemma
                                                               pfj_snp_site_ok (FR_cmd at "%s%s": pf_a11b_js.v)
     0x8869c a2 = 240 ; ld a1,0x70(s1) ; ld a1,0(a1) (= 11) ; bgeu s3,a1 -> KEXIT (pass 10 only)
     0x886ac kn += a0 ; s3 += 1 ; s8 += 0x128 ; a0 = kn + 2 ; s4 += 0x25 ; s7 += 0x128 ; bltu a0,a2 -> 0x8865c
                                                               (always taken: kn <= 77 and a pass adds <= 12)
   The pass is pfj_head (the head, the separator split and the join: both arms give a3 the seed's atom 35, the
   separator's address) and pfj_body (from the join: the call, the reload, the exit test, the back edge). The call
   returns at an FP state fx1 of its own: the post is lifted with pfj_lift (PaFx.srr_apost_baseF_lift), the symbolic
   state moved by jafter_call_keep_pi and st_ok_pi_restrict_xfx, and the next cut (HA_KEXIT, or the next pass) is
   applied at fx1. The cut's facts cross the call through the step's own keep clause (every byte outside the
   destination [known + kn, known + kn + |T| + 1) and the scratch window below s1 is kept): pfj_carry, over
   pf_a11b_jk.v's pfj_keep and pfj_kmem_step; the registers come back because they are callee-saved and the
   pass writes none of pf_fi's / PF_RL's / PF_RM's. The loop is pfj_loop, by induction on the passes left
   (cwc_turn / cwc_loop_ok of proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_chain_s3.v at 501c0d516c69).
   Section hypotheses: SNP (the interceptor owner's row 4 at the listing's snprintf trampoline) and OBJ (SegObj.seg_val_objs,
   for the three literal atoms). No SSPX, no VRO, no SIGP, no TL: the stack-protector cells, the read-only view and
   the image facts come from the cut's own pf_obj and the step's keep clause. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFPf RtPFShared RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow
PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob SegPaLib PaCall PaDenot PaLibG PaLibF PaLibH PaSB PaCallRun
PaArt PaFx PaWalk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
reac_segconf_parse_file_c SegInstA pf_pieces pf_a11b_d pf_a11b_f pf_a8b_t pf_a11b_js pf_a5_k pf_a11b_jk
  pf_a11b_jsite.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x88680, after check 28: where the two arms of the separator choice join *)
Definition PF_KCHK : Z := AF_reac_segconf_parse_file + 0xc08.

Definition pfj_slotR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x70 0x80 0 0
    [YP09.mkChunk 0x70 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))].
Definition pfj_ntokR : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))].
Definition pfj_shR : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition pfj_rowR : YP09.region := YP09.mkRegion (Some 23%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition pfj_regions : smem := [pfj_slotR; pfj_ntokR; pfj_shR; pfj_rowR].
Definition pfj_ss : sstate := mkSS PF_KLOOP sr_atoms pfj_regions None (mkFacts [] [] []).
Definition pfj_Bx : sv := SOff 22 0.
(* the state at 0x88680, where the two arms of the separator choice join: a0 = 0 (check 28's byte) and a3 = atom 35,
   the separator's address *)
Definition pfj_ss_chk : sstate :=
mkSS PF_KCHK
  [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 8 0; SOff 9 0; SLit 0; SOff 11 0; SOff 12 0; SOff 35 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
  pfj_regions None (mkFacts [] [] []).


(* ---- the arithmetic of the pass's registers ---- *)
Lemma pfj_add_lit : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b Ha Hb Hab. apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
rewrite (bv_wrap_small 64 a) by (unfold bv_modulus; cbn; lia).
rewrite (bv_wrap_small 64 b) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
(* 0x8868c sub a1,a2,s9: the executor's a2 + s9 * (-1) *)
Lemma pfj_sub_val : forall a k, 0 <= k <= a -> a < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 k) (Z_to_bv 64 (-1))) = Z_to_bv 64 (a - k).
Proof.
intros a k Hk Ha. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw zmd_raw].
unfold bv_wrap, bv_modulus. replace (Z.of_N 64) with 64 by reflexivity.
rewrite (Z.mod_small a (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 64)) by lia.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
rewrite Z.add_mod_idemp_r by lia.
replace (a + k * (2 ^ 64 - 1)) with ((a - k) + k * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. reflexivity.
Qed.
(* a register list kept register by register *)
Lemma pfj_rg_kept : forall (rX rX' : bvmap 5 word) (L : list (Z * Z)),
  Forall (fun rv => getr rX' (Z_to_bv 5 (fst rv)) = getr rX (Z_to_bv 5 (fst rv))) L ->
  pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L HK H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HK rv Hin). exact (H rv Hin).
Qed.
(* the 8 bytes of ntok (sa_val) as a word *)
Lemma pfj_rdword_11 : forall (rd : reader) a, sa_val rd a 8%nat 11 -> rdword rd a = Some 11.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0%nat ltac:(lia)) as H0. change (a + Z.of_nat 0) with (a + 0) in H0. rewrite Z.add_0_r in H0.
pose proof (H 1%nat ltac:(lia)) as H1. change (a + Z.of_nat 1) with (a + 1) in H1.
pose proof (H 2%nat ltac:(lia)) as H2. change (a + Z.of_nat 2) with (a + 2) in H2.
pose proof (H 3%nat ltac:(lia)) as H3. change (a + Z.of_nat 3) with (a + 3) in H3.
pose proof (H 4%nat ltac:(lia)) as H4. change (a + Z.of_nat 4) with (a + 4) in H4.
pose proof (H 5%nat ltac:(lia)) as H5. change (a + Z.of_nat 5) with (a + 5) in H5.
pose proof (H 6%nat ltac:(lia)) as H6. change (a + Z.of_nat 6) with (a + 6) in H6.
pose proof (H 7%nat ltac:(lia)) as H7. change (a + Z.of_nat 7) with (a + 7) in H7.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. vm_compute. reflexivity.
Qed.
(* row ti of the table, its shadow byte *)
Lemma pfj_row_mod8 : forall ti, pin_spec.row_addr catA ti mod 8 = 0.
Proof.
intros ti. unfold pin_spec.row_addr, pin_spec.CAT_ROW, catA.
replace (0xa18e0 + 0x128 * Z.of_nat ti) with ((0x1431c + 37 * Z.of_nat ti) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma pfj_row_rng : forall ti, (ti < 11)%nat ->
  0xa18e0 <= pin_spec.row_addr catA ti /\ pin_spec.row_addr catA ti + 0x128 <= 0xa18e0 + pin_spec.CAT_BYTES.
Proof. intros ti Hti. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, catA. lia. Qed.
Lemma pfj_row_S : forall ti, pin_spec.row_addr catA (S ti) = pin_spec.row_addr catA ti + 296.
Proof. intros ti. unfold pin_spec.row_addr, pin_spec.CAT_ROW. lia. Qed.
Lemma pfj_row_sh_S : forall ti,
  SHADOW_OFF + pin_spec.row_addr catA (S ti) / 8 = SHADOW_OFF + pin_spec.row_addr catA ti / 8 + 37.
Proof.
intros ti. rewrite pfj_row_S. replace (pin_spec.row_addr catA ti + 296) with (pin_spec.row_addr catA ti + 37 * 8) by lia.
rewrite Z.div_add by lia. lia.
Qed.
(* the shadow byte of an 8-aligned word all of whose bytes are addressable is 0 *)
Lemma pfj_sh_zero : forall (rd : reader) q n x, range_addressable rd SHADOW_OFF q n -> x mod 8 = 0 ->
  q <= x -> x + 8 <= q + n -> rd (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros rd q n x HR Hx H1 H2. destruct (HR (x + 7) ltac:(lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs.
assert (E : (x + 7) / 8 = x / 8).
{ pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
  symmetry; apply (Z.div_unique (x + 7) 8 (x / 8) 7); lia. }
rewrite E in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (Hm & Hs8)]; [reflexivity|].
exfalso. replace ((x + 7) mod 8) with 7 in Hm; [lia|].
rewrite Z.add_mod, Hx by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition pfj_E (rX : bvmap 5 word) (F tp sepa : Z) : env :=
  Eimg (Ereg rX (map (Z_to_bv 64) [F + PF_O_NTOK; F + PF_O_KNOWN; tp; sepa])).

Section t. Context {fx : YK11.FPState}.

Lemma pfj_vm1 : forall (W : world SEGS) mem a, rdW W mem a = Some 0 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 0.
Proof.
intros W mem a H k Hk. destruct k as [|k]; [|lia]. rewrite Z.add_0_r. unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|] eqn:E; cbn in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite H. vm_compute. reflexivity.
Qed.

Lemma pfj_soff0 : forall E n v, ew E n = w64 v -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* what a call keeps of a read-only region (cwc_mb_kept / cwc_region_kept of
   proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_chain_s3.v at 501c0d516c69) *)
Lemma pfj_mb_kept : forall (W : world SEGS) (m m' : word -> option byte) a,
  rdW W m' a = rdW W m a -> mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
intros W m m' a E. unfold aview in E.
destruct (mbyte SEGS (mrestrict (w_H W) m') a) as [b'|], (mbyte SEGS (mrestrict (w_H W) m) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma pfj_region_kept : forall E (W : world SEGS) m m' (rg : YP09.region),
  (forall a, base_val E (YP09.r_base rg) + YP09.r_lo rg <= a < base_val E (YP09.r_base rg) + YP09.r_hi rg ->
     rdW W m' a = rdW W m a) ->
  YP09.r_whi rg <= YP09.r_wlo rg ->
  region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m') rg.
Proof. intros E W m m' rg HK Hro. split; intros a Ha; [|lia]. exact (pfj_mb_kept W m m' a (HK a Ha)). Qed.

(* the state at the head of the loop, from the cut's facts *)
Lemma pfj_entry : forall (W : world SEGS) (rX : bvmap 5 word) memc (s1 F tp sepa row : Z),
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 20) = w64 (SHADOW_OFF + row / 8) ->
  getr rX (Z_to_bv 5 23) = w64 row ->
  rdword (rdW W memc) (s1 + 0x70) = Some (F + PF_O_NTOK) ->
  rdword (rdW W memc) (s1 + 0x78) = Some (F + PF_O_KNOWN) ->
  rdword (rdW W memc) (F + PF_O_NTOK) = Some 11 ->
  rdW W memc (SHADOW_OFF + row / 8) = Some 0 ->
  rdword (rdW W memc) row = Some tp ->
  alloc_ceiling <= s1 -> s1 + 0x80 <= 2 ^ 47 ->
  4096 <= F -> F + 2048 <= alloc_ceiling -> in_app F 2048 -> off_img F 2048 ->
  0x10000 <= row -> row + 8 <= 0x601000 -> 0 <= tp < 2 ^ 64 -> 0 <= sepa < 2 ^ 64 ->
  st_ok_pi SEGS VAL (pfj_E rX F tp sepa) pfj_ss
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + PF_KLOOP)) memc (seg_rom SEGS))).
Proof.
intros W rX memc s1 F tp sepa row R9 R20 R23 V70 V78 VNT VSH VTP Hs1 Hs1h HF0 HFc HFapp HFoff Hr0 Hr1 Htp Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := pfj_E rX F tp sepa).
assert (EN : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr rX rr)
  by (intros n rr Hrr; unfold E, pfj_E; apply ew_Eimg_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [F + PF_O_NTOK; F + PF_O_KNOWN; tp; sepa]) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, pfj_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFoff.
assert (Hrow8 : 0 <= row / 8 <= 786944) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (rewrite (EN 9%nat (Z_to_bv 5 9) ltac:(reflexivity)), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF + row / 8)
  by (rewrite (EN 20%nat (Z_to_bv 5 20) ltac:(reflexivity)), R20; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF in *; lia).
assert (U23 : bv_unsigned (ew E 23) = row)
  by (rewrite (EN 23%nat (Z_to_bv 5 23) ltac:(reflexivity)), R23; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = F + PF_O_NTOK)
  by (rewrite E32; apply unsigned_lit_small; unfold PF_O_NTOK; lia).
rewrite restrict_mkst_fx. unfold pfj_ss. apply pa_entry_st_ok_full.
- unfold E, pfj_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pfj_regions, pfj_slotR, pfj_ntokR, pfj_shR, pfj_rowR.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ s1 0x70 8 (SOff 32 0) (F + PF_O_NTOK));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold PF_O_NTOK; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ V70).
    * apply (chunk_ok_val SEGS E _ s1 0x78 8 (SOff 33 0) (F + PF_O_KNOWN));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold PF_O_KNOWN; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) memc _ _ V78).
  + cbn [base_val]. rewrite U32. unfold PF_O_NTOK in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (F + 1104) 0 8 (SLit 11) 11);
    [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ VNT).
  + cbn [base_val]. rewrite U20. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (2147450880 + row / 8) 0 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (pfj_vm1 W memc _ VSH).
  + cbn [base_val]. rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ row 0 8 (SOff 34 0) tp);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ VTP).
- apply pairwise_disjoint_of_extents.
  unfold pfj_regions, pfj_slotR, pfj_ntokR, pfj_shR, pfj_rowR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U23, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PF_O_NTOK, SHADOW_OFF in *. repeat split; lia.
- split; [exact I | split; exact I].
Qed.

End t.

Section e.
Variable B : asyms.
(* the interceptor owner's interface row 4: snprintf at the listing's trampoline *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
(* the listing's facts over the abstract instance (SegObj.v) *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the post at the FP state a call returned is the post at the entry's *)
Lemma pfj_lift : forall (fx fx1 : YK11.FPState) (W : world SEGS) (c : config) v cf gi nm val o ln,
  fxrel fx fx1 -> SRr SEGS W c (PF_MISSPOST (fx := fx1) B v cf gi nm val o ln) ->
  SRr SEGS W c (PF_MISSPOST (fx := fx) B v cf gi nm val o ln).
Proof.
intros fx fx1 W c v cf gi nm val o ln H01 H. unfold PF_MISSPOST, pf_postm, PF_POSTr in *.
exact (srr_apost_baseF_lift (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ _ H01 H).
Qed.

(* the object atoms the loop forms with auipc / addi (SegAddr.seg_objs: 62 = .str.18 "|", 63 = .str.19 "",
   64 = .str.17 "%s%s") *)
Lemma pfj_obj_atom : forall E (i : nat) a, img_env VAL A_LIM E -> (i < length seg_objs)%nat ->
  nth i seg_objs 0 = a -> ew E (A_OBJ i) = w64 a.
Proof.
intros E i a HE Hi Ha. rewrite (img_env_atomP E (A_OBJ i) HE) by (unfold A_OBJ, A_TEXT, A_LIM; cbn in Hi; lia).
rewrite (OBJ i Hi), Ha. reflexivity.
Qed.

Ltac pfj_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac pfj_inl := unfold PF_RM, PF_RL, a5_FI; cbn [In app]; repeat (first [left; reflexivity | right]).
(* the registers of pf_fi, PF_RL's 18 / 27 and PF_RM kept by a run whose ss leaves them SOff r 0 *)
Ltac pfj_rgk HK := unfold a5_FI, PF_RM; cbn [app];
  repeat (apply Forall_cons; [cbn [fst]; apply HK; apply in_map; cbn [In]; repeat (first [left; reflexivity | right]) |]);
  apply Forall_nil.

Section t. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a reader looks at an address through Z_to_bv 64 *)
Lemma pfj_aview_mod : forall (W : world SEGS) m a, rdW W m a = rdW W m (a mod 2 ^ 64).
Proof.
intros W m a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. replace (Z.of_N 64) with 64 by reflexivity.
rewrite Zmod_mod. reflexivity.
Qed.

(* what the snprintf call leaves (its keep clause and the bytes it wrote at known + kn): every fact of INV_KLOOP
   that names no register, through pf_a11b_jk.v's pfj_keep, and known[] one pass longer, through pfj_kmem_step *)
Lemma pfj_carry : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val mem2,
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (pf_F v pos + PF_O_KNOWN + pf_kn ti <= a <
        pf_F v pos + PF_O_KNOWN + pf_kn ti + (Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1)) ->
     ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - RtPFCmd.CMD_SNP_K <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v)) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  (forall i, 0 <= i < Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1 ->
     rdW Wc mem2 (pf_F v pos + PF_O_KNOWN + pf_kn ti + i) =
     Some (nth (Z.to_nat i) ((pf_sep ti ++ pf_tok ti) ++ [0]) 0)) ->
  (forall a, pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_sp0 v -> apresent (w_H Wc) mem2 a) ->
  pf_obj B v lyc Sc (rdW Wc mem2) /\
  pf_sl (rdW Wc mem2) (pf_s1 v) (PF_SL v pos) /\
  pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_KN /\
  pf_saved (rdW Wc mem2) (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc mem2) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\
  pf_st v pos (rdW Wc mem2) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc mem2) vp val /\
  sa_val (rdW Wc mem2) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc mem2) (pf_s1 v) [(0x18, vp); (0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_kmem (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN) (S ti).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val mem2 HINV HK HBY HPW.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof HINV as (HB & _ & _ & _ & _ & Hti & HKM & _).
pose proof HB as (_ & _ & HOBJ & _).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as (HAR & Hly & Hin & G & _ & _).
pose proof G as G'. unfold a5_G, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G'. rewrite SPF in G'.
pose proof (pf_kn_bound ti ltac:(lia)) as Hkn.
pose proof (pf_sep_len ti) as Hsl. pose proof (pf_tok_len ti ltac:(lia)) as Htl.
assert (HTn : (length (pf_sep ti ++ pf_tok ti) <= 12)%nat) by (rewrite length_app; lia).
assert (HVW : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ intros a Hv. rewrite pfj_aview_mod in Hv |- *.
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (pf_F v pos + PF_O_KNOWN + pf_kn ti)) as [Hd1 | Hd1];
  [| destruct (Z_lt_le_dec a' (pf_F v pos + PF_O_KNOWN + pf_kn ti +
       (Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1))) as [Hd2 | Hd2]].
  2: { replace a' with (pf_F v pos + PF_O_KNOWN + pf_kn ti + (a' - (pf_F v pos + PF_O_KNOWN + pf_kn ti))) by lia.
       rewrite HBY by lia. discriminate. }
  all: destruct (Z_lt_le_dec a' (pf_sp0 v + (pf_s1 v - pf_sp0 v) - RtPFCmd.CMD_SNP_K)) as [Hw1 | Hw1];
       [| destruct (Z_lt_le_dec a' (pf_sp0 v + (pf_s1 v - pf_sp0 v))) as [Hw2 | Hw2]].
  all: first [ rewrite HK; [exact Hv | lia | lia | lia]
             | apply (aview_some_of_apresent SEGS); apply HPW; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia ]. }
assert (KL : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword (rdW Wc mem2) a = rdword (rdW Wc memc) a).
{ intros a H1 H2. apply rdword_ext. intros k Hk. apply HK; [unfold kImgEnd in *; lia | |].
  - intros Hr. apply (pfj_low_out B v pos lyc Sc Wc memc mdc (a + k) G HAR Hin Hly);
      [unfold kImgEnd in *; lia | unfold pfj_Wr; right; unfold PF_O_KNOWN in *; lia].
  - intros Hr. unfold RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd in *. lia. }
assert (HSS2 : sa_ssp (rdW Wc mem2) gotwA guardA).
{ destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & g & S2).
  split; [rewrite KL by (unfold gotwA, kImgEnd; lia); exact S1|].
  exists g. rewrite KL by (unfold guardA, kImgEnd; lia). exact S2. }
lazymatch type of (pfj_keep B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti mem2 HINV) with
| ?P -> _ => assert (HKW : P) end.
{ intros a Ha Hw. apply HK; [exact Ha | |]; intros Hr; apply Hw; unfold pfj_Wr;
    unfold PF_O_KNOWN, RtPFCmd.CMD_SNP_K, ESTACK in *; lia. }
destruct (pfj_keep B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti mem2 HINV HKW HVW HSS2) as
  (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
split; [exact K6|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|].
apply (pfj_kmem_step (rdW Wc memc) (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN) ti ltac:(lia) HKM).
- intros i Hi. apply HK; [unfold PF_O_KNOWN in *; lia | |]; intros Hr; unfold PF_O_KNOWN, RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
- exact HBY.
Qed.

(* the cut facts at an exit of the pass, at the FP state fx1 the call returned: pf_base again (the journal at the
   exit, the rounding mode of fx1, the registers of pf_fi kept), and the rest of the cut *)
Lemma pfj_inv_exit : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (fx1 : YK11.FPState) rX' mem2 md2,
  INV_KLOOP (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 ->
  frm0 fx1 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (pf_F v pos + PF_O_KNOWN + pf_kn ti <= a <
        pf_F v pos + PF_O_KNOWN + pf_kn ti + (Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1)) ->
     ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - RtPFCmd.CMD_SNP_K <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v)) ->
     rdW Wc mem2 a = rdW Wc memc a) ->
  (forall i, 0 <= i < Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1 ->
     rdW Wc mem2 (pf_F v pos + PF_O_KNOWN + pf_kn ti + i) =
     Some (nth (Z.to_nat i) ((pf_sep ti ++ pf_tok ti) ++ [0]) 0)) ->
  Forall (fun rv => getr rX' (Z_to_bv 5 (fst rv)) = getr rX (Z_to_bv 5 (fst rv)))
    (a5_FI B v ++ [(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln) ->
  pf_base (fx := fx1) B v pos lyc Sc Wc rX' mem2 md2 PF_SC_KN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc mem2) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc mem2) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  sa_val (rdW Wc mem2) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc mem2) (pf_s1 v) [(0x18, vp); (0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_rg rX' ([(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln) /\
  pf_kmem (rdW Wc mem2) (pf_F v pos + PF_O_KNOWN) (S ti).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val fx1 rX' mem2 md2 HINV HJ2 HFR1 HK HBY HRK.
pose proof HINV as (HB & HMID & HST & HVS & HVB & Hti & HKM & HNT & HSL2 & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ0 & Hly & HSc & HPm & HSV & HFL & HFRM & HRGF).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPW & _).
destruct (pfj_carry n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val mem2 HINV HK HBY HPW)
  as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10).
apply Forall_app in HRK as (HRK1 & HRK2).
rewrite app_assoc in HRG. apply a5_rg_app in HRG as (HRG1 & _).
split.
{ split; [exact HCX|]. split; [|exact (conj K1 (conj K2 K3))].
  split; [exact HJ2|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPm|].
  split; [exact K4|]. split; [exact K5|]. split; [exact HFR1|].
  exact (pfj_rg_kept rX rX' _ HRK1 HRGF). }
split; [exact HMID|]. split; [exact K6|]. split; [exact K7|]. split; [exact HVB|].
split; [exact K8|]. split; [exact K9|]. split; [exact (pfj_rg_kept rX rX' _ HRK2 HRG1)|]. exact K10.
Qed.

(* one pass from the join 0x88680 (the separator in a3 = atom 35): the token pointer, the snprintf call, ntok
   reloaded, then KEXIT (pass 10) or the back edge into the next pass at the FP state the call returned *)
Lemma pfj_body : forall n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val tp (msb : machine_state) mdx,
  HA_KEXIT B n -> ((ti < 10)%nat -> HA_KLOOP B n (S ti)) ->
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  rdword (rdW Wc memc) (pin_spec.row_addr catA ti) = Some tp ->
  sa_lit SEGS B (rdW Wc memc) tp (pf_tok ti) ->
  st_ok_pi SEGS VAL (pfj_E rX (pf_F v pos) tp (seg_litA_rc (pf_sep ti))) pfj_ss_chk (restrict (w_H Wc) msb) ->
  ms_mem msb = memc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem msb) mdx 0 ->
  SRr SEGS Wc (mkCfg msb mdx) (PF_MISSPOST B v cf gi nm val o ln).
Proof.
intros n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val tp msb mdx HKX HIH HINV HTP HTL HS HMb HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof HINV as (HB & HMID & HST & HVS & HVB & Hti & HKM & HNT & HSL2 & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ0 & Hly & HSc & HPm & HSV & HFL & HFRM & HRGF).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as (HAR & _ & Hin & G & _ & _).
pose proof G as G'. unfold a5_G, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G'. rewrite SPF in G'.
pose proof (pf_kn_bound ti ltac:(lia)) as Hkn.
pose proof (pf_sep_len ti) as Hsl. pose proof (pf_tok_len ti ltac:(lia)) as Htl.
set (T := pf_sep ti ++ pf_tok ti) in *.
assert (HTn : (length T <= 12)%nat) by (unfold T; rewrite length_app; lia).
(* the registers of the cut *)
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 2 _ HRGF); pfj_inl).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (a5_rg_get rX _ 3 _ HRGF); pfj_inl).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (a5_rg_get rX _ 4 _ HRGF); pfj_inl).
assert (R12 : getr rX (Z_to_bv 5 12) = w64 240) by (apply (a5_rg_get rX _ 12 _ HRG); pfj_inl).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (Z.of_nat ti + 1)) by (apply (a5_rg_get rX _ 19 _ HRG); pfj_inl).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (SHADOW_OFF + pin_spec.row_addr catA ti / 8))
  by (apply (a5_rg_get rX _ 20 _ HRG); pfj_inl).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (pin_spec.row_addr catA ti)) by (apply (a5_rg_get rX _ 23 _ HRG); pfj_inl).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 (pf_kn ti)) by (apply (a5_rg_get rX _ 25 _ HRG); pfj_inl).
set (E := pfj_E rX (pf_F v pos) tp (seg_litA_rc (pf_sep ti))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, pfj_E; apply Eimg_env).
assert (EN : forall (k : nat) (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr rX rr)
  by (intros k rr Hrr; unfold E, pfj_E; apply ew_Eimg_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j (map (Z_to_bv 64) [pf_F v pos + PF_O_NTOK; pf_F v pos + PF_O_KNOWN; tp; seg_litA_rc (pf_sep ti)]) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, pfj_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth map] in E32, E33, E34, E35. clear EX.
assert (E2r : ew E 2 = w64 (pf_s1 v)) by (rewrite (EN 2%nat (Z_to_bv 5 2) ltac:(reflexivity)); exact R2).
assert (E3r : ew E 3 = w64 (as_gp B)) by (rewrite (EN 3%nat (Z_to_bv 5 3) ltac:(reflexivity)); exact R3).
assert (E4r : ew E 4 = w64 (as_tp B)) by (rewrite (EN 4%nat (Z_to_bv 5 4) ltac:(reflexivity)); exact R4).
assert (E12r : ew E 12 = w64 240) by (rewrite (EN 12%nat (Z_to_bv 5 12) ltac:(reflexivity)); exact R12).
assert (E19r : ew E 19 = w64 (Z.of_nat ti + 1)) by (rewrite (EN 19%nat (Z_to_bv 5 19) ltac:(reflexivity)); exact R19).
assert (E25r : ew E 25 = w64 (pf_kn ti)) by (rewrite (EN 25%nat (Z_to_bv 5 25) ltac:(reflexivity)); exact R25).
assert (SHOK : sh_ok SEGS pfj_Bx [] E (mrestrict (w_H Wc) (ms_mem msb))) by constructor.
(* 0x88680 .. 0x88698: the row's token pointer, a0 = known + kn, a1 = 240 - kn, a2 = "%s%s", the call *)
paj_run_tok RUN HS HJ SHOK Bspan; [pfj_awr|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv1 := mdq) in *; clearbody mdv1 end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HMc : ms_mem msx = memc)
  by (rewrite <- HMb; exact (frame_of_read_only _ pfj_regions _ _ ltac:(vm_compute; reflexivity) HF)) end.
clear_frames.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (13%bv : bv 5) P13. prreg HS (14%bv : bv 5) P14.
rewrite HMc in HJ |- *.
assert (QD : getr (ms_regs ms) 10 = w64 (pf_F v pos + PF_O_KNOWN + pf_kn ti)).
{ rewrite P10, E25r, E33. unfold w64. rewrite pfj_add_lit by (unfold PF_O_KNOWN; lia). f_equal. lia. }
assert (QN : getr (ms_regs ms) 11 = w64 (240 - pf_kn ti)).
{ rewrite P11, E12r, E25r. unfold w64. apply pfj_sub_val; lia. }
assert (QF : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_ss)).
{ rewrite P12. change 305%nat with (A_OBJ 64). rewrite pf_lit_ss.
  apply pfj_obj_atom; [exact HEI | vm_compute; lia | vm_compute; reflexivity]. }
assert (Qsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite P2, E2r. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact E3r).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact E4r).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (A3 : argZ (ms_regs ms) 3 = seg_litA_rc (pf_sep ti)).
{ unfold argZ. change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13).
  replace (getr (ms_regs ms) (Z_to_bv 5 13)) with (getr (ms_regs ms) 13) by (f_equal; apply bv_eq; reflexivity).
  rewrite P13, E35. apply unsigned_lit_small. destruct ti; vm_compute; split; congruence. }
assert (A4 : argZ (ms_regs ms) 4 = tp).
{ unfold argZ. change (Z_to_bv 5 (10 + 4)) with (Z_to_bv 5 14).
  replace (getr (ms_regs ms) (Z_to_bv 5 14)) with (getr (ms_regs ms) 14) by (f_equal; apply bv_eq; reflexivity).
  rewrite P14, E34. apply unsigned_lit_small.
  destruct HTL as (Htp0 & _ & _ & _ & Himg). pose proof (proj1 (Himg tp ltac:(lia))) as Hi.
  pose proof (pa_img_range _ Hi) as Hr. unfold kImgEnd in Hr. lia. }
assert (Hsp1 : spZ (ms_regs ms) = pf_s1 v) by (rewrite Qsp; lia).
destruct (pfj_snp_site_ok B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti tp (ms_regs ms) HINV HTP HTL
  A3 A4 Hsp1) as (SDEST & SPC & SAMR & SRA & SHV & SOFF & SIMG & SGU & SFR & STL & SROM & SLEN & SBY).
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ pose proof G as (_ & _ & G3 & _ & G5 & _).
  assert (H1 : pf_s1 v mod 16 = 0).
  { pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D. rewrite G5, Z.add_0_r in D.
    rewrite D. replace (32 * (pf_s1 v / 32)) with ((2 * (pf_s1 v / 32)) * 16) by lia. apply Z_mod_mult. }
  rewrite Zminus_mod, H1, G3. reflexivity. }
(* the call *)
eapply SRr_bind.
{ exact (pfa8b_aj_snprintf_atSF (fx := fx) SEGS B LAWS pa_segs_low gotwA guardA _ (SNP fx)
    Wc (ms_regs ms) memc STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv1 0 (pf_F v pos + PF_O_KNOWN + pf_kn ti) (240 - pf_kn ti)
    (seg_litA_rc F_ss) T (pf_s1 v - pf_sp0 v) (getr (ms_regs ms) 1)
    HJ QD QN QF ltac:(lia) ltac:(unfold PF_O_KNOWN; lia) ltac:(unfold PF_O_KNOWN; lia) Qsp
    Ho16
    ltac:(lia) ltac:(unfold RtPFCmd.CMD_SNP_K, ESTACK; lia) Qgp Qtp eq_refl Qra
    SDEST SPC SAMR SRA SHV SOFF SIMG SGU
    ltac:(unfold gotwA; lia) ltac:(unfold gotwA, RtPFCmd.CMD_IMG_HI, kImgEnd; lia)
    ltac:(unfold guardA; lia) ltac:(unfold guardA, RtPFCmd.CMD_IMG_HI, kImgEnd; lia)
    ltac:(unfold gotwA, RtPFCmd.CMD_IMG_LO; lia) ltac:(unfold guardA, RtPFCmd.CMD_IMG_LO; lia)
    SFR STL SROM HFRM). }
cbv beta. intros W2 c2 _ (HW2 & fx1 & regs2 & mem2 & md2 & Hfx & Hc2 & HJ2 & HP2 & HR2 & HBY2 & HKP2 & HPR2 & _).
subst W2 c2.
apply (pfj_lift fx fx1 _ _ v cf gi nm val o ln Hfx).
rewrite P1.
unfold T in *. rewrite SLEN in HBY2, HKP2. rewrite SBY in HBY2.
assert (HFR1 : frm0 fx1) by exact (fxrel_frm0 fx fx1 HFRM Hfx).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 9 _ HRGF); pfj_inl).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EN 9%nat (Z_to_bv 5 9) ltac:(reflexivity)), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pf_F v pos + PF_O_NTOK)
  by (rewrite E32; apply unsigned_lit_small; unfold PF_O_NTOK; lia).
assert (E20r : ew E 20 = w64 (SHADOW_OFF + pin_spec.row_addr catA ti / 8))
  by (rewrite (EN 20%nat (Z_to_bv 5 20) ltac:(reflexivity)); exact R20).
assert (E23r : ew E 23 = w64 (pin_spec.row_addr catA ti))
  by (rewrite (EN 23%nat (Z_to_bv 5 23) ltac:(reflexivity)); exact R23).
pose proof (pfj_row_rng ti Hti) as Hrow. unfold pin_spec.CAT_BYTES in Hrow.
assert (Hr8 : 0 <= pin_spec.row_addr catA ti / 8 <= 786944)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
(* back at 0x8869c, at the FP state fx1 the wrapper returned: slot 0x70 and ntok are kept *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H Wc) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HMc.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply pfj_region_kept; [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9. intros a Ha.
    apply HKP2; [lia | intros Hr; unfold PF_O_KNOWN in *; lia | intros Hr; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia].
  - apply pfj_region_kept; [|cbn; lia].
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U32. intros a Ha.
    apply HKP2; [unfold PF_O_NTOK in *; lia | intros Hr; unfold PF_O_NTOK, PF_O_KNOWN in *; lia
                | intros Hr; unfold PF_O_NTOK, RtPFCmd.CMD_SNP_K, ESTACK in *; lia]. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx)) in HS2. apply (st_ok_pi_restrict_xfx fx fx1) in HS2.
lazymatch type of HS2 with st_ok_pi _ _ ?Ev _ _ => remember Ev as E2 eqn:HE2 in HS2 end.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall m, (m < 40)%nat -> ew E2 m = ew E m) by (intros m Hm; rewrite HE2; apply ew_havoc_old; lia).
assert (M44 : ew E2 44 = getr regs2 10)
  by (rewrite HE2; exact (ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (SHOK2 : sh_ok SEGS pfj_Bx [] E2 (mrestrict (w_H Wc) mem2)) by constructor.
assert (HAE : env_agree 32 (Ereg rX (map (Z_to_bv 64)
  [pf_F v pos + PF_O_NTOK; pf_F v pos + PF_O_KNOWN; tp; seg_litA_rc (pf_sep ti)])) E2).
{ split; [|rewrite HE2; reflexivity]. intros k Hk. rewrite OLD2 by lia. unfold E, pfj_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. }
pose proof (paj_run (fx := fx1) B LAWS) as RUN1. pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
(* 0x8869c .. 0x886a8: a2 = 240, ntok reloaded through slot 0x70 (11), the exit test *)
paj_run_tok RUN1 HS2 HJ2 SHOK2 Bspan; [pfj_awr|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdw3 := mdq) in *; clearbody mdw3 end.
lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HMd : ms_mem msx = mem2)
  by (exact (frame_of_read_only _ [pfj_slotR; pfj_ntokR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
clear_frames.
psrr_branch_tok RUN1 BR1 HS2 SHOK2 Bspan.
- (* ti + 1 >= 11: pass 10 was the last, KEXIT *)
  rewrite branch_geu_U, (U_atom E2 19 (Z.of_nat ti + 1) ltac:(rewrite OLD2 by lia; exact E19r) ltac:(lia)),
    (U_lit E2 11 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Ht10 : ti = 10%nat) by lia.
  paj_run_to_tok RUNTO1 HS2 HJ2 SHOK2 Bspan PF_KEXIT; [pfj_awr|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdw4 := mdq) in *; clearbody mdw4 end.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMf : ms_mem msx = mem2)
    by (rewrite <- HMd; exact (frame_of_read_only _ [pfj_slotR; pfj_ntokR] _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms4 end.
  clear_frames.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 21; 22; 26; 27]) HS2 HAE
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS2. rewrite HMf in HJ2 |- *.
  assert (EK : BASE + 14740 = BASE + PF_KEXIT) by (f_equal; vm_compute; reflexivity).
  rewrite EK.
  apply (HKX fx1 v pos lyc Sc Wc (ms_regs ms4) mem2 mdw4 cf nm o ln d gi vp val).
  destruct (pfj_inv_exit n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val fx1 (ms_regs ms4) mem2 mdw4
    HINV HJ2 HFR1 HKP2 HBY2) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  { pfj_rgk HK. }
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
  split; [|exact (conj I7 I8)].
  rewrite Ht10 in I9. cbn [pf_kmem] in I9. rewrite pf_J_11 in I9. exact I9.
- (* ti + 1 < 11: the counters move on *)
  rewrite branch_geu_U, (U_atom E2 19 (Z.of_nat ti + 1) ltac:(rewrite OLD2 by lia; exact E19r) ltac:(lia)),
    (U_lit E2 11 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hlt : (ti < 10)%nat) by lia.
  rename Hc into Hgeu.
  paj_run_tok RUN1 HS2 HJ2 SHOK2 Bspan; [pfj_awr|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdw4 := mdq) in *; clearbody mdw4 end.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HMe : ms_mem msx = mem2)
    by (rewrite <- HMd; exact (frame_of_read_only _ [pfj_slotR; pfj_ntokR] _ _ ltac:(vm_compute; reflexivity) HF)) end.
  clear_frames.
  psrr_branch_tok RUN1 BR1 HS2 SHOK2 Bspan.
  + (* kn + 2 < 240: the back edge, into pass ti + 1 at fx1 *)
    paj_run_to_tok RUNTO1 HS2 HJ2 SHOK2 Bspan PF_KLOOP; [pfj_awr|].
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
      set (mdw5 := mdq) in *; clearbody mdw5 end.
    lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (HMf : ms_mem msx = mem2)
      by (rewrite <- HMe; exact (frame_of_read_only _ [pfj_slotR; pfj_ntokR] _ _ ltac:(vm_compute; reflexivity) HF));
      rename msx into ms5 end.
    clear_frames.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 21; 22; 26; 27]) HS2 HAE
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS2 (Z_to_bv 5 19) T19. prreg HS2 (Z_to_bv 5 25) T25. prreg HS2 (Z_to_bv 5 20) T20.
    prreg HS2 (Z_to_bv 5 23) T23. prreg HS2 (Z_to_bv 5 12) T12.
    pmkst HS2. rewrite HMf in HJ2 |- *.
    assert (EL : BASE + 14632 = BASE + PF_KLOOP) by (f_equal; vm_compute; reflexivity).
    rewrite EL.
    apply (HIH Hlt fx1 v pos lyc Sc Wc (ms_regs ms5) mem2 mdw5 cf nm o ln d gi vp val).
    destruct (pfj_inv_exit n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val fx1 (ms_regs ms5) mem2 mdw5
      HINV HJ2 HFR1 HKP2 HBY2) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    { pfj_rgk HK. }
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [lia|]. split; [exact I9|]. split; [exact I6|]. split; [exact I7|].
    rewrite app_assoc. apply a5_rg_app. split; [exact I8|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    * rewrite T19, OLD2, E19r by lia. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite T25, OLD2, E25r, M44, HR2 by lia. unfold w64. rewrite pfj_add_lit by lia. f_equal.
      rewrite (pf_kn_step ti) by lia. rewrite (pf_snp_r ti) by lia. reflexivity.
    * rewrite T20, OLD2, E20r by lia. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      rewrite pfj_row_sh_S. reflexivity.
    * rewrite T23, OLD2, E23r by lia. unfold w64. rewrite unsigned_lit_small by lia.
      rewrite pfj_row_S. reflexivity.
    * rewrite T12. reflexivity.
  + (* kn + 2 >= 240 is impossible: kn <= 77 and the pass adds at most 12 *)
    exfalso.
    rewrite branch_ltu_U, U_SAlu,
      (U_atom_off E2 25 (pf_kn ti) 2 ltac:(rewrite OLD2 by lia; exact E25r) ltac:(lia) ltac:(lia)),
      (U_atom E2 44 (Z.of_nat (length (pf_sep ti ++ pf_tok ti))) ltac:(rewrite M44; exact HR2) ltac:(lia)),
      (U_lit E2 240 ltac:(lia)) in Hc.
    cbn [zalu_raw] in Hc. rewrite zcanon_id in Hc by (unfold M64; lia).
    apply Z.ltb_ge in Hc. lia.
Qed.

(* one pass at the ambient FP state: from the head 0x8865c to the separator choice (`beq s3, 1`, s3 = ti + 1), the
   two arms (a3 = "" at pass 0, "|" after) joined at 0x88680 after check 28 by giving a3 the atom 35, then pfj_body *)
Lemma pfj_head : forall n ti, HA_KEXIT B n -> ((ti < 10)%nat -> HA_KLOOP B n (S ti)) -> H_KLOOP B n ti.
Proof.
intros n ti HKX HIH. unfold H_KLOOP.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof HINV as (HB & HMID & HST & HVS & HVB & Hti & HKM & HNT & HSL2 & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ0 & Hly & HSc & HPm & HSV & HFL & HFRM & HRGF).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_KN HB) as (HAR & _ & Hin & G & _ & _).
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & HFapp & _).
pose proof G as G'. unfold a5_G, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G'. rewrite SPF in G'.
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 5 pos HAR Hin) as HFoff.
rewrite Hly in HFoff. change (fs_frame_bytes 5) with 2048 in HFoff.
pose proof (pfj_row_rng ti Hti) as Hrow. unfold pin_spec.CAT_BYTES in Hrow.
(* the row's token pointer and its token (sa_cat), check 28's byte (the table pinned at every AR state) *)
pose proof HOBJ as (_ & _ & _ & _ & _ & HCAT & _).
pose proof HCAT as (HPIN & _ & HROWS).
destruct (HROWS ti ltac:(unfold pin_spec.CAT_N; lia)) as (tp & HTP & HTL).
rewrite (pf_tok_cat ti Hti) in HTL.
assert (VSH : rdW Wc memc (SHADOW_OFF + pin_spec.row_addr catA ti / 8) = Some 0).
{ destruct (HPIN _ _ _ _ _ HAR) as (_ & _ & _ & HRA & _).
  apply (pfj_sh_zero _ catA pin_spec.CAT_BYTES); [exact HRA | apply pfj_row_mod8 | unfold catA in *; lia
    | unfold catA, pin_spec.CAT_BYTES in *; lia]. }
assert (Htp : 0 <= tp < 2 ^ 64).
{ destruct HTL as (Htp0 & _ & _ & _ & Himg). pose proof (proj1 (Himg tp ltac:(lia))) as Hi.
  pose proof (pa_img_range _ Hi) as Hr. unfold kImgEnd in Hr. lia. }
assert (Hsepa : seg_litA_rc (pf_sep ti) = 0x21860 \/ seg_litA_rc (pf_sep ti) = 0x21840)
  by (destruct ti; [left | right]; vm_compute; reflexivity).
assert (V70 : rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some (pf_F v pos + PF_O_NTOK))
  by exact (proj1 (Forall_forall _ _) HSL (0x70, pf_F v pos + PF_O_NTOK)
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))).
assert (V78 : rdword (rdW Wc memc) (pf_s1 v + 0x78) = Some (pf_F v pos + PF_O_KNOWN))
  by exact (proj1 (Forall_forall _ _) HSL (0x78, pf_F v pos + PF_O_KNOWN)
    ltac:(unfold PF_SL; cbn [In]; repeat (first [left; reflexivity | right]))).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 9 _ HRGF); pfj_inl).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (Z.of_nat ti + 1)) by (apply (a5_rg_get rX _ 19 _ HRG); pfj_inl).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (SHADOW_OFF + pin_spec.row_addr catA ti / 8))
  by (apply (a5_rg_get rX _ 20 _ HRG); pfj_inl).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 (pin_spec.row_addr catA ti)) by (apply (a5_rg_get rX _ 23 _ HRG); pfj_inl).
pose proof (pfj_entry Wc rX memc (pf_s1 v) (pf_F v pos) tp (seg_litA_rc (pf_sep ti)) (pin_spec.row_addr catA ti)
  R9 R20 R23 V70 V78 (pfj_rdword_11 _ _ HNT) VSH HTP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFapp HFoff
  ltac:(unfold catA in *; lia) ltac:(unfold catA in *; lia) Htp ltac:(lia)) as HS.
set (E := pfj_E rX (pf_F v pos) tp (seg_litA_rc (pf_sep ti))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, pfj_E; apply Eimg_env).
assert (EN : forall (k : nat) (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr rX rr)
  by (intros k rr Hrr; unfold E, pfj_E; apply ew_Eimg_Ereg_nat; exact Hrr).
assert (E35 : ew E 35 = w64 (seg_litA_rc (pf_sep ti))).
{ unfold E, pfj_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra rX (map (Z_to_bv 64) [pf_F v pos + PF_O_NTOK; pf_F v pos + PF_O_KNOWN; tp;
    seg_litA_rc (pf_sep ti)]) 3). }
assert (E19r : ew E 19 = w64 (Z.of_nat ti + 1)) by (rewrite (EN 19%nat (Z_to_bv 5 19) ltac:(reflexivity)); exact R19).
assert (SHOK : sh_ok SEGS pfj_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_KLOOP)) with (Z_to_bv 64 (BASE + PF_KLOOP)).
(* 0x8865c .. 0x88660: a0 = 1, `beq s3, a0` *)
paj_run_tok RUN HS HJ0 SHOK Bspan; [pfj_awr|].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
  set (mdv1 := mdq) in *; clearbody mdv1 end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HM1 : ms_mem msx = memc) by (exact (frame_of_read_only _ pfj_regions _ _ ltac:(vm_compute; reflexivity) HF)) end.
clear_frames.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* ti = 0: 0x88670 a3 = 0x21860, the empty separator *)
  rewrite branch_eq_U, (U_atom E 19 (Z.of_nat ti + 1) E19r ltac:(lia)), (U_lit E 1 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. assert (Ht0 : ti = 0%nat) by lia.
  paj_run_to_tok RUNTO HS HJ0 SHOK Bspan PF_KCHK; [pfj_awr|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HM2 : ms_mem msx = memc)
    by (rewrite <- HM1; exact (frame_of_read_only _ pfj_regions _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms2 end.
  clear_frames.
  prreg HS (13%bv : bv 5) Q13.
  assert (A3v : sv_denot E (SOff 35 0) = getr (ms_regs ms2) 13).
  { rewrite Q13, (pfj_soff0 E 35 _ E35). change 304%nat with (A_OBJ 63).
    rewrite (pfj_obj_atom E 63 0x21860 HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)).
    rewrite Ht0. reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (13%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity) A3v)
      as HS3; clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (@nil (nat * afact)) (@nil acond) (@nil (sv * sv)) HS
      ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx))
      as HS3; clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = pfj_ss_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  exact (pfj_body n ti v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val tp ms2 mdv2 HKX HIH HINV HTP HTL HS HM2 HJ0).
- (* ti > 0: 0x88664 a3 = 0x21840, "|" *)
  rewrite branch_eq_U, (U_atom E 19 (Z.of_nat ti + 1) E19r ltac:(lia)), (U_lit E 1 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc. destruct ti as [|ti']; [lia|].
  paj_run_to_tok RUNTO HS HJ0 SHOK Bspan PF_KCHK; [pfj_awr|].
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ =>
    set (mdv2 := mdq) in *; clearbody mdv2 end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HM2 : ms_mem msx = memc)
    by (rewrite <- HM1; exact (frame_of_read_only _ pfj_regions _ _ ltac:(vm_compute; reflexivity) HF));
    rename msx into ms2 end.
  clear_frames.
  prreg HS (13%bv : bv 5) Q13.
  assert (A3v : sv_denot E (SOff 35 0) = getr (ms_regs ms2) 13).
  { rewrite Q13, (pfj_soff0 E 35 _ E35). change 303%nat with (A_OBJ 62).
    rewrite (pfj_obj_atom E 62 0x21840 HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)).
    reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (13%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity) A3v)
      as HS3; clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ev ssx msx (@nil (nat * afact)) (@nil acond) (@nil (sv * sv)) HS
      ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx) ltac:(intros xx Hxx; destruct Hxx))
      as HS3; clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let Hq := fresh "Hss" in assert (Hq : ssx = pfj_ss_chk) by (vm_compute; reflexivity);
    rewrite Hq in HS; clear Hq end.
  exact (pfj_body n (S ti') v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val tp ms2 mdv2 HKX HIH HINV HTP HTL HS
    HM2 HJ0).
Qed.

End t.

(* the loop, by induction on the passes left, each pass at whatever FP state the previous call returned *)
Lemma pfj_loop : forall n, HA_KEXIT B n -> forall (k : nat) (f0 : YK11.FPState) (ti : nat), (ti + k = 10)%nat ->
  H_KLOOP (fx := f0) B n ti.
Proof.
intros n HKX k. induction k as [|k IH]; intros f0 ti Hk.
- apply (pfj_head (fx := f0) n ti HKX). intros Hlt. lia.
- apply (pfj_head (fx := f0) n ti HKX). intros Hlt f1. apply (IH f1 (S ti)). lia.
Qed.

Section w. Context {fx : YK11.FPState}.
(* the join loop 0x8865c .. 0x886c4, every pass ti < 11 *)
Theorem pfj_kloop_ok : forall n : nat, HA_KEXIT B n -> forall ti : nat, (ti < 11)%nat -> H_KLOOP B n ti.
Proof. intros n HKX ti Hti. exact (pfj_loop n HKX (10 - ti) fx ti ltac:(lia)). Qed.
End w.

End e.
End f.
End d.
