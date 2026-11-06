(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d check_words_ki.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* CmdRecFacts' cmd_ro_ok_of_aro (2026-10-29): the image's read-only bytes at any AR state
   whose reader satisfies arodata_okP. cmd_ro_bytes holds the RELRO GOT words, which are runtime-owned, so neither
   the journal's image clause nor arodata_okP alone carries cmd_ro_ok from the entry to a call state. *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).


(* ---------------------------------------------------------------------------------------------------------- *)
(* Segment D (0x87c90 .. 0x87d64; listing 0x17ac .. 0x1880). After the item loop of call c (cp = &call->fn =
   A_G_REC + 16 + 56 c): the dispatch on call->fn: fn = 20 -> check_words_pin_set (jal at 0x87d30), fn = 17 ->
   check_words_chain (0x87d04), fn = 0 -> check_words_add (0x87ce0), any other fn -> no call; each call gets
   (cp, w->w, read). Then the call loop's latch at 0x87d34: c + 1, the two cursors at s1 + 128 and s1 + 136 move on by
   one call (56 bytes), and `blt c+1 ncalls` goes back to the loop head LH (0x87a7c), else on to REL (0x87db8).
   Every inline check is removed by the token engine (PaShadow.v): cp and A_G_REC + 8 lie in g_rec (ZSH_cw), W + 16 in
   the stack window (AR's zero shadow over [ly_stk_lo, ly_stk_hi)).
   Two seeds: ssD at D (0x17ac), ssP at the latch (0x1850) or at the `j` back to it after add (0x1800) and chain
   (0x1824). *)
Definition DBx : sv := SOff 23 0.
Definition DBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition shx (n : nat) (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n o) (SLit 3)) DBx.
Definition CW_PC_LATCH : Z := 0x1850.   (* 0x87d34 *)
Definition CW_PC_RADD : Z := 0x1800.    (* 0x87ce4, after `jal check_words_add` *)
Definition CW_PC_RCHAIN : Z := 0x1824.  (* 0x87d08, after `jal check_words_chain` *)
(* the seed at D: atoms 9 sp1, 23 SB; extra atoms 32 A_G_REC, 33 cp, 34 W + 16, 35 w->w, 36 fn, 37 c, 38 read,
   39 ncalls *)
Definition d_scr : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 160 0 0
[YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 72 (CVal 8 (shx 32 8)); YP09.mkChunk 80 (CVal 8 (SOff 37 0));
 YP09.mkChunk 88 (CVal 8 (shx 34 0)); YP09.mkChunk 96 (CVal 8 (SOff 34 0));
 YP09.mkChunk 112 (CVal 8 (SAlu ALU_SRL (SOff 33 0) (SLit 3))); YP09.mkChunk 120 (CVal 8 (SOff 33 0));
 YP09.mkChunk 128 (CVal 8 (SOff 33 8)); YP09.mkChunk 136 (CVal 8 (SOff 33 8)); YP09.mkChunk 152 (CVal 8 (SOff 38 0))].
Definition d_nc : YP09.region := YP09.mkRegion (Some 32%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 39 0))].
Definition d_fn : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition d_ww : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition d_regions : smem := [d_scr; d_nc; d_fn; d_ww].
Definition d_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (23%nat, mkAF SB SB 0); (32%nat, mkAF A_G_REC A_G_REC 3);
(33%nat, mkAF (A_G_REC + 16) (A_G_REC + 16 + 56 * 15) 3); (34%nat, mkAF (2^46) (2^47 - 16) 0);
(35%nat, mkAF 0 (2^64 - 1) 0); (36%nat, mkAF 0 25 0); (37%nat, mkAF 0 15 0); (38%nat, mkAF 0 64 0);
(39%nat, mkAF 0 16 0) ] [] [].
Definition d_SH : list shent := [mkSHE 33 0 8; mkSHE 34 0 8; mkSHE 32 8 16].
Definition ssD : sstate := mkSS CW_PC_D sr_atoms d_regions None d_facts.
Definition d_extra (cp W16 arr fn c rdv nc : Z) : list word :=
[Z_to_bv 64 A_G_REC; Z_to_bv 64 cp; Z_to_bv 64 W16; Z_to_bv 64 arr; Z_to_bv 64 fn; Z_to_bv 64 c; Z_to_bv 64 rdv;
 Z_to_bv 64 nc].
(* the seed at the latch: atoms 9 sp1, 19 A_G_REC, 20 c, 23 SB; extra atoms 32 q = A_G_REC + 24 + 56 c, 33 ncalls *)
Definition p_scr : YP09.region :=
YP09.mkRegion (Some 9%nat) 72 144 128 144
[YP09.mkChunk 72 (CVal 8 (shx 19 8)); YP09.mkChunk 128 (CVal 8 (SOff 32 0)); YP09.mkChunk 136 (CVal 8 (SOff 32 0))].
Definition p_nc : YP09.region := YP09.mkRegion (Some 19%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition p_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (19%nat, mkAF A_G_REC A_G_REC 3); (20%nat, mkAF 0 15 0);
(23%nat, mkAF SB SB 0); (32%nat, mkAF (A_G_REC + 24) (A_G_REC + 24 + 56 * 15) 3); (33%nat, mkAF 0 16 0) ] [] [].
Definition p_SH : list shent := [mkSHE 19 8 16].
Definition ssP (pc : Z) : sstate := mkSS pc sr_atoms [p_scr; p_nc] None p_facts.
Definition p_extra (c nc : Z) : list word := [Z_to_bv 64 (A_G_REC + 24 + 56 * c); Z_to_bv 64 nc].

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwd_val_of_aval : forall H (m : word -> option byte) a n v,
aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as Hv.
rewrite <- (Z_to_bv_bv_unsigned 8 b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma cwd_aval_of_val : forall H (m : word -> option byte) a n v,
val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
Lemma cwd_aval_kept : forall (rd rd' : reader) a n v,
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cwd_denot_srl3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = Z_to_bv 64 (v / 8).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small v) by lia. rewrite zcanon_small by lia. reflexivity.
Qed.
Lemma cwd_cp_al : forall c, (A_G_REC + 16 + 56 * c) mod 8 = 0.
Proof. intros c. replace (A_G_REC + 16 + 56 * c) with ((771818 + 7 * c) * 8) by (unfold A_G_REC; lia). apply Z_mod_mult. Qed.
(* a range of the stack window is addressable at every AR state (AR's zero shadow over [ly_stk_lo, ly_stk_hi)) *)
Lemma cwd_stk_addressable : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n + 8 <= ly_stk_hi ly -> 0 <= n ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi Hn.
pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as Z. unfold zshadow_ok, zero_shadow_ranges in Z.
pose proof (Forall_inv Z) as Z0. cbn [fst snd] in Z0.
destruct (YG0t.zshadow_range_facts B ly S _ _ (proj1 HAR) (or_introl eq_refl)) as (Hal & _). cbn [fst] in Hal.
intros x Hx. exists 0. split; [|left; reflexivity].
replace x with (ly_stk_lo ly + (x - ly_stk_lo ly)) by lia. rewrite shadow_of_addr_aligned_off by exact Hal.
apply Z0. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|].
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
pose proof (Z.mul_div_le (x - ly_stk_lo ly) 8 ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seeds *)
Lemma cwd_seedD : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 c W16 arr fn rdv nc,
getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
0 <= c <= 15 -> 2 ^ 46 <= W16 <= 2 ^ 47 - 16 -> sp1 + 160 <= W16 -> 0 <= arr < 2 ^ 64 ->
0 <= fn <= 25 -> 0 <= rdv <= 64 -> 0 <= nc <= 16 ->
aval_mem (rdW W memc) (sp1 + 64) 8 A_G_REC -> aval_mem (rdW W memc) (sp1 + 72) 8 (CW_SB + (A_G_REC + 8) / 8) ->
aval_mem (rdW W memc) (sp1 + 80) 8 c -> aval_mem (rdW W memc) (sp1 + 88) 8 (CW_SB + W16 / 8) ->
aval_mem (rdW W memc) (sp1 + 96) 8 W16 ->
aval_mem (rdW W memc) (sp1 + 112) 8 ((A_G_REC + 16 + 56 * c) / 8) ->
aval_mem (rdW W memc) (sp1 + 120) 8 (A_G_REC + 16 + 56 * c) ->
aval_mem (rdW W memc) (sp1 + 128) 8 (A_G_REC + 24 + 56 * c) ->
aval_mem (rdW W memc) (sp1 + 136) 8 (A_G_REC + 24 + 56 * c) ->
aval_mem (rdW W memc) (sp1 + 152) 8 rdv ->
aval_mem (rdW W memc) (A_G_REC + 8) 4 nc -> aval_mem (rdW W memc) (A_G_REC + 16 + 56 * c) 4 fn ->
aval_mem (rdW W memc) W16 8 arr ->
range_addressable (rdW W memc) SHADOW_OFF (A_G_REC + 16 + 56 * c) 8 ->
range_addressable (rdW W memc) SHADOW_OFF W16 8 ->
range_addressable (rdW W memc) SHADOW_OFF (A_G_REC + 8) 8 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) W16 arr fn c rdv nc))) ssD
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_D)) memc (seg_rom SEGS))) /\
sh_ok SEGS DBx d_SH (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) W16 arr fn c rdv nc))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc sp1 c W16 arr fn rdv nc H9 Hsp Hsp32 H23 Hc HW HWs Harr Hfn Hrdv Hnc
  V64 V72 V80 V88 V96 V112 V120 V128 V136 V152 VNC VFN VWW RA1 RA2 RA3.
set (cp := A_G_REC + 16 + 56 * c) in *.
assert (Hcp : A_G_REC + 16 <= cp <= A_G_REC + 16 + 56 * 15) by (subst cp; lia).
assert (HG : A_G_REC = 6174528) by reflexivity.
set (E := Eimg (Ereg regsc (d_extra cp W16 arr fn c rdv nc))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (d_extra cp W16 arr fn c rdv nc) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. subst E. rewrite Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 39%nat ltac:(unfold A_TEXT; lia)) as E39.
cbn [Nat.sub nth d_extra] in E32, E33, E34, E35, E36, E37, E38, E39.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (DO : forall n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off)).
{ intros n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity. }
unfold CW_SB in *.
split.
- unfold ssD. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold d_regions, d_scr, d_nc, d_fn, d_ww.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 64 8 _ A_G_REC); [rewrite (DO 32%nat _ 0 E32); f_equal; lia | rewrite HG; lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V64).
      -- apply (chunk_ok_val SEGS E _ sp1 72 8 _ (2147450880 + (A_G_REC + 8) / 8));
           [unfold shx, DBx; apply (denot_shx E 32 23 8 A_G_REC 2147450880 E32 E23); rewrite ?HG; lia
           | replace ((A_G_REC + 8) / 8) with 771817 by (vm_compute; reflexivity); lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V72).
      -- apply (chunk_ok_val SEGS E _ sp1 80 8 _ c); [rewrite (DO 37%nat _ 0 E37); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V80).
      -- apply (chunk_ok_val SEGS E _ sp1 88 8 _ (2147450880 + W16 / 8));
           [unfold shx, DBx; rewrite (denot_shx E 34 23 0 W16 2147450880 E34 E23) by lia; f_equal; rewrite Z.add_0_r; reflexivity
           | split; [pose proof (Z.div_pos W16 8 ltac:(lia) ltac:(lia)); lia | pose proof (Z.div_le_upper_bound W16 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]
           | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V88).
      -- apply (chunk_ok_val SEGS E _ sp1 96 8 _ W16); [rewrite (DO 34%nat _ 0 E34); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V96).
      -- apply (chunk_ok_val SEGS E _ sp1 112 8 _ (cp / 8));
           [apply (cwd_denot_srl3 E 33 cp E33); lia
           | split; [apply Z.div_pos; lia | pose proof (Z.div_le_upper_bound cp 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia] | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V112).
      -- apply (chunk_ok_val SEGS E _ sp1 120 8 _ cp); [rewrite (DO 33%nat _ 0 E33); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V120).
      -- apply (chunk_ok_val SEGS E _ sp1 128 8 _ (A_G_REC + 24 + 56 * c)); [rewrite (DO 33%nat _ 8 E33); f_equal; subst cp; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V128).
      -- apply (chunk_ok_val SEGS E _ sp1 136 8 _ (A_G_REC + 24 + 56 * c)); [rewrite (DO 33%nat _ 8 E33); f_equal; subst cp; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V136).
      -- apply (chunk_ok_val SEGS E _ sp1 152 8 _ rdv); [rewrite (DO 38%nat _ 0 E38); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V152).
    * rewrite (VB 32%nat A_G_REC E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 _ nc); [rewrite (DO 39%nat _ 0 E39); f_equal; lia | lia | lia |].
      exact (cwd_val_of_aval _ _ _ _ _ VNC).
    * rewrite (VB 33%nat cp E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ cp 0 4 _ fn); [rewrite (DO 36%nat _ 0 E36); f_equal; lia | lia | lia |].
      rewrite Z.add_0_r. exact (cwd_val_of_aval _ _ _ _ _ VFN).
    * rewrite (VB 34%nat W16 E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ W16 0 8 _ arr); [rewrite (DO 35%nat _ 0 E35); f_equal; lia | lia | lia |].
      rewrite Z.add_0_r. exact (cwd_val_of_aval _ _ _ _ _ VWW).
  + apply pairwise_disjoint_of_extents. unfold d_regions, d_scr, d_nc, d_fn, d_ww, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 32%nat A_G_REC E32) by lia. rewrite (VB 33%nat cp E33) by lia.
    rewrite (VB 34%nat W16 E34) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HG in *. repeat split; lia.
  + split; [|split; exact I].
    cbn [f_atoms atoms_ok d_facts]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E23, E32, E33, E34, E35, E36, E37, E38, E39.
    rewrite !unsigned_lit_small by (rewrite ?HG; lia).
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    pose proof (cwd_cp_al c) as Hcpa. fold cp in Hcpa.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | exact Hsp32 | exact Hcpa | reflexivity].
- assert (Hcpn : 6174544 <= cp <= 6175384) by (rewrite HG in Hcp; lia).
  unfold sh_ok, d_SH. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) memc E DBx 33 cp 8 cp 0 8 RA1).
    * unfold DBx. rewrite U_SOff. rewrite E23. rewrite unsigned_lit_small by lia.
      rewrite Z.add_0_r. vm_compute. reflexivity.
    * rewrite U_SOff. rewrite E33. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
      apply zcanon_id. unfold M64. lia.
    * lia. * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memc E DBx 34 W16 8 W16 0 8 RA2).
    * unfold DBx. rewrite U_SOff. rewrite E23. rewrite unsigned_lit_small by lia.
      rewrite Z.add_0_r. vm_compute. reflexivity.
    * rewrite U_SOff. rewrite E34. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
      apply zcanon_id. unfold M64. lia.
    * lia. * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memc E DBx 32 (A_G_REC + 8) 8 A_G_REC 8 16 RA3).
    * unfold DBx. rewrite U_SOff. rewrite E23. rewrite unsigned_lit_small by lia.
      rewrite Z.add_0_r. vm_compute. reflexivity.
    * rewrite U_SOff. rewrite E32. rewrite unsigned_lit_small by (rewrite HG; lia). rewrite Z.add_0_r.
      apply zcanon_id. unfold M64. rewrite HG. lia.
    * lia. * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. rewrite HG in *. lia.
Qed.

Lemma cwd_seedP : forall (W : world SEGS) (regsc : bvmap 5 word) memc pc sp1 c nc,
getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
getr regsc 19 = w64 A_G_REC -> getr regsc 20 = w64 c -> 0 <= c <= 15 -> 0 <= nc <= 16 ->
aval_mem (rdW W memc) (sp1 + 72) 8 (CW_SB + (A_G_REC + 8) / 8) ->
aval_mem (rdW W memc) (sp1 + 128) 8 (A_G_REC + 24 + 56 * c) ->
aval_mem (rdW W memc) (sp1 + 136) 8 (A_G_REC + 24 + 56 * c) ->
aval_mem (rdW W memc) (A_G_REC + 8) 4 nc ->
(forall a, sp1 + 128 <= a < sp1 + 144 -> apresent (w_H W) memc a) ->
range_addressable (rdW W memc) SHADOW_OFF (A_G_REC + 8) 8 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (p_extra c nc))) (ssP pc)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
sh_ok SEGS DBx p_SH (Eimg (Ereg regsc (p_extra c nc))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc pc sp1 c nc H9 Hsp Hsp32 H23 H19 H20 Hc Hnc V72 V128 V136 VNC HPR RA3.
assert (HG : A_G_REC = 6174528) by reflexivity.
set (E := Eimg (Ereg regsc (p_extra c nc))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (p_extra c nc) (Z_to_bv 64 0)).
{ intros m Hm. replace m with (32 + (m - 32))%nat at 1 by lia. subst E. rewrite Eimg_low by lia. apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 A_G_REC) by (rewrite (EE 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 c) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.sub nth p_extra] in E32, E33.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (DO : forall n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off)).
{ intros n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity. }
unfold CW_SB in *.
split.
- unfold ssP. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold p_scr, p_nc.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 72 8 _ (2147450880 + (A_G_REC + 8) / 8));
           [unfold shx, DBx; apply (denot_shx E 19 23 8 A_G_REC 2147450880 E19 E23); rewrite ?HG; lia
           | replace ((A_G_REC + 8) / 8) with 771817 by (vm_compute; reflexivity); lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V72).
      -- apply (chunk_ok_val SEGS E _ sp1 128 8 _ (A_G_REC + 24 + 56 * c)); [rewrite (DO 32%nat _ 0 E32); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V128).
      -- apply (chunk_ok_val SEGS E _ sp1 136 8 _ (A_G_REC + 24 + 56 * c)); [rewrite (DO 32%nat _ 0 E32); f_equal; lia | lia | lia |].
         exact (cwd_val_of_aval _ _ _ _ _ V136).
    * rewrite (VB 19%nat A_G_REC E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 _ nc); [rewrite (DO 33%nat _ 0 E33); f_equal; lia | lia | lia |].
      exact (cwd_val_of_aval _ _ _ _ _ VNC).
  + apply pairwise_disjoint_of_extents. unfold p_scr, p_nc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 19%nat A_G_REC E19) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite HG in *. repeat split; lia.
  + split; [|split; exact I].
    cbn [f_atoms atoms_ok p_facts]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E19, E20, E23, E32, E33.
    rewrite !unsigned_lit_small by (rewrite ?HG; lia).
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    assert (Hqa : (A_G_REC + 24 + 56 * c) mod 8 = 0).
    { replace (A_G_REC + 24 + 56 * c) with ((771819 + 7 * c) * 8) by (unfold A_G_REC; lia). apply Z_mod_mult. }
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | exact Hsp32 | exact Hqa | reflexivity].
- unfold sh_ok, p_SH. repeat apply Forall_cons; try apply Forall_nil.
  apply (shent_ok_of_range SEGS (w_H W) memc E DBx 19 (A_G_REC + 8) 8 A_G_REC 8 16 RA3).
  + unfold DBx. rewrite U_SOff. rewrite E23. rewrite unsigned_lit_small by lia.
    rewrite Z.add_0_r. vm_compute. reflexivity.
  + rewrite U_SOff. rewrite E19. rewrite unsigned_lit_small by (rewrite HG; lia). rewrite Z.add_0_r.
    apply zcanon_id. unfold M64. rewrite HG. lia.
  + lia. + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. rewrite HG in *. lia.
Qed.


(* ---------------------------------------------------------------------------------------------------------- *)
(* the call loop's latch (0x87d34 .. 0x87d64; listing 0x1850 .. 0x1880), entered there or by the `j` after the add
   call (0x1800) and the chain call (0x1824): the inline check of g_rec.ncalls, c + 1, the two cursors at s1 + 128
   and s1 + 136 move on by one call (56 bytes), `blt c+1 ncalls` back to LH (0x1598), else on to REL (0x18d4). The
   three entries reach the `blt` in the same symbolic state; the runs write only [s1 + 128, s1 + 144). *)
Definition cwdl_Z (sp1 a : Z) : Prop := sp1 + 128 <= a < sp1 + 144.
Definition cwdl_wok (ws : list (option nat * Z * Z)) : bool :=
forallb (fun w => match w with (b, lo, hi) =>
  (hi <=? lo) || (match b with Some n => Nat.eqb n 9 | None => false end && ((128 <=? lo) && (hi <=? 144))) end) ws.
Lemma cwdl_kept : forall E rs H (m m' : word -> option byte) sp1,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> bv_unsigned (ew E 9) = sp1 -> cwdl_wok (windows rs) = true ->
  forall a, 0 <= a < 2 ^ 64 -> ~ cwdl_Z sp1 a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' sp1 HF H9 Hw. apply (kept_of_frame E rs H m m' (cwdl_Z sp1) HF).
intros b wlo whi a Hin Ha. unfold cwdl_wok in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Hin). cbn beta iota in Hw.
apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hb Hw].
destruct b as [n|]; cbn beta iota in Hb; [|discriminate Hb]. apply Nat.eqb_eq in Hb. subst n.
cbn [base_val] in Ha. rewrite H9 in Ha. unfold cwdl_Z.
apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma cwdl_aval_keep : forall (rd rd' : reader) sp1 a n v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ cwdl_Z sp1 x -> rd' x = rd x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= sp1 + 128 \/ sp1 + 144 <= a) ->
  aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' sp1 a n v K H0 H1 H2 H k Hk. rewrite K; [exact (H k Hk) | lia | unfold cwdl_Z; lia]. Qed.
Lemma cwdl_DO : forall E n v off, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + off < 2 ^ 64 ->
  sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn Hv Hvo.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n off))). f_equal.
change (U E (SOff n off) = v + off). apply U_atom_off; [exact Hn | lia | lia].
Qed.
Lemma cwdl_lt_off : forall E n m c x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x -> 0 <= c -> x + c < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n c)) (sv_denot E (SOff m 0)) = (x + c <? y).
Proof.
intros E n m c x y Hn Hm Hx Hc Hxc Hy. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n c))) with (Sg E (SOff n c)).
change (bv_signed (sv_denot E (SOff m 0))) with (Sg E (SOff m 0)).
rewrite !S_SOff, Hn, Hm, !unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cwdl_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH].
- unfold PJn.join_need. cbn [join_sp length fold_right]. apply Z.le_refl.
- assert (E : join_sp (w :: ws) = match ws with [] => w | _ :: _ => w ++ SPACE :: join_sp ws end) by reflexivity.
  rewrite E. unfold PJn.join_need in *. cbn [fold_right].
  assert (0 <= fold_right (fun w acc => Z.of_nat (length w) + 1 + acc) 0 ws).
  { clear IH E. induction ws as [|w1 ws1 IH1]; cbn [fold_right]; [apply Z.le_refl|].
    pose proof (Nat2Z.is_nonneg (length w1)). lia. }
  destruct ws as [|w2 ws2]; cbv beta iota; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.
(* the recorder holds at most 16 calls (cw_ent's rec_repA: ag1_calls) *)
Lemma cwdl_ncalls_le : forall e, cw_ent B MT e -> cw_ncalls e <= 16.
Proof.
intros e Hent. unfold cw_ent in Hent. cbv zeta in Hent.
destruct Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrec & _).
destruct Hrec as (Q & (_ & _ & _ & (Hl & _) & _) & _).
unfold cw_ncalls. lia.
Qed.
(* cw_core and cw_line at a state that differs from the current one only in [s1 + 128, s1 + 144) and the registers
   the latch writes *)
Lemma cwdl_common : forall e lyc Sc Wc regsc memc mdc regs2 mem2 mdc2 pos sp1 line,
  cw_core B e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem2 mdc2 EV_JOINED ->
  getr regs2 2 = getr regsc 2 -> getr regs2 3 = getr regsc 3 -> getr regs2 4 = getr regsc 4 ->
  getr regs2 8 = getr regsc 8 -> getr regs2 9 = getr regsc 9 -> getr regs2 23 = getr regsc 23 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cwdl_Z sp1 a -> rdW Wc mem2 a = rdW Wc memc a) ->
  cw_core B e lyc Sc Wc regs2 mem2 mdc2 pos sp1 EV_JOINED /\ cw_line B MT e lyc Sc (rdW Wc mem2) line.
Proof.
intros e lyc Sc Wc regsc memc mdc regs2 mem2 mdc2 pos sp1 line HC HL HJ2 R2 R3 R4 R8 R9 R23 KEEP.
destruct HC as (HJ & Hsp & Hsp32 & Hspr & H3 & H4 & H8 & H9 & H23 & Hsav & V16 & V24 & V32 & V152 & V56F & SB4 & SB5).
pose proof HJ2 as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (HF : 4096 <= frame_addr (e_ly e) 0 pos /\ frame_addr (e_ly e) 0 pos + 64 <= alloc_ceiling).
{ assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc mem2 mdc2 0 pos HAR Hin) as (Hf1 & Hf2 & _).
  assert (Hfa : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
  assert (Hfb : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
  rewrite Hfa, Hfb in *. lia. }
pose proof (Z.div_pos (frame_addr (e_ly e) 0 pos) 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound (frame_addr (e_ly e) 0 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8b.
split.
- split; [exact HJ2|]. split; [unfold spZ in *; rewrite R2; exact Hsp|]. split; [exact Hsp32|]. split; [exact Hspr|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R23; exact H23|].
  split.
  { intros j r Hj. assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length cw_saved] in Hj13.
    apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact (Hsav j r Hj)]. }
  split; [apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V16]|].
  split; [apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V24]|].
  split; [apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V32]|].
  split; [apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V152]|].
  split; [apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V56F]|].
  split; (rewrite KEEP; [assumption | unfold CW_SB; lia | unfold cwdl_Z, CW_SB; lia]).
- destruct HL as (Hperm & H4096 & Hfa & Hbytes & Hmo).
  split; [exact Hperm|]. split; [exact H4096|]. split; [exact Hfa|]. split; [|exact Hmo].
  assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem2 mdc2 line (cw_JN e) HAR Hin) as (_ & Hl4096 & Hlceil & _).
  pose proof (cwdl_join_len (e_ws e)) as HJL.
  assert (HRS : req_size (cw_JN e) = cw_JN e) by (unfold req_size, cw_JN in *; destruct (Z.eqb_spec (PJn.join_need (e_ws e) + 1) 0); lia).
  rewrite HRS in Hlceil. unfold cw_JN in Hlceil.
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KEEP; [exact (Hbytes i ltac:(rewrite length_app; cbn [length]; lia)) | lia | unfold cwdl_Z; lia].
Qed.
(* the scratch slots of call c + 1: the two cursors moved on, every other slot kept *)
Lemma cwdl_lscr : forall e (rd rd' : reader) sp1 F line c,
  (forall a, 0 <= a < 2 ^ 64 -> ~ cwdl_Z sp1 a -> rd' a = rd a) -> 0 <= sp1 -> sp1 + 160 <= 2 ^ 64 ->
  cw_lscr e rd sp1 F line c ->
  aval_mem rd' (sp1 + 128) 8 (A_G_REC + 24 + 56 * (c + 1)) ->
  aval_mem rd' (sp1 + 136) 8 (A_G_REC + 24 + 56 * (c + 1)) ->
  cw_lscr e rd' sp1 F line (c + 1).
Proof.
intros e rd rd' sp1 F line c KEEP H0 H1 HS N128 N136.
destruct HS as (V144 & V8 & V40 & V48 & V56 & V64 & V72 & V88 & V96 & V104 & _ & _).
unfold cw_lscr.
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V144]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V8]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V40]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V48]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V56]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V64]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V72]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V88]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V96]|].
split; [apply (cwdl_aval_keep rd rd' sp1 _ _ _ KEEP); [lia | lia | lia | exact V104]|].
split; [exact N128 | exact N136].
Qed.
(* the latch's tactics: the run's write window (base atom 9 = s1, sp0 + (s1 - sp0)), the bytes it keeps, a register
   and a region of the symbolic state *)
Ltac cwdl_awr sp1 sp0 U9 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk s0 fp b0 bc fr ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | apply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
Ltac cwdl_keep sp1 U9 K :=
  lazymatch goal with HFr : frame_of ?E _ (mrestrict ?H ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (cwdl_kept E _ H m0 m1 sp1 HFr U9 ltac:(cbn [ssP ss_mem]; vm_compute; reflexivity)) as K;
    clear HFr end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cwdl_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let x := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with x in Hr end.
Ltac cwdl_region HS i RG :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?R =>
      pose proof (st_ok_region_nth E _ _ i R HS ltac:(vm_compute; reflexivity)) as RG end end.
(* the run's continuation, given the run's hypotheses while they still exist (as paj_run_tok passes them) *)
Ltac cwdl_post HS HJ SHOK := clear HS HJ SHOK; paj_after_run_tok HS HJ SHOK.

Lemma cwd_latch : forall (pc : Z) e lyc Sc Wc regsc memc mdc pos sp1 line c,
ST_LH B MT (c + 1) -> ST_REL B MT ->
(pc = CW_PC_LATCH \/ pc = CW_PC_RADD \/ pc = CW_PC_RCHAIN) ->
cw_ent B MT e -> INV_LH B MT e lyc Sc Wc regsc memc mdc pos sp1 line c ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e) ->
cw_at B MT e Wc regsc (BASE + pc) memc mdc.
Proof.
intros pc e lyc Sc Wc regsc memc mdc pos sp1 line c HLH HREL Hpc Hent HI VNC.
unfold ST_LH, cw_at in HLH. unfold ST_REL, cw_at in HREL.
destruct HI as (HC & HL & HS0 & H19 & H20 & H24 & Hcr).
pose proof HC as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H23 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (HG : A_G_REC = 6174528) by reflexivity.
pose proof (cwdl_ncalls_le e Hent) as Hn16.
assert (Hn0 : 0 <= cw_ncalls e) by (unfold cw_ncalls; lia).
pose proof HS0 as (_ & _ & _ & _ & _ & _ & V72 & _ & _ & _ & V128 & V136).
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HAR ltac:(unfold CW_ZSH; left; reflexivity)) as [RA _].
assert (RA3 : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 8) 8)
  by (apply range_addressable_sub with (a := A_G_REC) (len := 960); [exact RA | lia | lia]).
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (Hc15 : 0 <= c <= 15) by lia.
unfold OFF_NCALLS in VNC.
destruct (cwd_seedP Wc regsc memc pc sp1 c (cw_ncalls e) H9 Hsp1 Hsp32 H23 H19 H20 Hc15 ltac:(lia)
  V72 V128 V136 VNC ltac:(intros a Ha; apply Hpres; lia) RA3) as [HS SHOK].
remember (Eimg (Ereg regsc (p_extra c (cw_ncalls e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (p_extra c (cw_ncalls e))) E)
  by (split; [intros n Hn; rewrite HE; apply Eimg_low; unfold A_TEXT; lia | rewrite HE; reflexivity]).
assert (E9 : ew E 9 = Z_to_bv 64 sp1).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl). exact H9. }
assert (E20 : ew E 20 = Z_to_bv 64 c).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl). exact H20. }
assert (E32 : ew E 32 = Z_to_bv 64 (A_G_REC + 24 + 56 * c)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsc _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 (cw_ncalls e)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsc _ 1). }
clear HE.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
unfold cw_at.
(* the latch to its `blt`: the run from each of the three entries is the run from 0x1850 *)
lazymatch paj_tables RUN with (?tpi, ?tw) =>
  let K := eval vm_compute in (run_K A_LIM DBx p_SH (ssP CW_PC_LATCH)) in
  let r := eval vm_compute in (sym_runN_pi_tok tpi tw K DBx DBspan p_SH FUEL (ssP CW_PC_LATCH)) in
  lazymatch r with (?st', ?rs) =>
    assert (Hrun : sym_runN_pi_tok tpi tw K DBx DBspan p_SH FUEL (ssP pc) = (st', rs))
      by (destruct Hpc as [-> | [-> | ->]]; vm_compute; reflexivity);
    eapply (RUN Wc FUEL E K DBx DBspan p_SH (ssP pc) st' rs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK ltac:(cbn [ssP ss_facts ss_mem]; vm_compute; reflexivity) Hrun HJ);
    [ clear Hrun; cbn [sh_obls]; srr_obls
    | clear Hrun; cbn [ssP ss_mem]; cwdl_awr sp1 (cw_sp0 e) U9
    | clear Hrun; cwdl_post HS HJ SHOK ]
  end
end.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
cwdl_keep sp1 U9 K1.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* c + 1 < ncalls: back to the loop head, call c + 1 *)
  rewrite (cwdl_lt_off E 20 33 1 c (cw_ncalls e) E20 E33) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK DBspan CW_PC_LH; [cwdl_awr sp1 (cw_sp0 e) U9 |].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  cwdl_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwdl_Z sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  pose proof (regs_kept_of_st_ok_pi E _ _ regsc _
    [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (19%bv : bv 5); (23%bv : bv 5);
     (24%bv : bv 5)] HS HAE ltac:(vm_compute; reflexivity)) as RK.
  pose proof (RK (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R2.
  pose proof (RK (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R3.
  pose proof (RK (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R4.
  pose proof (RK (8%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R8.
  pose proof (RK (9%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R9.
  pose proof (RK (19%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R19.
  pose proof (RK (23%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R23.
  pose proof (RK (24%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R24.
  cbn [ms_regs restrict] in R2, R3, R4, R8, R9, R19, R23, R24.
  cwdl_reg HS (20%bv : bv 5) Q20.
  assert (X20 : getr (ms_regs ms2) 20 = w64 (c + 1)).
  { rewrite Q20, (cwdl_DO E 20 c 1 E20) by lia. reflexivity. }
  cwdl_region HS 0%nat RG.
  cbn [ms_mem restrict] in RG.
  assert (N128 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 128) 8 (A_G_REC + 24 + 56 * (c + 1))).
  { apply cwd_aval_of_val.
    apply (field_of_region E _ 9%nat sp1 _ 72 144 128 144 128 8 (SOff 32 56) (A_G_REC + 24 + 56 * (c + 1)) RG U9);
      [repeat (first [left; reflexivity | right]) | rewrite (cwdl_DO E 32 _ 56 E32) by lia; f_equal; lia | zside | zside]. }
  assert (N136 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 136) 8 (A_G_REC + 24 + 56 * (c + 1))).
  { apply cwd_aval_of_val.
    apply (field_of_region E _ 9%nat sp1 _ 72 144 128 144 136 8 (SOff 32 56) (A_G_REC + 24 + 56 * (c + 1)) RG U9);
      [repeat (first [left; reflexivity | right]) | rewrite (cwdl_DO E 32 _ 56 E32) by lia; f_equal; lia | zside | zside]. }
  destruct (cwdl_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line HC HL HJ
    R2 R3 R4 R8 R9 R23 KEEP) as [HC2 HL2].
  pose proof (cwdl_lscr e (rdW Wc memc) (rdW Wc (ms_mem ms2)) sp1 (frame_addr (e_ly e) 0 pos) line c KEEP
    ltac:(lia) ltac:(lia) HS0 N128 N136) as HS2.
  assert (Hc1 : 0 <= c + 1 < cw_ncalls e) by lia.
  pmkst HS. change (BASE + 5528) with (BASE + CW_PC_LH).
  apply (HLH e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line Hent).
  exact (conj HC2 (conj HL2 (conj HS2 (conj (eq_trans R19 H19) (conj X20 (conj (eq_trans R24 H24) Hc1)))))).
- (* c + 1 >= ncalls: on to REL *)
  paj_run_to_tok RUNTO HS HJ SHOK DBspan CW_PC_REL; [cwdl_awr sp1 (cw_sp0 e) U9 |].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  cwdl_keep sp1 U9 K2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ cwdl_Z sp1 a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hz; rewrite (K2 a Ha Hz); exact (K1 a Ha Hz)).
  pose proof (regs_kept_of_st_ok_pi E _ _ regsc _
    [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (23%bv : bv 5)]
    HS HAE ltac:(vm_compute; reflexivity)) as RK.
  pose proof (RK (2%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R2.
  pose proof (RK (3%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R3.
  pose proof (RK (4%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R4.
  pose proof (RK (8%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R8.
  pose proof (RK (9%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R9.
  pose proof (RK (23%bv : bv 5) ltac:(repeat (first [left; reflexivity | right]))) as R23.
  cbn [ms_regs restrict] in R2, R3, R4, R8, R9, R23.
  destruct (cwdl_common e lyc Sc Wc regsc memc mdc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line HC HL HJ
    R2 R3 R4 R8 R9 R23 KEEP) as [HC2 HL2].
  pose proof HS0 as (V144 & _).
  assert (N144 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 144) 8 line)
    by (apply (cwdl_aval_keep _ _ sp1 _ _ _ KEEP); [lia | lia | lia | exact V144]).
  pmkst HS. change (BASE + 6356) with (BASE + CW_PC_REL).
  apply (HREL e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 line Hent).
  exact (conj HC2 (conj HL2 N144)).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* transports: a fact of the entry still holds at the current state (the journal from the entry, footprint []) *)
Lemma cwdt_str_kept : forall (rd rd' : reader) p s n,
(forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) -> Z.of_nat (length s) + 1 <= n ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s n Hk Hn [Hb Hnul]. split; [|exact Hnul].
apply (cw_abytes_kept rd); [|exact Hb]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
(* the recorder's state over two readers that agree on g_rec, record.spill and the bytes of the blocks it points to *)
Lemma cwdt_call_kept : forall bl bl' (rd rd' : reader) a c P,
(forall x, a <= x < a + 56 -> rd' x = rd x) ->
(forall p n, In (p, n) bl -> In (p, n) bl' /\ forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
acall_at bl rd a c P -> acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P HA HB (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold acall_at. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (cwd_aval_kept rd); [intros k Hk; apply HA; unfold CALL_OFF_FN; lia | exact H4]|].
split; [apply (cwd_aval_kept rd); [intros k Hk; apply HA; unfold CALL_OFF_NARGS; lia | exact H5]|].
split; [exact H6|].
intros k s [p n] Hs Hpn. destruct (H7 k s (p, n) Hs Hpn) as (V & Hnz & Hin & Hsz & Hstr). cbn [fst snd] in *.
assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
destruct (HB p n Hin) as [Hin' Hb].
split; [apply (cwd_aval_kept rd); [intros j Hj; apply HA; unfold CALL_OFF_ARGS; lia | exact V]|].
split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (cwdt_str_kept rd rd' p s n); [exact Hb | lia | exact Hstr].
Qed.
Lemma cwdt_rep_kept : forall bl bl' (rd rd' : reader) R Q,
(forall x, A_G_REC <= x < A_G_REC + 960 -> rd' x = rd x) ->
(forall x, A_REC_SPILL <= x < A_REC_SPILL + 56 -> rd' x = rd x) ->
(forall p n, In (p, n) bl -> In (p, n) bl' /\ forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl rd A_G_REC A_REC_SPILL R Q -> arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HG HS HB (Ha1 & Ha2 & Hap & (Hl & HlQ & Hnc & Hcalls & Hsp & Hspl) & Hans & Hrep & Hsc & Hown).
assert (AV : forall off n v, 0 <= off -> off + Z.of_nat n <= 960 -> aval_mem rd (A_G_REC + off) n v ->
  aval_mem rd' (A_G_REC + off) n v).
{ intros off n v H0 H1 Hv. apply (cwd_aval_kept rd); [intros k Hk; apply HG; lia | exact Hv]. }
unfold arep_at. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact Hap|].
split.
{ unfold ag1_calls. split; [exact Hl|]. split; [exact HlQ|].
  split; [apply AV; [unfold OFF_NCALLS; lia | unfold OFF_NCALLS; lia | exact Hnc]|].
  split; [|split; [apply (cwdt_call_kept bl bl' rd rd' A_REC_SPILL); [exact HS | exact HB | exact Hsp] | exact Hspl]].
  intros i c P Hc HP. destruct (Hcalls i c P Hc HP) as [Hca Hf]. split; [|exact Hf].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  apply (cwdt_call_kept bl bl' rd rd'); [| exact HB | exact Hca]. intros x Hx. apply HG. unfold OFF_CALLS, CALL_SIZE in *. lia. }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|], (l_answer Q) as [[p n]|]; cbv iota beta in Hans |- *;
  try contradiction.
  - destruct Hans as (V & Hnz & Hin & Hsz & Hstr & Hx). cbn [fst snd] in *. destruct (HB p n Hin) as [Hin' Hb].
    split; [apply AV; [unfold OFF_ANSWER; lia | unfold OFF_ANSWER; lia | exact V]|].
    split; [exact Hnz|]. split; [exact Hin'|]. split; [exact Hsz|]. split; [|exact Hx].
    apply (cwdt_str_kept rd rd' p x n); [exact Hb | lia | exact Hstr].
  - apply AV; [unfold OFF_ANSWER; lia | unfold OFF_ANSWER; lia | exact Hans]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|], (l_reply Q) as [[p n]|]; cbv iota beta in Hrep |- *;
  try contradiction.
  - destruct Hrep as (V1 & V2 & Hnz & Hne & Hin & Hsz & Hb0 & Hx). cbn [fst snd] in *. destruct (HB p n Hin) as [Hin' Hb].
    split; [apply AV; [unfold OFF_REPLY; lia | unfold OFF_REPLY; lia | exact V1]|].
    split; [apply AV; [unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE; lia | exact V2]|].
    split; [exact Hnz|]. split; [exact Hne|]. split; [exact Hin'|]. split; [exact Hsz|]. split; [|exact Hx].
    apply (cw_abytes_kept rd rd' p x); [intros i Hi; apply Hb; lia | exact Hb0].
  - destruct Hrep as [V1 V2].
    split; [apply AV; [unfold OFF_REPLY; lia | unfold OFF_REPLY; lia | exact V1]|].
    apply AV; [unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE; lia | exact V2]. }
split; [|exact Hown].
destruct Hsc as (V1 & V2 & V3 & V4 & V5 & Rr). unfold ag1_scalars.
split; [apply AV; [unfold OFF_REFUSE; lia | unfold OFF_REFUSE; lia | exact V1]|].
split; [apply AV; [unfold OFF_CODE; lia | unfold OFF_CODE; lia | exact V2]|].
split; [apply AV; [unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES; lia | exact V3]|].
split; [apply AV; [unfold OFF_STATE; lia | unfold OFF_STATE; lia | exact V4]|].
split; [apply AV; [unfold OFF_HOST; lia | unfold OFF_HOST; lia | exact V5]|].
exact Rr.
Qed.

(* the program's statics g_rec, record.spill, g_quitting: the journal's image clause with cmd_prog_unowned *)
Lemma cwd_keep_prog : forall e lyc Sc Wc regsc memc mdc pos sp1 k a,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k -> inFP cmd_PG a ->
rdW Wc memc a = cw_rd0 e a.
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k a _ Hc Ha.
unfold cw_core in Hc. cbv zeta in Hc. destruct Hc as (HJ & _).
destruct (cmd_prog_unowned a Ha) as (Himg & Hno & Herr).
exact (cw_img_kept B e lyc Sc Wc memc mdc pos k a HJ Himg Hno Herr).
Qed.

(* a block live at the entry and now: the journal's block clause *)
Lemma cwd_keep_blk : forall e lyc Sc Wc regsc memc mdc pos sp1 k p n a,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k ->
In (p, n) (ablocks B (e_ly e) (e_S e)) -> In (p, n) (ablocks B lyc Sc) -> p <= a < p + req_size n ->
rdW Wc memc a = cw_rd0 e a.
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k p n a _ Hc H0 H1 Ha.
unfold cw_core in Hc. cbv zeta in Hc. destruct Hc as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace a with (p + (a - p)) by lia.
exact (F2 p n (a - p) H0 H1 ltac:(lia) (inFP_nil _)).
Qed.

(* the caller's memory at or above sp0 *)
Lemma cwd_keep_above : forall e lyc Sc Wc regsc memc mdc pos sp1 k a,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k -> cw_sp0 e <= a < 2 ^ 64 ->
rdW Wc memc a = cw_rd0 e a.
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k a _ Hc Ha.
unfold cw_core in Hc. cbv zeta in Hc. destruct Hc as (HJ & _).
exact (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha (inFP_nil a)).
Qed.

(* the image's read-only bytes: the journal's image clause (RRO for the RELRO range), then cmd_ro_ok_of_aro *)
Lemma cwd_rodata_at : forall e lyc Sc Wc regsc memc mdc pos sp1 k,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc).
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k Hent Hc.
unfold cw_core in Hc. cbv zeta in Hc. destruct Hc as (HJ & _).
assert (Haro0 : arodata_okP SEGS RLO RHI B (cw_rd0 e)).
{ unfold cw_ent in Hent. cbv zeta in Hent. destruct Hent as (_ & _ & Haro & _). exact Haro. }
assert (Haro : arodata_okP SEGS RLO RHI B (rdW Wc memc)).
{ intros a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (Haro0 a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil (inFP_nil a))].
  destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hgot)]. }
split; [exact Haro|].
pose proof HJ as (HAR & _).
exact (cmd_ro_ok_of_aro lyc Sc Wc memc mdc HAR Haro).
Qed.

(* the recorder's state: the entry's rec_repA, g_rec / record.spill by cwd_keep_prog, the argument strings by
   cwd_keep_blk (every entry block is still live: cw_line's Permutation) *)
Lemma cwd_rec_at : forall e lyc Sc Wc regsc memc mdc pos sp1 k line,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k ->
cw_line B MT e lyc Sc (rdW Wc memc) line ->
rec_repA B lyc Sc (rdW Wc memc) (e_R e) (e_O e).
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k line Hent Hc Hl.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Q & HQ & HO) & _).
destruct Hl as (Hperm & _).
exists Q. split; [|exact HO].
apply (cwdt_rep_kept (ablocks B (e_ly e) (e_S e)) _ (cw_rd0 e)); [| | | exact HQ].
- intros x Hx. apply (cwd_keep_prog e lyc Sc Wc regsc memc mdc pos sp1 k x Hent Hc).
  exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; lia].
- intros x Hx. apply (cwd_keep_prog e lyc Sc Wc regsc memc mdc pos sp1 k x Hent Hc).
  exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; lia].
- intros p n Hin.
  assert (Hin' : In (p, n) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hin).
  split; [exact Hin'|]. intros i Hi.
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  apply (cwd_keep_blk e lyc Sc Wc regsc memc mdc pos sp1 k p n (p + i) Hent Hc Hin Hin'). lia.
Qed.

(* call c's record at the current state: cwd_rec_at's acall_at; an argument's block bounds from AR *)
Lemma cwd_call_at : forall e lyc Sc Wc regsc memc mdc pos sp1 k line c fn args,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k ->
cw_line B MT e lyc Sc (rdW Wc memc) line ->
nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) -> 0 <= c ->
0 <= fn < REC_FN_COUNT /\ (length args <= 6)%nat /\
aval_mem (rdW Wc memc) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_FN) 4 fn /\
aval_mem (rdW Wc memc) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_NARGS) 4 (Z.of_nat (length args)) /\
aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e) /\
(forall j s, nth_error args j = Some s -> exists q,
 aval_mem (rdW Wc memc) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 8 * Z.of_nat j) 8 q /\
 0 < q < 2 ^ 64 /\ in_blockA (ablocks B lyc Sc) q (Z.of_nat (length s) + 1) /\
 astr_atR (rdW Wc memc) q s).
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k line c fn args Hent Hc Hl Hnth Hc0.
pose proof (cwd_rec_at e lyc Sc Wc regsc memc mdc pos sp1 k line Hent Hc Hl) as (Q & Hrep & _).
destruct Hrep as (_ & _ & _ & (_ & HlQ & Hnc & Hcalls & _) & _).
assert (HAR : AR SEGS B lyc Sc Wc memc mdc).
{ unfold cw_core in Hc. cbv zeta in Hc. destruct Hc as (HJ & _). destruct HJ as (HAR & _). exact HAR. }
assert (Hlt : (Z.to_nat c < length (r_calls (e_R e)))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
destruct (nth_error (l_calls Q) (Z.to_nat c)) as [P|] eqn:HP.
2: { exfalso. apply nth_error_None in HP. lia. }
destruct (Hcalls _ _ _ Hnth HP) as (Hca & _).
rewrite Z2Nat.id in Hca by exact Hc0.
destruct Hca as (Hfn & Hna & HlP & Vfn & Vna & _ & Hargs). cbn [fst snd] in Hfn, Hna, HlP, Vfn, Vna, Hargs.
split; [exact Hfn|]. split; [exact Hna|]. split; [exact Vfn|]. split; [exact Vna|]. split; [exact Hnc|].
intros j s Hs.
assert (Hj : (j < length P)%nat) by (rewrite HlP; apply nth_error_Some; rewrite Hs; discriminate).
destruct (nth_error P j) as [[p n]|] eqn:Hpn.
2: { exfalso. apply nth_error_None in Hpn. lia. }
destruct (Hargs j s (p, n) Hs Hpn) as (V & Hnz & Hin & Hsz & Hstr). cbn [fst snd] in V, Hnz, Hsz, Hstr.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hin) as (_ & H4096 & Hceil & _).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 _].
pose proof alloc_ceiling_lt as Hcl.
exists p. split; [exact V|]. split; [lia|]. split; [|exact Hstr].
exists p, n. split; [exact Hin|]. lia.
Qed.

(* the caller's struct words (above sp0) and the word array and words (blocks live at the entry) *)
Lemma cwd_words_at : forall e lyc Sc Wc regsc memc mdc pos sp1 k line,
cw_ent B MT e -> cw_core B e lyc Sc Wc regsc memc mdc pos sp1 k ->
cw_line B MT e lyc Sc (rdW Wc memc) line ->
aval_mem (rdW Wc memc) (e_Wd e + 16) 8 (e_arr e) /\
aval_mem (rdW Wc memc) (e_Wd e + 24) 4 (Z.of_nat (length (e_ws e))) /\
in_blockA (ablocks B lyc Sc) (e_arr e) (8 * Z.of_nat (length (e_ws e))) /\
(forall j, (j < length (e_ws e))%nat ->
 aval_mem (rdW Wc memc) (e_arr e + 8 * Z.of_nat j) 8 (nth j (e_wp e) 0) /\
 0 <= nth j (e_wp e) 0 < 2 ^ 64 /\
 in_blockA (ablocks B lyc Sc) (nth j (e_wp e) 0) (Z.of_nat (length (nth j (e_ws e) [])) + 1) /\
 astr_atR (rdW Wc memc) (nth j (e_wp e) 0) (nth j (e_ws e) [])).
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 k line Hent Hc Hl.
pose proof Hent as (_ & _ & _ & _ & _ & _ & Hsp & Hhi & V16 & _ & V24 & _ & _ & Harr & _).
pose proof Hc as Hc1. unfold cw_core in Hc1. cbv zeta in Hc1. destruct Hc1 as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & Hstk & _) & _).
assert (KA : forall a, e_Wd e + 16 <= a < e_Wd e + 32 -> rdW Wc memc a = cw_rd0 e a).
{ intros a Ha. apply (cwd_keep_above e lyc Sc Wc regsc memc mdc pos sp1 k a Hent Hc). unfold cw_sp0. lia. }
destruct Hl as (Hperm & _).
assert (HIN : forall pn, In pn (ablocks B (e_ly e) (e_S e)) -> In pn (ablocks B lyc Sc)).
{ intros pn Hin. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hin. }
split; [apply (cwd_aval_kept (cw_rd0 e)); [intros i Hi; apply KA; lia | exact V16]|].
split; [apply (cwd_aval_kept (cw_rd0 e)); [intros i Hi; apply KA; lia | exact V24]|].
split; [destruct Harr as (p & m & Hin & H1 & H2); exists p, m; split; [exact (HIN _ Hin) | lia]|].
intros j Hj.
destruct (cw_word_at B MT LAWS e lyc Sc Wc memc mdc pos k j Hent HJ HIN Hj) as (_ & _ & _ & Vw & Hb & Hwb & Hstr).
split; [exact Vw|]. split; [exact Hb|]. split; [exact Hwb | exact Hstr].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the three program callees' entries: SIGP (cmd_sig_prog) and cmd_af by computation *)
Lemma cwd_sig_add : SIG CS_check_words_add = BASE + AF_check_words_add.
Proof. rewrite (SIGP CS_check_words_add ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.
Lemma cwd_sig_chain : SIG CS_check_words_chain = BASE + AF_check_words_chain.
Proof. rewrite (SIGP CS_check_words_chain ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.
Lemma cwd_sig_pin : SIG CS_check_words_pin_set = BASE + AF_check_words_pin_set.
Proof. rewrite (SIGP CS_check_words_pin_set ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.

(* the dispatch's branch conditions: fn against a literal *)
Lemma cwd_eq_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v =? z).
Proof.
intros E n v z Hn Hv Hz. rewrite branch_eq_U. rewrite U_SOff. rewrite U_SLit. rewrite Hn.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id z) by (unfold M64; lia). reflexivity.
Qed.

(* the atoms of the seed at D, and the value a register holds after a run *)
Lemma cwd_extra_ew : forall (regs : bvmap 5 word) cp W16 arr fn c rdv nc i, (i < 8)%nat ->
ew (Eimg (Ereg regs (d_extra cp W16 arr fn c rdv nc))) (32 + i) =
nth i (d_extra cp W16 arr fn c rdv nc) (Z_to_bv 64 0).
Proof. intros regs cp W16 arr fn c rdv nc i Hi. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma cwd_denot_off : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* a run of this segment writes nothing: every region of its seed has an empty write window *)
Lemma cwd_kept_run : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hw a Ha.
apply (kept_of_frame E rs H m m' (fun _ => False) Hf); [| exact Ha | tauto].
intros b wlo whi x Hin Hx. exfalso.
unfold windows in Hin. apply in_map_iff in Hin as (r & Hr & Hinr).
rewrite forallb_forall in Hw. pose proof (Hw r Hinr) as Hr0. apply Z.leb_le in Hr0.
injection Hr as Hb Hlo Hhi. subst. lia.
Qed.
Lemma cwd_mem_kept_eq : forall (rd rd' : reader) sp1 F, (forall x, 0 <= x < 2 ^ 64 -> rd' x = rd x) ->
cw_mem_kept B rd rd' sp1 F.
Proof. intros rd rd' sp1 F He x Hx _ _ _. exact (He x Hx). Qed.

(* a range inside a live block is addressable at an AR state *)
Lemma cwd_blk_ra : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) a n -> 0 <= n -> range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR (p & m & Hin & H1 & H2) Hn.
pose proof (req_size_pos m) as Hrq.
apply (range_addressable_of_block SEGS B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia |].
destruct (Z.eq_dec m 0) as [->|Hm0]; [cbn in H2; unfold req_size; cbn; lia|].
unfold req_size. replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm0). lia.
Qed.
(* o = sp1 - sp0 is a multiple of 16 (lia cannot divide: PaDenot.v:23 turns the euclidean flag off) *)
Lemma cwd_o16 : forall sp1 sp0, sp1 mod 32 = 0 -> sp0 mod 16 = 0 -> (sp1 - sp0) mod 16 = 0.
Proof.
intros sp1 sp0 H32 H16. apply Z.mod_divide; [lia|].
apply Z.mod_divide in H32; [|lia]. apply Z.mod_divide in H16; [|lia].
destruct H32 as [k Hk]. destruct H16 as [m Hm]. exists (2 * k - m). lia.
Qed.

(* what the harness fact says about the recorded call c (check_words_c.v's words_prop_at) *)
Lemma cwd_cwok : forall e c fn args, cw_ent B MT e -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) ->
call_words_ok_at atoi_a (cw_read e) (e_ws e) (fn, args).
Proof.
intros e c fn args Hent Hnth.
unfold cw_ent in Hent. cbv zeta in Hent.
destruct Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWP & _).
unfold words_prop_at in HWP. cbv zeta in HWP. rewrite Forall_forall in HWP.
unfold cw_read, cw_n. exact (HWP (fn, args) (nth_error_In _ _ Hnth)).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the loop-head invariant across a program callee (check_words_add / _chain / _pin_set): the callee's journal
   (stack base sp1, footprint [], own []) keeps every byte the invariant reads *)
Lemma cwdc_join_sp_len : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH]; [exact (Z.le_refl 0)|]. destruct ws as [|w2 ws'].
- change (join_sp [w]) with w. unfold PJn.join_need. cbn [fold_right]. lia.
- change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  change (PJn.join_need (w :: w2 :: ws')) with (Z.of_nat (length w) + 1 + PJn.join_need (w2 :: ws')).
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma cwdc_pres_r : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Ltac cwdc_cs_tac := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

Lemma cwd_inv_after : forall e lyc Sc Wc regsc memc mdc pos sp1 line c ly2 S2 W2 regs2 mem2 md2 STK1 EV1,
cw_ent B MT e ->
cw_core B e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED ->
cw_line B MT e lyc Sc (rdW Wc memc) line ->
cw_lscr e (rdW Wc memc) sp1 (frame_addr (e_ly e) 0 pos) line c ->
ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
  ly2 S2 W2 mem2 md2 EV_JOINED ->
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV1 ->
0 <= STK1 ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
ly2 = lyc ->
aregs_preserved regsc regs2 ->
getr regs2 19 = w64 A_G_REC -> getr regs2 20 = w64 c -> getr regs2 24 = w64 0x21120 ->
0 <= c < cw_ncalls e ->
mo_le MT Sc S2 0 ->
INV_LH B MT e ly2 S2 W2 regs2 mem2 md2 pos sp1 line c.
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 line c ly2 S2 W2 regs2 mem2 md2 STK1 EV1
  Hent Hcore Hline Hlscr HJ1 HJ2 HSTK HP2 Hly2 Hpres G19 G20 G24 Hc Hmo2.
unfold INV_LH, cw_core in *. cbv zeta in Hcore |- *.
destruct Hcore as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & G8 & G9 & G23 & Hsv & V16 & V24 & V32 & V152 & VF56 & RF4 & RF5).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (_ & _ & _ & _ & Hshi & H47 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _ & _ & Hastk2 & _ & _).
pose proof Hastk2 as (_ & _ & Hceil2 & Hslo2 & _).
set (F := frame_addr (e_ly e) 0 pos) in *.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr lyc 0 pos = F).
{ subst F. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. }
(* the bytes at or above sp1 (the scratch slots, the saved registers): clause F1 *)
assert (KH : forall a, sp1 <= a < cw_sp0 e -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply F1; [lia | lia | apply inFP_nil]. }
(* the frame's bytes and its shadow bytes: clause F4 *)
assert (KFR : forall a, F <= a < F + 64 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. assert (Hz : in_zr a (frame_rng lyc (0, pos))).
  { unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia. }
  exact (F4 0 pos a Hin (or_introl Hz) (inFP_nil a)). }
assert (KSH : forall a, shadow_addr F <= a < shadow_addr F + 8 -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. assert (Hz : in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)).
  { unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8. lia. }
  exact (F4 0 pos a Hin (or_intror Hz) (inFP_nil a)). }
(* joined's block, live at both states: clause F2 *)
destruct Hline as (Hperm & Hl4096 & Hapart & Hbytes & Hmo).
assert (HinC : In (line, cw_JN e) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (HinN : In (line, cw_JN e) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP2) HinC).
assert (HJN : Z.of_nat (length (join_sp (e_ws e))) + 1 <= req_size (cw_JN e)).
{ pose proof (cwdc_join_sp_len (e_ws e)) as HL.
  pose proof (req_size_pos (cw_JN e) ltac:(unfold cw_JN; lia)) as [_ Hr]. unfold cw_JN in *. lia. }
assert (LB : forall i, 0 <= i < req_size (cw_JN e) -> rdW W2 mem2 (line + i) = rdW Wc memc (line + i)).
{ intros i Hi. exact (F2 line (cw_JN e) i HinC HinN Hi (inFP_nil _)). }
(* the callee-saved registers *)
assert (R2 : getr regs2 2 = getr regsc 2) by exact (cwdc_pres_r regsc regs2 2 Hpres ltac:(cwdc_cs_tac)).
assert (R3 : getr regs2 3 = getr regsc 3) by exact (cwdc_pres_r regsc regs2 3 Hpres ltac:(cwdc_cs_tac)).
assert (R4 : getr regs2 4 = getr regsc 4) by exact (cwdc_pres_r regsc regs2 4 Hpres ltac:(cwdc_cs_tac)).
assert (R8 : getr regs2 8 = getr regsc 8) by exact (cwdc_pres_r regsc regs2 8 Hpres ltac:(cwdc_cs_tac)).
assert (R9 : getr regs2 9 = getr regsc 9) by exact (cwdc_pres_r regsc regs2 9 Hpres ltac:(cwdc_cs_tac)).
assert (R23 : getr regs2 23 = getr regsc 23) by exact (cwdc_pres_r regsc regs2 23 Hpres ltac:(cwdc_cs_tac)).
split.
{ split; [exact HJ1|]. split; [unfold spZ in Hsp |- *; rewrite R2; exact Hsp|].
  split; [exact Hsp32|]. split; [exact Hspr|].
  split; [rewrite R3; exact G3|]. split; [rewrite R4; exact G4|]. split; [rewrite R8; exact G8|].
  split; [rewrite R9; exact G9|]. split; [rewrite R23; exact G23|].
  split.
  { intros j r Hj. specialize (Hsv j r Hj).
    assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length cw_saved); apply nth_error_Some; rewrite Hj; discriminate).
    apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | exact Hsv]. }
  split; [apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | exact V16]|].
  split; [apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | exact V24]|].
  split; [apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | exact V32]|].
  split; [apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | exact V152]|].
  split; [apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KFR; lia | exact VF56]|].
  split.
  - rewrite (KSH (CW_SB + F / 8 + 4)) by (unfold shadow_addr, SHADOW_OFF, CW_SB; lia). exact RF4.
  - rewrite (KSH (CW_SB + F / 8 + 5)) by (unfold shadow_addr, SHADOW_OFF, CW_SB; lia). exact RF5. }
split.
{ split; [exact (Permutation_trans HP2 Hperm)|]. split; [exact Hl4096|]. split; [exact Hapart|]. split.
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (LB (Z.of_nat i)) by lia. exact (Hbytes i ltac:(rewrite length_app; cbn [length]; lia)).
  - pose proof (mle_station MT _ _ _ _ _ MTL Hmo Hmo2) as Hm. rewrite Z.add_0_r in Hm. exact Hm. }
split.
{ unfold cw_lscr in Hlscr |- *.
  destruct Hlscr as (S144 & S8 & S40 & S48 & S56 & S64 & S72 & S88 & S96 & S104 & S128 & S136).
  repeat split; (apply (cwd_aval_kept (rdW Wc memc)); [intros k Hk; apply KH; lia | assumption]). }
split; [exact G19|]. split; [exact G20|]. split; [exact G24 | exact Hc].
Qed.

Lemma cwd_ne_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof.
intros E n v z Hn Hv Hz. rewrite branch_ne_U. rewrite U_SOff. rewrite U_SLit. rewrite Hn.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id z) by (unfold M64; lia). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the calls of check_words_add (jal at 0x87ce0) and check_words_pin_set (jal at 0x87d30): PaNoChain.v's
   cl_callS_na (both callees' pre is afn_pre_na, no frame chain), the callee's statement at its entry, then INV_LH at
   the return (cwd_inv_after) and the latch (cwd_latch) *)
(* a return address in the listing *)
Lemma cwdh_ra : forall k, 0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  YK0s.ret_ok (Z_to_bv 64 (BASE + k)) /\ 4096 <= bv_unsigned (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk Hk2. pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
split; [exact (ret_ok_codeptr_v k Hk Hk2) | rewrite unsigned_lit_small by lia; lia].
Qed.
(* slot j of the word array w->w (j < read) and the word it points at, at a state of the call loop *)
Lemma cwdh_word : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line (j : nat),
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> Z.of_nat j < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 8 * Z.of_nat j) 8 /\
  aval_mem (rdW Wc mem2) (e_arr e + 8 * Z.of_nat j) 8 (nth j (e_wp e) 0) /\ 0 <= nth j (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth j (e_wp e) 0) (Z.of_nat (length (nth j (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth j (e_wp e) 0) (nth j (e_ws e) []).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line j Hent Hc Hl Hj.
destruct (cwd_words_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line Hent Hc Hl) as (_ & _ & Harrb & Hw).
assert (Hjn : (j < length (e_ws e))%nat) by (unfold cw_read, cw_n in Hj; lia).
destruct (Hw j Hjn) as (V & Hb & Hwb & Hst).
split; [|exact (conj V (conj Hb (conj Hwb Hst)))].
destruct Harrb as (p & m & Hin & H1 & H2). exists p, m. split; [exact Hin|]. lia.
Qed.
(* after a callee that keeps the allocator state (ly' = lyc, S' = Sc): the loop-head invariant at the return
   (cwd_inv_after), the call count from the recorder (cwd_rec_at), then the latch (cwd_latch) *)
Lemma cwdh_after : forall (pc : Z) e lyc Sc Wc regs2 mem2 md2 pos sp1 line c STK1 EV1 W3 ly3 S3 regs3 mem3 md3,
  ST_LH B MT (c + 1) -> ST_REL B MT -> (pc = CW_PC_LATCH \/ pc = CW_PC_RADD \/ pc = CW_PC_RCHAIN) ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 20 = w64 c -> getr regs2 24 = w64 0x21120 -> 0 <= c < cw_ncalls e ->
  0 <= STK1 ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    ly3 S3 W3 mem3 md3 EV_JOINED ->
  ajournal SEGS B STK1 sp1 [] lyc Sc Wc mem2 md2 [] ly3 S3 W3 mem3 md3 EV1 ->
  aregs_preserved regs2 regs3 -> ly3 = lyc -> S3 = Sc ->
  cw_at B MT e W3 regs3 (BASE + pc) mem3 md3.
Proof.
intros pc e lyc Sc Wc regs2 mem2 md2 pos sp1 line c STK1 EV1 W3 ly3 S3 regs3 mem3 md3
  HLH HREL Hpc Hent Hc Hl Hs G19 G20 G24 Hcr HSTK HJ3 HJc HP Hly3 HS3.
subst ly3 S3.
assert (G19' : getr regs3 19 = w64 A_G_REC) by (rewrite (cwdc_pres_r regs2 regs3 _ HP) by cwdc_cs_tac; exact G19).
assert (G20' : getr regs3 20 = w64 c) by (rewrite (cwdc_pres_r regs2 regs3 _ HP) by cwdc_cs_tac; exact G20).
assert (G24' : getr regs3 24 = w64 0x21120) by (rewrite (cwdc_pres_r regs2 regs3 _ HP) by cwdc_cs_tac; exact G24).
pose proof (cwd_inv_after e lyc Sc Wc regs2 mem2 md2 pos sp1 line c lyc Sc W3 regs3 mem3 md3 STK1 EV1 Hent Hc Hl Hs
  HJ3 HJc HSTK (Permutation_refl (ablocks B lyc Sc)) eq_refl HP G19' G20' G24' Hcr (mo_le_refl MT MTL Sc)) as HINV.
pose proof HINV as (Hc3 & Hl3 & _).
pose proof (cwd_rec_at e lyc Sc W3 regs3 mem3 md3 pos sp1 EV_JOINED line Hent Hc3 Hl3) as (Q & HQ & _).
destruct HQ as (_ & _ & _ & (_ & _ & VNC & _) & _).
exact (cwd_latch pc e lyc Sc W3 regs3 mem3 md3 pos sp1 line c HLH HREL Hpc Hent HINV VNC).
Qed.

Lemma cwd_call_add : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args, ST_LH B MT (c + 1) -> ST_REL B MT ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  cw_cscr (rdW Wc mem2) sp1 c -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (0, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_RADD) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 20 = w64 c -> getr regs2 24 = w64 0x21120 ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_add)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args HLH HREL Hent Hc Hl Hs _ Hnth Hcr R10 R11 R12 R1 R19 R20 R24.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (HPRE0 & _ & _ & _ & _ & HVO & _ & _ & _ & Harr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev
  & _ & _ & _ & Harr8 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _).
pose proof Hc as Hc0. unfold cw_core in Hc0. cbv zeta in Hc0.
destruct Hc0 as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (cwdl_ncalls_le e Hent) as Hn16.
destruct (cwd_rodata_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent Hc) as [HRO HROK].
destruct (cwd_call_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 0 args Hent Hc Hl Hnth ltac:(lia))
  as (_ & Hla & _ & Vna & _ & Hargs).
destruct (cwd_cwok e c 0 args Hent Hnth) as (_ & Hok0 & _ & _).
destruct (Hok0 eq_refl) as (Hl4 & Hx2 & Hx3). cbn [fst snd] in Hl4, Hx2, Hx3.
assert (N2 : nth_error args 2 = Some (nth 2 args [])) by (apply nth_error_nth'; lia).
assert (N3 : nth_error args 3 = Some (nth 3 args [])) by (apply nth_error_nth'; lia).
destruct (Hargs 2%nat (nth 2 args []) N2) as (q2 & V2 & Hq2 & Hb2 & Hs2).
destruct (Hargs 3%nat (nth 3 args []) N3) as (q3 & V3 & Hq3 & Hb3 & Hs3).
change (8 * Z.of_nat 2) with 16 in V2. change (8 * Z.of_nat 3) with 24 in V3.
assert (Hr : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn4 : Z.of_nat (length args) = 4) by lia.
assert (HA2 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 16) 8 q2 /\ 0 <= q2 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q2 (Z.of_nat (length (nth 2 args [])) + 1) /\ astr_atR (rdW Wc mem2) q2 (nth 2 args []))
  by (intros _; split; [exact V2|]; split; [lia|]; split; [exact Hb2 | exact Hs2]).
assert (HA3 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q3 (Z.of_nat (length (nth 3 args [])) + 1) /\ astr_atR (rdW Wc mem2) q3 (nth 3 args []))
  by (intros _; split; [exact V3|]; split; [lia|]; split; [exact Hb3 | exact Hs3]).
assert (HW3 : 3 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 24) 8 /\ aval_mem (rdW Wc mem2) (e_arr e + 24) 8 (nth 3 (e_wp e) 0) /\
  0 <= nth 3 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 3 (e_wp e) 0) (Z.of_nat (length (nth 3 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 3 (e_wp e) 0) (nth 3 (e_ws e) [])).
{ intros H3. pose proof (cwdh_word e lyc Sc Wc regs2 mem2 md2 pos sp1 line 3%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 3) with 24 in X. exact X. }
assert (HW4 : 4 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 32) 8 /\ aval_mem (rdW Wc mem2) (e_arr e + 32) 8 (nth 4 (e_wp e) 0) /\
  0 <= nth 4 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 4 (e_wp e) 0) (Z.of_nat (length (nth 4 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 4 (e_wp e) 0) (nth 4 (e_ws e) [])).
{ intros H4. pose proof (cwdh_word e lyc Sc Wc regs2 mem2 md2 pos sp1 line 4%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 4) with 32 in X. exact X. }
assert (Hev1 : st_nev Sc + EV_CHECK_WORDS_ADD <= EV_MAX) by (unfold EV_CHECK_WORDS_ADD; unfold EV_CHECK_WORDS in Hev; lia).
assert (HSTKa : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
destruct (cwdh_ra CW_PC_RADD ltac:(unfold CW_PC_RADD; lia) eq_refl) as [Hraw Hra4].
rewrite <- R1 in Hraw, Hra4.
eapply SRr_bind.
{ exact (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.PaNoChain.cl_callS_na B LAWS Wc regs2 mem2
    (Z_to_bv 64 (BASE + AF_check_words_add)) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(0, pos)] lyc Sc md2 EV_JOINED CHECK_WORDS_ADD_STK [] EV_CHECK_WORDS_ADD (sp1 - cw_sp0 e) (getr regs2 1)
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc)
    HJ ltac:(lia) (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal0) ltac:(lia) ltac:(lia) ltac:(lia)
    (eq_trans G3 Hgp0) (eq_trans G4 Htp0) eq_refl Hraw Hra4
    (fun HPRE1 => HADD lyc Sc Wc regs2 mem2 md2 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
       (Z.of_nat (length args)) (nth 3 (e_wp e) 0) (nth 4 (e_wp e) 0) q2 q3 (nth 3 (e_ws e) []) (nth 4 (e_ws e) [])
       (nth 2 args []) (nth 3 args []) HPRE1 HRO R10 R11 R12 Hr Harr HROK HVO Hcp1 Hcp2 Hcp8 Vna Hna HA2 HA3 HW3 HW4
       Harr8 Hn4 Hx2 Hx3 Hev1)
    (fun a Ha => False_ind _ (inFP_nil a Ha))). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP & (_ & Hly3 & HS3)).
change (EV_JOINED + EV_CHECK_WORDS_ADD) with EV_JOINED in HJ3.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJc by lia.
rewrite R1.
exact (cwdh_after CW_PC_RADD e lyc Sc Wc regs2 mem2 md2 pos sp1 line c CHECK_WORDS_ADD_STK EV_CHECK_WORDS_ADD
  W3 ly3 S3 regs3 mem3 md3 HLH HREL (or_intror (or_introl eq_refl)) Hent Hc Hl Hs R19 R20 R24 Hcr ltac:(lia)
  HJ3 HJc HP Hly3 HS3).
Qed.

Lemma cwd_call_pin : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args, ST_LH B MT (c + 1) -> ST_REL B MT ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  cw_cscr (rdW Wc mem2) sp1 c -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (20, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_LATCH) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 20 = w64 c -> getr regs2 24 = w64 0x21120 ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_pin_set)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args HLH HREL Hent Hc Hl Hs _ Hnth Hcr R10 R11 R12 R1 R19 R20 R24.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (HPRE0 & _ & _ & _ & _ & HVO & _ & _ & _ & Harr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev
  & _ & _ & _ & Harr8 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _).
pose proof Hc as Hc0. unfold cw_core in Hc0. cbv zeta in Hc0.
destruct Hc0 as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof (cwdl_ncalls_le e Hent) as Hn16.
destruct (cwd_rodata_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent Hc) as [HRO HROK].
destruct (cwd_call_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 20 args Hent Hc Hl Hnth ltac:(lia))
  as (_ & Hla & _ & Vna & _ & Hargs).
destruct (cwd_cwok e c 20 args Hent Hnth) as (_ & _ & _ & Hok20).
destruct (Hok20 eq_refl) as (Hl4 & Hx3). cbn [fst snd] in Hl4, Hx3.
assert (N3 : nth_error args 3 = Some (nth 3 args [])) by (apply nth_error_nth'; lia).
destruct (Hargs 3%nat (nth 3 args []) N3) as (q3 & V3 & Hq3 & Hb3 & Hs3).
change (8 * Z.of_nat 3) with 24 in V3.
assert (Hr : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn4 : Z.of_nat (length args) = 4) by lia.
assert (HA3 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q3 (Z.of_nat (length (nth 3 args [])) + 1) /\ astr_atR (rdW Wc mem2) q3 (nth 3 args []))
  by (intros _; split; [exact V3|]; split; [lia|]; split; [exact Hb3 | exact Hs3]).
assert (HW4 : 4 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 32) 8 /\ range_addressable (rdW Wc mem2) SHADOW_OFF (e_arr e + 32) 8 /\
  aval_mem (rdW Wc mem2) (e_arr e + 32) 8 (nth 4 (e_wp e) 0) /\ 0 <= nth 4 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 4 (e_wp e) 0) (Z.of_nat (length (nth 4 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 4 (e_wp e) 0) (nth 4 (e_ws e) [])).
{ intros H4. pose proof (cwdh_word e lyc Sc Wc regs2 mem2 md2 pos sp1 line 4%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 4) with 32 in X. destruct X as (Xb & X).
  split; [exact Xb|]. split; [exact (cwd_blk_ra lyc Sc Wc mem2 md2 (e_arr e + 32) 8 HAR Xb ltac:(lia)) | exact X]. }
assert (Hev1 : st_nev Sc + EV_CWPS <= EV_MAX) by (unfold EV_CWPS; unfold EV_CHECK_WORDS in Hev; lia).
assert (HSTKp : CWPS_STK = 8224) by reflexivity.
assert (HSTK : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
destruct (cwdh_ra CW_PC_LATCH ltac:(unfold CW_PC_LATCH; lia) eq_refl) as [Hraw Hra4].
rewrite <- R1 in Hraw, Hra4.
eapply SRr_bind.
{ exact (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.PaNoChain.cl_callS_na B LAWS Wc regs2 mem2
    (Z_to_bv 64 (BASE + AF_check_words_pin_set)) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(0, pos)] lyc Sc md2 EV_JOINED CWPS_STK [] EV_CWPS (sp1 - cw_sp0 e) (getr regs2 1)
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       ly' = lyc /\ S' = Sc)
    HJ ltac:(lia) (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal0) ltac:(lia) ltac:(lia) ltac:(lia)
    (eq_trans G3 Hgp0) (eq_trans G4 Htp0) eq_refl Hraw Hra4
    (fun HPRE1 => HPIN lyc Sc Wc regs2 mem2 md2 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
       (Z.of_nat (length args)) (nth 4 (e_wp e) 0) q3 (nth 4 (e_ws e) []) (nth 3 args [])
       HPRE1 HRO HROK HVO R10 R11 R12 Hr Hcp1 Hcp2 Hcp8 Vna Hna HA3 HW4 Harr8 Hn4 Hx3 Hev1)
    (fun a Ha => False_ind _ (inFP_nil a Ha))). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP & (Hly3 & HS3)).
change (EV_JOINED + EV_CWPS) with EV_JOINED in HJ3.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJc by lia.
rewrite R1.
exact (cwdh_after CW_PC_LATCH e lyc Sc Wc regs2 mem2 md2 pos sp1 line c CWPS_STK EV_CWPS
  W3 ly3 S3 regs3 mem3 md3 HLH HREL (or_introl eq_refl) Hent Hc Hl Hs R19 R20 R24 Hcr ltac:(lia)
  HJ3 HJc HP Hly3 HS3).
Qed.
(* ---------------------------------------------------------------------------------------------------------- *)
(* the call loop's latch at every FP state: cwd_latch, a lemma of this closed Section, at the FP state fx1 the call
   of check_words_chain returns (statement pass 4; seg_D below supplies it) *)
Definition CWD_GL : Prop := forall (fx1 : YK11.FPState) (pc : Z) e lyc Sc Wc regsc memc mdc pos sp1 line c,
  ST_LH (fx := fx1) B MT (c + 1) -> ST_REL (fx := fx1) B MT ->
  (pc = CW_PC_LATCH \/ pc = CW_PC_RADD \/ pc = CW_PC_RCHAIN) ->
  cw_ent (fx := fx1) B MT e -> INV_LH B MT e lyc Sc Wc regsc memc mdc pos sp1 line c ->
  aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e) ->
  cw_at (fx := fx1) B MT e Wc regsc (BASE + pc) memc mdc.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the call of check_words_chain (fn = 17) at 0x87d04, through PaCall.v's cl_callS (the callee's footprint is []) and
   its statement HCHAIN, back at 0x87d08 to the call loop's latch (cwd_latch) *)
Lemma cwdg_rdword : forall H (m : word -> option byte) a v,
  aval_mem (aview SEGS H m) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) a = Some v.
Proof. intros H m a v Hv Hr. exact (rdword_of_val_mem SEGS H m a v (cwd_val_of_aval H m a 8 v Hv) Hr). Qed.
Lemma cwdg_bv64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
(* lia here has no Z.modulo / Z.div support: alignment goes through explicit multiples *)
Lemma cwdg_mod_of : forall x m, 0 < m -> (exists q, x = m * q) -> x mod m = 0.
Proof. intros x m Hm (q & ->). rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.
Lemma cwdg_div_of : forall x m, 0 < m -> x mod m = 0 -> exists q, x = m * q.
Proof. intros x m Hm H. exists (x / m). pose proof (Z.div_mod x m ltac:(lia)) as E. rewrite H, Z.add_0_r in E. exact E. Qed.

Lemma cwd_call_chain : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args, CWD_GL ->
  (forall fx0 : YK11.FPState, ST_LH (fx := fx0) B MT (c + 1)) -> (forall fx0 : YK11.FPState, ST_REL (fx := fx0) B MT) ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  cw_cscr (rdW Wc mem2) sp1 c -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (17, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_RCHAIN) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 20 = w64 c -> getr regs2 24 = w64 0x21120 ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_chain)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args GL HLH HREL Hent HC HL HLS HCS Hnth Hc H10 H11 H12 H1 H19 H20 H24.
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & HSTKP & HROD & _ & _ & HOBJ & Hspw & Hhi & Harr & Harr64 & Hn & Hlen & Hn31 & Hblk & Hwords
  & HJN & _ & _ & _ & HC4 & Hev & Hlive & MOK & HWd8 & Harr8 & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htophi).
pose proof HC as HC'. unfold cw_core in HC'. cbv zeta in HC'.
destruct HC' as (HJ & Hsp & Hsp32 & Hsprng & H3 & H4 & H8 & H9 & H23 & Hsaves & _).
assert (Esp0 : cw_sp0 e = spZ (e_regs e)) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (WC : CHECK_WORDS_CHAIN_STK = 12496) by (vm_compute; reflexivity).
assert (EVJ : EV_JOINED = 1) by reflexivity.
assert (EVC : EV_CHECK_WORDS = 2) by reflexivity.
assert (EVCC : EV_CHECK_WORDS_CHAIN = 0) by reflexivity.
destruct (cwdg_div_of _ 16 ltac:(lia) Hal16) as (q0 & Hq0).
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & Hnev1 & _).
destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (cwdl_ncalls_le e Hent) as Hn16.
(* check_words_chain's premises at the call state *)
destruct (cwd_rodata_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent HC) as [P3 P9].
destruct (cwd_call_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 17 args Hent HC HL Hnth ltac:(lia))
  as (_ & Hna6 & _ & Vna & _ & Hargs).
destruct (cwd_cwok e c 17 args Hent Hnth) as (_ & _ & H17 & _).
destruct (H17 eq_refl) as (Hl3 & Hx1 & Hx2). cbn [snd] in Hl3, Hx1, Hx2.
assert (Hl1 : (1 < length args)%nat) by lia. assert (Hl2 : (2 < length args)%nat) by lia.
destruct (Hargs 1%nat (nth 1 args []) (nth_error_nth' args [] Hl1)) as (p1 & Vp1 & Rp1 & Bp1 & Sp1).
destruct (Hargs 2%nat (nth 2 args []) (nth_error_nth' args [] Hl2)) as (p2 & Vp2 & Rp2 & Bp2 & Sp2).
destruct (cwd_words_at e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line Hent HC HL) as (_ & _ & Harr' & Hw').
assert (PW : forall k, 2 <= k < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 8 * k) 8 /\
  aval_mem (rdW Wc mem2) (e_arr e + 8 * k) 8 (nth (Z.to_nat k) (e_wp e) 0) /\
  0 <= nth (Z.to_nat k) (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth (Z.to_nat k) (e_wp e) 0) (Z.of_nat (length (nth (Z.to_nat k) (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth (Z.to_nat k) (e_wp e) 0) (nth (Z.to_nat k) (e_ws e) [])).
{ intros k Hk. unfold cw_read, cw_n in Hk.
  assert (Hkn : (Z.to_nat k < length (e_ws e))%nat) by lia.
  destruct (Hw' (Z.to_nat k) Hkn) as (W1 & W2 & W3 & W4). rewrite Z2Nat.id in W1 by lia.
  split; [|split; [exact W1 | split; [exact W2 | split; [exact W3 | exact W4]]]].
  destruct Harr' as (p & m & Hin & Hp1 & Hp2). exists p, m. split; [exact Hin | lia]. }
assert (Hr64 : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn3 : Z.of_nat (length args) = 3) by (rewrite Hl3; reflexivity).
assert (Hp1f : Z.of_nat (length args) = 3 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 8) 8 p1 /\ 0 <= p1 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) p1 (Z.of_nat (length (nth 1 args [])) + 1) /\ astr_atR (rdW Wc mem2) p1 (nth 1 args []))
  by (intros _; split; [exact Vp1 | split; [lia | split; [exact Bp1 | exact Sp1]]]).
assert (Hp2f : Z.of_nat (length args) = 3 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 16) 8 p2 /\ 0 <= p2 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) p2 (Z.of_nat (length (nth 2 args [])) + 1) /\ astr_atR (rdW Wc mem2) p2 (nth 2 args []))
  by (intros _; split; [exact Vp2 | split; [lia | split; [exact Bp2 | exact Sp2]]]).
assert (HC4' : count_cid 4 (frames Sc) < fs_frames 4) by (rewrite Hfrs1; exact HC4).
assert (HEV : st_nev Sc + EV_CHECK_WORDS_CHAIN <= EV_MAX) by lia.
(* s0 = sp0 at the call: the frame chain pushes check_words' own record (ra at sp0 - 8, s0 at sp0 - 16) *)
assert (Hs0 : s0Z regs2 = cw_sp0 e) by (unfold s0Z; rewrite H8; reflexivity).
assert (HCH : exists ch1, achain lyc (rdW Wc mem2) (cw_sp0 e + (sp1 - cw_sp0 e)) (s0Z regs2) ch1).
{ rewrite Hs0. replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 by lia.
  destruct (Z_lt_le_dec (cw_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
  - exists ((cw_sp0 e, bv_unsigned (getr (e_regs e) (Z_to_bv 5 1)), s0Z (e_regs e)) :: e_ch e).
    apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
    apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc mem2) (cw_sp0 e) (s0Z (e_regs e))
      (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1))) (e_ch e) sp1 Hch0).
    + lia.
    + intros a Ha. exact (cwd_keep_above e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED a Hent HC Ha).
    + pose proof (Hsaves 0%nat 1 eq_refl) as HS0.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 0) with (cw_sp0 e - 8) in HS0 by lia.
      exact (cwdg_rdword _ _ _ _ HS0 (cwdg_bv64 _)).
    + pose proof (Hsaves 1%nat 8 eq_refl) as HS1.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 1) with (cw_sp0 e - 16) in HS1 by lia.
      exact (cwdg_rdword _ _ _ _ HS1 (cwdg_bv64 (getr (e_regs e) (Z_to_bv 5 8)))).
    + exact Hra4.
    + lia.
    + apply (cwdg_mod_of _ 8 ltac:(lia)). exists (2 * q0). lia.
    + exact Hlt.
    + lia.
  - exists []. unfold achain. left. split; [right; left; rewrite Etop; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hch1).
pose proof (fun HPRE1 : afn_pre SEGS B CHECK_WORDS_CHAIN_STK lyc Sc Wc regs2 mem2 md2 ch1 =>
  HCHAIN lyc Sc Wc regs2 mem2 md2 ch1 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
    (Z.of_nat (length args)) p1 p2 (e_wp e) (e_ws e) (nth 1 args []) (nth 2 args [])
    HPRE1 HSTKP P3 H10 H11 H12 Hr64 Harr64 P9 HOBJ Hcp1 Hcp2 Hcp8 Vna Hna Hp1f Hp2f PW Harr8 Hn3 Hx1 Hx2 HC4' HEV)
  as HCALL.
unfold apost_baseF, cfg_at in HCALL.
(* the call rule's premises *)
assert (Hspo : spZ regs2 = cw_sp0 e + (sp1 - cw_sp0 e)) by lia.
assert (Halo : (sp1 - cw_sp0 e) mod 16 = 0) by exact (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal16).
assert (Hnego : sp1 - cw_sp0 e <= 0) by lia.
assert (Hstk1 : 0 <= CHECK_WORDS_CHAIN_STK) by lia.
assert (Hbud : CHECK_WORDS_CHAIN_STK - (sp1 - cw_sp0 e) <= CHECK_WORDS_STK) by lia.
assert (Hgp' : getr regs2 3 = w64 (as_gp B)) by (rewrite H3; exact Hgp).
assert (Htp' : getr regs2 4 = w64 (as_tp B)) by (rewrite H4; exact Htp).
assert (Hraw : YK0s.ret_ok (getr regs2 1))
  by (rewrite H1; exact (ret_ok_codeptr_v CW_PC_RCHAIN ltac:(unfold CW_PC_RCHAIN; lia) eq_refl)).
assert (Hra4' : 4096 <= bv_unsigned (getr regs2 1)).
{ rewrite H1. rewrite unsigned_lit_small by (unfold CW_PC_RCHAIN; lia). unfold CW_PC_RCHAIN. lia. }
unfold cw_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ exact (cl_callS_wideF (fx := fx) B LAWS Wc regs2 mem2 _ CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [(0, pos)] lyc Sc md2 EV_JOINED CHECK_WORDS_CHAIN_STK [] EV_CHECK_WORDS_CHAIN (sp1 - cw_sp0 e)
    (getr regs2 1) ch1 _ HJ Hspo Halo Hnego Hstk1 Hbud Hgp' Htp' eq_refl Hraw Hra4' Hch1 HCALL
    (fun a Hf => False_ind _ (inFP_nil a Hf)) (fun _ _ _ _ _ _ _ a Hf _ _ => False_ind _ (inFP_nil a Hf))). }
(* back at 0x87d08 at the FP state fx1 the call returned: the loop head's invariant (cwd_inv_after), then the latch at
   fx1 (CWD_GL), whose apost_baseF at fx1 srr_after_callF lifts to fx *)
intros fx1 ly2 S2 W2 regs3 mem3 md3 Hle Hfx (HJ2 & HJ1 & HP & HK).
destruct HK as (HPerm2 & Hly2 & f & HS2).
rewrite EVCC, Z.add_0_r in HJ2.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJ1 by lia.
assert (G19 : getr regs3 19 = w64 A_G_REC) by (rewrite (cwdc_pres_r regs2 regs3 19 HP ltac:(cwdc_cs_tac)); exact H19).
assert (G20 : getr regs3 20 = w64 c) by (rewrite (cwdc_pres_r regs2 regs3 20 HP ltac:(cwdc_cs_tac)); exact H20).
assert (G24 : getr regs3 24 = w64 0x21120) by (rewrite (cwdc_pres_r regs2 regs3 24 HP ltac:(cwdc_cs_tac)); exact H24).
assert (Hmo2 : mo_le MT Sc S2 0) by (rewrite HS2; exact (mo_le_set_fs_r MT MTFL _ _ _ _ (mo_le_refl MT MTL Sc))).
pose proof (cwd_inv_after e lyc Sc Wc regs2 mem2 md2 pos sp1 line c ly2 S2 W2 regs3 mem3 md3
  CHECK_WORDS_CHAIN_STK EV_CHECK_WORDS_CHAIN Hent HC HL HLS HJ2 HJ1 Hstk1 HPerm2 Hly2 HP G19 G20 G24 Hc Hmo2) as INV.
pose proof INV as (HC2 & HL2 & _).
destruct (cwd_call_at e ly2 S2 W2 regs3 mem3 md3 pos sp1 EV_JOINED line c 17 args Hent HC2 HL2 Hnth ltac:(lia))
  as (_ & _ & _ & _ & VNC & _).
pose proof (cw_ent_fx fx fx1 B MT e Hent (fxrel_frm0 fx fx1 HSTKP Hfx)) as Hent1.
rewrite H1.
exact (GL fx1 CW_PC_RCHAIN e ly2 S2 W2 regs3 mem3 md3 pos sp1 line c (HLH fx1) (HREL fx1)
  (or_intror (or_intror eq_refl)) Hent1 INV VNC).
Qed.

(* a register of the symbolic state, without prreg's normalisation *)
Ltac cwd_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* ---------------------------------------------------------------------------------------------------------- *)
Lemma seg_D_core : forall c, CWD_GL ->
  (forall fx0 : YK11.FPState, ST_LH (fx := fx0) B MT (c + 1)) -> (forall fx0 : YK11.FPState, ST_REL (fx := fx0) B MT) ->
  ST_D B MT c.
Proof.
intros c GL HLHg HRELg. pose proof (HLHg fx) as HLH. pose proof (HRELg fx) as HREL. unfold ST_D. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
destruct HI as (HC & HLN & HLS & HCS & H24 & Hcr).
pose proof HC as (HJ & Hsp1 & Hsp32 & Hsp1lo & Hgp3 & Hgp4 & Hr8 & Hr9 & Hr23 & HSAV
  & V16 & V24 & V32 & V152 & VF56 & VSH4 & VSH5).
pose proof HJ as (HARc & HLY & Hsecs & Hwle & Hios & HFRc & Hnev & Hk0 & FM1 & FM2 & FM3 & FM4 & FM5
  & HPRESc & HSTKOK & HEXTRA & HQTc).
destruct HSTKOK as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & HSTKP & HROD & H10e & HRO & HOBJ & Hspw & Hhiw & Harr & Harr64 & Hn4 & Hlenwp
  & Hn31 & Hblk & Hwords & HJN & HREC & HWP & Hcid0 & Hcid4 & Hev & Hlive & MOK).
assert (Hnthx : exists fn args, nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args)).
{ destruct (nth_error (r_calls (e_R e)) (Z.to_nat c)) as [[fn args]|] eqn:E1; [exists fn, args; reflexivity|].
  exfalso. apply nth_error_None in E1. unfold cw_ncalls in Hcr. lia. }
destruct Hnthx as (fn & args & Hnth).
destruct (cwd_call_at e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED line c fn args Hent HC HLN Hnth
  ltac:(lia)) as (Hfn0 & Hargs6 & VFN & VNA & VNC & HARGS).
destruct (cwd_words_at e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED line Hent HC HLN)
  as (VW16 & VW24 & HARRB & HWORD).
assert (Hnc : 0 <= cw_ncalls e <= 16).
{ destruct HREC as (Q & (_ & _ & _ & (Hl & _) & _) & _). unfold cw_ncalls.
  split; [apply Zle_0_nat | lia]. }
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47) by (unfold cw_sp0 in *; lia).
assert (HW16b : 2 ^ 46 <= e_Wd e + 16 <= 2 ^ 47 - 16) by (unfold cw_sp0 in *; lia).
assert (HW16s : sp1 + 160 <= e_Wd e + 16) by (unfold cw_sp0 in *; lia).
assert (Hfnb : 0 <= fn <= 25) by (unfold REC_FN_COUNT in Hfn0; lia).
assert (Hrdvb : 0 <= cw_read e <= 64).
{ unfold cw_read, cw_n. split; [apply Z.min_glb; [apply Zle_0_nat | lia] | apply Z.le_min_r]. }
assert (Hcb : 0 <= c <= 15) by lia.
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HARc ltac:(left; reflexivity)) as (RAG & _).
assert (RA1 : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 16 + 56 * c) 8).
{ apply (range_addressable_sub (rdW Wc memc) SHADOW_OFF A_G_REC 960); [exact RAG | lia | lia]. }
assert (RA3 : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 8) 8).
{ apply (range_addressable_sub (rdW Wc memc) SHADOW_OFF A_G_REC 960); [exact RAG | lia | lia]. }
destruct HLY as (LY1 & LY2 & LY3 & LY4 & LY5 & LYF & LY7 & LY8 & LYtop & LYlo & LYhi & LYrest).
assert (RA2 : range_addressable (rdW Wc memc) SHADOW_OFF (e_Wd e + 16) 8).
{ apply (cwd_stk_addressable lyc Sc Wc memc mdc (e_Wd e + 16) 8 HARc);
  [rewrite LYlo | rewrite LYhi | ]; unfold cw_sp0 in *; lia. }
assert (VNCo : aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e)) by exact VNC.
replace (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_FN) with (A_G_REC + 16 + 56 * c) in VFN
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia).
replace (A_G_REC + OFF_NCALLS) with (A_G_REC + 8) in VNC by (unfold OFF_NCALLS; lia).
pose proof HLS as (L144 & L8 & L40 & L48 & L56 & L64 & L72 & L88 & L96 & L104 & L128 & L136).
pose proof HCS as (C80 & C112 & C120).
destruct (cwd_seedD Wc regsc memc sp1 c (e_Wd e + 16) (e_arr e) fn (cw_read e) (cw_ncalls e)
  Hr9 Hsp1b Hsp32 Hr23 Hcb HW16b HW16s Harr64 Hfnb Hrdvb Hnc
  L64 L72 C80 L88 L96 C112 C120 L128 L136 V152 VNC VFN VW16 RA1 RA2 RA3) as (HS & SHOK).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e))))) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))
  (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16) (e_arr e) fn c (cw_read e) (cw_ncalls e)))))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 32 = Z_to_bv 64 A_G_REC).
{ change 32%nat with (32 + 0)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
assert (E33 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 33 = Z_to_bv 64 (A_G_REC + 16 + 56 * c)).
{ change 33%nat with (32 + 1)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
assert (E35 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 35 = Z_to_bv 64 (e_arr e)).
{ change 35%nat with (32 + 3)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
assert (E36 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 36 = Z_to_bv 64 fn).
{ change 36%nat with (32 + 4)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
assert (E37 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 37 = Z_to_bv 64 c).
{ change 37%nat with (32 + 5)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
assert (E38 : ew (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16)
  (e_arr e) fn c (cw_read e) (cw_ncalls e)))) 38 = Z_to_bv 64 (cw_read e)).
{ change 38%nat with (32 + 6)%nat. rewrite cwd_extra_ew by lia. cbn [nth d_extra]. reflexivity. }
unfold cw_at.
paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pose proof (cwd_kept_run _ (ss_mem ssD) (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as K1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* fn = 20: check_words_pin_set at 0x87d30, back at the latch *)
  rewrite (cwd_eq_atom _ 36%nat fn 20 E36 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => set (mA := m) in * end.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mA) x = rdW Wc memc x)
    by (intros x Hx; rewrite (KK x Hx); exact (K1 x Hx)).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 23; 24]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (HCRK : cw_cregs_kept regsc (ms_regs mA)).
  { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
    split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
    split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 23%bv ltac:(cbn; tauto))]. }
  destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mA) (ms_mem mA) mdv2
    pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
    (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
  cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
  cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (20%bv : bv 5) R20.
  change (SOff 240 6224) with (SOff A_TEXT 6224) in Rra. rewrite (codeptr_val _ 6224 HEI) in Rra.
  rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
  rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
  rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
  rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
  rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R20.
  replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
    by (unfold OFF_CALLS, CALL_SIZE; lia).
  assert (R24' : getr (ms_regs mA) 24 = w64 0x21120) by (rewrite <- H24; exact (RK 24%bv ltac:(cbn; tauto))).
  pmkst HS. rewrite cwd_sig_pin.
  rewrite Hc in Hnth.
  replace (BASE + 6224) with (BASE + CW_PC_LATCH) in Rra by (unfold CW_PC_LATCH; lia).
  exact (cwd_call_pin e lyc Sc Wc (ms_regs mA) (ms_mem mA) mdv2 pos sp1 line c args HLH HREL Hent
    HC2 HLN2 HLS2 HCS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R20 R24').
- (* fn <> 20 *)
  rewrite (cwd_eq_atom _ 36%nat fn 20 E36 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K2.
  assert (K12 : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms0) x = rdW Wc memc x)
    by (intros x Hx; rewrite (K2 x Hx); exact (K1 x Hx)).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* fn = 17: check_words_chain at 0x87d04 *)
    rewrite (cwd_eq_atom _ 36%nat fn 17 E36 ltac:(lia) ltac:(lia)) in Hc0. apply Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
    set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => set (mB := m) in * end.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mB) x = rdW Wc memc x)
    by (intros x Hx; rewrite (KK x Hx); exact (K12 x Hx)).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 23; 24]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (HCRK : cw_cregs_kept regsc (ms_regs mB)).
  { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
    split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
    split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 23%bv ltac:(cbn; tauto))]. }
  destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mB) (ms_mem mB) mdv3
    pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
    (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
  cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
  cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (20%bv : bv 5) R20.
  change (SOff 240 6180) with (SOff A_TEXT 6180) in Rra. rewrite (codeptr_val _ 6180 HEI) in Rra.
  rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
  rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
  rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
  rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
  rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R20.
  replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
    by (unfold OFF_CALLS, CALL_SIZE; lia).
  assert (R24' : getr (ms_regs mB) 24 = w64 0x21120) by (rewrite <- H24; exact (RK 24%bv ltac:(cbn; tauto))).
  pmkst HS. rewrite cwd_sig_chain.
    rewrite Hc0 in Hnth.
    replace (BASE + 6180) with (BASE + CW_PC_RCHAIN) in Rra by (unfold CW_PC_RCHAIN; lia).
    exact (cwd_call_chain e lyc Sc Wc (ms_regs mB) (ms_mem mB) mdv3 pos sp1 line c args GL HLHg HRELg Hent
      HC2 HLN2 HLS2 HCS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R20 R24').
  + (* fn <> 17 *)
    rewrite (cwd_eq_atom _ 36%nat fn 17 E36 ltac:(lia) ltac:(lia)) in Hc0. apply Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
    set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
    pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K3.
    assert (K13 : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms1) x = rdW Wc memc x)
      by (intros x Hx; rewrite (K3 x Hx); exact (K12 x Hx)).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* fn <> 0: no call of this call's fn, straight to the latch *)
      paj_run_to_tok RUNTO HS HJ SHOK DBspan CW_PC_LATCH; [awr_ok_tac | ].
      set (mdv4 := with_vm_backing _ _ _) in *; clearbody mdv4.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => set (mD := m) in * end.
      pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K4.
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mD) x = rdW Wc memc x)
        by (intros x Hx; rewrite (K4 x Hx); exact (K13 x Hx)).
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _ [2; 3; 4; 8; 9; 23; 24]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as RK.
      assert (HCRK : cw_cregs_kept regsc (ms_regs mD)).
      { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
        split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
        split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 23%bv ltac:(cbn; tauto))]. }
      destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mD) (ms_mem mD) mdv4
        pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
        (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
      cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (20%bv : bv 5) R20.
      rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
      rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R20.
      assert (R24' : getr (ms_regs mD) 24 = w64 0x21120) by (rewrite <- H24; exact (RK 24%bv ltac:(cbn; tauto))).
      assert (HNC2 : aval_mem (rdW Wc (ms_mem mD)) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e)).
      { apply (cw_aval_kept (rdW Wc memc)); [|exact VNCo].
        intros k Hk. apply KEEP. unfold A_G_REC, OFF_NCALLS. lia. }
      pmkst HS.
      exact (cwd_latch CW_PC_LATCH e lyc Sc Wc (ms_regs mD) (ms_mem mD) mdv4 pos sp1 line c HLH HREL
        (or_introl eq_refl) Hent
        (conj HC2 (conj HLN2 (conj HLS2 (conj R19 (conj R20 (conj R24' Hcr)))))) HNC2).
    * (* fn = 0: check_words_add at 0x87ce0 *)
      rewrite (cwd_ne_atom _ 36%nat fn 0 E36 ltac:(lia) ltac:(lia)) in Hc1.
      apply Bool.negb_false_iff in Hc1. apply Z.eqb_eq in Hc1.
      paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
      set (mdv4 := with_vm_backing _ _ _) in *; clearbody mdv4.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => set (mC := m) in * end.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mC) x = rdW Wc memc x)
    by (intros x Hx; rewrite (KK x Hx); exact (K13 x Hx)).
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 23; 24]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (HCRK : cw_cregs_kept regsc (ms_regs mC)).
  { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
    split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
    split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 23%bv ltac:(cbn; tauto))]. }
  destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mC) (ms_mem mC) mdv4
    pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
    (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
  cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
  cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (20%bv : bv 5) R20.
  change (SOff 240 6144) with (SOff A_TEXT 6144) in Rra. rewrite (codeptr_val _ 6144 HEI) in Rra.
  rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
  rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
  rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
  rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
  rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R20.
  replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
    by (unfold OFF_CALLS, CALL_SIZE; lia).
  assert (R24' : getr (ms_regs mC) 24 = w64 0x21120) by (rewrite <- H24; exact (RK 24%bv ltac:(cbn; tauto))).
  pmkst HS. rewrite cwd_sig_add.
      rewrite Hc1 in Hnth.
      replace (BASE + 6144) with (BASE + CW_PC_RADD) in Rra by (unfold CW_PC_RADD; lia).
      exact (cwd_call_add e lyc Sc Wc (ms_regs mC) (ms_mem mC) mdv4 pos sp1 line c args HLH HREL Hent
        HC2 HLN2 HLS2 HCS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R20 R24').
Qed.
End e.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------- *)
(* seg_D at the shape of check_words_d.v (statement pass 4): the generic latch CWD_GL is cwd_latch of the Section
   above, closed, at every FP state *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* CmdRecFacts' cmd_ro_ok_of_aro (2026-10-29): the image's read-only bytes at any AR state
   whose reader satisfies arodata_okP. cmd_ro_bytes holds the RELRO GOT words, which are runtime-owned, so neither
   the journal's image clause nor arodata_okP alone carries cmd_ro_ok from the entry to a call state. *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).

Lemma seg_D : forall c, (forall fx0 : YK11.FPState, ST_LH (fx := fx0) B MT (c + 1)) ->
  (forall fx0 : YK11.FPState, ST_REL (fx := fx0) B MT) -> ST_D B MT c.
Proof.
intros c HLH HREL.
assert (GL : CWD_GL B MT).
{ intros fx1 pc e lyc Sc Wc regsc memc mdc pos sp1 line c0 G1 G2 G3 G4 G5 G6.
  apply (cwd_latch (fx := fx1) B MT) with (lyc := lyc) (Sc := Sc) (pos := pos) (sp1 := sp1) (line := line) (c := c0);
    assumption. }
apply (seg_D_core (fx := fx) B MT); assumption.
Qed.
End e.
End f.
End d.
