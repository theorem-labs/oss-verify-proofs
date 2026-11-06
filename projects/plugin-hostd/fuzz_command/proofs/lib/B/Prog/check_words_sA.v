(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: written after lib/A/Prog/check_words_sA.v (an earlier version) for
   fuzz_command.asan-ubsan: module paths, B's 320-byte frame, its registers and scratch slots, its UBSan trap site;
   the `andi sp,sp,-32` helpers are the kit's CmdSnText.v snt_land_m32, snt_denot_and_m32 and snt_sp1_facts
   (copies of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v:93-117). *)
(* check_words (plugin-hostd/fuzz_command, ASan+UBSan build fuzz_command.asan-ubsan), walk segment A
   (lib/B/Prog/check_words_d.v): from the entry 0x87ae8 to the entry of joined (`jal joined` at 0x87c24),
   seg_A : ST_J -> ST_ENTRY. The B twin of the A segment, re-derived on B's code.

   The segment is three symbolic stretches around one call:
   1. 0x87ae8 .. 0x87b54 (tok run from the entry seed cwsa_entry): the 320-byte frame, `sd zero,0(sp)` at sp0 - 320,
      the 13 saves at sp0 - 104 .. sp0 - 8, s0 := sp0, sp := sp1 = 32 * ((sp0 - 320) / 32) (andi sp,sp,-32 at
      0x87b28), s1 := sp1, the use-after-return flag (the const cell, 1: `beqz a2` at 0x87b4c is not taken), s6 := the
      shadow base, s4 := Wd and the call of __asan_stack_malloc_0 with a0 = 64 at 0x87b54. The stack region is
      trimmed to the saves before the call, so that the callee's window [sp1 - 4096, sp1) leaves it as it is
      (acall_kept).
   2. 0x87b58 .. 0x87c00 (plain run): after the call a0 = F = frame_addr ly 0 pos (aj_stack_malloc_atS, cid 0), sp
      and s1 are re-seated at the atom 56 = sp1, F's shadow SB + F / 8 is the atom 57 (with the alias of the shadow
      address), the flag word is the atom 58, w->n the atom 59. The run takes the side-stack branch (bnez a0 at
      0x87b64, F >= 4096; the real-stack fallback 0x87b68 .. 0x87b84 is not reached), stores F at sp1 + 24, the frame
      header at F, F + 8, F + 16, the 8 shadow bytes of F with SB + F / 8 at sp1 + 16, F at sp1 + 32 and sp1 + 200,
      passes the UBSan trap site 0x87bf4 and stops on the instrumented check of w->n (0x87c04), whose shadow address
      the plain executor does not resolve. The trap site (`andi a0,s4,7; bnez a0` to `unimp` 0x8816c) is not
      reached: cw_ent's `Wd mod 8 = 0` (check_words_d.v:222) is the alignment of the atom 10 = Wd in the seed
      (cwsa_facts0), so the executor computes a0 = 0.
   3. 0x87c04 .. 0x87c24 (tok run, the frame and its shadow read-only): the instrumented check of w->n is covered by
      the shadow entry of [Wd + 16, Wd + 32) (the caller's stack, zero shadow by AR's zero-shadow law, cwsa_shok), so
      neither the partial-granule path 0x8817c .. 0x88184 nor the error path 0x88188 is reached; s2 := w->n, the
      branch `blt s2, 64` split by psrr_branch_tok (s2 = read = min(n, 64) on both sides), a1 := sp1 + 208,
      a0 := Wd and the call of joined. Each side ends at SIG CS_joined, where ST_J applies with INV_J read off the
      final symbolic state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require joined_c check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d CmdSnText.
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
(* the statement's hypotheses this segment uses (check_words_c.v:133-134), word for word *)
Hypothesis ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
(* the walk hypotheses this segment uses, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.

(* ---------------------------------------------------------------------------------------------------------- *)
Lemma cwsa_denot_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. apply U_inj. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.
Lemma cwsa_havoc_a0 : forall E k (regs2 : bvmap 5 word), ew (havoc E k (map (getr regs2) CLOB)) (k + 4) = getr regs2 10.
Proof. intros E k regs2. rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). reflexivity. Qed.
Lemma cwsa_lt_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v <? z).
Proof.
intros E n v z Hn Hv Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cwsa_aval_of_val : forall H (mem : word -> option byte) a (n : nat) v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YG0f.le_byte. try unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma cwsa_val_of_aval : forall H (mem : word -> option byte) a (n : nat) v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
(* an 8-byte chunk of a symbolic region, read back as aval_mem; a zero shadow byte read back *)
Lemma cwsa_field8 : forall E H (m : word -> option byte) n cs lo hi wlo whi od e b v,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
aval_mem (aview SEGS H m) (b + od) 8 v.
Proof.
intros E H m n cs lo hi wlo whi od e b v Hr Hb Hc He Hv. apply cwsa_aval_of_val.
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 8 e v Hr Hb Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma cwsa_field1z : forall E H (m : word -> option byte) n cs lo hi wlo whi od b,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit 0))) cs -> aview SEGS H m (b + od) = Some 0.
Proof.
intros E H m n cs lo hi wlo whi od b Hr Hb Hc.
apply (aview_of_val_mem1 SEGS H m (b + od) 0); [|lia].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 1 (SLit 0) 0 Hr Hb Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
(* a byte of the caller's memory above sp0, at a state the journal reaches *)
Lemma cwsa_aval_above : forall STK sp0 ly S W0 mem md own ly' S' W' mem' md' k a (n : nat) v,
ajournal SEGS B STK sp0 [] ly S W0 mem md own ly' S' W' mem' md' k -> sp0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
aval_mem (aview SEGS (w_H W0) mem) a n v -> aval_mem (aview SEGS (w_H W') mem') a n v.
Proof.
intros STK sp0 ly S W0 mem md own ly' S' W' mem' md' k a n v HJ Ha Hn Hv i Hi.
rewrite (aview_above_of_journal B STK sp0 [] ly S W0 mem md own ly' S' W' mem' md' k HJ (a + Z.of_nat i));
[exact (Hv i Hi) | lia | exact (inFP_nil _)].
Qed.
(* the read-only version of a region (window emptied), and its submem step *)
Definition cwsa_ro (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
Lemma cwsa_subregion_ro : forall r, subregion (cwsa_ro r) r.
Proof.
intros r. unfold subregion, cwsa_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc.
Qed.
(* the index of the region based at atom n *)
Fixpoint cwsa_idx (rs : smem) (n : nat) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => match YP09.r_base r with Some m => if Nat.eqb m n then i else cwsa_idx rs' n (S i) | None => cwsa_idx rs' n (S i) end
end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the entry seed. Atoms: the registers (0..31), the shadow base SB (32), the use-after-return cell (33). Regions: the
   320 + 16 bytes below sp0, the GOT word 0xa5f50 of the shadow-base cell and that cell 0xb0c38, the GOT word 0xa5fa8
   of the use-after-return cell and that cell. The atom 10 = Wd carries cw_ent's `Wd mod 8 = 0` (alignment 2 ^ 3),
   which decides the UBSan trap site 0x87bf4. No shadow entry: the stretch to the call makes no instrumented
   check. *)
Definition cwsa_Bx : sv := SOff 32 0.
Definition cwsa_regions0 : smem :=
[stack_region 336; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33].
Definition cwsa_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (2^46 - 16) (2^47 - 32) 3); (32%nat, mkAF SB SB 0);
          (33%nat, mkAF 0x10000 0x606000 2) ] [] [].
Definition ss_cwsa : sstate := mkSS AF_check_words sr_atoms cwsa_regions0 None cwsa_facts0.
Definition cwsa_extra : list word := [Z_to_bv 64 SB; Z_to_bv 64 (as_uar_cell B)].
Definition EA (regs : bvmap 5 word) : env := Eimg (Ereg regs cwsa_extra).

Lemma cwsa_entry : forall ly S W (regs : bvmap 5 word) mem md ch Wd,
afn_pre SEGS B CHECK_WORDS_STK ly S W regs mem md ch -> cmd_val_objs ->
getr regs 10 = w64 Wd -> spZ regs <= Wd + 16 -> Wd + 32 <= ly_stk_hi ly -> Wd mod 8 = 0 ->
st_ok_pi SEGS VAL (EA regs) ss_cwsa
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_words)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch Wd HPRE HOBJ H10 HW1 HW2 HW8.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_WORDS_STK = 16848) by reflexivity. rewrite WS in Hslo, Hpres.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kgotu.
pose proof (palf_uar_img B TLF) as Hui. pose proof (palf_uar_al B TLF) as Hua. pose proof (palf_sep B TLF) as Hsep.
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V1 : VAL (A_OBJ 1) = 0xa5fa8) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
rewrite V0, V1, V12 in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := EA regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs cwsa_extra) n)
by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 Wd) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B241 : base_val E (Some (A_OBJ 0)) = 0xa5f50) by (rewrite <- V0; apply VB; [exact E241 | pose proof (pa_val_range (A_OBJ 0)); lia]).
assert (B242 : base_val E (Some (A_OBJ 1)) = 0xa5fa8) by (rewrite <- V1; apply VB; [exact E242 | pose proof (pa_val_range (A_OBJ 1)); lia]).
assert (B253 : base_val E (Some (A_OBJ 12)) = 0xb0c38) by (rewrite <- V12; apply VB; [exact E253 | pose proof (pa_val_range (A_OBJ 12)); lia]).
assert (B33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (B2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (RS : region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 336)).
{ unfold stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RG : region_ok SEGS E (mrestrict (w_H W) mem) got_regionP).
{ unfold got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa5f50 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite <- V0, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot). }
assert (RB : region_ok SEGS E (mrestrict (w_H W) mem) (bcell_regionP 32)).
{ unfold bcell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xb0c38 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite <- V12, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RUG : region_ok SEGS E (mrestrict (w_H W) mem) (uar_got_regionP 33)).
{ unfold uar_got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B242. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa5fa8 0 8 (SOff 33 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite <- V1, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu). }
assert (RUC : region_ok SEGS E (mrestrict (w_H W) mem) (uar_cell_regionP 33)).
{ unfold uar_cell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar). }
unfold ss_cwsa. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cwsa_regions0. repeat apply Forall_cons; try apply Forall_nil; assumption.
- apply pairwise_disjoint_of_extents.
unfold cwsa_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B241, B242, B253, B33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [cwsa_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the shadow entry of the stretch from 0x87c04: [Wd + 16, Wd + 32) on the caller's stack (zero shadow at every AR
   state: the stack range of the zero-shadow law), atom 10 = Wd *)
Definition cwsa_SH : list shent := [mkSHE 10 16 32].
Lemma cwsa_shok : forall ly S W mem md E Wd,
AR SEGS B ly S W mem md -> ew E 32 = Z_to_bv 64 SB -> ew E 10 = Z_to_bv 64 Wd ->
ly_stk_lo ly <= Wd + 16 -> Wd + 32 <= ly_stk_hi ly ->
sh_ok SEGS cwsa_Bx cwsa_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E Wd HAR E32 E10 Hlo Hhi.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR (or_introl eq_refl)) as Hz.
cbn [fst snd] in Hz.
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. destruct (lo_top _ LO) as (_ & _ & _ & HhE & Hal1 & Hal2 & Hhb). clear LO.
unfold YG0f.page_aligned in Hal1, Hal2. unfold kHighMemEnd in HhE. unfold kHighMemBeg in Hhb.
assert (M1 : ly_stk_lo ly mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)) as D3. rewrite Hal1 in D1. lia. }
assert (M2 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D2.
  pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as D4. rewrite Hal2 in D1. rewrite Hal1 in D2. lia. }
assert (RA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly))
by exact (zero_shadow_range _ _ _ _ M1 M2 Hz).
clear Hz HAR.
assert (UB : U E cwsa_Bx = SHADOW_OFF) by (unfold cwsa_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (U10 : U E (SOff 10 0) = Wd) by (apply U_atom; [exact E10 | lia]).
unfold sh_ok, cwsa_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E cwsa_Bx 10 (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) Wd 16 32 RA UB U10); [lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the walk's tactics *)
(* the model term a run leaves is abstracted at once (else it doubles per run) *)
Ltac cwsa_mdv := try (lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
  let m := fresh "mdv" in set (m := mdx) in *; clearbody m end).
Ltac cwsa_norm HS := lazymatch type of HS with
| st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let v := eval vm_compute in ssx in let Hss := fresh "Hss" in
  assert (Hss : ssx = v) by (vm_compute; reflexivity); rewrite Hss in HS; clear Hss
| st_ok ?sg ?Ex ?ssx ?msx =>
  let v := eval vm_compute in ssx in let Hss := fresh "Hss" in
  assert (Hss : ssx = v) by (vm_compute; reflexivity); rewrite Hss in HS; clear Hss
end.
Ltac cwsa_prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* region_ok of the region based at atom n, from the state *)
Ltac cwsa_reg HS n Hr :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss ?ms =>
let i := eval vm_compute in (cwsa_idx (ss_mem ss) n 0) in
let r := eval vm_compute in (nth i (ss_mem ss) (stack_region 0)) in
pose proof (st_ok_region_nth E ss ms i r HS eq_refl) as Hr; cbn [ms_mem restrict mkst] in Hr
| st_ok_pi ?sg ?vl ?E ?ss ?ms =>
let i := eval vm_compute in (cwsa_idx (ss_mem ss) n 0) in
let r := eval vm_compute in (nth i (ss_mem ss) (stack_region 0)) in
pose proof (st_ok_pi_region_nth E ss ms i r HS eq_refl) as Hr; cbn [ms_mem restrict mkst] in Hr
end.
Ltac cwsa_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the write set of a run: the stack (saves), the scratch area at atom 56 (in the caller's stack window of the
   journal), the frame (atom 44) and its shadow (atom 57) as the own frame (0, pos), the rest read-only *)
Ltac cwsa_awr1 B2 B56 B44 B57 Fdef dsp :=
lazymatch goal with
| |- awr_ok _ _ _ [] _ _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ _ _ (YP09.mkRegion ?b _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ _ =>
  lazymatch (eval vm_compute in (Z.leb whi wlo)) with
  | true => apply awr_ok_cons_ro; [cbn; lia|]
  | false =>
    lazymatch b with
    | Some 2%nat => eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact B2 | cbn; lia | cbn; lia |]
    | Some 56%nat => eapply awr_ok_cons_stack_off with (n := 56%nat) (d := dsp); [reflexivity | rewrite B56; lia | cbn; lia | cbn; lia |]
    | Some 44%nat => eapply awr_ok_cons_gen with (n := 44%nat); [reflexivity | exact B44 |
        cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; eexists 0, _; split; [left; reflexivity|];
        left; unfold in_zr; cbn [fst snd]; rewrite <- Fdef; change (fs_frame_bytes 0) with 64; lia |]
    | Some 57%nat => eapply awr_ok_cons_gen with (n := 57%nat); [reflexivity | exact B57 |
        cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; eexists 0, _; split; [left; reflexivity|];
        right; unfold in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd]; rewrite <- Fdef; change (fs_frame_bytes 0 / 8) with 8;
        unfold SB in Ha; lia |]
    end
  end
end.
Ltac cwsa_awr B2 B56 B44 B57 Fdef dsp :=
lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
do 6 (try (cwsa_awr1 B2 B56 B44 B57 Fdef dsp)); cwsa_awr1 B2 B56 B44 B57 Fdef dsp.
(* one save of the prologue (register cw_saved[j] at sp0 - 8 - 8 j), read off the trimmed stack region *)
Ltac cwsa_save RSV B2 E3_low EE :=
lazymatch goal with |- aval_mem _ (?s - 8 - 8 * Z.of_nat ?j) 8 (bv_unsigned (getr ?rg (Z_to_bv 5 ?r))) =>
let od := eval vm_compute in (- 8 - 8 * Z.of_nat j) in
let a := eval vm_compute in (Z.to_nat r) in
replace (s - 8 - 8 * Z.of_nat j) with (s + od) by (cbn; lia);
apply (cwsa_field8 _ _ _ _ _ _ _ _ _ od (SOff a 0) s _ RSV B2);
[ cwsa_in
| cbn [sv_denot]; rewrite E3_low by lia; rewrite (EE a (Z_to_bv 5 r)) by (vm_compute; reflexivity);
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr rg (Z_to_bv 5 r))) as RR; change (bv_modulus 64) with (2 ^ 64) in RR; lia ]
end.
(* the entry of joined: INV_J read off the final symbolic state (either side of the branch; H18 is the side's
   s2 = read = min(n, 64)), then ST_J *)
Ltac cwsa_finish F FL HS E3 E56 E3_low EE E3_32 E3_10 B2 B44 B56 B57 B58 H18 HJST Hent ly S2 W pos sp1 regs Wd :=
subst F FL;
pmkst HS;
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in
let R8 := fresh "R8" in let R9 := fresh "R9" in let R10 := fresh "R10" in let R11 := fresh "R11" in
let R20 := fresh "R20" in let R22 := fresh "R22" in
let RSV := fresh "RSV" in let RSC := fresh "RSC" in let RFR := fresh "RFR" in let RSH := fresh "RSH" in
prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11;
prreg HS (20%bv : bv 5) R20; prreg HS (22%bv : bv 5) R22;
assert (spZ (ms_regs msF) = sp1) by (unfold spZ; rewrite R2, E56; apply unsigned_lit_small; lia);
assert (getr (ms_regs msF) (3%bv : bv 5) = getr regs (3%bv : bv 5)) by (rewrite R3, E3_low by lia; apply EE; reflexivity);
assert (getr (ms_regs msF) (4%bv : bv 5) = getr regs (4%bv : bv 5)) by (rewrite R4, E3_low by lia; apply EE; reflexivity);
assert (getr (ms_regs msF) (8%bv : bv 5) = getr regs (2%bv : bv 5)) by (rewrite R8, E3_low by lia; apply EE; reflexivity);
assert (getr (ms_regs msF) (9%bv : bv 5) = w64 sp1) by (rewrite R9, E56; reflexivity);
assert (getr (ms_regs msF) (22%bv : bv 5) = w64 CW_SB) by (rewrite R22, E3_32; reflexivity);
assert (getr (ms_regs msF) (10%bv : bv 5) = w64 Wd) by (rewrite R10, E3_10; reflexivity);
assert (getr (ms_regs msF) (20%bv : bv 5) = w64 Wd) by (rewrite R20, E3_10; reflexivity);
assert (getr (ms_regs msF) (11%bv : bv 5) = w64 (sp1 + 208)) by (rewrite R11, B56; reflexivity);
assert (getr (ms_regs msF) (1%bv : bv 5) = w64 (BASE + CW_PC_P1)) by (rewrite R1; reflexivity);
cwsa_reg HS 2%nat RSV; cwsa_reg HS 56%nat RSC; cwsa_reg HS 44%nat RFR; cwsa_reg HS 57%nat RSH;
assert (aval_mem (rdW W (ms_mem msF)) (sp1 + 16) 8 (SB + frame_addr ly 0 pos / 8))
by (apply (cwsa_field8 E3 _ _ _ _ _ _ _ _ 16 (SOff 57 0) sp1 _ RSC B56);
[cwsa_in | cbn [sv_denot]; rewrite B57, Z.add_0_r; reflexivity | unfold SB; lia]);
assert (aval_mem (rdW W (ms_mem msF)) (sp1 + 24) 8 (frame_addr ly 0 pos))
by (apply (cwsa_field8 E3 _ _ _ _ _ _ _ _ 24 (SOff 44 0) sp1 _ RSC B56);
[cwsa_in | cbn [sv_denot]; rewrite B44, Z.add_0_r; reflexivity | lia]);
assert (aval_mem (rdW W (ms_mem msF)) (sp1 + 32) 8 (frame_addr ly 0 pos))
by (apply (cwsa_field8 E3 _ _ _ _ _ _ _ _ 32 (SOff 44 0) sp1 _ RSC B56);
[cwsa_in | cbn [sv_denot]; rewrite B44, Z.add_0_r; reflexivity | lia]);
assert (aval_mem (rdW W (ms_mem msF)) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos))
by (apply (cwsa_field8 E3 _ _ _ _ _ _ _ _ 56 (SOff 58 0) (frame_addr ly 0 pos) _ RFR B44);
[cwsa_in | cbn [sv_denot]; rewrite B58, Z.add_0_r; reflexivity | lia]);
assert (rdW W (ms_mem msF) (SB + frame_addr ly 0 pos / 8 + 4) = Some 0)
by (apply (cwsa_field1z E3 _ _ _ _ _ _ _ _ 4 _ RSH B57); cwsa_in);
assert (rdW W (ms_mem msF) (SB + frame_addr ly 0 pos / 8 + 5) = Some 0)
by (apply (cwsa_field1z E3 _ _ _ _ _ _ _ _ 5 _ RSH B57); cwsa_in);
assert (cw_saves (rdW W (ms_mem msF)) (spZ regs) regs);
[ let j := fresh "j" in let r := fresh "r" in let Hj := fresh "Hj" in
  intros j r Hj;
  do 13 (destruct j as [|j]; [cbv [cw_saved nth_error] in Hj; injection Hj; intros <-; cwsa_save RSV B2 E3_low EE |]);
  destruct j; cbv [cw_saved nth_error] in Hj; discriminate
| ];
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rF _ ?mF _; cfg_model := ?dF |} _ =>
refine (HJST _ ly S2 W rF mF dF pos sp1 Hent _) end;
unfold INV_J, cw_core, cw_sp0, cw_read, cw_n; cbn [e_ly e_S e_W e_regs e_mem e_md e_ws e_Wd];
repeat match goal with |- _ /\ _ => split end;
first [assumption | lia]
end.

(* ---------------------------------------------------------------------------------------------------------- *)
Lemma seg_A : ST_J B MT -> ST_ENTRY B MT.
Proof.
intros HJST e Hent.
destruct e as [ly S W regs mem md ch Wd arr wp ws R O].
pose proof Hent as Hent0. unfold cw_ent in Hent0.
cbn [e_ly e_S e_W e_regs e_mem e_md e_ch e_Wd e_arr e_wp e_ws e_R e_O] in Hent0.
destruct Hent0 as (HPRE & _ & _ & H10 & _ & HOBJ & HWd1 & HWd2 & _ & _ & HWn & _ & Hn31 & _ & _ & _ & _ & _ & Hcnt0
  & _ & _ & _ & _ & HWd8 & _).
cbn [e_W e_regs e_mem e_md e_ly e_S] in *.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_WORDS_STK = 16848) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
rewrite WS in Hslo.
pose proof pa_segs_low as Hsegs.
set (n := Z.of_nat (length ws)) in *.
assert (Hn0 : 0 <= n) by apply Nat2Z.is_nonneg.
pose proof (cwsa_entry ly S W regs mem md ch Wd HPRE HOBJ H10 HWd1 HWd2 HWd8) as HS.
pose proof (ajournal_init SEGS B CHECK_WORDS_STK [] ly S W regs mem md ch HPRE) as HJ.
assert (SHOK : sh_ok SEGS cwsa_Bx [] (EA regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (EA regs)) by (unfold EA; apply Eimg_env).
assert (EE : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew (EA regs) k = getr regs rr)
by (intros k rr Hk; unfold EA; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (EA regs) 32 = Z_to_bv 64 SB)
by (unfold EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp0 : bv_unsigned (ew (EA regs) 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
remember (EA regs) as E0 eqn:HE0. clear HE0.
unfold cfg_at. change (w64 (BASE + AF_check_words)) with (Z_to_bv 64 (BASE + AF_check_words)).
(* 1. 0x87ae8 .. 0x87b54: the prologue, to the call of __asan_stack_malloc_0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. exact Usp0. }
cwsa_mdv. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
cwsa_prreg_raw HS (2%bv : bv 5) Q2. cwsa_prreg_raw HS (9%bv : bv 5) Q9.
destruct (snt_sp1_facts (spZ regs + -320) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
assert (Q2' : getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs + -320) / 32))).
{ rewrite Q2. apply snt_denot_and_m32; [rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia]. }
assert (Q9' : getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs + -320) / 32))).
{ rewrite Q9. rewrite ?cwsa_denot_add0.
apply snt_denot_and_m32; [rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia]. }
clear Q2 Q9.
set (sp1 := 32 * ((spZ regs + -320) / 32)) in *.
assert (Hsp1 : spZ regs - 336 <= sp1 <= spZ regs - 320) by lia. clear Hsp1r.
(* the stack region trimmed to the 13 saves [sp0 - 104, sp0), before the call *)
lazymatch type of HS with st_ok ?sg ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
let rt := eval vm_compute in (trim_lo r0 (-104)) in
pose proof (st_ok_submem sg Ex ssx msx [rt] HS
(submem_keep rt r0 [] (tl (ss_mem ssx)) (subregion_trim_lo r0 (-104)) (submem_nil _)) ltac:(vm_compute; reflexivity)) as HS1
end.
clear HS. rename HS1 into HS. cbn [setpc ss_pc ss_regs ss_resv ss_facts] in HS.
pmkst HS.
assert (HSM : SIG CS___asan_stack_malloc_0 = pc_stack_malloc (as_code B) 0) by exact (palf_sm B TLF 0 (or_introl eq_refl)).
rewrite HSM.
eapply SRr_bind.
{ apply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 (ASMALLOC0 fx) ltac:(lia) W (ms_regs ms) (ms_mem ms)
CHECK_WORDS_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 5672)) HJ).
- unfold spZ at 1. rewrite Q2'. rewrite unsigned_lit_small by lia. lia.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- lia.
- rewrite WS, Hes. lia.
- rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- exact Hcnt0. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS & ES2)).
(* back at 0x87b58: a0 = F; the saves are kept (outside the callee's window [sp1 - 4096, sp1)) *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp0; intros a Ha.
- apply (mbyte_of_aview SEGS). destruct HK as (HK1 & _). apply HK1; [lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (HMO : mo_le MT S S2 0) by (rewrite ES2; exact (mo_le_set_fs_r MT MTFL S S fS 0 (mle_start MT S MTL))).
assert (HPERM : Permutation (ablocks B ly S2) (ablocks B ly S)) by (rewrite Eab; apply Permutation_refl).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HF4096 & HFceil & _).
destruct (al_flag _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (_ & _ & HFLapp & HFLceil).
change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFSpres, HFceil, Hflag, Hz. change (64 / 8) with 8 in HFSpres.
remember (frame_addr ly 0 pos) as F eqn:Fdef. remember (flag_addr ly 0 pos) as FL eqn:FLdef.
assert (HF8 : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HF8lo : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8le : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
(* the environment after the call (atoms 40 .. 55 the clobbered registers, a0 = atom 44 = F), then the atoms of the
   frame setup: 56 = sp1, 57 = SB + F / 8, 58 = the flag address, 59 = w->n *)
assert (E44 : ew (havoc E0 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by exact (cwsa_havoc_a0 E0 40 regs2).
assert (HEI1 : img_env VAL A_LIM (havoc E0 40 (map (getr regs2) CLOB)))
by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; reflexivity]).
assert (OLD1 : forall k, (k < 40)%nat -> ew (havoc E0 40 (map (getr regs2) CLOB)) k = ew E0 k)
by (intros k Hk; apply ew_havoc_old; exact Hk).
remember (havoc E0 40 (map (getr regs2) CLOB)) as E1 eqn:HE1. clear HE1.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
assert (HAT : ss_atoms_p (pband 56 60) ssx = true) by (vm_compute; reflexivity) end.
pose proof (st_ok_pi_havoc_hi 56 E1 _ _ [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n] HS HAT) as HS3.
clear HAT.
clear HS. rename HS3 into HS.
assert (HEI3 : img_env VAL A_LIM (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]))
by (apply img_env_havoc; [exact HEI1 | apply Nat.leb_le; reflexivity]).
assert (OLD3 : forall k, (k < 56)%nat ->
ew (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) k = ew E1 k)
by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (E56 : ew (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) 56 = Z_to_bv 64 sp1)
by exact (ew_havoc_new E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E57 : ew (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) 57 = Z_to_bv 64 (SB + F / 8))
by exact (ew_havoc_new E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E58 : ew (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) 58 = Z_to_bv 64 FL)
by exact (ew_havoc_new E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n] 2 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E59 : ew (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) 59 = Z_to_bv 64 n)
by exact (ew_havoc_new E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n] 3 (Z_to_bv 64 0) ltac:(cbn; lia)).
remember (havoc E1 56 [Z_to_bv 64 sp1; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 FL; Z_to_bv 64 n]) as E3 eqn:HE3. clear HE3.
assert (E3_low : forall k, (k < 40)%nat -> ew E3 k = ew E0 k) by (intros k Hk; rewrite OLD3, OLD1 by lia; reflexivity).
assert (B2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite E3_low by lia; exact Usp0).
assert (E3_10 : ew E3 10 = Z_to_bv 64 Wd) by (rewrite E3_low, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
assert (B10 : bv_unsigned (ew E3 10) = Wd) by (rewrite E3_10; apply unsigned_lit_small; lia).
assert (E3_32 : ew E3 32 = Z_to_bv 64 SB) by (rewrite E3_low by lia; exact E32).
assert (E3_44 : ew E3 44 = Z_to_bv 64 F) by (rewrite OLD3 by lia; rewrite E44; exact Ha0).
assert (B44 : bv_unsigned (ew E3 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (B56 : bv_unsigned (ew E3 56) = sp1) by (rewrite E56; apply unsigned_lit_small; lia).
assert (B57 : bv_unsigned (ew E3 57) = SB + F / 8) by (rewrite E57; apply unsigned_lit_small; unfold SB; lia).
assert (B58 : bv_unsigned (ew E3 58) = FL) by (rewrite E58; apply unsigned_lit_small; lia).
assert (B59 : bv_unsigned (ew E3 59) = n) by (rewrite E59; apply unsigned_lit_small; lia).
(* sp and s1 at atom 56 *)
assert (P2 : getr regs2 (2%bv : bv 5) = Z_to_bv 64 sp1).
{ assert (Hz2 : Z_to_bv 5 2 = (2%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
  pose proof (HP2 2 ltac:(unfold acallee_saved; lia)) as P. rewrite Hz2 in P. rewrite P. exact Q2'. }
assert (P9 : getr regs2 (9%bv : bv 5) = Z_to_bv 64 sp1).
{ assert (Hz9 : Z_to_bv 5 9 = (9%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
  pose proof (HP2 9 ltac:(unfold acallee_saved; lia)) as P. rewrite Hz9 in P. rewrite P. exact Q9'. }
pose proof (ast_ok_pi_set_reg_fp E3 _ _ (2%bv : bv 5) (SOff 56 0) HS eq_refl
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite B56, Z.add_0_r, P2; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
pose proof (ast_ok_pi_set_reg_fp E3 _ _ (9%bv : bv 5) (SOff 56 0) HS eq_refl
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite B56, Z.add_0_r, P9; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
(* the facts of F, sp1, SB + F / 8, w->n, and the shadow alias of F *)
pose proof (st_ok_pi_add_fact E3 _ _ 44 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite B44; change (2 ^ 5) with 32; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_fact E3 _ _ 56 (mkAF (2 ^ 46 - 336) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B56; change (2 ^ 5) with 32; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_fact E3 _ _ 57 (mkAF SB (SB + 2 ^ 44) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B57; rewrite Z.pow_0_r, Z.mod_1_r; unfold SB; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_fact E3 _ _ 59 (mkAF 0 (2 ^ 31 - 1) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B59; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_alias E3 _ _ _ _ HS (shadow_decl_ok E3 44 32 57 F SB E3_44 ltac:(lia) E3_32 E57)) as HS3.
clear HS. rename HS3 into HS. cwsa_norm HS.
(* the regions of the frame setup, added in the order RW, RS, RF, RH *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HWn2 : aval_mem (rdW W mem2) (Wd + 24) 4 n)
by (eapply cwsa_aval_above; [exact HJ2 | lia | cbn; lia | exact HWn]).
pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 10%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 59 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite B10; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ Wd 24 4 (SOff 59 0) n); [cbn [sv_denot]; rewrite B59, Z.add_0_r; reflexivity | zside | zside |];
exact (cwsa_val_of_aval _ _ _ _ _ HWn2))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B10, B2; repeat split; clear - HWd1; lia)) as HS3.
clear HS. rename HS3 into HS. cwsa_norm HS.
pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 56%nat) 0 208 0 208 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite B56; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres2; rewrite WS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B56, B10, B2; repeat split; clear - Hsp1 HWd1; lia)) as HS3.
clear HS. rename HS3 into HS. cwsa_norm HS.
pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 44%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 58 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite B44; split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS E3 _ F 56 8 (SOff 58 0) FL);
[cbn [sv_denot]; rewrite B58, Z.add_0_r; reflexivity | zside | zside |
replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B44, B56, B10, B2; repeat split; clear - Hsp1 HWd1 HFceil C1 Hceil Hslo; lia)) as HS3.
clear HS. rename HS3 into HS. cwsa_norm HS.
pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 57%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite B57; split; [unfold SB; clear - HF8lo; lia|]; split; [unfold SB; clear - HF8; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SHADOW_OFF, SB; lia);
apply (proj1 (HFSpres o ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B57, B44, B56, B10, B2; unfold SB; repeat split; clear - Hsp1 HWd1 HFceil C1 Hceil Hslo HFapp HF8 HF8lo HF8le; lia)) as HS3.
clear HS. rename HS3 into HS. cwsa_norm HS.
(* 2. 0x87b58 .. 0x87c00: the side-stack frame's header and shadow, the trap site 0x87bf4, to the instrumented
   check of w->n *)
paj_run_sh RUNP HS HJ2.
{ cwsa_awr B2 B56 B44 B57 Fdef (sp1 - spZ regs). }
cwsa_mdv. clear HF HFr HG.
(* the frame and its shadow read-only from here on *)
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?h :: ?f :: ?rest =>
pose proof (st_ok_pi_submem Ex ssx msx (cwsa_ro h :: cwsa_ro f :: rest) HS
(submem_keep _ _ _ _ (cwsa_subregion_ro h) (submem_keep _ _ _ _ (cwsa_subregion_ro f) (submem_refl rest)))
ltac:(vm_compute; reflexivity)) as HS3
end end.
clear HS. rename HS3 into HS. cwsa_norm HS.
clear SHOK. pose proof (cwsa_shok ly S2 W _ _ E3 Wd (proj1 HJ2) E3_32 E3_10 ltac:(lia) HWd2) as SHOK.
(* 3. 0x87c04 .. 0x87c14: the instrumented check of w->n (covered), to `blt s2, 64` *)
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ cwsa_awr B2 B56 B44 B57 Fdef (sp1 - spZ regs). }
cwsa_mdv. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* w->n < 64: s2 = read = n; 0x87c1c .. 0x87c24 to the entry of joined *)
assert (Hlt : n < 64).
{ lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite (cwsa_lt_atom E3 59 n 64 E59) in Hc by lia; apply Z.ltb_lt in Hc; exact Hc end. }
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ cwsa_awr B2 B56 B44 B57 Fdef (sp1 - spZ regs). }
cwsa_mdv. clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
prreg HS (18%bv : bv 5) R18;
assert (H18 : getr (ms_regs msF) (18%bv : bv 5) = w64 (Z.min n 64))
by (rewrite R18, E59, Z.min_l by lia; reflexivity) end.
cwsa_finish F FL HS E3 E56 E3_low EE E3_32 E3_10 B2 B44 B56 B57 B58 H18 HJST Hent ly S2 W pos sp1 regs Wd.
- (* 64 <= w->n: s2 = read = 64 (0x87c18), then to the entry of joined *)
assert (Hge : 64 <= n).
{ lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite (cwsa_lt_atom E3 59 n 64 E59) in Hc by lia; apply Z.ltb_ge in Hc; exact Hc end. }
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ cwsa_awr B2 B56 B44 B57 Fdef (sp1 - spZ regs). }
cwsa_mdv. clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msF) =>
prreg HS (18%bv : bv 5) R18;
assert (H18 : getr (ms_regs msF) (18%bv : bv 5) = w64 (Z.min n 64))
by (rewrite R18, Z.min_r by lia; reflexivity) end.
cwsa_finish F FL HS E3 E56 E3_low EE E3_32 E3_10 B2 B44 B56 B57 B58 H18 HJST Hent ly S2 W pos sp1 regs Wd.
Qed.
End e.
End f.
End d.
