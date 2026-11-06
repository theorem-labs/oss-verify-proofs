(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:136-141;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC93.v:83-84. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/put_dec_epi.v, with its module paths, module names and numbers changed; 434 of its 474 lines of code are new or changed and 347 lines of the source are left out. *)
(* The walk of check_words_chain on the ASan build of plugin-hostd/fuzz_command, the teardown and the epilogue
   (0x88f6c .. the ret at 0x88ff4, 23 instructions and two calls of a shadow-fill entry).

   With F the side-stack frame of class 4 and SH = 0x7fff8000 + F / 8 its first metadata byte, the code
   writes 0xf8 into the metadata bytes SH + 118 and SH + 119, calls the shadow-fill entry for 0xf8 on
   97 bytes from SH + 4 (its argument comes from the spill slot at sp1 + 0), writes the frame's end marker
   0x45e0360e at F + 0, skips the real-stack arm at 0x88fac (the branch at 0x88f90 tests the frame's address,
   which the AR frames law puts at or above 4096), calls the shadow-fill entry for 0xf5 on the whole 128
   metadata bytes from SH, and sets the frame's flag byte (whose address the frame holds at F + 1016) to 0.
   That last store releases the frame: the journal then owns nothing and the abstract state is
   stack_free_state 4 fpos. The epilogue restores the thirteen saved registers from sp0 - 8 .. sp0 - 104,
   puts the entry stack pointer back and returns.

   The stage builds its symbolic state again from check_words_chain_iv.v's cwc_pre and cwc_mid, in the shape of
   check_words_add.v's cwa_tail_entry: atom 2 is the realigned stack pointer, 8 the entry stack pointer, 18 the
   frame, 20 its metadata bytes, 32 the frame's flag cell and 33 .. 45 the thirteen saved registers. The two
   stores of the teardown put a writable region in the metadata band, which the token executor's cells_safe_b
   refuses, so the stage runs the plain executor (SRr_run_pi_AJ, SRr_run_pi_AJ_call) and takes the flag store
   with aj_flag_store_pi. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun PaArt PaRt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c HarnessPropsA CwcText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_chain_c check_words_chain_s0 check_words_chain_iv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the values the teardown's state names besides the registers: the frame's flag cell, then the thirteen
   registers the prologue saved, in the order of cwc_saved *)
Definition cwc_td_extra (FLv : Z) (regs : bvmap 5 word) : list word :=
[Z_to_bv 64 FLv;
 getr regs (Z_to_bv 5 1); getr regs (Z_to_bv 5 8); getr regs (Z_to_bv 5 9);
 getr regs (Z_to_bv 5 18); getr regs (Z_to_bv 5 19); getr regs (Z_to_bv 5 20);
 getr regs (Z_to_bv 5 21); getr regs (Z_to_bv 5 22); getr regs (Z_to_bv 5 23);
 getr regs (Z_to_bv 5 24); getr regs (Z_to_bv 5 25); getr regs (Z_to_bv 5 26);
 getr regs (Z_to_bv 5 27)].

(* the frame's 128 metadata bytes, with the window of the two inline stores *)
Definition cwc_td_shR : YP09.region := YP09.mkRegion (Some 20%nat) 0 128 118 120 [].
(* the frame, with the window of the end marker, and the word that holds the flag's address *)
Definition cwc_td_frR : YP09.region :=
YP09.mkRegion (Some 18%nat) 0 1024 0 8 [YP09.mkChunk 1016 (CVal 8 (SOff 32 0))].
(* the spill slots at sp1: only the one the teardown reads *)
Definition cwc_td_spR : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 20 4))].
(* the thirteen saved registers below the entry stack pointer *)
Definition cwc_td_svR : YP09.region :=
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
(* the frame's flag byte: added only for the store that releases the frame *)
Definition cwc_td_flR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].

Definition cwc_td_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
(18%nat, HPTR 5); (20%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592186044416) 2);
(32%nat, HPTR 0)] [] [].

Definition cwc_td_ss : sstate :=
mkSS CWC_TEARDOWN sr_atoms [cwc_td_shR; cwc_td_frR; cwc_td_spR; cwc_td_svR] None cwc_td_facts.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* one of the thirteen slots of the saved-register region *)
Lemma cwc_td_saved_chunk : forall E (W : world SEGS) memc (regs : bvmap 5 word) (rr : bv 5) (n : nat) (off b : Z),
ew E n = getr regs rr ->
val_mem SEGS (mrestrict (w_H W) memc) (b + off) 8 (bv_unsigned (getr regs rr)) ->
YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) b
(YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E W memc regs rr n off b Hn Hv.
pose proof (bv_unsigned_in_range 64 (getr regs rr)) as HRg.
change (bv_modulus 64) with (2 ^ 64) in HRg.
apply (chunk_ok_val SEGS E _ b off 8 (SOff n 0) (bv_unsigned (getr regs rr)));
[ cbn [sv_denot]; rewrite Hn, Z.add_0_r; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact HRg
| cbn; lia
| exact Hv ].
Qed.

(* a region of the state survives a shadow-fill call: the call writes only [q, q + n) *)
Lemma cwc_td_rk : forall E (W : world SEGS) memc mem2 (q n : Z) lo hi wlo whi cs (b : Z) (nn : nat),
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> rdW W mem2 a = rdW W memc a) ->
bv_unsigned (ew E nn) = b ->
(b + hi <= q \/ q + n <= b + lo) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W) mem2 a) ->
0 <= b + lo -> b + hi <= 2 ^ 64 ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2)
(YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E W memc mem2 q n lo hi wlo whi cs b nn HK Hn Hap Hpres H0 H1.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply HK; lia.
- intros _. apply (apresent_writable SEGS). apply Hpres. exact Ha.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HR : CwcRec B RLO RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
Hypothesis ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASETF5 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Hypothesis ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma cwc_td_ok : CWC_TD_stmt B RLO RHI.
Proof.
unfold CWC_TD_stmt.
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 memc mdc fpos sp1 regsc.
intros PRE MID FRM R2 R3 R4 R8 R9 R18 R19 R20.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
unfold CWC_CID in *.
destruct PRE as (HPRE & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12496) by reflexivity.
destruct MID as (HJ & Eab & Esp1 & HFR & HSP & HFLG & HFSH).
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hrest).
assert (Hin : In (4, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (F := frame_addr ly 4 fpos) in *.
set (FL := flag_addr ly 4 fpos) in *.
assert (EFL : flag_addr ly 4 fpos = FL) by reflexivity.
assert (EFA : frame_addr ly 4 fpos = F) by reflexivity.
destruct (al_frames _ _ LAWS ly S2 W memc mdc 4 fpos HAR2 Hin) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds SEGS B LAWS ly S2 W memc mdc 4 fpos HAR2 Hin) as (HF0 & HFceil & _).
destruct (FFL ly S2 W memc mdc 4 fpos HAR2 Hin) as (HFLpres & HFLown & HFLimg & HFL0 & HFLz & HFLceil).
rewrite EFA in HFal, HFapp, HFb, HFsh, HF0, HFceil.
rewrite EFL in HFLpres, HFLown, HFLimg, HFL0, HFLz, HFLceil.
change (fs_frame_bytes 4 / 8) with 128 in HFsh.
change (fs_frame_bytes 4) with 1024 in HFb, HFceil, HFapp.
unfold shadow_addr in HFsh.
destruct HFapp as (HFapp0 & HFapp2).
unfold kLowShadowBeg, kHighMemBeg in HFapp2.
(* the frame's address as 32 q, so the arithmetic of the frame against its metadata bytes is linear *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as D; lia).
assert (HF8 : F / 8 = 4 * (F / 32)).
{ rewrite HFq at 1. replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (HFqlo : 128 <= F / 32) by lia.
(* the frame's bytes and its flag byte are present in every state of the record the journal reaches *)
assert (HFbN : forall mem' md', AR SEGS B ly S2 W mem' md' -> forall a, F <= a < F + 1024 ->
apresent (w_H W) mem' a).
{ intros mem' md' HARx a Ha.
  destruct (al_frames _ _ LAWS ly S2 W mem' md' 4 fpos HARx Hin) as (_ & _ & Hb & _).
  change (fs_frame_bytes 4) with 1024 in Hb. rewrite EFA in Hb. exact (proj1 (Hb a Ha)). }
assert (HFLpN : forall mem' md', AR SEGS B ly S2 W mem' md' -> apresent (w_H W) mem' FL).
{ intros mem' md' HARx.
  destruct (FFL ly S2 W mem' md' 4 fpos HARx Hin) as (Hp & _). rewrite EFL in Hp. exact Hp. }
(* the frame's flag cell is the runtime's, so it is not one of the frame's own bytes *)
assert (HFLnotF : FL + 1 <= F \/ F + 1024 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hx|Hx]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 1024)) as [Hy|Hy]; [exfalso | right; lia].
  exact (proj2 (HFb FL ltac:(lia)) HFLown). }
(* the realigned stack pointer *)
destruct (sp1_facts (spZ regs + -192) ltac:(lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hsp0al; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
assert (Esp1' : sp1 = 32 * ((spZ regs + -192) / 32))
by (rewrite Esp1; do 2 f_equal; lia).
rewrite <- Esp1' in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by lia.
clear Hsp1r.
assert (Hoal : (sp1 - spZ regs) mod 16 = 0)
by (rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity).

(* --- the symbolic state at 0x88f6c --- *)
set (E := Eimg (Ereg regsc (cwc_td_extra FL regs))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr)
by (intros n rr Hn Hrr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (cwc_td_extra FL regs) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 2%nat 2%bv ltac:(lia) eq_refl) as Ea2.
pose proof (EN 3%nat 3%bv ltac:(lia) eq_refl) as Ea3.
pose proof (EN 4%nat 4%bv ltac:(lia) eq_refl) as Ea4.
pose proof (EN 8%nat 8%bv ltac:(lia) eq_refl) as Ea8.
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 18%nat 18%bv ltac:(lia) eq_refl) as Ea18.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 20%nat 20%bv ltac:(lia) eq_refl) as Ea20.
pose proof (EX 0%nat ltac:(lia)) as E32.
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42.
pose proof (EX 11%nat ltac:(lia)) as E43. pose proof (EX 12%nat ltac:(lia)) as E44.
pose proof (EX 13%nat ltac:(lia)) as E45.
cbn [Nat.add nth cwc_td_extra] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45.
assert (E2u : bv_unsigned (ew E 2) = sp1)
by (rewrite Ea2, R2; apply unsigned_lit_small; lia).
assert (E8u : bv_unsigned (ew E 8) = spZ regs)
by (rewrite Ea8, R8; apply unsigned_lit_small; unfold spZ in *; lia).
assert (E18u : bv_unsigned (ew E 18) = F)
by (rewrite Ea18, R18; apply unsigned_lit_small; lia).
assert (E20u : bv_unsigned (ew E 20) = SHADOW_OFF + F / 8)
by (rewrite Ea20, R20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32u : bv_unsigned (ew E 32) = FL)
by (rewrite E32; apply unsigned_lit_small; lia).

assert (HS : st_ok_pi SEGS VAL E cwc_td_ss
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CWC_TEARDOWN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold cwc_td_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cwc_td_shR, cwc_td_frR, cwc_td_spR, cwc_td_svR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E20u. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFsh o ltac:(lia))).
    + rewrite E18u. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFb (F + o) ltac:(lia))). }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 1016 8 (SOff 32 0) FL);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ HFLG).
    + rewrite E2u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp1 0 8 (SOff 20 4) (SHADOW_OFF + F / 8 + 4));
      [ cbn [sv_denot]; rewrite E20u; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (proj1 HSP).
    + rewrite E8u. split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 1) 33 (-8) (spZ regs) E33).
        replace (spZ regs + -8) with (spZ regs - 8 - 8 * Z.of_nat 0) by (cbn; lia).
        exact (HFR 0%nat 1 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 8) 34 (-16) (spZ regs) E34).
        replace (spZ regs + -16) with (spZ regs - 8 - 8 * Z.of_nat 1) by (cbn; lia).
        exact (HFR 1%nat 8 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 9) 35 (-24) (spZ regs) E35).
        replace (spZ regs + -24) with (spZ regs - 8 - 8 * Z.of_nat 2) by (cbn; lia).
        exact (HFR 2%nat 9 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 18) 36 (-32) (spZ regs) E36).
        replace (spZ regs + -32) with (spZ regs - 8 - 8 * Z.of_nat 3) by (cbn; lia).
        exact (HFR 3%nat 18 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 19) 37 (-40) (spZ regs) E37).
        replace (spZ regs + -40) with (spZ regs - 8 - 8 * Z.of_nat 4) by (cbn; lia).
        exact (HFR 4%nat 19 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 20) 38 (-48) (spZ regs) E38).
        replace (spZ regs + -48) with (spZ regs - 8 - 8 * Z.of_nat 5) by (cbn; lia).
        exact (HFR 5%nat 20 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 21) 39 (-56) (spZ regs) E39).
        replace (spZ regs + -56) with (spZ regs - 8 - 8 * Z.of_nat 6) by (cbn; lia).
        exact (HFR 6%nat 21 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 22) 40 (-64) (spZ regs) E40).
        replace (spZ regs + -64) with (spZ regs - 8 - 8 * Z.of_nat 7) by (cbn; lia).
        exact (HFR 7%nat 22 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 23) 41 (-72) (spZ regs) E41).
        replace (spZ regs + -72) with (spZ regs - 8 - 8 * Z.of_nat 8) by (cbn; lia).
        exact (HFR 8%nat 23 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 24) 42 (-80) (spZ regs) E42).
        replace (spZ regs + -80) with (spZ regs - 8 - 8 * Z.of_nat 9) by (cbn; lia).
        exact (HFR 9%nat 24 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 25) 43 (-88) (spZ regs) E43).
        replace (spZ regs + -88) with (spZ regs - 8 - 8 * Z.of_nat 10) by (cbn; lia).
        exact (HFR 10%nat 25 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 26) 44 (-96) (spZ regs) E44).
        replace (spZ regs + -96) with (spZ regs - 8 - 8 * Z.of_nat 11) by (cbn; lia).
        exact (HFR 11%nat 26 eq_refl).
      * apply (cwc_td_saved_chunk E W memc regs (Z_to_bv 5 27) 45 (-104) (spZ regs) E45).
        replace (spZ regs + -104) with (spZ regs - 8 - 8 * Z.of_nat 12) by (cbn; lia).
        exact (HFR 12%nat 27 eq_refl).
  - apply pairwise_disjoint_of_extents.
    unfold cwc_td_shR, cwc_td_frR, cwc_td_spR, cwc_td_svR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2u, E8u, E18u, E20u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF, spZ in *.
    revert HF0 HFceil HFapp2 HFq HF8 HFqlo Hsp1 Hceil Hslo Hshi H47 Hstk0 C1 HTS. clear. intros.
    destruct HFapp2 as [HA | HA]; repeat split; lia.
  - unfold facts_ok, cwc_td_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat apply conj; try exact I; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2];
    rewrite ?E2u, ?E8u, ?E18u, ?E20u, ?E32u;
    rewrite ?Z.pow_0_r, ?Z.mod_1_r; change (2 ^ 2) with 4; change (2 ^ 4) with 16; change (2 ^ 5) with 32;
    unfold SHADOW_OFF, spZ in *;
    try (split; [lia|]); try (split; [|lia]);
    try lia;
    try (rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
         apply Z_mod_mult). }
(* s1 and s3 hold the same values as sp and s2: one atom each, so the regions stay disjoint *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 2 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; cbn [ms_regs restrict mkst];
rewrite Ea2, R2, R9; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (19%bv : bv 5) (SOff 18 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; cbn [ms_regs restrict mkst];
rewrite Ea18, R18, R19; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss_pi HS.

(* --- 0x88f6c .. the call of the shadow-fill entry for 0xf8 at 0x88f80 --- *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 20%nat) (b := SHADOW_OFF + F / 8);
  [reflexivity | exact E20u
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left;
    exists 4, fpos; split; [left; reflexivity|]; right;
    unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA;
    change (fs_frame_bytes 4 / 8) with 128; lia
  |].
  eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 18%nat) (b := F);
  [reflexivity | exact E18u
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left;
    exists 4, fpos; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4) with 1024; lia
  |].
  repeat (apply (YCbq.awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (YCbq.awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs))
by (unfold spZ; rewrite Q2, E2u; lia).
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Ea3, R3; reflexivity).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Ea4, R4; reflexivity).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1))
by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 (SHADOW_OFF + F / 8 + 4))
by (rewrite Q10, E20u; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 97) by (rewrite Q11; reflexivity).
eapply SRr_bind.
{ exact (aj_set_shadow_atS SEGS B LAWS Hsegs (SIG CS___asan_set_shadow_f8) 0xf8 (ASETF8 fx)
  W (ms_regs ms) (ms_mem ms) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(4, fpos)] ly S2 mdv1 0
  4 fpos (SHADOW_OFF + F / 8 + 4) 97 (sp1 - spZ regs) (getr (ms_regs ms) 1)
  HJ ltac:(left; reflexivity) Qa0 Qa1 ltac:(lia)
  ltac:(unfold shadow_addr; rewrite EFA; lia)
  ltac:(unfold shadow_addr; rewrite EFA; change (fs_frame_bytes 4 / 8) with 128; lia)
  Qsp Hoal ltac:(lia) ltac:(rewrite HTS; unfold ESTACK; lia) Qgp Qtp eq_refl Qra). }
cbv beta. intros W2 c2 _ (HW2 & regs2 & mem2 & md2 & Hc2 & HJa & HPa & Hfilla & HKa & Hpresa & Hsamea).
subst W2 c2. rewrite Q1.
jafter_call_keep_pi HS 60%nat regs2 (mrestrict (w_H W) mem2) HPa [1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (cwc_td_rk E W (ms_mem ms) mem2 (SHADOW_OFF + F / 8 + 4) 97 0 1024 0 8 _ F 18%nat
    ltac:(intros a Ha Hn; exact (HKa a Ha Hn)) E18u);
    [ unfold SHADOW_OFF in *; destruct HFapp2 as [HA | HA]; lia
    | intros a Ha; exact (HFbN mem2 md2 (proj1 HJa) a ltac:(lia))
    | lia | lia ].
  - apply (cwc_td_rk E W (ms_mem ms) mem2 (SHADOW_OFF + F / 8 + 4) 97 0 64 0 0 _ sp1 2%nat
    ltac:(intros a Ha Hn; exact (HKa a Ha Hn)) E2u);
    [ unfold SHADOW_OFF, spZ in *; lia | intros a Ha; lia | lia | lia ].
  - apply (cwc_td_rk E W (ms_mem ms) mem2 (SHADOW_OFF + F / 8 + 4) 97 (-104) 0 0 0 _ (spZ regs) 8%nat
    ltac:(intros a Ha Hn; exact (HKa a Ha Hn)) E8u);
    [ unfold SHADOW_OFF, spZ in *; lia | intros a Ha; lia | unfold spZ in *; lia | unfold spZ in *; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HEI2 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [exact HEI | cbv; lia]) end.
clear HF HFr HG Q1 Q2 Q3 Q4 Q10 Q11 Qsp Qgp Qtp Qra Qa0 Qa1 Hfilla Hpresa Hsamea HKa HPa HJ.
clear ms mdv1.

(* --- 0x88f84 .. the call of the shadow-fill entry for 0xf5 at 0x88f9c --- *)
paj_run_shc RUNP RUNC HS HJa.
{ lazymatch goal with |- awr_ok _ _ ?Ex _ _ _ _ _ _ _ _ _ =>
  eapply (YCbq.awr_ok_cons_gen SEGS B Ex) with (k := 18%nat) (b := F);
  [reflexivity | rewrite ?ew_havoc_old by lia; exact E18u
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left;
    exists 4, fpos; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4) with 1024; lia
  |] end.
  repeat (apply (YCbq.awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (YCbq.awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs))
by (unfold spZ; rewrite Q2, E2u; lia).
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Ea3, R3; reflexivity).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Ea4, R4; reflexivity).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1))
by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 (SHADOW_OFF + F / 8))
by (rewrite Q10, Ea20, R20; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 128) by (rewrite Q11; reflexivity).
eapply SRr_bind.
{ exact (aj_set_shadow_atS SEGS B LAWS Hsegs (SIG CS___asan_set_shadow_f5) 0xf5 (ASETF5 fx)
  W (ms_regs ms) (ms_mem ms) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(4, fpos)] ly S2 mdv2 0
  4 fpos (SHADOW_OFF + F / 8) 128 (sp1 - spZ regs) (getr (ms_regs ms) 1)
  HJa ltac:(left; reflexivity) Qa0 Qa1 ltac:(lia)
  ltac:(unfold shadow_addr; rewrite EFA; lia)
  ltac:(unfold shadow_addr; rewrite EFA; change (fs_frame_bytes 4 / 8) with 128; lia)
  Qsp Hoal ltac:(lia) ltac:(rewrite HTS; unfold ESTACK; lia) Qgp Qtp eq_refl Qra). }
cbv beta. intros W3 c3 _ (HW3 & regs3 & mem3 & md3 & Hc3 & HJb & HPb & Hfillb & HKb & Hpresb & Hsameb).
subst W3 c3. rewrite Q1.
jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HPb [0; 1; 2]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
    apply (cwc_td_rk Ex W (ms_mem ms) mem3 (SHADOW_OFF + F / 8) 128 0 1024 0 8 _ F 18%nat
    ltac:(intros a Ha Hn; exact (HKb a Ha Hn)) ltac:(rewrite ?ew_havoc_old by lia; exact E18u)) end;
    [ unfold SHADOW_OFF in *; destruct HFapp2 as [HA | HA]; lia
    | intros a Ha; exact (HFbN mem3 md3 (proj1 HJb) a ltac:(lia))
    | lia | lia ].
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
    apply (cwc_td_rk Ex W (ms_mem ms) mem3 (SHADOW_OFF + F / 8) 128 0 64 0 0 _ sp1 2%nat
    ltac:(intros a Ha Hn; exact (HKb a Ha Hn)) ltac:(rewrite ?ew_havoc_old by lia; exact E2u)) end;
    [ unfold SHADOW_OFF, spZ in *; lia | intros a Ha; lia | lia | lia ].
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
    apply (cwc_td_rk Ex W (ms_mem ms) mem3 (SHADOW_OFF + F / 8) 128 (-104) 0 0 0 _ (spZ regs) 8%nat
    ltac:(intros a Ha Hn; exact (HKb a Ha Hn)) ltac:(rewrite ?ew_havoc_old by lia; exact E8u)) end;
    [ unfold SHADOW_OFF, spZ in *; lia | intros a Ha; lia | unfold spZ in *; lia | unfold spZ in *; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HEI3 : img_env VAL A_LIM Ev) by (apply img_env_havoc; [exact HEI2 | cbv; lia]) end.
clear HF HFr HG Q1 Q2 Q3 Q4 Q10 Q11 Qsp Qgp Qtp Qra Qa0 Qa1 Hfillb Hpresb Hsameb HKb HPb HJa.
clear ms mdv2.

(* --- the frame's flag byte, then the epilogue --- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_region Ev ssx msx cwc_td_flR HS eq_refl
ltac:(unfold cwc_td_flR, region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_havoc_old by lia; rewrite E32u;
split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (FL + o) with FL by lia; exact (HFLpN mem3 md3 (proj1 HJb)))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold cwc_td_flR, extent_disjoint;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2u, E8u, E18u, E32u;
unfold spZ in *;
revert HFLnotF HFL0 HFLceil HF0 HFceil Hsp1 Hceil Hslo Hshi H47 Hstk0 C1 HTS; clear; intros;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss_pi HS.
paj_run_flag_sh RUNF HS HJb.
{ lia. }
{ intros a Ha. unfold in_wrange in Ha. destruct Ha as (rr & Hin2 & Hrr).
  lazymatch type of Hin2 with In _ ?rsy => let rs2 := eval vm_compute in rsy in change (In rr rs2) in Hin2 end.
  cbn [In] in Hin2.
  destruct Hin2 as [Ex1 | [Ex1 | [Ex1 | [Ex1 | []]]]]; subst rr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr;
  rewrite ?ew_havoc_old in Hrr by lia.
  - right. rewrite E32u in Hrr. rewrite EFL. lia.
  - left. right; right; right; left. exists 4, fpos. split; [left; reflexivity|]. left.
    rewrite E18u in Hrr. unfold in_zr. cbn [fst snd]. rewrite EFA.
    change (fs_frame_bytes 4) with 1024. lia.
  - rewrite E2u in Hrr. lia.
  - rewrite E8u in Hrr. lia. }
{ flag0 E32 EFL. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv3 := mdx) in *; clearbody mdv3 end.

(* --- the return --- *)
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := msF) in * end.
prreg HS (1%bv : bv 5) F1.
assert (FIN : forall rr : Z, acallee_saved rr -> getr (ms_regs mF) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
{ intros rr Hrr. unfold acallee_saved in Hrr.
  assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  clear Hrr.
  repeat (destruct Hc as [-> | Hc]); [..|subst rr];
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
  first [ exact E34 | exact E35 | exact E36 | exact E37 | exact E38 | exact E39 | exact E40
        | exact E41 | exact E42 | exact E43 | exact E44 | exact E45
        | rewrite Ea3, R3; symmetry; exact Hgp
        | rewrite Ea4, R4; symmetry; exact Htp
        | rewrite Ea8, R8; unfold spZ; apply Z_to_bv_bv_unsigned ]. }
unfold cwc_postB, cwc_postQ, apost_base.
exists ly, (stack_free_state 4 fpos S2), (ms_regs mF), (ms_mem mF),
(with_vm_backing (m_vm_lazy mdv3) mat' mdv3).
assert (Hra1 : v_jalr (getr regs (Z_to_bv 5 1)) 0 = getr regs (Z_to_bv 5 1)) by exact Hra.
split; [rewrite F1, E33, Hra1; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJb|].
split; [intros rr Hrr; exact (FIN rr Hrr)|].
split; [unfold ablocks; rewrite blocks_stack_free_state; unfold ablocks in Eab; rewrite Eab;
apply Permutation_refl|].
split; [reflexivity|].
(* the release is a set_fs over the take's set_fs, so the final state is the entry's up to st_fs *)
destruct FRM as (f0 & Ef0). rewrite Ef0.
exists (st_fs (stack_free_state 4 fpos (set_fs f0 S))).
first [reflexivity | destruct S; reflexivity].
Qed.

End e.
End c.
End b.
