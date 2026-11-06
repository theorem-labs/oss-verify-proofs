(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 570 of its 728 lines of code are new or changed and 1502 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command), segment JB: seg_B, from joined's return (P1, 0x879ec) to the
   head of the call loop (LH, 0x87a7c) or to the release (REL, 0x87db8), and seg_J, the call of joined at its entry.
   The cut points, invariants and segment statements are check_words_d.v's. *)
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
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH
PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecRo.
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
(* the per-binary facts seg_B reads g_rec's GOT word through (CmdRecRo.v's cmd_got_rec; cgif's names) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------- *)
(* Segment B (listing 0x1508 .. 0x1598 / 0x18d4; image 0x879ec .. 0x87a7c / 0x87db8). After joined has returned
   (a0 = line): s3 := g_rec (from its GOT word 0xa7068), the slot s1 + 8 := &g_rec.ncalls and s1 + 72 := its shadow
   address, s1 + 144 := line, the inline check of g_rec.ncalls (removed by the token engine: g_rec has zero shadow,
   ZSH_cw), then `blez ncalls`: taken -> REL; else the call loop's set-up stores the slots cw_lscr names and reaches LH
   with c = 0. One seed (atoms 32 = A_G_REC, 33 = ncalls, 34 = CW_SB + F / 8, 35 = F), one run to the branch, one run
   to each target. The memory outside the scratch window [s1 + 8, s1 + 152) is kept (kept_of_frame); the slots inside
   it come out of the final symbolic region. *)
Definition JBx : sv := SOff 23 0.
Definition JBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition jb_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 160 8 152
  [YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition jb_got : YP09.region := YP09.mkRegion (Some 243%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition jb_grec : YP09.region := YP09.mkRegion (Some 32%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition jb_regions : smem := [jb_stk; jb_got; jb_grec].
Definition jb_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 5); (9%nat, mkAF (2^46) (2^47) 5); (23%nat, mkAF 2147450880 2147450880 0);
            (18%nat, mkAF (2^46) (2^47) 0); (10%nat, mkAF 4096 140737479966720 4);
            (32%nat, mkAF 6174528 6174528 3); (33%nat, mkAF 0 16 0);
            (34%nat, mkAF 2147450880 (2147450880 + 2^44) 0); (35%nat, mkAF 4096 140737479966720 5) ] [] [].
Definition ssB : sstate := mkSS CW_PC_P1 sr_atoms jb_regions None jb_facts.
Definition SHB : list shent := [mkSHE 32 0 960].
Definition jb_extra (nc F : Z) : list word :=
  [Z_to_bv 64 A_G_REC; Z_to_bv 64 nc; Z_to_bv 64 (CW_SB + F / 8); Z_to_bv 64 F].
Definition JBW : list (option nat * Z * Z) := [(Some 9%nat, 8, 152); (Some 243%nat, 0, 0); (Some 32%nat, 0, 0)].

(* small facts *)
Lemma cwb_val_of_aval : forall H (mem : word -> option byte) a (n : nat) v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma cwb_aval_of_val : forall H (m : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> aval_mem (aview SEGS H m) a n v.
Proof.
intros H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma cwb_aval_kept : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hk'. rewrite (Hk k Hk'). exact (H k Hk'). Qed.
Lemma cwb_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn Hv. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite U_SOff, Hn, (unsigned_lit_small v) by lia. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma cwb_ge_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = negb (0 <? v).
Proof.
intros E n v Hn Hv. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, (unsigned_lit_small v) by lia. rewrite !swrap64_id by (unfold half64; lia).
reflexivity.
Qed.
Lemma cwb_join_len0 : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH]; [exact (Z.le_refl 0)|].
destruct ws as [|w2 ws'].
- change (join_sp [w]) with w. change (PJn.join_need [w]) with (Z.of_nat (length w) + 1 + 0). lia.
- change (join_sp (w :: w2 :: ws')) with (w ++ RecFacts.SPACE :: join_sp (w2 :: ws')).
  rewrite length_app. cbn [length].
  change (PJn.join_need (w :: w2 :: ws')) with (Z.of_nat (length w) + 1 + PJn.join_need (w2 :: ws')). lia.
Qed.
Lemma cwb_join_len : forall e, Z.of_nat (length (join_sp (e_ws e))) + 1 <= cw_JN e.
Proof. intros e. unfold cw_JN. pose proof (cwb_join_len0 (e_ws e)). lia. Qed.
(* the run's write windows are those of the seed: the scratch window [s1 + 8, s1 + 152) and two read-only regions *)
Lemma cwb_win : forall E rs sp1, windows rs = JBW -> bv_unsigned (ew E 9) = sp1 ->
  forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
  sp1 + 8 <= a < sp1 + 152.
Proof.
intros E rs sp1 Hw H9 b wlo whi a Hin Ha. rewrite Hw in Hin. unfold JBW in Hin.
destruct Hin as [Hq|[Hq|[Hq|[]]]]; injection Hq as Hb Hl Hh; subst b wlo whi.
- cbn [base_val] in Ha. rewrite H9 in Ha. lia.
- lia.
- lia.
Qed.
Lemma cwb_awr : forall E rs sp1 STK sp0 FP bl0 blc fr0 ly own,
  windows rs = JBW -> bv_unsigned (ew E 9) = sp1 -> sp0 - STK <= sp1 + 8 -> sp1 + 152 <= sp0 ->
  awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E rs sp1 STK sp0 FP bl0 blc fr0 ly own Hw H9 Hlo Hhi a Ha.
destruct (in_wrange_windows E rs a Ha) as (b & wlo & whi & Hin & Hr).
pose proof (cwb_win E rs sp1 Hw H9 b wlo whi a Hin Hr) as Hz.
left. lia.
Qed.
(* a scratch slot of the final symbolic state *)
Lemma cwb_slot : forall E ss ms (W : world SEGS) sp1 lo hi wlo whi cs od e v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = sp1 ->
  In (YP09.mkChunk od (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  aval_mem (rdW W (ms_mem ms)) (sp1 + od) 8 v.
Proof.
intros E ss ms W sp1 lo hi wlo whi cs od e v HS Hn H9 Hin He Hv.
pose proof (st_ok_region_nth E _ (restrict (w_H W) ms) 0 _ HS Hn) as RG.
apply cwb_aval_of_val.
exact (field_of_region E _ 9%nat sp1 cs lo hi wlo whi od 8%N e v RG H9 Hin He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(zside)).
Qed.

(* the seed at P1 *)
Lemma cwb_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 Wd line nc F,
  cmd_val_objs ->
  spZ regsc = sp1 -> getr regsc 9 = w64 sp1 -> getr regsc 23 = w64 CW_SB -> getr regsc 18 = w64 Wd ->
  getr regsc 10 = w64 line ->
  2 ^ 46 <= sp1 <= 2 ^ 47 - 160 -> sp1 mod 32 = 0 -> 2 ^ 46 <= Wd <= 2 ^ 47 ->
  4096 <= line <= 140737479966720 -> line mod 16 = 0 -> 4096 <= F <= 140737479966720 -> F mod 32 = 0 ->
  0 <= nc <= 16 ->
  (forall a, sp1 + 8 <= a < sp1 + 152 -> apresent (w_H W) memc a) ->
  aval_mem (rdW W memc) (sp1 + 16) 8 (CW_SB + F / 8) ->
  aval_mem (rdW W memc) (sp1 + 24) 8 F -> aval_mem (rdW W memc) (sp1 + 32) 8 F ->
  aval_mem (rdW W memc) 0xa7068 8 A_G_REC -> aval_mem (rdW W memc) (A_G_REC + 8) 4 nc ->
  range_addressable (rdW W memc) SHADOW_OFF A_G_REC 960 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc (jb_extra nc F))) ssB
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_P1)) memc (seg_rom SEGS))) /\
  sh_ok SEGS JBx SHB (Eimg (Ereg regsc (jb_extra nc F))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc sp1 Wd line nc F HOBJ Hsp H9 H23 H18 H10 Rsp Hsp32 RWd Rl Hl16 RF HF32 Rnc HPR
  V16 V24 V32 VGOT VNC RA.
assert (HG : A_G_REC = 6174528) by reflexivity.
assert (HSB : CW_SB = 2147450880) by reflexivity.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (V2 : VAL (A_OBJ 2) = 0xa7068) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
set (E := Eimg (Ereg regsc (jb_extra nc F))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = Z_to_bv 64 sp1).
{ rewrite (EE 2%nat 2%bv eq_refl). rewrite <- Hsp. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 line) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 Wd) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 A_G_REC)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nc)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (CW_SB + F / 8))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 F)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E243 : ew E 243 = Z_to_bv 64 0xa7068)
  by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 243%nat with (A_OBJ 2); rewrite V2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold CW_SB in *.
split.
- unfold ssB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold jb_regions, jb_stk, jb_got, jb_grec.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPR; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ sp1 16 8 _ (2147450880 + F / 8));
           [rewrite (cwb_denot_off E 34 _ 0 E34) by lia; f_equal; lia | zside | zside |].
         exact (cwb_val_of_aval _ _ _ _ _ V16).
      -- apply (chunk_ok_val SEGS E _ sp1 24 8 _ F); [rewrite (cwb_denot_off E 35 _ 0 E35) by lia; f_equal; lia | zside | zside |].
         exact (cwb_val_of_aval _ _ _ _ _ V24).
      -- apply (chunk_ok_val SEGS E _ sp1 32 8 _ F); [rewrite (cwb_denot_off E 35 _ 0 E35) by lia; f_equal; lia | zside | zside |].
         exact (cwb_val_of_aval _ _ _ _ _ V32).
    * rewrite (VB 243%nat 0xa7068 E243) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ 0xa7068 0 8 _ A_G_REC);
        [rewrite (cwb_denot_off E 32 _ 0 E32) by lia; f_equal; lia | zside | zside |].
      rewrite Z.add_0_r. exact (cwb_val_of_aval _ _ _ _ _ VGOT).
    * rewrite (VB 32%nat A_G_REC E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 _ nc); [rewrite (cwb_denot_off E 33 _ 0 E33) by lia; f_equal; lia | zside | zside |].
      exact (cwb_val_of_aval _ _ _ _ _ VNC).
  + apply pairwise_disjoint_of_extents. unfold jb_regions, jb_stk, jb_got, jb_grec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 243%nat 0xa7068 E243) by lia. rewrite (VB 32%nat A_G_REC E32) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok jb_facts]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E23, E18, E10, E32, E33, E34, E35.
    rewrite !unsigned_lit_small by lia.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    repeat match goal with |- _ /\ _ => split end;
    first [exact I | lia | exact Hsp32 | exact Hl16 | exact HF32 | reflexivity].
- unfold sh_ok, SHB. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) memc E JBx 32 A_G_REC 960 A_G_REC 0 960 RA).
  + unfold U, JBx. rewrite (cwb_denot_off E 23 _ 0 E23) by lia. rewrite unsigned_lit_small by lia. reflexivity.
  + unfold U. rewrite (cwb_denot_off E 32 _ 0 E32) by lia. rewrite unsigned_lit_small by lia. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* cw_core and cw_line at a state whose memory differs from the old one only inside the scratch window *)
Lemma cwb_core_line : forall e lyc Sc Wc regsc memc regs2 mem2 md2 pos sp1 line,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem2 md2 EV_JOINED ->
  spZ regsc = sp1 -> sp1 mod 32 = 0 -> cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 ->
  getr regsc 3 = getr (e_regs e) 3 -> getr regsc 4 = getr (e_regs e) 4 -> getr regsc 8 = getr (e_regs e) 2 ->
  getr regsc 9 = w64 sp1 -> getr regsc 23 = w64 CW_SB ->
  cw_saves (rdW Wc memc) (cw_sp0 e) (e_regs e) ->
  aval_mem (rdW Wc memc) (sp1 + 152) 8 (cw_read e) ->
  aval_mem (rdW Wc memc) (frame_addr (e_ly e) 0 pos + 56) 8 (flag_addr (e_ly e) 0 pos) ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) = Some 0 ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) = Some 0 ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 152) -> rdW Wc mem2 a = rdW Wc memc a) ->
  spZ regs2 = sp1 -> getr regs2 3 = getr regsc 3 -> getr regs2 4 = getr regsc 4 -> getr regs2 8 = getr regsc 8 ->
  getr regs2 9 = getr regsc 9 -> getr regs2 23 = getr regsc 23 ->
  aval_mem (rdW Wc mem2) (sp1 + 16) 8 (CW_SB + frame_addr (e_ly e) 0 pos / 8) ->
  aval_mem (rdW Wc mem2) (sp1 + 24) 8 (frame_addr (e_ly e) 0 pos) ->
  aval_mem (rdW Wc mem2) (sp1 + 32) 8 (frame_addr (e_ly e) 0 pos) ->
  2 ^ 46 <= sp1 -> cw_sp0 e <= 2 ^ 47 ->
  0 <= frame_addr (e_ly e) 0 pos -> frame_addr (e_ly e) 0 pos + 64 <= sp1 ->
  0 <= line -> line + Z.of_nat (length (join_sp (e_ws e))) < sp1 ->
  cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED /\ cw_line B MT e lyc Sc (rdW Wc mem2) line.
Proof.
intros e lyc Sc Wc regsc memc regs2 mem2 md2 pos sp1 line HJ Hsp Hsp32 Hspr H3 H4 H8 H9 H23 Hsav V152 V56 Sh4 Sh5
  HL KK Q2 Q3 Q4 Q8 Q9 Q23 V16 V24 V32 Hs46 Hs47 HF0 HF64 Hl0 HlJ.
assert (HSB : CW_SB = 2147450880) by reflexivity.
assert (HF8 : 0 <= frame_addr (e_ly e) 0 pos / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (KP : forall a n v, aval_mem (rdW Wc memc) a n v ->
  (forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < 2 ^ 64 /\ ~ (sp1 + 8 <= a + Z.of_nat k < sp1 + 152)) ->
  aval_mem (rdW Wc mem2) a n v).
{ intros a n v H Hk k Hkn. destruct (Hk k Hkn) as [R N]. rewrite (KK _ R N). exact (H k Hkn). }
split.
- unfold cw_core. cbv zeta.
  split; [exact HJ|]. split; [exact Q2|]. split; [exact Hsp32|]. split; [exact Hspr|].
  split; [rewrite Q3; exact H3|]. split; [rewrite Q4; exact H4|]. split; [rewrite Q8; exact H8|].
  split; [rewrite Q9; exact H9|]. split; [rewrite Q23; exact H23|].
  split.
  { intros j r Hj. apply (KP _ _ _ (Hsav j r Hj)). intros k Hk.
    assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length cw_saved) with 13%nat in Hj13. unfold cw_sp0 in *. lia. }
  split; [exact V16|]. split; [exact V24|]. split; [exact V32|].
  split; [apply (KP _ _ _ V152); intros k Hk; lia|].
  split; [apply (KP _ _ _ V56); intros k Hk; lia|].
  split; rewrite KK by lia; assumption.
- destruct HL as (Hp & H4096 & Hap & Hby & Hmo). unfold cw_line.
  split; [exact Hp|]. split; [exact H4096|]. split; [exact Hap|]. split; [|exact Hmo].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KK by lia. apply Hby. rewrite length_app.
  cbn [length]. lia.
Qed.

(* tactics of the segment: a scratch slot of the final state; the denotation of a chunk *)
Ltac cwb_den :=
  lazymatch goal with
  | |- sv_denot ?E (SOff ?n ?c) = Z_to_bv 64 _ =>
    lazymatch goal with Hn : ew E n = Z_to_bv 64 ?v |- _ =>
      rewrite (cwb_denot_off E n v c Hn) by lia; f_equal; lia end
  | |- sv_denot ?E (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff ?m 0)) = Z_to_bv 64 _ =>
    lazymatch goal with Hn : ew E n = Z_to_bv 64 ?v |- _ =>
    lazymatch goal with Hm : ew E m = Z_to_bv 64 ?sb |- _ =>
      rewrite (denot_shx E n m c v sb Hn Hm) by lia; f_equal; lia end end
  end.
Ltac cwb_slot_tac :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms), U9 : bv_unsigned (ew ?E 9%nat) = ?sp1
    |- aval_mem _ (?sp1 + ?od) _ ?v =>
    let rg := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch rg with Some (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
    let ch := eval vm_compute in (find (fun c => Z.eqb (YP09.c_off c) od) cs) in
    lazymatch ch with Some (YP09.mkChunk _ (CVal _ ?e)) =>
    apply (cwb_slot E ss ms W sp1 lo hi wlo whi cs od e v HS ltac:(vm_compute; reflexivity) U9);
    [ repeat (first [left; reflexivity | right]) | cwb_den | lia ]
    end end
  end.
Ltac cwb_mdv := let m := fresh "mdv" in set (m := with_vm_backing _ _ _) in *; clearbody m.

Lemma seg_B : ST_LH B MT 0 -> ST_REL B MT -> ST_P1 B MT.
Proof.
intros HLH HREL. unfold ST_P1.
intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
(* the entry's premises the segment reads *)
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (HPRE & _ & HROD & _ & _ & HOBJ & HspW & HWhi & _ & _ & _ & _ & _ & _ & _ & _ & HREC & _).
pose proof (proj1 HPRE) as HARe.
(* the invariant *)
unfold INV_P1 in HI. destruct HI as (HC & HL & H10 & H18).
pose proof HL as HL0.
unfold cw_core in HC. cbv zeta in HC.
destruct HC as (HJ & Hsp & Hsp32 & Hspr & H3 & H4 & H8 & H9 & H23 & Hsav & V16 & V24 & V32 & V152 & V56 & Sh4 & Sh5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & KIMG & _ & _ & Hpres & Hstk & _ & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
pose proof alloc_ceiling_value as ((AC1 & AC2) & _).
assert (HG : A_G_REC = 6174528) by reflexivity.
assert (HSB : CW_SB = 2147450880) by reflexivity.
unfold cw_sp0 in *.
(* the frame F = frame_addr (e_ly e) 0 pos *)
assert (HinF : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR HinF) as (HF1 & HF2 & _).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 0 pos HAR HinF) as (HF32 & _).
destruct (al_layout _ _ LAWS (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) lyc HARe Hly) as (_ & HFL & _).
rewrite HFL in HF1, HF2, HF32.
assert (FS0 : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
rewrite FS0 in HF2.
assert (HF8 : 0 <= frame_addr (e_ly e) 0 pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* lia here does not turn a division into equations (PaDenot.v's zify flag): the quotients the slots hold *)
assert (HD72 : (A_G_REC + 8) / 8 = 771817) by (rewrite HG; reflexivity).
assert (HD88 : 0 <= (e_Wd e + 16) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
(* joined's block *)
destruct HL as (Hperm & Hl4096 & _ & _ & _).
assert (Hinl : In (line, cw_JN e) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc line (cw_JN e) HAR Hinl) as (Hl16 & _ & Hlceil & _ & _ & _ & HJNr).
pose proof (req_size_pos0 (cw_JN e) ltac:(lia)) as [_ HrJN].
pose proof (cwb_join_len e) as HJL.
(* g_rec.ncalls: rec_repA at the entry, kept by the journal's image clause (g_rec is program-owned) *)
destruct HREC as (Q & (_ & _ & _ & (Hn16 & _ & HNC & _) & _) & _).
assert (VNC : aval_mem (rdW Wc memc) (A_G_REC + 8) 4 (cw_ncalls e)).
{ unfold cw_ncalls. apply (cwb_aval_kept (rdW (e_W e) (e_mem e))); [|exact HNC].
  intros k Hk.
  assert (HPG : inFP cmd_PG (A_G_REC + 8 + Z.of_nat k))
    by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct (cmd_prog_unowned _ HPG) as (Hi & Ho & Her).
  apply KIMG; [exact Hi | exact Ho | exact Her | apply fp_spares_closed; [exact sink_closed_nil | apply inFP_nil]]. }
assert (Hnc : 0 <= cw_ncalls e <= 16) by (unfold cw_ncalls; lia).
(* g_rec's GOT word (runtime-owned RELRO): arodata_okP at this state, from the entry's through the journal *)
assert (HROc : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW Wc memc)).
{ eapply (arodata_ok_journalP (RO := CmdRecBase.cif_ro_below_ofl _ _ IMG) SEGS CMD_RLO CMD_RHI RRO);
    [exact HJ | intros a _; apply inFP_nil | exact HROD]. }
pose proof (CmdRecRo.cmd_got_rec SEGS B LAWS HB IMG lyc Sc Wc memc mdc HAR HROc) as VGOT.
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HAR ltac:(left; reflexivity)) as [RAG _].
(* the seed *)
destruct (cwb_seed Wc regsc memc sp1 (e_Wd e) line (cw_ncalls e) (frame_addr (e_ly e) 0 pos) HOBJ Hsp H9 H23 H18 H10
  ltac:(lia) Hsp32 ltac:(lia) ltac:(lia) Hl16 ltac:(lia) HF32 Hnc
  ltac:(intros a Ha; apply Hpres; lia) V16 V24 V32 VGOT VNC RAG) as [HS SHOK].
assert (V22 : VAL (A_OBJ 22) = 0xa5dc0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V23 : VAL (A_OBJ 23) = 0x21120) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V24o : VAL (A_OBJ 24) = 0x21280) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V25 : VAL (A_OBJ 25) = 0x218a0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
remember (Eimg (Ereg regsc (jb_extra (cw_ncalls e) (frame_addr (e_ly e) 0 pos)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 line) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 (e_Wd e)) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 A_G_REC)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (cw_ncalls e))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (CW_SB + frame_addr (e_ly e) 0 pos / 8))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (frame_addr (e_ly e) 0 pos))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E263 : ew E 263 = Z_to_bv 64 0xa5dc0)
  by (rewrite HE, Eimg_img by (unfold A_TEXT, A_LIM; lia); change 263%nat with (A_OBJ 22); rewrite V22; reflexivity).
assert (E264 : ew E 264 = Z_to_bv 64 0x21120)
  by (rewrite HE, Eimg_img by (unfold A_TEXT, A_LIM; lia); change 264%nat with (A_OBJ 23); rewrite V23; reflexivity).
assert (E265 : ew E 265 = Z_to_bv 64 0x21280)
  by (rewrite HE, Eimg_img by (unfold A_TEXT, A_LIM; lia); change 265%nat with (A_OBJ 24); rewrite V24o; reflexivity).
assert (E266 : ew E 266 = Z_to_bv 64 0x218a0)
  by (rewrite HE, Eimg_img by (unfold A_TEXT, A_LIM; lia); change 266%nat with (A_OBJ 25); rewrite V25; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
clear HE.
(* the run to `blez ncalls` (0x87a18) *)
unfold cw_at.
paj_run_tok RUN HS HJ SHOK JBspan.
{ apply (cwb_awr E _ sp1); [vm_compute; reflexivity | exact U9 | lia | lia]. }
cwb_mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ memc) (mrestrict _ (ms_mem ?m1)) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) E rs (w_H Wc) memc (ms_mem m1) (fun a => sp1 + 8 <= a < sp1 + 152) HFr
    (cwb_win E rs sp1 ltac:(vm_compute; reflexivity) U9)) as K1 end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
psrr_branch_tok RUN BR HS SHOK JBspan.
- (* ncalls <= 0: on to the release *)
  paj_run_to_tok RUNTO HS HJ SHOK JBspan 0x18d4.
  { apply (cwb_awr E _ sp1); [vm_compute; reflexivity | exact U9 | lia | lia]. }
  cwb_mdv.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E rs (w_H Wc) (ms_mem m1) (ms_mem m2) (fun a => sp1 + 8 <= a < sp1 + 152) HFr
      (cwb_win E rs sp1 ltac:(vm_compute; reflexivity) U9)) as K2;
    assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 152) -> rdW Wc (ms_mem m2) a = rdW Wc memc a)
      by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- SRr _ _ {| cfg_ms := _; cfg_model := ?md |} _ =>
    rename m into ms2; rename md into md2 end.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (23%bv : bv 5) R23.
  assert (W16 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 16) 8 (CW_SB + frame_addr (e_ly e) 0 pos / 8)) by cwb_slot_tac.
  assert (W24 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 24) 8 (frame_addr (e_ly e) 0 pos)) by cwb_slot_tac.
  assert (W32 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 32) 8 (frame_addr (e_ly e) 0 pos)) by cwb_slot_tac.
  assert (W144 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 144) 8 line) by cwb_slot_tac.
  destruct (cwb_core_line e lyc Sc Wc regsc memc (ms_regs ms2) (ms_mem ms2) md2 pos sp1 line HJ Hsp Hsp32 Hspr
    H3 H4 H8 H9 H23 Hsav V152 V56 Sh4 Sh5 HL0 KK
    ltac:(unfold spZ; rewrite R2, (EE 2%nat 2%bv eq_refl); exact Hsp)
    ltac:(rewrite R3; apply EE; reflexivity) ltac:(rewrite R4; apply EE; reflexivity)
    ltac:(rewrite R8; apply EE; reflexivity) ltac:(rewrite R9; apply EE; reflexivity)
    ltac:(rewrite R23; apply EE; reflexivity)
    W16 W24 W32 ltac:(lia) ltac:(unfold cw_sp0; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [HC2 HL2].
  pmkst HS.
  exact (HREL e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos sp1 line Hent (conj HC2 (conj HL2 W144))).
- (* 0 < ncalls: the call loop's set-up, to its head with c = 0 *)
  assert (Hpos : 0 < cw_ncalls e).
  { rewrite (cwb_ge_atom E 33 (cw_ncalls e) E33) in Hc by lia. apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
    exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK JBspan 0x1598.
  { apply (cwb_awr E _ sp1); [vm_compute; reflexivity | exact U9 | lia | lia]. }
  cwb_mdv.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E rs (w_H Wc) (ms_mem m1) (ms_mem m2) (fun a => sp1 + 8 <= a < sp1 + 152) HFr
      (cwb_win E rs sp1 ltac:(vm_compute; reflexivity) U9)) as K2;
    assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 152) -> rdW Wc (ms_mem m2) a = rdW Wc memc a)
      by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- SRr _ _ {| cfg_ms := _; cfg_model := ?md |} _ =>
    rename m into ms2; rename md into md2 end.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (23%bv : bv 5) R23.
  prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R24.
  assert (W16 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 16) 8 (CW_SB + frame_addr (e_ly e) 0 pos / 8)) by cwb_slot_tac.
  assert (W24 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 24) 8 (frame_addr (e_ly e) 0 pos)) by cwb_slot_tac.
  assert (W32 : aval_mem (rdW Wc (ms_mem ms2)) (sp1 + 32) 8 (frame_addr (e_ly e) 0 pos)) by cwb_slot_tac.
  assert (WL : cw_lscr e (rdW Wc (ms_mem ms2)) sp1 (frame_addr (e_ly e) 0 pos) line 0)
    by (unfold cw_lscr; repeat split; cwb_slot_tac).
  destruct (cwb_core_line e lyc Sc Wc regsc memc (ms_regs ms2) (ms_mem ms2) md2 pos sp1 line HJ Hsp Hsp32 Hspr
    H3 H4 H8 H9 H23 Hsav V152 V56 Sh4 Sh5 HL0 KK
    ltac:(unfold spZ; rewrite R2, (EE 2%nat 2%bv eq_refl); exact Hsp)
    ltac:(rewrite R3; apply EE; reflexivity) ltac:(rewrite R4; apply EE; reflexivity)
    ltac:(rewrite R8; apply EE; reflexivity) ltac:(rewrite R9; apply EE; reflexivity)
    ltac:(rewrite R23; apply EE; reflexivity)
    W16 W24 W32 ltac:(lia) ltac:(unfold cw_sp0; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [HC2 HL2].
  assert (G19 : getr (ms_regs ms2) 19 = w64 A_G_REC) by (rewrite R19, E32; reflexivity).
  assert (G20 : getr (ms_regs ms2) 20 = w64 0) by exact R20.
  assert (G24 : getr (ms_regs ms2) 24 = w64 0x21120) by (rewrite R24, E264; reflexivity).
  pmkst HS.
  exact (HLH e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 pos sp1 line Hent
    (conj HC2 (conj HL2 (conj WL (conj G19 (conj G20 (conj G24 (conj (Z.le_refl 0) Hpos)))))))).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* Segment J: the call of joined at its entry (after `jal joined` at 0x879e8; ra = BASE + 0x1508). More small facts. *)
Lemma cwj_rdword : forall H (m : word -> option byte) a v,
  aval_mem (aview SEGS H m) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) a = Some v.
Proof. intros H m a v Hv Hr. exact (rdword_of_val_mem SEGS H m a v (cwb_val_of_aval H m a 8 v Hv) Hr). Qed.
Lemma cwj_bv64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
Lemma cwj_bytes_kept : forall (rd rd' : reader) a l,
  (forall i, (i < length l)%nat -> rd' (a + Z.of_nat i) = rd (a + Z.of_nat i)) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l Hk H i Hi. rewrite (Hk i Hi). exact (H i Hi). Qed.
Lemma cwj_str_kept : forall (rd rd' : reader) p s n,
  (forall i, 0 <= i < n -> rd' (p + i) = rd (p + i)) -> Z.of_nat (length s) + 1 <= n ->
  astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s n Hk Hn [Hb Hnul]. split; [|exact Hnul].
apply (cwj_bytes_kept rd); [|exact Hb]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma cwj_saved_lt : forall j r, nth_error cw_saved j = Some r -> (j < 13)%nat.
Proof. intros j r H. assert (Hl : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite H; discriminate). exact Hl. Qed.
Lemma cwj_jn_nonneg : forall ws, 0 <= PJn.join_need ws.
Proof. induction ws as [|w ws IH]; unfold PJn.join_need in *; cbn [fold_right] in *; lia. Qed.
Lemma cwj_inblk_perm : forall (bl bl' : list (Z * Z)) a n, Permutation bl bl' -> in_blockA bl' a n -> in_blockA bl a n.
Proof.
intros bl bl' a n HP (p & k & Hin & H1 & H2). exists p, k.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
(* lia here has no Z.modulo / Z.div support: alignment goes through explicit multiples *)
Lemma cwj_mod_of : forall x m, 0 < m -> (exists q, x = m * q) -> x mod m = 0.
Proof. intros x m Hm (q & ->). rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.
Lemma cwj_div_of : forall x m, 0 < m -> x mod m = 0 -> exists q, x = m * q.
Proof. intros x m Hm H. exists (x / m). pose proof (Z.div_mod x m ltac:(lia)) as E. rewrite H, Z.add_0_r in E. exact E. Qed.
(* the read-only image bytes over a journal without footprint (the journal's image clause; RRO for the RELRO range) *)
Lemma cwj_arodata : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil (inFP_nil a))].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hgot)].
Qed.
(* discharge every premise of H after its first by an assumption or lia *)
Ltac cwj_fill H :=
  lazymatch type of H with
  | ?A -> ?P -> ?Q =>
      let h := fresh "h" in
      assert (h : P) by first [assumption | lia];
      let H' := fresh "H" in
      pose proof (fun x : A => H x h) as H'; clear H h; rename H' into H; cwj_fill H
  | _ => idtac
  end.

(* seg_J: from joined's entry (after `jal joined` at 0x879e8) to check_words' post, through joined's statement and
   cl_callS_wide (joined writes *len = s1 + 176 in this frame), then ST_P1 at the return address 0x879ec *)
Lemma seg_J : ST_P1 B MT -> ST_J B MT.
Proof.
intros HP1. unfold ST_J. intros e lyc Sc Wc regsc memc mdc pos sp1 Hent HI.
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & HFRM & HROD & _ & _ & _ & Hspw & Hhi & Harr & Harr64 & Hn & Hlen & Hn31 & Hblk & Hwords
  & HJN & _ & _ & _ & _ & Hev & Hlive & REST).
assert (MOK : mo_ok MT (e_S e) (XM_CHECK_WORDS MT (e_ws e))) by first [exact REST | exact (proj1 REST)].
destruct REST as (_ & HWd8 & Harr8 & HPRES).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htophi).
destruct HI as (HC & MLE0 & H10 & H11 & H1 & H18 & HPerm & HBB).
unfold cw_core in HC. cbv zeta in HC.
destruct HC as (HJ & Hsp & Hsp32 & Hsprng & H3 & H4 & H8 & H9 & H23 & Hsaves & V16 & V24 & V32 & V152 & VFL & VS4 & VS5).
assert (Esp0 : cw_sp0 e = spZ (e_regs e)) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
assert (WS : CHECK_WORDS_STK = 16800) by reflexivity.
assert (WJ : JOINED_STK = 16496) by reflexivity.
assert (EVJ : EV_JOINED = 1) by reflexivity.
assert (EVC : EV_CHECK_WORDS = 2) by reflexivity.
assert (LV : LIVE_CHECK_WORDS = LIVE_JOINED) by reflexivity.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
assert (Hsp1c : alloc_ceiling + 16496 <= sp1) by lia.
destruct (cwj_div_of _ 16 ltac:(lia) Hal16) as (q0 & Hq0).
destruct (cwj_div_of _ 32 ltac:(lia) Hsp32) as (q1 & Hq1).
(* the journal at the call: layout, frames, the bytes it keeps *)
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & Hnev1 & _ & F1 & F2 & _).
destruct Hly1 as (_ & _ & _ & _ & _ & EF1 & _ & _ & Etop & Eslo & Eshi & _).
assert (EFA1 : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos) by (unfold frame_addr; rewrite EF1; reflexivity).
assert (Hin1 : In (0, pos) (frames Sc)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin1) as (HF4096 & HFceil & _).
rewrite EFA1 in HF4096. rewrite EFA1, Hfb in HFceil.
assert (HF8 : 8 * (frame_addr (e_ly e) 0 pos / 8) <= frame_addr (e_ly e) 0 pos) by (apply Z.mul_div_le; lia).
assert (KA : forall a, cw_sp0 e <= a < 2 ^ 64 -> rdW Wc memc a = rdW (e_W e) (e_mem e) a)
  by (intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha (inFP_nil a))).
assert (KB : forall a n i, in_blockA (ablocks B (e_ly e) (e_S e)) a n -> 0 <= i < n ->
  rdW Wc memc (a + i) = rdW (e_W e) (e_mem e) (a + i)).
{ intros a n i (p & k & Hin & Hp1 & Hp2) Hi.
  pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
  replace (a + i) with (p + (a + i - p)) by lia.
  apply (F2 p k (a + i - p)); [exact Hin | exact (Permutation_in _ (Permutation_sym HPerm) Hin) | lia | exact (inFP_nil _)]. }
(* joined's premises at the call state *)
(* len's 8 bytes are present: in the window [sp0 - STK, sp0), kept present by the journal *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRS & _).
assert (Pout : forall i, 0 <= i < 8 -> apresent (w_H Wc) memc (sp1 + 176 + i)) by (intros i Hi; apply HPRS; lia).
(* the stack from len - 16 = s1 + 160 up (pass 5b): present from the entry sp (cw_ent) kept by the journal, which has no
   footprint, so presence holds from sp0 - STK, and s1 + 160 lies above that *)
assert (P2 : astack_pres lyc (w_H Wc) memc (sp1 + 176 - 16)).
{ apply (astack_pres_mono lyc _ _ (cw_sp0 e - CHECK_WORDS_STK)); [lia|].
  exact (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HPRES
    (fun a Hf _ => False_ind _ (inFP_nil a Hf))). }
assert (P3 : arodata_okP SEGS RLO RHI B (rdW Wc memc)) by exact (cwj_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
assert (P10 : aval_mem (rdW Wc memc) (e_Wd e + 24) 4 (Z.of_nat (length (e_ws e)))).
{ apply (cwb_aval_kept (rdW (e_W e) (e_mem e))); [|exact Hn]. intros k Hk. apply KA. lia. }
assert (P11 : aval_mem (rdW Wc memc) (e_Wd e + 16) 8 (e_arr e)).
{ apply (cwb_aval_kept (rdW (e_W e) (e_mem e))); [|exact Harr]. intros k Hk. apply KA. lia. }
assert (P13 : in_blockA (ablocks B lyc Sc) (e_arr e) (8 * Z.of_nat (length (e_ws e))))
  by exact (cwj_inblk_perm _ _ _ _ HPerm Hblk).
assert (P14 : forall k, (k < length (e_ws e))%nat ->
  aval_mem (rdW Wc memc) (e_arr e + 8 * Z.of_nat k) 8 (nth k (e_wp e) 0) /\ 0 <= nth k (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth k (e_wp e) 0) (Z.of_nat (length (nth k (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc memc) (nth k (e_wp e) 0) (nth k (e_ws e) [])).
{ intros k Hk. destruct (Hwords k Hk) as (W1 & W2 & W3 & W4).
  split; [|split; [exact W2 | split]].
  - apply (cwb_aval_kept (rdW (e_W e) (e_mem e))); [|exact W1]. intros j Hj.
    replace (e_arr e + 8 * Z.of_nat k + Z.of_nat j) with (e_arr e + (8 * Z.of_nat k + Z.of_nat j)) by lia.
    apply (KB _ _ _ Hblk). lia.
  - exact (cwj_inblk_perm _ _ _ _ HPerm W3).
  - apply (cwj_str_kept (rdW (e_W e) (e_mem e)) (rdW Wc memc) (nth k (e_wp e) 0) (nth k (e_ws e) [])
      (Z.of_nat (length (nth k (e_ws e) [])) + 1)); [intros i Hi; exact (KB _ _ _ W3 Hi) | lia | exact W4]. }
assert (P22 : mo_ok MT Sc (XM_JOINED MT (e_ws e))).
{ apply (mok_station MT (e_S e) Sc (XM_CHECK_WORDS MT (e_ws e)) 0 (XM_JOINED MT (e_ws e)) MTL MOK MLE0).
  - unfold XM_JOINED. apply (mo_malloc_nonneg MT MTL). pose proof (cwj_jn_nonneg (e_ws e)). lia.
  - unfold XM_CHECK_WORDS. pose proof (mo_free_nonneg MT MTL). lia. }
(* s0 = sp0 at the call: the frame chain pushes check_words' own record (ra at sp0 - 8, s0 at sp0 - 16) *)
assert (Hs0 : s0Z regsc = cw_sp0 e) by (unfold s0Z; rewrite H8; reflexivity).
assert (HCH : exists ch1, achain lyc (rdW Wc memc) (cw_sp0 e + (sp1 - cw_sp0 e)) (s0Z regsc) ch1).
{ rewrite Hs0. replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 by lia.
  destruct (Z_lt_le_dec (cw_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
  - exists ((cw_sp0 e, bv_unsigned (getr (e_regs e) (Z_to_bv 5 1)), s0Z (e_regs e)) :: e_ch e).
    apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
    apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc memc) (cw_sp0 e) (s0Z (e_regs e))
      (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1))) (e_ch e) sp1 Hch0).
    + lia.
    + exact KA.
    + pose proof (Hsaves 0%nat 1 eq_refl) as HS0.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 0) with (cw_sp0 e - 8) in HS0 by lia.
      exact (cwj_rdword _ _ _ _ HS0 (cwj_bv64 _)).
    + pose proof (Hsaves 1%nat 8 eq_refl) as HS1.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 1) with (cw_sp0 e - 16) in HS1 by lia.
      exact (cwj_rdword _ _ _ _ HS1 (cwj_bv64 (getr (e_regs e) (Z_to_bv 5 8)))).
    + exact Hra4.
    + lia.
    + apply (cwj_mod_of _ 8 ltac:(lia)). exists (2 * q0). lia.
    + exact Hlt.
    + lia.
  - exists []. unfold achain. left. split; [right; left; rewrite Etop; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hch1).
(* joined's statement at this call *)
assert (Hout8 : (sp1 + 176) mod 8 = 0) by (apply (cwj_mod_of _ 8 ltac:(lia)); exists (4 * q1 + 22); lia).
assert (HCALL := HJOINED lyc Sc Wc regsc memc mdc ch1 (e_Wd e) (e_arr e) (sp1 + 176) (e_wp e) (e_ws e)).
cwj_fill HCALL.
unfold apost_base, cfg_at in HCALL.
assert (HF : forall a, inFP [(sp1 + 176, sp1 + 176 + 8)] a ->
  awr_byte SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (ablocks B (e_ly e) (e_S e)) (ablocks B lyc Sc) (frames (e_S e)) lyc
    [(0, pos)] a).
{ intros a Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
  unfold awr_byte. left. lia. }
assert (Hspo : spZ regsc = cw_sp0 e + (sp1 - cw_sp0 e)) by lia.
assert (Halo : (sp1 - cw_sp0 e) mod 16 = 0) by (apply (cwj_mod_of _ 16 ltac:(lia)); exists (2 * q1 - q0); lia).
assert (Hnego : sp1 - cw_sp0 e <= 0) by lia.
assert (Hstk1 : 0 <= JOINED_STK) by lia.
assert (Hbud : JOINED_STK - (sp1 - cw_sp0 e) <= CHECK_WORDS_STK) by lia.
assert (Hgp' : getr regsc 3 = w64 (as_gp B)) by (rewrite H3; exact Hgp).
assert (Htp' : getr regsc 4 = w64 (as_tp B)) by (rewrite H4; exact Htp).
assert (Hraw : YK0s.ret_ok (getr regsc 1))
  by (rewrite H1; exact (ret_ok_codeptr_v CW_PC_P1 ltac:(unfold CW_PC_P1; lia) eq_refl)).
assert (Hra4' : 4096 <= bv_unsigned (getr regsc 1)).
{ replace (getr regsc 1) with (Z_to_bv 64 (BASE + CW_PC_P1)) by (rewrite H1; reflexivity).
  rewrite unsigned_lit_small by (unfold CW_PC_P1; lia). unfold CW_PC_P1. lia. }
(* the call target *)
unfold cw_at.
assert (HIN : In CS_joined cmd_prog_syms) by (unfold cmd_prog_syms; cbn [In]; tauto).
assert (EAF : cmd_af CS_joined = AF_joined) by (vm_compute; reflexivity).
rewrite (SIGP CS_joined HIN), EAF.
eapply SRr_bind.
{ refine (cl_callS_wide B LAWS Wc regsc memc _ CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(0, pos)] lyc Sc mdc 0 JOINED_STK [(sp1 + 176, sp1 + 176 + 8)] EV_JOINED (sp1 - cw_sp0 e)
    (getr regsc 1) ch1 _ HJ Hspo Halo Hnego Hstk1 Hbud Hgp' Htp' eq_refl Hraw Hra4' Hch1 HCALL HF _).
  (* VIS: *len's bytes are readable after the call (joined's post) *)
  intros ly2 S2 W2 regs2 mem2 md2 HK a Hf _ _.
  destruct HK as (res & _ & _ & _ & _ & _ & _ & Hlen8 & _).
  apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [| destruct (inFP_nil a Hf)].
  pose proof (Hlen8 (Z.to_nat (a - (sp1 + 176))) ltac:(lia)) as Hb.
  rewrite Z2Nat.id in Hb by lia.
  replace (sp1 + 176 + (a - (sp1 + 176))) with a in Hb by lia.
  rewrite Hb. discriminate. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP & HK).
destruct HK as (res & R10 & Hres & HPerm2 & Hapart & _ & Hbytes & _ & _ & _ & MLE2).
rewrite Z.add_0_l in HJ2.
(* the bytes joined keeps: its footprint is only *len = [s1 + 176, s1 + 184) *)
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
assert (KS : forall a, sp1 <= a < cw_sp0 e -> ~ (sp1 + 176 <= a < sp1 + 184) -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hn'. apply G1; [lia | lia |].
  intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia | exact (inFP_nil a Hf)]. }
assert (KF : forall a, frame_addr (e_ly e) 0 pos <= a < frame_addr (e_ly e) 0 pos + 64 ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. apply (G4 0 pos a Hin1).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA1, Hfb. lia.
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia | exact (inFP_nil a Hf)]. }
assert (KSH : forall a, CW_SB + frame_addr (e_ly e) 0 pos / 8 <= a < CW_SB + frame_addr (e_ly e) 0 pos / 8 + 8 ->
  rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha. unfold CW_SB in Ha. apply (G4 0 pos a Hin1).
  - right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. rewrite EFA1, Hfb. change (64 / 8) with 8. lia.
  - intros Hf. apply inFP_cons in Hf. destruct Hf as [Hf | Hf]; [lia | exact (inFP_nil a Hf)]. }
(* the callee-saved registers *)
assert (R2 : spZ regs2 = sp1).
{ unfold spZ. change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)).
  rewrite (HP 2 ltac:(unfold acallee_saved; lia)). exact Hsp. }
assert (R3 : getr regs2 3 = getr (e_regs e) 3).
{ change (getr regs2 3) with (getr regs2 (Z_to_bv 5 3)). rewrite (HP 3 ltac:(unfold acallee_saved; lia)). exact H3. }
assert (R4 : getr regs2 4 = getr (e_regs e) 4).
{ change (getr regs2 4) with (getr regs2 (Z_to_bv 5 4)). rewrite (HP 4 ltac:(unfold acallee_saved; lia)). exact H4. }
assert (R8 : getr regs2 8 = getr (e_regs e) 2).
{ change (getr regs2 8) with (getr regs2 (Z_to_bv 5 8)). rewrite (HP 8 ltac:(unfold acallee_saved; lia)). exact H8. }
assert (R9 : getr regs2 9 = w64 sp1).
{ change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)). rewrite (HP 9 ltac:(unfold acallee_saved; lia)). exact H9. }
assert (R23 : getr regs2 23 = w64 CW_SB).
{ change (getr regs2 23) with (getr regs2 (Z_to_bv 5 23)). rewrite (HP 23 ltac:(unfold acallee_saved; lia)). exact H23. }
assert (R18 : getr regs2 18 = w64 (e_Wd e)).
{ change (getr regs2 18) with (getr regs2 (Z_to_bv 5 18)). rewrite (HP 18 ltac:(unfold acallee_saved; lia)). exact H18. }
(* INV_P1 at the return *)
assert (INV : INV_P1 B MT e ly2 S2 W2 regs2 mem2 md2 pos sp1 res).
{ unfold INV_P1, cw_core, cw_line. cbv zeta.
  split; [|split; [|split; [exact R10 | exact R18]]].
  - split; [exact HJ2|]. split; [exact R2|]. split; [exact Hsp32|]. split; [exact Hsprng|].
    split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|]. split; [exact R23|].
    split.
    { intros j r Hj. pose proof (cwj_saved_lt j r Hj) as Hj13.
      apply (cwb_aval_kept (rdW Wc memc)); [|exact (Hsaves j r Hj)]. intros k Hk. apply KS; lia. }
    split; [apply (cwb_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V16]|].
    split; [apply (cwb_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V24]|].
    split; [apply (cwb_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V32]|].
    split; [apply (cwb_aval_kept (rdW Wc memc)); [intros k Hk; apply KS; lia | exact V152]|].
    split; [apply (cwb_aval_kept (rdW Wc memc)); [intros k Hk; apply KF; lia | exact VFL]|].
    split.
    + rewrite (KSH (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) ltac:(lia)). exact VS4.
    + rewrite (KSH (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) ltac:(lia)). exact VS5.
  - split; [unfold cw_JN; exact (Permutation_trans HPerm2 (perm_skip _ HPerm))|].
    split; [lia|].
    split.
    { apply Forall_forall. intros x Hx.
      exact (proj1 (Forall_forall _ _) Hapart x (Permutation_in _ (Permutation_sym HPerm) Hx)). }
    split; [exact Hbytes|].
    rewrite <- (Z.add_0_l (XM_JOINED MT (e_ws e))). exact (mo_le_trans MT MTL _ _ _ _ _ MLE0 MLE2). }
rewrite H1.
exact (HP1 e ly2 S2 W2 regs2 mem2 md2 pos sp1 res Hent INV).
Qed.
End e.
End f.
End d.
