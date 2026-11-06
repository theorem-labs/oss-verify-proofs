(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 750 of its 901 lines of code are new or changed and 1509 lines of the source are left out. *)
(* check_words' ASan walk, segment I3 (check_words_d.v): the item's string compare.
   seg_I3a (listing 0x1718 .. 0x1728, image 0x87bfc .. 0x87c0c): `s2 += strcspn(s2, " ")` skips the template item.
   seg_I3b (listing 0x1728 .. 0x174c, image 0x87c0c .. 0x87c30): the inline check of &args[a], the load of args[a],
   its null test, `strcmp(args[a], s5)` and the test of its answer; both abort edges (0x87e78) are decided by the
   record (acall_at: args[a] <> 0) and by words_prop_at (args[a] is the string the item asks for).
   Method: fresh symbolic seeds at 0x1718, 0x1724, 0x1728 and 0x1748 (only the registers, and for 0x1728 the slot
   &args[a]), runs by paj_run_tok / paj_run_to_tok, the wrapper calls through check_words_art.v's aj_strcspn_at and
   PaArtStr.v's aj_strcmp_at, and the invariant carried across by the memory kept outside the call's window
   [sp1 - 2 ESTACK, sp1) and the callee-saved registers. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArtStr check_words_art.
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

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwi_skipn_cons : forall {A : Type} n (l : list A) x r, skipn n l = x :: r ->
  nth_error l n = Some x /\ skipn (S n) l = r.
Proof.
intros A n. induction n as [|n IH]; intros l x r H.
- change (skipn 0 l) with l in H. subst l. split; reflexivity.
- destruct l as [|b l]; [change (skipn (S n) (@nil A)) with (@nil A) in H; discriminate H|].
  change (skipn (S n) (b :: l)) with (skipn n l) in H. exact (IH l x r H).
Qed.
Lemma cwi_cspn_le : forall set s, (PCspn.cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn; [lia|]. destruct (existsb _ _); lia. Qed.
Lemma cwi_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= PJn.join_need ws.
Proof.
induction ws as [|w ws IH]; [change (Z.of_nat 0 <= 0); lia|].
destruct ws as [|w2 ws2].
- change (Z.of_nat (length w) <= Z.of_nat (length w) + 1 + 0). lia.
- change (Z.of_nat (length (w ++ SPACE :: join_sp (w2 :: ws2))) <= Z.of_nat (length w) + 1 + PJn.join_need (w2 :: ws2)).
  rewrite length_app. change (length (SPACE :: join_sp (w2 :: ws2))) with (S (length (join_sp (w2 :: ws2)))). lia.
Qed.
Lemma cwi_al16 : forall sp1 sp0, sp1 mod 32 = 0 -> sp0 mod 16 = 0 -> (sp1 - sp0) mod 16 = 0.
Proof.
intros sp1 sp0 H1 H2. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
destruct H1 as [q1 Hq1]. destruct H2 as [q2 Hq2]. exists (2 * q1 - q2). lia.
Qed.
Lemma cwi_notin0 : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate. Qed.
Lemma cwi_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono x x' H1) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma cwi_fp_nil : forall a, fp_spares [] a.
Proof. intros a. apply fp_spares_closed; [intros (x & Hx & _); destruct Hx | apply inFP_nil]. Qed.

(* memory kept outside a window *)
Lemma cwi_aval_kept : forall rd rd' lo hi a (n : nat) v, kept_out rd rd' lo hi -> aval_mem rd a n v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v HK H Ha Hn Hw k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma cwi_bytes_kept : forall rd rd' lo hi p l, kept_out rd rd' lo hi -> abytes_atR rd p l ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 -> (p + Z.of_nat (length l) <= lo \/ hi <= p) -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hw i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma cwi_str_kept : forall rd rd' lo hi p s, kept_out rd rd' lo hi -> astr_atR rd p s ->
  0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 -> (p + Z.of_nat (length s) + 1 <= lo \/ hi <= p) ->
  astr_atR rd' p s.
Proof.
intros rd rd' lo hi p s HK [H1 H2] Hp Hl Hw. split; [|exact H2].
apply (cwi_bytes_kept rd rd' lo hi p _ HK H1 Hp); rewrite length_app; cbn [length]; lia.
Qed.
Lemma cwi_kept_run : forall E (rs : smem) H (m m' : word -> option byte) lo hi, rs = [] ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> kept_out (aview SEGS H m) (aview SEGS H m') lo hi.
Proof.
intros E rs H m m' lo hi Hrs Hf a Ha _. subst rs. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & _). destruct Hr.
Qed.
Lemma cwi_kept_run_ro : forall E (rs : smem) H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> kept_out (aview SEGS H m) (aview SEGS H m') lo hi.
Proof.
intros E rs H m m' lo hi Hf Hw a Ha _. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Hb). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Lemma cwi_kept_call : forall (W : world SEGS) (m m' : word -> option byte) sp0 o stk sp1, sp0 + o = sp1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ False -> rdW W m' a = rdW W m a) ->
  kept_out (rdW W m) (rdW W m') (sp1 - stk) sp1.
Proof. intros W m m' sp0 o stk sp1 Hs Hf a Ha Hn. apply Hf; [exact Ha | lia | tauto]. Qed.

(* registers *)
Ltac cwi_cs_tac := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.
Lemma cwi_pres_r : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Definition CWI_KR : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
Definition cwi_rk (regs' regs : bvmap 5 word) : Prop := forall r, In r CWI_KR -> getr regs' r = getr regs r.
Ltac cwi_in := cbn [CWI_KR In]; repeat (first [left; reflexivity | right]).
Lemma cwi_rk_trans : forall r1 r2 r3, cwi_rk r2 r1 -> cwi_rk r3 r2 -> cwi_rk r3 r1.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
Lemma cwi_rk_pres : forall regs regs', aregs_preserved regs regs' -> cwi_rk regs' regs.
Proof.
intros regs regs' HP r Hr. cbn [CWI_KR In] in Hr.
repeat (destruct Hr as [<-|Hr]; [apply cwi_pres_r; [exact HP | cwi_cs_tac]|]). destruct Hr.
Qed.
Lemma cwi_EE : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma cwi_add_val : forall E n m x v, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 v -> 0 <= x -> 0 <= v ->
  x + v < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + v).
Proof.
intros E n m x v Hn Hm Hx Hv Hxv. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)))) with (U E (SAlu ALU_ADD (SOff n 0) (SOff m 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn) by lia. rewrite (U_atom E m v Hm) by lia.
apply zcanon_id. unfold M64. lia.
Qed.

(* the fresh seed: the registers only *)
Definition cwi_Bx : sv := SOff 23 0.
Definition cwi_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cwi_G : facts := mkFacts [(23%nat, mkAF SB SB 0)] [] [].
Definition cwi_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None cwi_G.
Lemma cwi_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc, getr regs 23 = w64 CW_SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (cwi_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc H23. rewrite restrict_mkst_fx. unfold cwi_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- assert (E23 : ew (Eimg (Ereg regs [])) 23 = Z_to_bv 64 CW_SB) by (rewrite (cwi_EE regs 23 23%bv eq_refl); exact H23).
  split; [|split; exact I]. cbn [f_atoms atoms_ok cwi_G]. split; [|exact I].
  unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E23. rewrite unsigned_lit_small by (unfold CW_SB; lia).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold CW_SB, SB. repeat split; lia.
Qed.
Lemma cwi_sh0 : forall E m, sh_ok SEGS cwi_Bx [] E m.
Proof. intros E m. apply Forall_nil. Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the entry's premises the segment reads *)
Lemma cwi_ent : forall e, cw_ent B MT e ->
  afn_pre SEGS B CHECK_WORDS_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
  arodata_okP SEGS RLO RHI B (cw_rd0 e) /\ cmd_ro_ok (cw_rd0 e) /\
  rec_repA B (e_ly e) (e_S e) (cw_rd0 e) (e_R e) (e_O e) /\ words_prop_at atoi_a (e_R e) (e_ws e).
Proof.
intros e H. unfold cw_ent in H. cbv zeta in H.
destruct H as (H1 & _ & H3 & _ & H5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H17 & H18 & _).
split; [exact H1|]. split; [exact H3|]. split; [exact H5|]. split; [exact H17 | exact H18].
Qed.
Lemma cwi_call : forall e i fn args, cw_ent B MT e -> nth_error (r_calls (e_R e)) i = Some (fn, args) ->
  exists P, acall_at (ablocks B (e_ly e) (e_S e)) (cw_rd0 e) (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) (fn, args) P.
Proof.
intros e i fn args H Hi. destruct (cwi_ent e H) as (_ & _ & _ & HR & _).
destruct HR as (Q & (_ & _ & _ & (Hl & HlQ & _ & Hcalls & _) & _) & _).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP.
- exists P. exact (proj1 (Hcalls i (fn, args) P Hi HP)).
- exfalso. apply nth_error_None in HP.
  assert (Hlt : (i < length (r_calls (e_R e)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). lia.
Qed.
(* where the window of a wrapper call at sp1 lies, and where the own frame lies *)
Lemma cwi_jloc : forall e lyc Sc Wc memc mdc pos k sp1,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 ->
  alloc_ceiling + 4 * ESTACK <= sp1 /\ cw_sp0 e <= 2 ^ 47 /\ cw_sp0 e mod 16 = 0 /\
  4096 <= frame_addr (e_ly e) 0 pos /\ frame_addr (e_ly e) 0 pos + 64 <= alloc_ceiling.
Proof.
intros e lyc Sc Wc memc mdc pos k sp1 HJ Hsp.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & _).
assert (FB : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold frame_addr in F1, F2 |- *. rewrite EF in F1, F2. rewrite FB in F2.
repeat split; lia.
Qed.
(* the read-only bytes and rom view at a state the journal reaches *)
Lemma cwi_rom : forall e lyc Sc Wc memc mdc pos k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros e lyc Sc Wc memc mdc pos k Hent HJ. destruct (cwi_ent e Hent) as (_ & HROD & _).
pose proof (cmd_rom_view_on (e_W e) (e_mem e) HROD) as HR0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Ha Ho He. rewrite F3; [exact (HR0 a Ha Ho He) | | exact Ho | exact He | apply cwi_fp_nil].
destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.
Lemma cwi_lit_ready : forall e lyc Sc Wc memc mdc pos k p s j,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  In (p, Z.of_nat (length s) + 1) CW_ZSH -> p <> A_G_REC -> In (p + Z.of_nat (length s)) cmd_ro_ends ->
  astr_atR (cw_rd0 e) p s -> (j <= length s)%nat ->
  astr_at SEGS Wc memc (p + Z.of_nat j) (skipn j s) /\
  (forall regsT, alloc_ceiling <= spZ regsT - 2 * ESTACK ->
     aread_ok SEGS (2 * ESTACK) Wc regsT memc (p + Z.of_nat j) (astr_len (skipn j s) + 1)) /\
  atail_vis SEGS Wc memc (p + Z.of_nat j + astr_len (skipn j s)).
Proof.
intros e lyc Sc Wc memc mdc pos k p s j HJ Hz Hg He Hs Hj.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KEEP : forall i, 0 <= i < Z.of_nat (length s) + 1 -> rdW Wc memc (p + i) = cw_rd0 e (p + i)).
{ intros i Hi. destruct (cw_ro_unowned p (Z.of_nat (length s) + 1) i Hz Hg Hi) as (Himg & Hno & Herr).
  unfold cw_rd0. apply F3; [exact Himg | exact Hno | exact Herr | apply cwi_fp_nil]. }
assert (Hp : 0x10000 <= p /\ p + Z.of_nat (length s) + 1 <= 0x606000).
{ destruct (cw_ro_unowned p (Z.of_nat (length s) + 1) 0 Hz Hg ltac:(lia)) as (Himg & _).
  destruct (cw_ro_unowned p (Z.of_nat (length s) + 1) (Z.of_nat (length s)) Hz Hg ltac:(lia)) as (Himg2 & _).
  pose proof (pa_img_range _ Himg) as R1. pose proof (pa_img_range _ Himg2) as R2. lia. }
assert (HS0 : astr_atR (rdW Wc memc) p s).
{ destruct Hs as [Hb Hn]. split; [|exact Hn]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KEEP by lia. exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
pose proof (astr_atR_skipn _ p s j HS0 Hj) as HSj.
destruct (ZSH_cw lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) HAR Hz) as [RA HV].
assert (Hlen : astr_len (skipn j s) = Z.of_nat (length s) - Z.of_nat j) by (unfold astr_len; rewrite length_skipn; lia).
split; [apply (astr_atR_view SEGS); exact HSj|]. split.
- intros regsT HspT. unfold aread_ok. rewrite Hlen. split; [lia|]. split; [lia|]. split; [lia|]. split.
  + intros x Hx. split.
    * destruct HS0 as [Hb _]. replace x with (p + Z.of_nat (Z.to_nat (x - p))) by lia.
      rewrite (Hb (Z.to_nat (x - p))) by (rewrite length_app; cbn [length]; lia). discriminate.
    * unfold ascratch_stk. lia.
  + split; [unfold amem_range; left; lia|]. split.
    * eapply range_addressable_sub; [exact RA | lia | lia].
    * intros _. apply (cwi_hull_sub _ p (Z.of_nat (length s) + 1)); [exact HV | lia | lia | lia].
- rewrite Hlen. replace (p + Z.of_nat j + (Z.of_nat (length s) - Z.of_nat j)) with (p + Z.of_nat (length s)) by lia.
  exact (cmd_tail_vis lyc Sc Wc memc mdc _ HAR He).
Qed.

(* the templates: the item string of call fn at cw_tptr fn (CmdRo.v's literals) *)
Definition cwi_fns : list Z := map Z.of_nat (seq 0 26).
Lemma cwi_in_fns : forall fn, 0 <= fn < 26 -> In fn cwi_fns.
Proof. intros fn H. unfold cwi_fns. apply in_map_iff. exists (Z.to_nat fn). split; [lia|]. apply in_seq. lia. Qed.
Definition cwi_tplb (fn : Z) : bool :=
  existsb (fun p => (fst p =? cw_tptr fn) && (snd p =? Z.of_nat (length (cw_tpl fn)) + 1)) CW_ZSH &&
  negb (cw_tptr fn =? A_G_REC) &&
  existsb (Z.eqb (cw_tptr fn + Z.of_nat (length (cw_tpl fn)))) cmd_ro_ends &&
  (length (cw_tpl fn) <=? 8)%nat &&
  forallb (fun b => negb (bv_unsigned b =? 0)) (cw_tpl fn) &&
  (0x21000 <=? cw_tptr fn) && (cw_tptr fn <=? 0x22000).
Lemma cwi_tplb_all : forallb cwi_tplb cwi_fns = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cwi_tpl_facts : forall fn, 0 <= fn < 26 ->
  In (cw_tptr fn, Z.of_nat (length (cw_tpl fn)) + 1) CW_ZSH /\ cw_tptr fn <> A_G_REC /\
  In (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) cmd_ro_ends /\ (length (cw_tpl fn) <= 8)%nat /\
  ~ In (Z_to_bv 8 0) (cw_tpl fn) /\ 0x21000 <= cw_tptr fn <= 0x22000.
Proof.
intros fn Hfn. pose proof (proj1 (forallb_forall _ _) cwi_tplb_all fn (cwi_in_fns fn Hfn)) as H.
unfold cwi_tplb in H. repeat rewrite andb_true_iff in H.
destruct H as ((((((H1 & H2) & H3) & H4) & H5) & H6) & H7).
split.
{ apply existsb_exists in H1 as ([p1 p2] & Hp & Hpe). cbn [fst snd] in Hpe.
  apply andb_true_iff in Hpe as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst p1 p2. exact Hp. }
split; [apply negb_true_iff in H2; apply Z.eqb_neq in H2; exact H2|].
split; [exact (In_of_existsb _ _ H3)|].
split; [apply Nat.leb_le in H4; exact H4|].
split; [exact (cwi_notin0 _ H5)|].
apply Z.leb_le in H6. apply Z.leb_le in H7. lia.
Qed.
Lemma cwi_tpl_bytes : forall rd fn, cmd_ro_bytes rd -> 0 <= fn < 26 ->
  abytes_atR rd (cw_tptr fn) (cw_tpl fn ++ [Z_to_bv 8 0]).
Proof.
intros rd fn HB Hfn. unfold cmd_ro_bytes in HB.
repeat match type of HB with _ /\ _ => let H := fresh "Hb" in destruct HB as [H HB] end.
assert (Hc : fn = 0 \/ fn = 1 \/ fn = 2 \/ fn = 3 \/ fn = 4 \/ fn = 5 \/ fn = 6 \/ fn = 7 \/ fn = 8 \/ fn = 9 \/
  fn = 10 \/ fn = 11 \/ fn = 12 \/ fn = 13 \/ fn = 14 \/ fn = 15 \/ fn = 16 \/ fn = 17 \/ fn = 18 \/ fn = 19 \/
  fn = 20 \/ fn = 21 \/ fn = 22 \/ fn = 23 \/ fn = 24 \/ fn = 25) by lia.
repeat (destruct Hc as [Hc|Hc]; [subst fn|]); [..|subst fn];
lazymatch goal with |- abytes_atR _ (cw_tptr ?k) _ =>
  let v := eval vm_compute in (cw_tptr k) in
  match goal with H : abytes_atR _ ?a _ |- _ => constr_eq a v; exact H end end.
Qed.
Lemma cwi_lits : forall rd, cmd_ro_bytes rd -> astr_atR rd 0x21120 CW_SP1 /\ astr_atR rd 0x21280 [].
Proof.
intros rd HB. unfold cmd_ro_bytes in HB.
repeat match type of HB with _ /\ _ => let H := fresh "Hb" in destruct HB as [H HB] end.
split; (split; [|apply cwi_notin0; vm_compute; reflexivity]);
match goal with |- abytes_atR _ ?v _ => match goal with H : abytes_atR _ ?a _ |- _ => constr_eq a v; exact H end end.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the item loop's invariant, carried to a state the journal reaches with the same layout, state and world: the
   callee-saved registers the invariant names are the same, and the memory is the same outside the window of a
   wrapper call at sp1 (every address the invariant names is at or above sp1, or below alloc_ceiling) *)
Lemma cwi_icommon_move : forall e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args regs' mem' mdc',
  cw_icommon B MT e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem' mdc' EV_JOINED ->
  cwi_rk regs' regsc ->
  kept_out (rdW Wc memc) (rdW Wc mem') (sp1 - 2 * ESTACK) sp1 ->
  cw_icommon B MT e lyc Sc Wc regs' mem' mdc' pos sp1 line c a fn args.
Proof.
intros e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args regs' mem' mdc' HC HJ' HR HK.
destruct HC as (HCORE & HLINE & HLSCR & HCSCR & HIR & Hc & Hnth & Ha).
destruct HCORE as (HJ & Hsp & Hsp32 & Hsp1 & H3 & H4 & H8 & H9 & H23 & HSAV & V16 & V24 & V32 & V152 & V56 & S4 & S5).
destruct (cwi_jloc e lyc Sc Wc mem' mdc' pos EV_JOINED sp1 HJ' Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
pose proof (proj1 HJ') as HAR'.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & _).
unfold cw_icommon, cw_core. cbv zeta.
set (F := frame_addr (e_ly e) 0 pos) in *. clearbody F.
assert (F8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
remember (F / 8) as fq eqn:Hfq in *. clear Hfq.
pose proof (HR 2%bv ltac:(cwi_in)) as R2. pose proof (HR 3%bv ltac:(cwi_in)) as R3.
pose proof (HR 4%bv ltac:(cwi_in)) as R4. pose proof (HR 8%bv ltac:(cwi_in)) as R8.
pose proof (HR 9%bv ltac:(cwi_in)) as R9. pose proof (HR 19%bv ltac:(cwi_in)) as R19.
pose proof (HR 20%bv ltac:(cwi_in)) as R20. pose proof (HR 23%bv ltac:(cwi_in)) as R23.
pose proof (HR 24%bv ltac:(cwi_in)) as R24. pose proof (HR 25%bv ltac:(cwi_in)) as R25.
pose proof (HR 26%bv ltac:(cwi_in)) as R26. pose proof (HR 27%bv ltac:(cwi_in)) as R27.
(* the line block lies below alloc_ceiling *)
pose proof HLINE as (HPL & Hl4096 & HAP & HLB & HMO).
assert (HLL : line + Z.of_nat (length (join_sp (e_ws e) ++ [Z_to_bv 8 0])) <= alloc_ceiling).
{ assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem' mdc' line (cw_JN e) HAR' Hin) as (_ & _ & Hce & _ & _ & _ & HJN).
  pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [_ Hrq]. pose proof (cwi_join_len (e_ws e)) as HJL.
  unfold cw_JN in *. rewrite length_app. cbn [length]. lia. }
split.
{ split; [exact HJ'|]. split; [unfold spZ in Hsp |- *; rewrite R2; exact Hsp|].
  split; [exact Hsp32|]. split; [exact Hsp1|].
  split; [rewrite R3; exact H3|]. split; [rewrite R4; exact H4|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R23; exact H23|].
  split.
  { intros j r Hj. pose proof (HSAV j r Hj) as Hv.
    assert (Hjl : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length cw_saved) with 13%nat in Hjl.
    apply (cwi_aval_kept _ _ _ _ _ _ _ HK Hv); lia. }
  split; [apply (cwi_aval_kept _ _ _ _ _ _ _ HK V16); lia|].
  split; [apply (cwi_aval_kept _ _ _ _ _ _ _ HK V24); lia|].
  split; [apply (cwi_aval_kept _ _ _ _ _ _ _ HK V32); lia|].
  split; [apply (cwi_aval_kept _ _ _ _ _ _ _ HK V152); lia|].
  split; [apply (cwi_aval_kept _ _ _ _ _ _ _ HK V56); lia|].
  split; [rewrite (HK _) by (unfold CW_SB; lia); exact S4 | rewrite (HK _) by (unfold CW_SB; lia); exact S5]. }
split.
{ split; [exact HPL|]. split; [exact Hl4096|]. split; [exact HAP|]. split; [|exact HMO].
  apply (cwi_bytes_kept _ _ _ _ _ _ HK HLB); lia. }
split.
{ destruct HLSCR as (L144 & L8 & L40 & L48 & L56 & L64 & L72 & L88 & L96 & L104 & L128 & L136).
  repeat split; apply (cwi_aval_kept _ _ _ _ _ _ _ HK); first [eassumption | lia]. }
split.
{ destruct HCSCR as (C80 & C112 & C120).
  repeat split; apply (cwi_aval_kept _ _ _ _ _ _ _ HK); first [eassumption | lia]. }
split.
{ destruct HIR as (I19 & I20 & I25 & I26 & I27 & I24).
  split; [rewrite R19; exact I19|]. split; [rewrite R20; exact I20|]. split; [rewrite R25; exact I25|].
  split; [rewrite R26; exact I26|]. split; [rewrite R27; exact I27 | rewrite R24; exact I24]. }
split; [exact Hc|]. split; [exact Hnth | exact Ha].
Qed.
Lemma cwi_wsrc_move : forall e lyc Sc Wc memc mdc mem' pos sp1 line q y k,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  cw_wsrc B e lyc Sc (rdW Wc memc) pos line q y ->
  kept_out (rdW Wc memc) (rdW Wc mem') (sp1 - 2 * ESTACK) sp1 ->
  cw_wsrc B e lyc Sc (rdW Wc mem') pos line q y.
Proof.
intros e lyc Sc Wc memc mdc mem' pos sp1 line q y k HJ Hsp1 HLINE (Hs & Hq & Hcase) HK.
destruct (cwi_jloc e lyc Sc Wc memc mdc pos k sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
pose proof (proj1 HJ) as HAR.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof HLINE as (HPL & Hl4096 & _).
assert (HB : q + Z.of_nat (length y) + 1 <= alloc_ceiling /\ 0 <= q).
{ destruct Hcase as [(-> & ->) | [(-> & ->) | [(-> & Hy) | (kk & Hk & -> & -> & Hblk)]]].
  - assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc))
      by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc line (cw_JN e) HAR Hin) as (_ & _ & Hce & _ & _ & _ & HJN).
    pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [_ Hrq]. pose proof (cwi_join_len (e_ws e)) as HJL.
    unfold cw_JN in *. lia.
  - cbn [length]. lia.
  - lia.
  - destruct Hblk as (bp & bk & Hin & Hb1 & Hb2).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bp bk HAR Hin) as (_ & Hb4096 & Hce & _ & _ & _ & Hbk).
    pose proof (req_size_pos bk ltac:(lia)) as [_ Hrq]. lia. }
split; [apply (cwi_str_kept _ _ _ _ _ _ HK Hs); lia|]. split; [exact Hq | exact Hcase].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* seg_I3a: 0x87bfc mv a0,s2; mv a1,s8; jal strcspn; 0x87c08 add s2,s2,a0 -> ICMP2 *)
Lemma seg_I3a : forall c a, ST_ICMP2 B MT c a -> ST_ICMP B MT c a.
Proof.
intros c a HC2. unfold ST_ICMP. intros e lyc Sc Wc regsc memc mdc pos sp1 line j1 q y Hent HI.
destruct HI as (fn & args & HCOM & Hj1 & H18 & Hparse & H21 & Hsrc & Hwant).
pose proof HCOM as (HCORE & HLINE & _ & _ & HIR & Hc & Hnth & Ha).
pose proof HCORE as (HJ & Hsp & Hsp32 & Hsp1 & H3 & H4 & _ & _ & H23 & _).
pose proof HIR as (_ & _ & _ & _ & _ & H24).
destruct (cwi_ent e Hent) as (HPRE & HROD & HRO & _ & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
destruct (cwi_call e (Z.to_nat c) fn args Hent Hnth) as (P & HP0 & _).
cbn [fst] in HP0. unfold REC_FN_COUNT in HP0.
destruct (cwi_jloc e lyc Sc Wc memc mdc pos EV_JOINED sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & _).
destruct (cwi_tpl_facts fn HP0) as (Tz & Tg & Te & T8 & T0 & Tb).
assert (TS : astr_atR (cw_rd0 e) (cw_tptr fn) (cw_tpl fn)) by (split; [exact (cwi_tpl_bytes _ fn (proj1 HRO) HP0) | exact T0]).
destruct (cwi_lits (cw_rd0 e) (proj1 HRO)) as [SPS _].
pose proof (cwi_cspn_le CW_SP1 (skipn j1 (cw_tpl fn))) as Hcs. rewrite length_skipn in Hcs.
unfold cw_at, CW_PC_ICMP.
pose proof (cwi_seed0 Wc regsc memc 0x1718 H23) as HS.
pose proof (cwi_sh0 (Eimg (Ereg regsc [])) (mrestrict (w_H Wc) memc)) as SHOK.
pose proof (Eimg_env (Ereg regsc [])) as HEI.
pose proof (cwi_EE regsc) as EE.
assert (HAE : env_agree 32 (Ereg regsc []) (Eimg (Ereg regsc []))) by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regsc [])) as E0 eqn:HE0 in *. clear HE0.
paj_run_tok RUN HS HJ SHOK cwi_Bspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regsc [] HS HAE ltac:(vm_compute; reflexivity)) as HPT;
  cbn [ms_regs restrict] in HPT;
  assert (HspT : spZ (ms_regs ms) = sp1) by (unfold spZ in Hsp |- *; rewrite Qsp, (EE 2%nat 2%bv eq_refl); exact Hsp);
  destruct (cwi_lit_ready e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED (cw_tptr fn) (cw_tpl fn) j1 HJ Tz Tg Te TS Hj1)
    as (Sx & Rx & Tx);
  destruct (cwi_lit_ready e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED 0x21120 CW_SP1 0 HJ
    ltac:(unfold CW_ZSH; cbn [In]; right; right; left; reflexivity) ltac:(unfold A_G_REC; lia)
    ltac:(apply In_of_existsb; vm_compute; reflexivity) SPS ltac:(cbn; lia)) as (Sy & Ry & Ty);
  pmkst HS;
  eapply SRr_bind;
  [ apply (aj_strcspn_at B LAWS TL cmd_rec_cells (SIG CS___interceptor_trampoline_strcspn) ASTRCSPN Wc (ms_regs ms) (ms_mem ms)
      CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)] lyc Sc mdv EV_JOINED
      (cw_tptr fn + Z.of_nat j1) 0x21120 (skipn j1 (cw_tpl fn)) CW_SP1 (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + 5924)) HJ);
    [ rewrite Ra0, (EE 18%nat 18%bv eq_refl); exact H18
    | rewrite Ra1, (EE 24%nat 24%bv eq_refl); exact H24
    | lia | lia | lia | exact (cwi_al16 _ _ Hsp32 H16) | lia | rewrite WS, Hes; lia
    | rewrite Qgp, (EE 3%nat 3%bv eq_refl), H3; exact Hgp
    | rewrite Qtp, (EE 4%nat 4%bv eq_refl), H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Sx | exact Sy
    | apply Rx; rewrite HspT, Hes; lia
    | (* the item's band (+ 8): a g_call_words literal in .rodata, low band (band-premise survey, call site 9) *)
      (pose proof asan_consts as (_ & _ & _ & _ & C5x); unfold amem_range, astr_len; rewrite length_skipn; left;
       rewrite C5x; lia)
    | apply Ry; rewrite HspT, Hes; lia
    | (* the set " " at 0x21120, .rodata, low band *)
      (change (astr_len CW_SP1 + 8) with 9; pose proof asan_consts as (_ & _ & _ & _ & C5x); unfold amem_range; left;
       rewrite C5x; lia)
    | exact Tx | exact Ty
    | exact (cwi_rom e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED Hent HJ) ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcs2 & Hfr2).
(* back at 0x87c08: the memory kept outside [sp1 - 2 ESTACK, sp1), the callee-saved registers *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  pose proof (cwi_kept_call Wc (ms_mem ms) mem2 (cw_sp0 e) (sp1 - cw_sp0 e) (2 * ESTACK) sp1 ltac:(lia) Hfr2) as KEEP2 end.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (cwi_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP1 end.
pose proof (cwi_rk_pres _ _ HPT) as RK1. pose proof (cwi_rk_pres _ _ HP2) as RK2.
pose proof (aregs_preserved_trans _ _ _ HPT HP2) as HP12.
assert (H18b : getr regs2 18 = w64 (cw_tptr fn + Z.of_nat j1))
  by (rewrite (cwi_pres_r _ _ 18%bv HP12 ltac:(cwi_cs_tac)); exact H18).
assert (H23b : getr regs2 23 = w64 CW_SB) by (rewrite (RK2 23%bv ltac:(cwi_in)), (RK1 23%bv ltac:(cwi_in)); exact H23).
clear HS SHOK HEI EE HAE.
pose proof (cwi_seed0 Wc regs2 mem2 0x1724 H23b) as HS.
pose proof (cwi_sh0 (Eimg (Ereg regs2 [])) (mrestrict (w_H Wc) mem2)) as SHOK.
pose proof (Eimg_env (Ereg regs2 [])) as HEI.
pose proof (cwi_EE regs2) as EE2.
assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 [])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2 in *. clear HE2.
(* 0x87c08 add s2,s2,a0, to ICMP2 *)
paj_run_to_tok RUNTO HS HJ2 SHOK cwi_Bspan 0x1728; [awr_ok_tac |].
set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) _ |- _ =>
  pose proof (cwi_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP3 end.
pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3
  ltac:(lia) ltac:(lia)) as KEEP.
pose proof HCOM as ((HJ0 & _) & _).
assert (Hsk : skipn (Z.to_nat a) (PCW.call_items fn) =
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn))) (skipn j1 (cw_tpl fn))))
  by (symmetry; exact Hparse).
destruct (cwi_skipn_cons _ _ _ _ Hsk) as [Hit Hrest].
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- _ =>
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [] CWI_KR HS HAE2 ltac:(vm_compute; reflexivity)) as RK3;
  cbn [ms_regs restrict] in RK3;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ (18%bv : bv 5) HS) as R18;
  let ev := eval vm_compute in (sr_get (ss_regs ss) (18%bv : bv 5)) in
  change (sr_get (ss_regs ss) (18%bv : bv 5)) with ev in R18;
  cbn [ms_regs restrict] in R18;
  pose proof (cwi_rk_trans _ _ _ (cwi_rk_trans _ _ _ RK1 RK2) RK3) as RK;
  assert (R18' : getr (ms_regs ms) 18 =
    w64 (cw_tptr fn + Z.of_nat (j1 + PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))));
  [ (* the engine leaves x18 = SAlu ALU_ADD (SOff 10 0) (SOff 18 0) *)
    rewrite R18, (cwi_add_val _ 10 18 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) (cw_tptr fn + Z.of_nat j1));
    [ unfold w64; f_equal; lia
    | rewrite (EE2 10%nat 10%bv eq_refl); exact Hcs2
    | rewrite (EE2 18%nat 18%bv eq_refl); exact H18b
    | lia | lia | lia ]
  | ];
  assert (INV2 : INV_ICMP2 B MT e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv2 pos sp1 line c a
    (j1 + PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))%nat q y);
  [ exists fn, args, (item_of_a (skipn j1 (cw_tpl fn)));
    split; [exact (cwi_icommon_move e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args (ms_regs ms) (ms_mem ms) mdv2
                     HCOM HJ2 RK KEEP)|];
    split; [lia|]; split; [exact R18'|]; split; [exact Hit|];
    split; [rewrite Hrest; f_equal; rewrite skipn_skipn; f_equal; lia|];
    split; [rewrite (RK 21%bv ltac:(cwi_in)); exact H21|];
    split; [exact (cwi_wsrc_move e lyc Sc Wc memc mdc (ms_mem ms) pos sp1 line q y EV_JOINED HJ0 Hsp1 HLINE Hsrc KEEP)
           | exact Hwant]
  | ];
  pmkst HS;
  exact (HC2 e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv2 pos sp1 line
    (j1 + PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))%nat q y Hent INV2) end.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* segment I3b's reads: the recorded argument (record + journal), the compared strings at the call *)
Lemma cwi_ncalls : forall e, cw_ent B MT e -> cw_ncalls e <= 16.
Proof.
intros e H. destruct (cwi_ent e H) as (_ & _ & _ & HR & _).
destruct HR as (Q & (_ & _ & _ & (Hl & _) & _) & _). unfold cw_ncalls. lia.
Qed.
Lemma cwi_grec_kept : forall e lyc Sc Wc memc mdc pos k a,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  A_G_REC <= a < A_G_REC + 960 -> rdW Wc memc a = cw_rd0 e a.
Proof.
intros e lyc Sc Wc memc mdc pos k a HJ Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Hpg : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; lia]).
destruct (cmd_prog_unowned a Hpg) as (Himg & Hno & Herr).
unfold cw_rd0. apply F3; [exact Himg | exact Hno | exact Herr | apply cwi_fp_nil].
Qed.
Lemma cwi_arg : forall e c fn args a, cw_ent B MT e -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) ->
  0 <= c -> 0 <= a < Z.of_nat (length args) ->
  exists s pb pk, nth_error args (Z.to_nat a) = Some s /\
    aval_mem (cw_rd0 e) (A_G_REC + 16 + 56 * c + 8 + 8 * a) 8 pb /\ pb <> 0 /\
    In (pb, pk) (ablocks B (e_ly e) (e_S e)) /\ Z.of_nat (length s) + 1 <= pk /\ astr_atR (cw_rd0 e) pb s /\
    (length args <= 6)%nat.
Proof.
intros e c fn args a Hent Hnth Hc Ha.
destruct (cwi_call e (Z.to_nat c) fn args Hent Hnth) as (P & (_ & Hl6 & HlP & _ & _ & _ & Hargs)).
change (snd (fn, args)) with args in Hl6, HlP, Hargs.
destruct (nth_error args (Z.to_nat a)) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
destruct (nth_error P (Z.to_nat a)) as [[pb pk]|] eqn:Hp; [|apply nth_error_None in Hp; lia].
destruct (Hargs (Z.to_nat a) s (pb, pk) Hs Hp) as (Hv & Hnz & Hin & (Hlen & _) & Hstr).
exists s, pb, pk. split; [reflexivity|].
split; [|split; [exact Hnz|split; [exact Hin|split; [exact Hlen|split; [exact Hstr | exact Hl6]]]]].
replace (A_G_REC + 16 + 56 * c + 8 + 8 * a) with
  (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_ARGS + 8 * Z.of_nat (Z.to_nat a))
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS; rewrite !Z2Nat.id by lia; lia).
exact Hv.
Qed.
Lemma cwi_words_eq : forall e c fn args a s it y, cw_ent B MT e ->
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) -> nth_error args (Z.to_nat a) = Some s ->
  nth_error (PCW.call_items fn) (Z.to_nat a) = Some it -> want_at atoi_a (cw_read e) (e_ws e) it = Some y -> s = y.
Proof.
intros e c fn args a s it y Hent Hnth Hs Hit Hw. destruct (cwi_ent e Hent) as (_ & _ & _ & _ & HW).
unfold words_prop_at in HW. cbv zeta in HW. rewrite Forall_forall in HW.
pose proof (HW (fn, args) (nth_error_In _ _ Hnth)) as Hc. unfold call_words_ok_at in Hc.
destruct Hc as (Hc1 & _). exact (Hc1 (Z.to_nat a) it s Hs Hit y Hw).
Qed.
(* a string inside a heap block live at the entry and at the current state *)
Lemma cwi_blk_str : forall e lyc Sc Wc memc mdc pos k b n p s,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  In (b, n) (ablocks B (e_ly e) (e_S e)) -> In (b, n) (ablocks B lyc Sc) ->
  b <= p -> p + Z.of_nat (length s) + 1 <= b + n -> astr_atR (cw_rd0 e) p s -> astr_atR (rdW Wc memc) p s.
Proof.
intros e lyc Sc Wc memc mdc pos k b n p s HJ Hin0 Hin1 Hb Hn [Hs Hnul].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
split; [|exact Hnul]. intros i Hi. rewrite length_app in Hi. change (length [Z_to_bv 8 0]) with 1%nat in Hi.
replace (p + Z.of_nat i) with (b + (p + Z.of_nat i - b)) by lia.
rewrite (F2 b n (p + Z.of_nat i - b) Hin0 Hin1 ltac:(lia) (inFP_nil _)).
replace (b + (p + Z.of_nat i - b)) with (p + Z.of_nat i) by lia.
apply Hs. rewrite length_app. change (length [Z_to_bv 8 0]) with 1%nat. lia.
Qed.
Lemma cwi_blk_ready : forall lyc Sc Wc memc mdc b n p s,
  AR SEGS B lyc Sc Wc memc mdc -> In (b, n) (ablocks B lyc Sc) ->
  b <= p -> p + Z.of_nat (length s) + 1 <= b + n -> astr_atR (rdW Wc memc) p s ->
  0 < p /\ astr_at SEGS Wc memc p s /\
  (forall regsT, alloc_ceiling <= spZ regsT - 2 * ESTACK ->
     aread_ok SEGS (2 * ESTACK) Wc regsT memc p (astr_len s + 1)) /\
  atail_vis SEGS Wc memc (p + astr_len s).
Proof.
intros lyc Sc Wc memc mdc b n p s HAR Hin Hb Hn Hs.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin) as (_ & Hb4096 & _ & _ & _ & _ & Hn0).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
split; [lia|]. split; [apply (astr_atR_view SEGS); exact Hs|]. split.
- intros regsT HspT. unfold astr_len.
  exact (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc regsT memc mdc b n p (Z.of_nat (length s) + 1) HAR Hin Hb
    ltac:(lia) ltac:(lia) HspT).
- unfold astr_len. exact (cmd_heap_tail_vis lyc Sc Wc memc mdc b n (p + Z.of_nat (length s)) HAR Hin ltac:(lia)).
Qed.
(* number[16] of the own frame, at F + 32 *)
Lemma cwi_frame_ready : forall e lyc Sc Wc memc mdc pos k y,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) = Some 0 ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) = Some 0 ->
  astr_atR (rdW Wc memc) (frame_addr (e_ly e) 0 pos + 32) y -> (length y < 16)%nat ->
  0 < frame_addr (e_ly e) 0 pos + 32 /\ astr_at SEGS Wc memc (frame_addr (e_ly e) 0 pos + 32) y /\
  (forall regsT, alloc_ceiling <= spZ regsT - 2 * ESTACK ->
     aread_ok SEGS (2 * ESTACK) Wc regsT memc (frame_addr (e_ly e) 0 pos + 32) (astr_len y + 1)) /\
  atail_vis SEGS Wc memc (frame_addr (e_ly e) 0 pos + 32 + astr_len y).
Proof.
intros e lyc Sc Wc memc mdc pos k y HJ S4 S5 Hy Hly.
pose proof HJ as (HAR & Hlyl & _ & _ & _ & Hfrs & _).
pose proof Hlyl as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (FEQ : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (FB : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & Fapp).
first [ destruct (frame_al64 SEGS B lyc Sc Wc memc mdc 0 pos HAR Hin) as (F64 & _)
      | destruct (frame_al64 SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F64 & _) ].
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (_ & _ & Fpres & _).
first [ pose proof (fun d n H1 H2 H3 => shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memc mdc 0 pos d n HAR Hin H1 H2 H3) as FHV
      | pose proof (fun d n H1 H2 H3 => shadow_hull_vis_of_frame SEGS B lyc Sc Wc memc mdc 0 pos d n HAR Hin H1 H2 H3) as FHV ].
rewrite FEQ in F1, F2, Fapp, F64, Fpres, FHV. rewrite FB in F2, Fapp, Fpres, FHV.
set (F := frame_addr (e_ly e) 0 pos) in *. clearbody F.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; pose proof (Z.div_mod F 8 ltac:(lia)) as D8;
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HD4 : (F + 32) / 8 = F / 8 + 4) by (rewrite HF8; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia;
  rewrite Z.div_mul by lia; replace (8 * (F / 8)) with ((F / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (Hl : Z.of_nat (length y) <= 15) by lia.
unfold astr_len. split; [lia|]. split; [apply (astr_atR_view SEGS); exact Hy|]. split.
- intros regsT HspT. unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
  + intros x Hx. split.
    * destruct Hy as [Hb _]. replace x with (F + 32 + Z.of_nat (Z.to_nat (x - (F + 32)))) by lia.
      rewrite (Hb (Z.to_nat (x - (F + 32)))) by (rewrite length_app; change (length [Z_to_bv 8 0]) with 1%nat; lia).
      discriminate.
    * unfold ascratch_stk. lia.
  + split.
    { unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp. unfold amem_range.
      destruct Fapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia. }
    split.
    { apply (range_addressable_sub _ _ (F + 32) 16); [| lia | lia].
      apply zero_shadow_range; [rewrite HF8; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia; apply Z_mod_mult
                               | reflexivity |].
      intros i Hi. change (16 / 8) with 2 in Hi. unfold shadow_of_addr. rewrite HD4.
      assert (Hi2 : i = 0 \/ i = 1) by lia.
      destruct Hi2 as [-> | ->].
      - replace (SHADOW_OFF + (F / 8 + 4) + 0) with (CW_SB + F / 8 + 4) by (unfold CW_SB, SHADOW_OFF; lia). exact S4.
      - replace (SHADOW_OFF + (F / 8 + 4) + 1) with (CW_SB + F / 8 + 5) by (unfold CW_SB, SHADOW_OFF; lia). exact S5. }
    intros _. apply FHV; lia.
- intros x Hx. apply (aview_some_of_apresent SEGS). apply (proj1 (Fpres x ltac:(
    pose proof (Z.div_mod (F + 32 + Z.of_nat (length y)) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length y)) 8 ltac:(lia)); lia))).
Qed.
Lemma cwi_wsrc_ready : forall e lyc Sc Wc memc mdc pos line q y k,
  cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) = Some 0 ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) = Some 0 ->
  cw_wsrc B e lyc Sc (rdW Wc memc) pos line q y ->
  0 < q /\ astr_at SEGS Wc memc q y /\
  (forall regsT, alloc_ceiling <= spZ regsT - 2 * ESTACK ->
     aread_ok SEGS (2 * ESTACK) Wc regsT memc q (astr_len y + 1)) /\
  atail_vis SEGS Wc memc (q + astr_len y).
Proof.
intros e lyc Sc Wc memc mdc pos line q y k Hent HJ HLINE S4 S5 (Hs & Hq & Hcase).
pose proof (proj1 HJ) as HAR. pose proof HLINE as (HPL & _).
destruct Hcase as [(-> & ->) | [(-> & ->) | [(-> & Hy) | (kk & Hk & -> & -> & Hblk)]]].
- assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
  pose proof (cwi_join_len (e_ws e)) as HJL.
  apply (cwi_blk_ready lyc Sc Wc memc mdc line (cw_JN e) line (join_sp (e_ws e)) HAR Hin); [lia | unfold cw_JN; lia | exact Hs].
- destruct (cwi_ent e Hent) as (_ & _ & HRO & _).
  destruct (cwi_lits (cw_rd0 e) (proj1 HRO)) as [_ HE].
  destruct (cwi_lit_ready e lyc Sc Wc memc mdc pos k 0x21280 [] 0 HJ
    ltac:(unfold CW_ZSH; cbn [In]; right; right; right; left; reflexivity) ltac:(unfold A_G_REC; lia)
    ltac:(apply In_of_existsb; vm_compute; reflexivity) HE ltac:(cbn; lia)) as (Sx & Rx & Tx).
  split; [lia|]. exact (conj Sx (conj Rx Tx)).
- exact (cwi_frame_ready e lyc Sc Wc memc mdc pos k y HJ S4 S5 Hs Hy).
- destruct Hblk as (bp & bk & Hin & Hb1 & Hb2).
  exact (cwi_blk_ready lyc Sc Wc memc mdc bp bk (nth kk (e_wp e) 0) (nth kk (e_ws e) []) HAR Hin Hb1 ltac:(lia) Hs).
Qed.
(* the fresh seed at 0x1728: the registers, and the slot &args[a] (atom 32 = args[a]) *)
Lemma cwi_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Definition cwi_rg25 : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition cwi_GB : facts := mkFacts [(20%nat, mkAF A_G_REC (A_G_REC + 960) 3); (23%nat, mkAF SB SB 0);
  (25%nat, mkAF A_G_REC (A_G_REC + 960) 3)] [] [].
Definition cwi_SHB : list shent := [mkSHE 20 0 8].
Definition cwi_ssB : sstate := mkSS 0x1728 sr_atoms [cwi_rg25] None cwi_GB.
Lemma cwi_seedB : forall (W : world SEGS) (regs : bvmap 5 word) mem s4 p,
  getr regs 23 = w64 CW_SB -> getr regs 20 = w64 s4 -> getr regs 25 = w64 s4 ->
  A_G_REC <= s4 -> s4 + 8 <= A_G_REC + 960 -> s4 mod 8 = 0 -> 0 <= p < 2 ^ 64 ->
  aval_mem (rdW W mem) s4 8 p -> range_addressable (rdW W mem) SHADOW_OFF A_G_REC 960 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 p])) cwi_ssB
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1728)) mem (seg_rom SEGS))) /\
  sh_ok SEGS cwi_Bx cwi_SHB (Eimg (Ereg regs [Z_to_bv 64 p])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s4 p H23 H20 H25 Hs1 Hs2 Hs3 Hp V RA.
assert (HG : A_G_REC = 6174528) by reflexivity.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [Z_to_bv 64 p])) n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 p])) 32 = Z_to_bv 64 p)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 p] 0)).
set (E := Eimg (Ereg regs [Z_to_bv 64 p])) in *.
assert (E20 : ew E 20 = Z_to_bv 64 s4) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E25 : ew E 25 = Z_to_bv 64 s4) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
assert (E23 : ew E 23 = Z_to_bv 64 SB) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold cwi_ssB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold cwi_rg25, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 25%nat s4 E25) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ s4 0 8 (SOff 32 0) p);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (cwi_val_of_aval _ _ _ _ _ V).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok cwi_GB]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E20, E23, E25. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SB.
    repeat split; lia.
- unfold sh_ok, cwi_SHB. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E cwi_Bx 20 A_G_REC 960 s4 0 8 RA).
  + unfold cwi_Bx. rewrite (U_atom E 23 SB E23) by (unfold SB; lia). reflexivity.
  + exact (U_atom E 20 s4 E20 ltac:(lia)).
  + lia. + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* seg_I3b: 0x87c0c the check of &args[a] (removed by the seed's shadow entry), ld a0,0(s9), beqz a0 -> abort,
   mv a1,s5, jal strcmp; 0x87c2c bnez a0 -> abort; IL *)
Lemma seg_I3b : forall c a, ST_IL B MT c a -> ST_ICMP2 B MT c a.
Proof.
intros c a HIL. unfold ST_ICMP2. intros e lyc Sc Wc regsc memc mdc pos sp1 line j2 q y Hent HI.
destruct HI as (fn & args & it & HCOM & Hj2 & H18 & Hit & Hparse & H21 & Hsrc & Hwant).
pose proof HCOM as (HCORE & HLINE & _ & _ & HIR & Hc & Hnth & Ha).
pose proof HCORE as (HJ & Hsp & Hsp32 & Hsp1 & H3 & H4 & _ & _ & H23 & _).
pose proof HJ as HJ0.
pose proof HIR as (_ & H20 & H25 & _ & _ & _).
destruct (cwi_ent e Hent) as (HPRE & _ & _ & _ & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & _).
pose proof (cwi_ncalls e Hent) as Hnc. unfold cw_ncalls in Hnc, Hc.
destruct (cwi_arg e c fn args a Hent Hnth ltac:(lia) Ha) as (s & pb & pk & Hs & Hv0 & Hnz & Hin0 & Hlen & Hstr0 & Hl6).
pose proof (cwi_words_eq e c fn args a s it y Hent Hnth Hs Hit Hwant) as Hsy.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pk HAR0 Hin0) as (_ & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (req_size_pos pk ltac:(lia)) as [_ Hrq].
destruct (cwi_jloc e lyc Sc Wc memc mdc pos EV_JOINED sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & _).
pose proof HLINE as (HPL & _).
assert (Hin1 : In (pb, pk) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hin0).
assert (Hs4 : A_G_REC <= A_G_REC + 16 + 56 * c + 8 + 8 * a /\ A_G_REC + 16 + 56 * c + 8 + 8 * a + 8 <= A_G_REC + 960 /\
  (A_G_REC + 16 + 56 * c + 8 + 8 * a) mod 8 = 0).
{ split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
  replace (A_G_REC + 16 + 56 * c + 8 + 8 * a) with ((771819 + 7 * c + a) * 8) by (unfold A_G_REC; lia).
  apply Z_mod_mult. }
assert (Hv : aval_mem (rdW Wc memc) (A_G_REC + 16 + 56 * c + 8 + 8 * a) 8 pb).
{ intros kk Hk. rewrite (cwi_grec_kept e lyc Sc Wc memc mdc pos EV_JOINED _ HJ) by lia. exact (Hv0 kk Hk). }
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 (proj1 HJ) ltac:(unfold CW_ZSH; left; reflexivity)) as [RA _].
unfold cw_at, CW_PC_ICMP2.
destruct Hs4 as (Hs4a & Hs4b & Hs4c).
destruct (cwi_seedB Wc regsc memc (A_G_REC + 16 + 56 * c + 8 + 8 * a) pb H23 H20 H25
  Hs4a Hs4b Hs4c ltac:(lia) Hv RA) as [HS SHOK].
pose proof (Eimg_env (Ereg regsc [Z_to_bv 64 pb])) as HEI.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regsc [Z_to_bv 64 pb])) n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew (Eimg (Ereg regsc [Z_to_bv 64 pb])) 32 = Z_to_bv 64 pb)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc [Z_to_bv 64 pb] 0)).
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 pb]) (Eimg (Ereg regsc [Z_to_bv 64 pb])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regsc [Z_to_bv 64 pb])) as E1 eqn:HE1 in *. clear HE1.
(* to the null test of args[a] *)
paj_run_tok RUN HS HJ SHOK cwi_Bspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (cwi_kept_run_ro _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HFr) as KEEP1;
  specialize (KEEP1 ltac:(vm_compute; reflexivity)); clear HFr end.
psrr_branch_tok RUN BR HS SHOK cwi_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_eq_U in Hc; apply Z.eqb_eq in Hc;
    rewrite (U_atom _ 32 pb E32) in Hc by lia; change (U _ (SLit 0)) with 0 in Hc end.
  lia. }
(* args[a] <> 0: to the strcmp call *)
paj_run_tok RUN HS HJ SHOK cwi_Bspan; [awr_ok_tac |].
set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi_kept_run_ro _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HFr) as KEEP2;
  specialize (KEEP2 ltac:(vm_compute; reflexivity)); clear HFr end.
pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) as KEEP12.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regsc [Z_to_bv 64 pb] HS HAE ltac:(vm_compute; reflexivity)) as HPT;
  cbn [ms_regs restrict] in HPT;
  assert (HspT : spZ (ms_regs ms) = sp1) by (unfold spZ in Hsp |- *; rewrite Qsp, (EE 2%nat 2%bv eq_refl); exact Hsp);
  pose proof (cwi_icommon_move e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args (ms_regs ms) (ms_mem ms) mdv1
    HCOM HJ (cwi_rk_pres _ _ HPT) KEEP12) as HCOM1;
  pose proof (cwi_wsrc_move e lyc Sc Wc memc mdc (ms_mem ms) pos sp1 line q y EV_JOINED HJ0 Hsp1 HLINE Hsrc KEEP12) as HSRC1;
  pose proof HCOM1 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S4 & S5) & HLINE1 & _);
  destruct (cwi_wsrc_ready e lyc Sc Wc (ms_mem ms) mdv1 pos line q y EV_JOINED Hent HJ HLINE1 S4 S5 HSRC1)
    as (Hq0 & Sy & Ry & Ty);
  pose proof (cwi_blk_str e lyc Sc Wc (ms_mem ms) mdv1 pos EV_JOINED pb pk pb s HJ Hin0 Hin1 ltac:(lia) ltac:(lia) Hstr0)
    as Hstr1;
  destruct (cwi_blk_ready lyc Sc Wc (ms_mem ms) mdv1 pb pk pb s (proj1 HJ) Hin1 ltac:(lia) ltac:(lia) Hstr1)
    as (Hx0 & Sx & Rx & Tx);
  pmkst HS;
  eapply SRr_bind;
  [ apply (aj_strcmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIG CS___interceptor_trampoline_strcmp) ASTRCMP Wc
      (ms_regs ms) (ms_mem ms) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc mdv1 EV_JOINED pb q s y (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + 5960)) HJ);
    [ rewrite Ra0; exact E32
    | rewrite Ra1, (EE 21%nat 21%bv eq_refl); exact H21
    | exact Hx0 | exact Hq0 | lia | exact (cwi_al16 _ _ Hsp32 H16) | lia | rewrite WS, Hes; lia
    | rewrite Qgp, (EE 3%nat 3%bv eq_refl), H3; exact Hgp
    | rewrite Qtp, (EE 4%nat 4%bv eq_refl), H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Sx | exact Sy
    | apply Rx; rewrite HspT, Hes; lia | apply Ry; rewrite HspT, Hes; lia
    | exact Tx | exact Ty
    | exact (cwi_rom e lyc Sc Wc (ms_mem ms) mdv1 pos EV_JOINED Hent HJ) ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp & Hfr3).
(* back at 0x87c2c: strcmp answered 0, args[a] is the item's string *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  pose proof (cwi_kept_call Wc (ms_mem ms) mem3 (cw_sp0 e) (sp1 - cw_sp0 e) (2 * ESTACK) sp1 ltac:(lia) Hfr3) as KEEP3 end.
pose proof (aregs_preserved_trans _ _ _ HPT HP3) as HP13.
assert (H23c : getr regs3 23 = w64 CW_SB) by (rewrite (cwi_pres_r _ _ 23%bv HP13 ltac:(cwi_cs_tac)); exact H23).
assert (H10c : getr regs3 10 = w64 0) by (apply Hcmp; exact Hsy).
clear HS SHOK HEI EE HAE E32.
pose proof (cwi_seed0 Wc regs3 mem3 0x1748 H23c) as HS.
pose proof (cwi_sh0 (Eimg (Ereg regs3 [])) (mrestrict (w_H Wc) mem3)) as SHOK.
pose proof (Eimg_env (Ereg regs3 [])) as HEI.
pose proof (cwi_EE regs3) as EE3.
assert (HAE3 : env_agree 32 (Ereg regs3 []) (Eimg (Ereg regs3 [])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3 in *. clear HE3.
paj_run_tok RUN HS HJ3 SHOK cwi_Bspan; [awr_ok_tac |].
set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem3) _ |- _ =>
  pose proof (cwi_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP4; clear HFr end.
psrr_branch_tok RUN BR HS SHOK cwi_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_ne_U in Hc;
    rewrite (U_atom E3 10 0 ltac:(rewrite (EE3 10%nat 10%bv eq_refl); exact H10c) ltac:(lia)) in Hc;
    change (U _ (SLit 0)) with 0 in Hc; vm_compute in Hc; discriminate Hc end. }
paj_run_to_tok RUNTO HS HJ3 SHOK cwi_Bspan 0x174c; [awr_ok_tac |].
set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP5; clear HFr end.
pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP12 KEEP3
  ltac:(lia) ltac:(lia)) KEEP4 ltac:(lia) ltac:(lia)) KEEP5 ltac:(lia) ltac:(lia)) as KEEP.
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- _ =>
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 [] (18%bv :: CWI_KR) HS HAE3 ltac:(vm_compute; reflexivity)) as RK3;
  cbn [ms_regs restrict] in RK3;
  assert (RK : cwi_rk (ms_regs ms) regsc);
  [ intros r Hr; rewrite (RK3 r (or_intror Hr)); exact (cwi_rk_pres _ _ HP13 r Hr) | ];
  assert (H18' : getr (ms_regs ms) 18 = w64 (cw_tptr fn + Z.of_nat j2));
  [ rewrite (RK3 18%bv (or_introl eq_refl)), (cwi_pres_r _ _ 18%bv HP13 ltac:(cwi_cs_tac)); exact H18 | ];
  assert (INV : INV_IL B MT e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv4 pos sp1 line c a j2);
  [ exists fn, args;
    split; [exact (cwi_icommon_move e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args (ms_regs ms) (ms_mem ms) mdv4
                     HCOM HJ3 RK KEEP)|];
    split; [exact Hj2|]; split; [exact H18' | exact Hparse]
  | ];
  pmkst HS;
  exact (HIL e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv4 pos sp1 line j2 Hent INV) end.
Qed.
End e.
End f.
End d.
