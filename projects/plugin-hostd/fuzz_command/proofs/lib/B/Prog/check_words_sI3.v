(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths, module names and numbers changed; 764 of its 878 lines of code are new or changed and 1546 lines of the source are left out. *)
(* check_words' ASan+UBSan walk, segment I3 (lib/B/Prog/check_words_d.v): the strcspn call that ends every item of
   the template and the compare of the item's string with the recorded argument. The B twin of
   lib/A/Prog/check_words_sI3.v (an earlier version), re-derived on B's code.
   seg_I3a (listing 0x19b4 .. 0x19d0, image 0x87ee4 .. 0x87f00): a1 := " " 0x21160 (auipc/addi, the object atom
   A_OBJ 23), a0 := s7, the strcspn wrapper (jal 0x45198 at 0x87ef0, the kit's PaArtStr.aj_strcspn_at). The trap
   site 0x87ef4 (`bltu s3,a0`, s3 = ~s7 by INV_ICMP) is not reached: s7 is inside the template and the answer is at
   most the template's length, so s7 + the answer < 2^64. s4 := a0; `beqz s5` goes to the latch IL 0x87f2c for an
   item that asks for nothing (want_at's None, s5 = 0) and on to ICMP2 0x87f00 for one that asks for y (s5 = q > 0).
   seg_I3b (listing 0x19d0 .. 0x19fc, image 0x87f00 .. 0x87f2c): the trap site 0x87f04 (`bltu 168(s1),s9`, the slot
   sp1 + 168 = ~(cp + 8), s9 = 8 a) is not reached: cp + 8 + 8 a < 2^64 (cp in g_rec, a < nargs <= 6). The
   instrumented check of &args[a] at s11 (a load of the shadow byte and a compare; error path 0x881a4) is covered by
   the seed's shadow entry over g_rec (CW_ZSH_P), so the error path is not reached. a0 := args[a] from s8; the two
   abort edges 0x88170 are not taken: `beqz a0` by the record (acall_at: args[a] <> 0), and `bnez a0` after the
   strcmp wrapper (jal 0x45188 at 0x87f24, PaArtStr.v's aj_strcmp_at) on (args[a], s5) by words_prop_at (args[a] is
   the string y the item asks for, INV_ICMP2's want_at = Some y).
   Method: fresh symbolic seeds at 0x19b4, 0x19c4, 0x19d0 and 0x19f8 (the registers; at 0x19d0 also the slots
   sp1 + 168 and &args[a]), runs by paj_run_tok / paj_run_to_tok; the state across each wrapper call is carried by
   the memory kept outside the call's window [sp1 - 2 ESTACK, sp1) and the callee-saved registers
   (check_words_ki.v's cw_icommon_kept). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArtStr check_words_ki.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* small facts *)
Lemma cwi3_skipn_cons : forall {A : Type} n (l : list A) x r, skipn n l = x :: r ->
  nth_error l n = Some x /\ skipn (S n) l = r.
Proof.
intros A n. induction n as [|n IH]; intros l x r H.
- change (skipn 0 l) with l in H. subst l. split; reflexivity.
- destruct l as [|b l]; [change (skipn (S n) (@nil A)) with (@nil A) in H; discriminate H|].
  change (skipn (S n) (b :: l)) with (skipn n l) in H. exact (IH l x r H).
Qed.
Lemma cwi3_cspn_le : forall set s, (PCspn.cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn; [lia|]. destruct (existsb _ _); lia. Qed.
Lemma cwi3_al16 : forall sp1 sp0, sp1 mod 32 = 0 -> sp0 mod 16 = 0 -> (sp1 - sp0) mod 16 = 0.
Proof.
intros sp1 sp0 H1 H2. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
destruct H1 as [q1 Hq1]. destruct H2 as [q2 Hq2]. exists (2 * q1 - q2). lia.
Qed.

(* the registers a fresh seed names, all callee-saved; the same list without s4 (x20), which seg_I3a writes *)
Definition CWI3_KR : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition CWI3_KR20 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac cwi3_in := repeat (first [left; reflexivity | right]).
Lemma cwi3_rk_of : forall regs regs', (forall r, In r CWI3_KR -> getr regs' r = getr regs r) -> cw_regs_kept regs regs'.
Proof. intros regs regs' H. unfold cw_regs_kept. repeat split; apply H; cbn [CWI3_KR In]; cwi3_in. Qed.
Lemma cwi3_rk_comp : forall regs regs2 regs3, cw_regs_kept regs regs2 ->
  (forall r, In r CWI3_KR20 -> getr regs3 r = getr regs2 r) ->
  cw_cregs_kept regs regs3 /\ getr regs3 18 = getr regs 18 /\ getr regs3 19 = getr regs 19 /\
  getr regs3 21 = getr regs 21 /\ getr regs3 23 = getr regs 23 /\ getr regs3 24 = getr regs 24 /\
  getr regs3 25 = getr regs 25 /\ getr regs3 26 = getr regs 26 /\ getr regs3 27 = getr regs 27.
Proof.
intros regs regs2 regs3 (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27) H.
unfold cw_cregs_kept.
repeat split; (rewrite H; [assumption | cbn [CWI3_KR20 In]; cwi3_in]).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma cwi3_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono x x' H1) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma cwi3_fp_nil : forall a, fp_spares [] a.
Proof. intros a. apply fp_spares_closed; [intros (x & Hx & _); destruct Hx | apply inFP_nil]. Qed.
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
(* the statement's hypotheses (check_words_c.v:138-139), word for word *)
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
(* the walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
(* the record facts of check_words_d.v, proved in check_words_rf.v *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Let RUN := paj_run (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

(* ---------------------------------------------------------------------------------------------------------- *)
(* memory kept outside a window *)
Lemma cwi3_aval_kept : forall rd rd' lo hi a (n : nat) v, kept_out rd rd' lo hi -> aval_mem rd a n v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v HK H Ha Hn Hw k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
Lemma cwi3_bytes_kept : forall rd rd' lo hi p l, kept_out rd rd' lo hi -> abytes_atR rd p l ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 -> (p + Z.of_nat (length l) <= lo \/ hi <= p) -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hw i Hi. rewrite (HK (p + Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma cwi3_str_kept : forall rd rd' lo hi p s, kept_out rd rd' lo hi -> astr_atR rd p s ->
  0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 -> (p + Z.of_nat (length s) + 1 <= lo \/ hi <= p) ->
  astr_atR rd' p s.
Proof.
intros rd rd' lo hi p s HK [H1 H2] Hp Hl Hw. split; [|exact H2].
apply (cwi3_bytes_kept rd rd' lo hi p _ HK H1 Hp); rewrite length_app; cbn [length]; lia.
Qed.
Lemma cwi3_kept_run : forall E (rs : smem) H (m m' : word -> option byte) lo hi, rs = [] ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> kept_out (aview SEGS H m) (aview SEGS H m') lo hi.
Proof.
intros E rs H m m' lo hi Hrs Hf a Ha _. subst rs. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & _). destruct Hr.
Qed.
Lemma cwi3_kept_run_ro : forall E (rs : smem) H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> kept_out (aview SEGS H m) (aview SEGS H m') lo hi.
Proof.
intros E rs H m m' lo hi Hf Hw a Ha _. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Hb). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Lemma cwi3_kept_call : forall (W : world SEGS) (m m' : word -> option byte) sp0 o stk sp1, sp0 + o = sp1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ False -> rdW W m' a = rdW W m a) ->
  kept_out (rdW W m) (rdW W m') (sp1 - stk) sp1.
Proof. intros W m m' sp0 o stk sp1 Hs Hf a Ha Hn. apply Hf; [exact Ha | lia | tauto]. Qed.
(* the window [sp1 - 2 ESTACK, sp1) lies inside check_words_ki.v's [sp1 - 3 ESTACK, sp1) *)
Lemma cwi3_mem_kept_of : forall rd rd' sp1 F, kept_out rd rd' (sp1 - 2 * ESTACK) sp1 -> cw_mem_kept B rd rd' sp1 F.
Proof. intros rd rd' sp1 F HK x Hx Hw _ _. apply HK; [exact Hx | unfold ESTACK in *; lia]. Qed.

(* registers *)
Lemma cwi3_EE : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* the fresh seed: the registers only; atom 22 is s6, the shadow base *)
Definition cwi3_Bx : sv := SOff 22 0.
Definition cwi3_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cwi3_G : facts := mkFacts [(22%nat, mkAF SB SB 0)] [] [].
Definition cwi3_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None cwi3_G.
Lemma cwi3_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc, getr regs 22 = w64 CW_SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (cwi3_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc H22. rewrite restrict_mkst_fx. unfold cwi3_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- assert (E22 : ew (Eimg (Ereg regs [])) 22 = Z_to_bv 64 CW_SB) by (rewrite (cwi3_EE regs [] 22 22%bv eq_refl); exact H22).
  split; [|split; exact I]. cbn [f_atoms atoms_ok cwi3_G]. split; [|exact I].
  unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E22. rewrite unsigned_lit_small by (unfold CW_SB; lia).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold CW_SB, SB. repeat split; lia.
Qed.
Lemma cwi3_sh0 : forall E m, sh_ok SEGS cwi3_Bx [] E m.
Proof. intros E m. apply Forall_nil. Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the entry's premises the segment reads *)
Lemma cwi3_ent : forall e, cw_ent B MT e ->
  afn_pre SEGS B CHECK_WORDS_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
  arodata_okP SEGS RLO RHI B (cw_rd0 e) /\ cmd_ro_ok (cw_rd0 e) /\
  rec_repA B (e_ly e) (e_S e) (cw_rd0 e) (e_R e) (e_O e) /\ words_prop_at atoi_a (e_R e) (e_ws e).
Proof.
intros e H. unfold cw_ent in H. cbv zeta in H.
destruct H as (H1 & _ & H3 & _ & H5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H17 & H18 & _).
split; [exact H1|]. split; [exact H3|]. split; [exact H5|]. split; [exact H17 | exact H18].
Qed.
(* " " 0x21160 is the listing's object atom A_OBJ 23 (cmd_val_objs, CmdAddr.v's cmd_objs) *)
Lemma cwi3_v23 : forall e, cw_ent B MT e -> VAL (A_OBJ 23) = 0x21160.
Proof.
intros e H. pose proof H as (_ & _ & _ & _ & _ & HOBJ & _).
rewrite HOBJ by (vm_compute; lia). vm_compute. reflexivity.
Qed.
Lemma cwi3_call : forall e i fn args, cw_ent B MT e -> nth_error (r_calls (e_R e)) i = Some (fn, args) ->
  exists P, acall_at (ablocks B (e_ly e) (e_S e)) (cw_rd0 e) (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) (fn, args) P.
Proof.
intros e i fn args H Hi. destruct (cwi3_ent e H) as (_ & _ & _ & HR & _).
destruct HR as (Q & (_ & _ & _ & (Hl & HlQ & _ & Hcalls & _) & _) & _).
destruct (nth_error (l_calls Q) i) as [P|] eqn:HP.
- exists P. exact (proj1 (Hcalls i (fn, args) P Hi HP)).
- exfalso. apply nth_error_None in HP.
  assert (Hlt : (i < length (r_calls (e_R e)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate). lia.
Qed.
(* where the window of a wrapper call at sp1 lies, and where the own frame lies *)
Lemma cwi3_jloc : forall e lyc Sc Wc memc mdc pos k sp1,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 ->
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
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold frame_addr in F1, F2 |- *. rewrite EF in F1, F2. rewrite FB in F2.
repeat split; lia.
Qed.
(* the rom view at a state the journal reaches *)
Lemma cwi3_rom : forall e lyc Sc Wc memc mdc pos k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros e lyc Sc Wc memc mdc pos k Hent HJ. destruct (cwi3_ent e Hent) as (_ & HROD & _).
pose proof (cmd_rom_view_on (e_W e) (e_mem e) HROD) as HR0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Ha Ho He. rewrite F3; [exact (HR0 a Ha Ho He) | | exact Ho | exact He | apply cwi3_fp_nil].
destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.
(* a read-only string of CW_ZSH at the current state, from its j-th byte: the wrappers' premises *)
Lemma cwi3_str_ready : forall lyc Sc Wc memc mdc p s j,
  AR SEGS B lyc Sc Wc memc mdc ->
  In (p, Z.of_nat (length s) + 1) CW_ZSH -> p <> A_G_REC -> In (p + Z.of_nat (length s)) cmd_ro_ends ->
  astr_atR (rdW Wc memc) p s -> (j <= length s)%nat ->
  astr_at SEGS Wc memc (p + Z.of_nat j) (skipn j s) /\
  (forall regsT, alloc_ceiling <= spZ regsT - 2 * ESTACK ->
     aread_ok SEGS (2 * ESTACK) Wc regsT memc (p + Z.of_nat j) (astr_len (skipn j s) + 1)) /\
  atail_vis SEGS Wc memc (p + Z.of_nat j + astr_len (skipn j s)).
Proof.
intros lyc Sc Wc memc mdc p s j HAR Hz Hg He HS0 Hj.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hp : 0x10000 <= p /\ p + Z.of_nat (length s) + 1 <= 0x606000).
{ destruct (cw_ro_unowned p (Z.of_nat (length s) + 1) 0 Hz Hg ltac:(lia)) as (Himg & _).
  destruct (cw_ro_unowned p (Z.of_nat (length s) + 1) (Z.of_nat (length s)) Hz Hg ltac:(lia)) as (Himg2 & _).
  pose proof (pa_img_range _ Himg) as R1. pose proof (pa_img_range _ Himg2) as R2. lia. }
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
    * intros _. apply (cwi3_hull_sub _ p (Z.of_nat (length s) + 1)); [exact HV | lia | lia | lia].
- rewrite Hlen. replace (p + Z.of_nat j + (Z.of_nat (length s) - Z.of_nat j)) with (p + Z.of_nat (length s)) by lia.
  exact (cmd_tail_vis lyc Sc Wc memc mdc _ HAR He).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the item loop's state carried across a stretch that writes s4 (x20): the registers cw_core and the item
   registers name are kept, and the memory outside check_words_ki.v's window *)
Lemma cwi3_icommon_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args,
  cw_ent B MT e -> cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem' md' EV_JOINED ->
  cw_cregs_kept regs regs' ->
  getr regs' 18 = getr regs 18 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  cw_mem_kept B (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
  cw_icommon B MT e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args HE HI HJ' HR R18 R24 R25 R26 R27 HM.
destruct HI as (HC & HL & HLS & HCS & H168 & HIR & Hcr & Hnth & Ha).
pose proof HC as (_ & _ & _ & Hrng & _).
destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c HE HC HL HLS HCS HJ' HR HM)
  as (HC' & HL' & HLS' & HCS').
destruct HIR as (I26 & I18 & I25 & I24 & I27).
split; [exact HC'|]. split; [exact HL'|]. split; [exact HLS'|]. split; [exact HCS'|].
split.
{ apply (cw_aval_kept (rdW Wc mem)); [|exact H168].
  intros k Hk. apply (cw_above_kept B LAWS TL e lyc Sc Wc regs mem md mem' pos sp1 EV_JOINED HC HM). lia. }
split; [|split; [exact Hcr | split; [exact Hnth | exact Ha]]].
split; [rewrite R26; exact I26|]. split; [rewrite R18; exact I18|]. split; [rewrite R25; exact I25|].
split; [rewrite R24; exact I24 | rewrite R27; exact I27].
Qed.
(* the string the item asks for: where it lies (below alloc_ceiling), and that it is kept by a wrapper call *)
Lemma cwi3_wsrc_lo : forall e lyc Sc Wc memc mdc pos line q y k,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  cw_wsrc B e lyc Sc (rdW Wc memc) pos line q y ->
  0 < q /\ q + Z.of_nat (length y) + 1 <= alloc_ceiling.
Proof.
intros e lyc Sc Wc memc mdc pos line q y k HJ HLINE (Hs & Hq & Hcase).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
pose proof HLINE as (HPL & Hl4096 & _).
split; [exact Hq|].
destruct Hcase as [(-> & ->) | [(-> & ->) | [(-> & Hy) | (kk & Hk & -> & -> & Hblk)]]].
- assert (Hin : In (line, cw_JN e) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc line (cw_JN e) HAR Hin) as (_ & _ & Hce & _ & _ & _ & HJN).
  pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [_ Hrq]. pose proof (cw_join_len (e_ws e)) as HJL.
  unfold cw_JN in *. lia.
- cbn [length]. lia.
- pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & _).
  assert (FB : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
  unfold frame_addr in F1, F2 |- *. rewrite EF in F1, F2. rewrite FB in F2. lia.
- destruct Hblk as (bp & bk & Hin & Hb1 & Hb2).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bp bk HAR Hin) as (_ & Hb4096 & Hce & _ & _ & _ & Hbk).
  pose proof (req_size_pos bk ltac:(lia)) as [_ Hrq]. lia.
Qed.
Lemma cwi3_wsrc_move : forall e lyc Sc Wc memc mdc mem' pos sp1 line q y k,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 ->
  cw_line B MT e lyc Sc (rdW Wc memc) line ->
  cw_wsrc B e lyc Sc (rdW Wc memc) pos line q y ->
  kept_out (rdW Wc memc) (rdW Wc mem') (sp1 - 2 * ESTACK) sp1 ->
  cw_wsrc B e lyc Sc (rdW Wc mem') pos line q y.
Proof.
intros e lyc Sc Wc memc mdc mem' pos sp1 line q y k HJ Hsp1 HLINE HSRC HK.
destruct (cwi3_jloc e lyc Sc Wc memc mdc pos k sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
destruct (cwi3_wsrc_lo e lyc Sc Wc memc mdc pos line q y k HJ HLINE HSRC) as [Hq0 Hqc].
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & _).
destruct HSRC as (Hs & Hq & Hcase).
split; [apply (cwi3_str_kept _ _ _ _ _ _ HK Hs); lia|]. split; [exact Hq | exact Hcase].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* seg_I3a: 0x87ee4 auipc a0; addi a1,a0,636 (" " 0x21160); mv a0,s7; jal strcspn (0x87ef0); 0x87ef4 bltu s3,a0
   (trap site); mv s4,a0; beqz s5 -> IL 0x87f2c, else ICMP2 0x87f00 *)
Lemma seg_I3a : forall c a, ST_ICMP2 B MT c a -> ST_IL B MT c a -> ST_ICMP B MT c a.
Proof.
intros c a HC2 HIL. unfold ST_ICMP. intros e lyc Sc Wc regsc memc mdc pos sp1 line j1 q wq Hent HI.
destruct HI as (fn & args & HCOM & Hj1 & H23 & H19 & Hparse & H21 & Hwq & Hwant).
pose proof HCOM as (HCORE & HLINE & _ & _ & _ & HIR & Hcr & Hnth & Ha).
pose proof HCORE as (HJ & Hsp & Hsp32 & Hsp1 & H3 & H4 & _ & _ & H22 & _).
pose proof HJ as HJ0.
destruct (cwi3_ent e Hent) as (HPRE & HROD & HRO & _ & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof (cwi3_v23 e Hent) as V23.
destruct (cwi3_jloc e lyc Sc Wc memc mdc pos EV_JOINED sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & _).
destruct (cw_tpl_facts fn) as (Te & Tz & T0 & Tlo & Thi & T8 & Tg & _).
pose proof (cwi3_cspn_le CW_SP1 (skipn j1 (cw_tpl fn))) as Hcsl. rewrite length_skipn in Hcsl.
unfold cw_at, CW_PC_ICMP.
pose proof (cwi3_seed0 Wc regsc memc 0x19b4 H22) as HS.
pose proof (cwi3_sh0 (Eimg (Ereg regsc [])) (mrestrict (w_H Wc) memc)) as SHOK.
pose proof (Eimg_env (Ereg regsc [])) as HEI.
pose proof (cwi3_EE regsc []) as EE.
assert (HAE : env_agree 32 (Ereg regsc []) (Eimg (Ereg regsc [])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regsc [])) as E0 eqn:HE0 in *. clear HE0.
(* to the strcspn call *)
paj_run_tok RUN HS HJ SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regsc [] HS HAE ltac:(vm_compute; reflexivity)) as HPT;
  cbn [ms_regs restrict] in HPT;
  assert (HspT : spZ (ms_regs ms) = sp1) by (unfold spZ in Hsp |- *; rewrite Qsp, (EE 2%nat 2%bv eq_refl); exact Hsp);
  assert (Ra1' : getr (ms_regs ms) 11 = w64 0x21160);
  [ rewrite Ra1, <- (Z_to_bv_bv_unsigned 64 (ew E0 264));
    lazymatch goal with HE : img_env _ _ E0 |- _ => rewrite (HE 264%nat ltac:(cbv; lia)) end;
    change (VAL 264%nat) with (VAL (A_OBJ 23)); rewrite V23; reflexivity
  | ];
  destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED fn Hent HJ)
    as (TS & _);
  destruct (cw_sp1_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED Hent HJ)
    as (SPS & _);
  destruct (cwi3_str_ready lyc Sc Wc (ms_mem ms) mdv (cw_tptr fn) (cw_tpl fn) j1 (proj1 HJ) Tz Tg Te TS Hj1)
    as (Sx & Rx & Tx);
  destruct (cwi3_str_ready lyc Sc Wc (ms_mem ms) mdv 0x21160 CW_SP1 0 (proj1 HJ)
    ltac:(apply cw_in_pair_of_existsb; vm_compute; reflexivity) ltac:(unfold A_G_REC; lia)
    ltac:(apply cw_in_of_existsb; vm_compute; reflexivity) SPS ltac:(cbn; lia)) as (Sy & Ry & Ty);
  pmkst HS;
  eapply SRr_bind;
  [ apply (PaArtStr.aj_strcspn_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIG CS___interceptor_trampoline_strcspn)
      0xa6bf8 0x604158 (ASTRCSPN fx) Wc
      (ms_regs ms) (ms_mem ms) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc mdv EV_JOINED (cw_tptr fn + Z.of_nat j1) 0x21160 (skipn j1 (cw_tpl fn)) CW_SP1 (sp1 - cw_sp0 e)
      (Z_to_bv 64 (BASE + 6596)) HJ);
    [ rewrite Ra0, (EE 23%nat 23%bv eq_refl); exact H23
    | exact Ra1'
    | lia | lia | lia | exact (cwi3_al16 _ _ Hsp32 H16) | lia | rewrite WS, Hes; lia
    | rewrite Qgp, (EE 3%nat 3%bv eq_refl), H3; exact Hgp
    | rewrite Qtp, (EE 4%nat 4%bv eq_refl), H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | (* the stack-protector GOT word and guard the entry reads, from the record fact at the journal's AR state *)
      exact (proj1 (proj2 (cmd_rec_cells _ _ _ _ _ (proj1 HJ))))
    | exact Sx | exact Sy
    | apply Rx; rewrite HspT, Hes; lia
    | (* the `+ 8` band premise of the string: the template is a .rodata literal *)
      unfold amem_range, astr_len, kLowMemEnd; rewrite length_skipn; left; lia
    | apply Ry; rewrite HspT, Hes; lia
    | (* the `+ 8` band premise of the set " " 0x21160 (.rodata) *)
      change (astr_len CW_SP1 + 8) with 9; unfold amem_range, kLowMemEnd; left; lia
    | exact Tx | exact Ty
    | exact (cwi3_rom e lyc Sc Wc (ms_mem ms) mdv pos EV_JOINED Hent HJ) ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcs2 & Hfr2).
(* back at 0x87ef4: the memory kept outside [sp1 - 2 ESTACK, sp1), the callee-saved registers *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  pose proof (cwi3_kept_call Wc (ms_mem ms) mem2 (cw_sp0 e) (sp1 - cw_sp0 e) (2 * ESTACK) sp1 ltac:(lia) Hfr2) as KEEP2 end.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP1; clear HFr end.
pose proof (cw_regs_kept_of_pres _ _ (aregs_preserved_trans _ _ _ HPT HP2)) as RKc.
pose proof RKc as (_ & _ & _ & _ & _ & _ & K19 & _ & K21 & K22 & K23 & _).
assert (H19b : getr regs2 19 = w64 (cw_not (cw_tptr fn + Z.of_nat j1))) by (rewrite K19; exact H19).
assert (H22b : getr regs2 22 = w64 CW_SB) by (rewrite K22; exact H22).
clear HS SHOK HEI EE HAE.
pose proof (cwi3_seed0 Wc regs2 mem2 0x19c4 H22b) as HS.
pose proof (cwi3_sh0 (Eimg (Ereg regs2 [])) (mrestrict (w_H Wc) mem2)) as SHOK.
pose proof (Eimg_env (Ereg regs2 [])) as HEI.
pose proof (cwi3_EE regs2 []) as EE2.
assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 [])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2 in *. clear HE2.
assert (E19 : ew E2 19 = Z_to_bv 64 (cw_not (cw_tptr fn + Z.of_nat j1))) by (rewrite (EE2 19%nat 19%bv eq_refl); exact H19b).
assert (E10 : ew E2 10 = Z_to_bv 64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))))
  by (rewrite (EE2 10%nat 10%bv eq_refl); exact Hcs2).
assert (E21 : ew E2 21 = Z_to_bv 64 q) by (rewrite (EE2 21%nat 21%bv eq_refl), K21; exact H21).
paj_run_tok RUN HS HJ2 SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) _ |- _ =>
  pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP3; clear HFr end.
(* the trap site 0x87ef4: s3 = ~s7 is not below strcspn's answer *)
psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_ltu_U in Hc;
    rewrite (U_atom E2 19 (cw_not (cw_tptr fn + Z.of_nat j1)) E19 ltac:(unfold cw_not; lia)) in Hc;
    rewrite (U_atom E2 10 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) E10 ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end.
  unfold cw_not in *. lia. }
(* s4 := a0, to `beqz s5` *)
paj_run_tok RUN HS HJ2 SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP4; clear HFr end.
pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2
  ltac:(lia) ltac:(lia)) KEEP3 ltac:(lia) ltac:(lia)) KEEP4 ltac:(lia) ltac:(lia)) as KEEP14.
destruct wq as [y|].
- (* the item asks for y: s5 = q > 0, on to ICMP2 *)
  destruct (cwi3_wsrc_lo e lyc Sc Wc memc mdc pos line q y EV_JOINED HJ0 HLINE Hwq) as [Hq0 Hqc].
  psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
  { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U in Hc; apply Z.eqb_eq in Hc;
      rewrite (U_atom E2 21 q E21 ltac:(lia)) in Hc; change (U _ (SLit 0)) with 0 in Hc end.
    lia. }
  paj_run_to_tok RUNTO HS HJ2 SHOK cwi3_Bspan 0x19d0; [awr_ok_tac |].
  set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
    pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP5; clear HFr end.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP14 KEEP5 ltac:(lia) ltac:(lia)) as KEEP.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- _ =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [] CWI3_KR20 HS HAE2 ltac:(vm_compute; reflexivity)) as RK3;
    cbn [ms_regs restrict] in RK3;
    prreg HS (20%bv : bv 5) R20;
    destruct (cwi3_rk_comp regsc regs2 (ms_regs ms) RKc RK3) as (KC & R18' & _ & R21' & R23' & R24' & R25' & R26' & R27');
    assert (R20' : getr (ms_regs ms) 20 = w64 (Z.of_nat (cw_cs (cw_tpl fn) j1)))
      by (rewrite R20; exact E10);
    assert (INV2 : INV_ICMP2 B MT e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line c a j1 q y);
    [ exists fn, args;
      split; [exact (cwi3_icommon_kept e lyc Sc Wc regsc memc mdc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line c a fn args
                       Hent HCOM HJ2 KC R18' R24' R25' R26' R27'
                       (cwi3_mem_kept_of _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP))|];
      split; [exact Hj1|]; split; [rewrite R23'; exact H23|]; split; [exact R20'|]; split; [exact Hparse|];
      split; [rewrite R21'; exact H21|];
      split; [exact (cwi3_wsrc_move e lyc Sc Wc memc mdc (ms_mem ms) pos sp1 line q y EV_JOINED HJ0 Hsp1 HLINE Hwq KEEP)
             | exact Hwant]
    | ];
    pmkst HS;
    exact (HC2 e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line j1 q y Hent INV2) end.
- (* the item asks for nothing: s5 = q = 0, to the latch *)
  cbn [cw_wq] in Hwq. subst q.
  psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
  2: { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
         rewrite branch_eq_U in Hc;
         rewrite (U_atom E2 21 0 E21 ltac:(lia)) in Hc; change (U _ (SLit 0)) with 0 in Hc;
         vm_compute in Hc; discriminate Hc end. }
  paj_run_to_tok RUNTO HS HJ2 SHOK cwi3_Bspan 0x19fc; [awr_ok_tac |].
  set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
    pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP5; clear HFr end.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP14 KEEP5 ltac:(lia) ltac:(lia)) as KEEP.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- _ =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [] CWI3_KR20 HS HAE2 ltac:(vm_compute; reflexivity)) as RK3;
    cbn [ms_regs restrict] in RK3;
    prreg HS (20%bv : bv 5) R20;
    destruct (cwi3_rk_comp regsc regs2 (ms_regs ms) RKc RK3) as (KC & R18' & _ & _ & R23' & R24' & R25' & R26' & R27');
    assert (R20' : getr (ms_regs ms) 20 = w64 (Z.of_nat (cw_cs (cw_tpl fn) j1)))
      by (rewrite R20; exact E10);
    assert (INV : INV_IL B MT e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line c a j1);
    [ exists fn, args;
      split; [exact (cwi3_icommon_kept e lyc Sc Wc regsc memc mdc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line c a fn args
                       Hent HCOM HJ2 KC R18' R24' R25' R26' R27'
                       (cwi3_mem_kept_of _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP))|];
      split; [exact Hj1|]; split; [rewrite R23'; exact H23|]; split; [exact R20' | exact Hparse]
    | ];
    pmkst HS;
    exact (HIL e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv3 pos sp1 line j1 Hent INV) end.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* segment I3b's reads: the recorded argument (record + journal), the compared strings at the call *)
Lemma cwi3_ncalls : forall e, cw_ent B MT e -> cw_ncalls e <= 16.
Proof.
intros e H. destruct (cwi3_ent e H) as (_ & _ & _ & HR & _).
destruct HR as (Q & (_ & _ & _ & (Hl & _) & _) & _). unfold cw_ncalls. lia.
Qed.
Lemma cwi3_grec_kept : forall e lyc Sc Wc memc mdc pos k a,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  A_G_REC <= a < A_G_REC + 960 -> rdW Wc memc a = cw_rd0 e a.
Proof.
intros e lyc Sc Wc memc mdc pos k a HJ Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Hpg : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; lia]).
destruct (cmd_prog_unowned a Hpg) as (Himg & Hno & Herr).
unfold cw_rd0. apply F3; [exact Himg | exact Hno | exact Herr | apply cwi3_fp_nil].
Qed.
Lemma cwi3_arg : forall e c fn args a, cw_ent B MT e -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) ->
  0 <= c -> 0 <= a < Z.of_nat (length args) ->
  exists s pb pk, nth_error args (Z.to_nat a) = Some s /\
    aval_mem (cw_rd0 e) (A_G_REC + 16 + 56 * c + 8 + 8 * a) 8 pb /\ pb <> 0 /\
    In (pb, pk) (ablocks B (e_ly e) (e_S e)) /\ Z.of_nat (length s) + 1 <= pk /\ astr_atR (cw_rd0 e) pb s /\
    (length args <= 6)%nat.
Proof.
intros e c fn args a Hent Hnth Hc Ha.
destruct (cwi3_call e (Z.to_nat c) fn args Hent Hnth) as (P & (_ & Hl6 & HlP & _ & _ & _ & Hargs)).
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
Lemma cwi3_words_eq : forall e c fn args a s it y, cw_ent B MT e ->
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) -> nth_error args (Z.to_nat a) = Some s ->
  nth_error (PCW.call_items fn) (Z.to_nat a) = Some it -> want_at atoi_a (cw_read e) (e_ws e) it = Some y -> s = y.
Proof.
intros e c fn args a s it y Hent Hnth Hs Hit Hw. destruct (cwi3_ent e Hent) as (_ & _ & _ & _ & HW).
unfold words_prop_at in HW. cbv zeta in HW. rewrite Forall_forall in HW.
pose proof (HW (fn, args) (nth_error_In _ _ Hnth)) as Hc. unfold call_words_ok_at in Hc.
destruct Hc as (Hc1 & _). exact (Hc1 (Z.to_nat a) it s Hs Hit y Hw).
Qed.
(* a string inside a heap block live at the entry and at the current state *)
Lemma cwi3_blk_str : forall e lyc Sc Wc memc mdc pos k b n p s,
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
Lemma cwi3_blk_ready : forall lyc Sc Wc memc mdc b n p s,
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
Lemma cwi3_frame_ready : forall e lyc Sc Wc memc mdc pos k y,
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
Lemma cwi3_wsrc_ready : forall e lyc Sc Wc memc mdc pos line q y k,
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
  pose proof (cw_join_len (e_ws e)) as HJL.
  apply (cwi3_blk_ready lyc Sc Wc memc mdc line (cw_JN e) line (join_sp (e_ws e)) HAR Hin); [lia | unfold cw_JN; lia | exact Hs].
- destruct (cwi3_str_ready lyc Sc Wc memc mdc 0x212c0 [] 0 HAR
    ltac:(apply cw_in_pair_of_existsb; vm_compute; reflexivity) ltac:(unfold A_G_REC; lia)
    ltac:(apply cw_in_of_existsb; vm_compute; reflexivity) Hs ltac:(cbn; lia)) as (Sx & Rx & Tx).
  split; [lia|]. exact (conj Sx (conj Rx Tx)).
- exact (cwi3_frame_ready e lyc Sc Wc memc mdc pos k y HJ S4 S5 Hs Hy).
- destruct Hblk as (bp & bk & Hin & Hb1 & Hb2).
  exact (cwi3_blk_ready lyc Sc Wc memc mdc bp bk (nth kk (e_wp e) 0) (nth kk (e_ws e) []) HAR Hin Hb1 ltac:(lia) Hs).
Qed.
(* the fresh seed at 0x19d0: the registers, the slot sp1 + 168 (atom 32 = ~(cp + 8)) and the slot &args[a] at s8
   (atom 33 = args[a]); the shadow entry of [s11, s11 + 8) in g_rec covers the instrumented check of &args[a] *)
Lemma cwi3_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Definition cwi3_rg9 : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition cwi3_rg24 : YP09.region := YP09.mkRegion (Some 24%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition cwi3_GB : facts := mkFacts [(22%nat, mkAF SB SB 0); (24%nat, mkAF A_G_REC (A_G_REC + 960) 3);
  (27%nat, mkAF A_G_REC (A_G_REC + 960) 3)] [] [].
Definition cwi3_SHB : list shent := [mkSHE 27 0 8].
Definition cwi3_ssB : sstate := mkSS 0x19d0 sr_atoms [cwi3_rg9; cwi3_rg24] None cwi3_GB.
Lemma cwi3_seedB : forall (W : world SEGS) (regs : bvmap 5 word) mem sp1 v s4 p,
  getr regs 22 = w64 CW_SB -> getr regs 9 = w64 sp1 -> getr regs 24 = w64 s4 -> getr regs 27 = w64 s4 ->
  0 <= sp1 -> sp1 + 176 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  A_G_REC <= s4 -> s4 + 8 <= A_G_REC + 960 -> s4 mod 8 = 0 -> 0 <= p < 2 ^ 64 -> A_G_REC + 960 <= sp1 ->
  aval_mem (rdW W mem) (sp1 + 168) 8 v -> aval_mem (rdW W mem) s4 8 p ->
  range_addressable (rdW W mem) SHADOW_OFF A_G_REC 960 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 p])) cwi3_ssB
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x19d0)) mem (seg_rom SEGS))) /\
  sh_ok SEGS cwi3_Bx cwi3_SHB (Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 p])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem sp1 v s4 p H22 H9 H24 H27 Hs0 Hs1 Hv Hp1 Hp2 Hp3 Hp Hdis V1 V2 RA.
assert (HG : A_G_REC = 6173376) by reflexivity.
pose proof (cwi3_EE regs [Z_to_bv 64 v; Z_to_bv 64 p]) as EE.
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 p])) 32 = Z_to_bv 64 v)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 v; Z_to_bv 64 p] 0)).
assert (E33 : ew (Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 p])) 33 = Z_to_bv 64 p)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 v; Z_to_bv 64 p] 1)).
set (E := Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 p])) in *.
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 s4) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = Z_to_bv 64 s4) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
{ intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
split.
- unfold cwi3_ssB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold cwi3_rg9, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sp1 168 8 (SOff 32 0) v);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      exact (cwi3_val_of_aval _ _ _ _ _ V1).
    * unfold cwi3_rg24, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 24%nat s4 E24) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ s4 0 8 (SOff 33 0) p);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (cwi3_val_of_aval _ _ _ _ _ V2).
  + apply pairwise_disjoint_of_extents. unfold cwi3_rg9, cwi3_rg24, extent_of_region.
    cbn [map zpairwise_disjoint zall_disjoint YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9), (VB 24%nat s4 E24) by lia.
    split; [split; [unfold zdisj; cbn [fst snd]; right; lia | exact I] | split; exact I].
  + split; [|split; exact I]. cbn [f_atoms atoms_ok cwi3_GB]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E22, E24, E27. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SB.
    repeat split; lia.
- unfold sh_ok, cwi3_SHB. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E cwi3_Bx 27 A_G_REC 960 s4 0 8 RA).
  + unfold cwi3_Bx. rewrite (U_atom E 22 SB E22) by (unfold SB; lia). reflexivity.
  + exact (U_atom E 27 s4 E27 ltac:(lia)).
  + lia. + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* seg_I3b: 0x87f00 ld a0,168(s1); bltu a0,s9 (trap site 0x87f04); the instrumented check of &args[a] at s11
   (error path 0x881a4, removed by the seed's shadow entry); ld a0,0(s8); beqz a0 -> abort; mv a1,s5; jal strcmp
   (0x87f24); 0x87f28 bnez a0 -> abort; IL *)
Lemma seg_I3b : forall c a, ST_IL B MT c a -> ST_ICMP2 B MT c a.
Proof.
intros c a HIL. unfold ST_ICMP2. intros e lyc Sc Wc regsc memc mdc pos sp1 line j1 q y Hent HI.
destruct HI as (fn & args & HCOM & Hj1 & H23 & H20 & Hparse & H21 & Hsrc & Hwant).
pose proof HCOM as (HCORE & HLINE & _ & _ & H168 & HIR & Hcr & Hnth & Ha).
pose proof HCORE as (HJ & Hsp & Hsp32 & Hsp1 & H3 & H4 & _ & H9 & H22 & _).
pose proof HJ as HJ0.
pose proof HIR as (H26 & H18 & H25 & H24 & H27).
destruct (cwi3_ent e Hent) as (HPRE & _ & _ & _ & _).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & _).
pose proof (cwi3_ncalls e Hent) as Hnc. unfold cw_ncalls in Hnc, Hcr.
destruct (cwi3_arg e c fn args a Hent Hnth ltac:(lia) Ha) as (s & pb & pk & Hs & Hv0 & Hnz & Hin0 & Hlen & Hstr0 & Hl6).
assert (Hsk : skipn (Z.to_nat a) (PCW.call_items fn) =
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn))))
  by (symmetry; exact Hparse).
destruct (cwi3_skipn_cons _ _ _ _ Hsk) as [Hit _].
pose proof (cwi3_words_eq e c fn args a s _ y Hent Hnth Hs Hit Hwant) as Hsy.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pk HAR0 Hin0) as (_ & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (req_size_pos pk ltac:(lia)) as [_ Hrq].
destruct (cwi3_jloc e lyc Sc Wc memc mdc pos EV_JOINED sp1 HJ Hsp1) as (HLO & H47 & H16 & HF1 & HF2).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (HG : A_G_REC = 6173376) by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof HLINE as (HPL & _).
assert (Hin1 : In (pb, pk) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hin0).
assert (Hs4 : A_G_REC <= A_G_REC + 16 + 56 * c + 8 + 8 * a /\ A_G_REC + 16 + 56 * c + 8 + 8 * a + 8 <= A_G_REC + 960 /\
  (A_G_REC + 16 + 56 * c + 8 + 8 * a) mod 8 = 0).
{ split; [lia|]. split; [lia|].
  replace (A_G_REC + 16 + 56 * c + 8 + 8 * a) with ((771675 + 7 * c + a) * 8) by lia.
  apply Z_mod_mult. }
assert (Hv : aval_mem (rdW Wc memc) (A_G_REC + 16 + 56 * c + 8 + 8 * a) 8 pb).
{ intros kk Hk. rewrite (cwi3_grec_kept e lyc Sc Wc memc mdc pos EV_JOINED _ HJ) by lia. exact (Hv0 kk Hk). }
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 (proj1 HJ) ltac:(unfold CW_ZSH; left; reflexivity)) as [RA _].
assert (Hpb : 0 <= pb < 2 ^ 64) by lia.
unfold cw_at, CW_PC_ICMP2.
destruct Hs4 as (Hs4a & Hs4b & Hs4c).
destruct (cwi3_seedB Wc regsc memc sp1 (cw_not (A_G_REC + 16 + 56 * c + 8)) (A_G_REC + 16 + 56 * c + 8 + 8 * a) pb
  H22 H9 H24 H27 ltac:(lia) ltac:(lia) ltac:(unfold cw_not; lia) Hs4a Hs4b Hs4c Hpb ltac:(lia) H168 Hv RA) as [HS SHOK].
pose proof (Eimg_env (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])) as HEI.
pose proof (cwi3_EE regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb]) as EE.
assert (E32 : ew (Eimg (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])) 32 =
  Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (Eimg (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])) 33 = Z_to_bv 64 pb)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (HAE : env_agree 32 (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])
  (Eimg (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb])) as E1 eqn:HE1 in *.
clear HE1.
assert (E25 : ew E1 25 = Z_to_bv 64 (8 * a)) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
(* to the trap site 0x87f04 *)
paj_run_tok RUN HS HJ SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (cwi3_kept_run_ro _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HFr) as KEEP1;
  specialize (KEEP1 ltac:(vm_compute; reflexivity)); clear HFr end.
psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
{ (* ~(cp + 8) is not below 8 a: cp + 8 + 8 a < 2^64 *)
  exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_ltu_U in Hc;
    rewrite (U_atom E1 32 (cw_not (A_G_REC + 16 + 56 * c + 8)) E32 ltac:(unfold cw_not; lia)) in Hc;
    rewrite (U_atom E1 25 (8 * a) E25 ltac:(lia)) in Hc;
    apply Z.ltb_lt in Hc end.
  unfold cw_not in *. lia. }
(* the instrumented check of &args[a] (its error path 0x881a4 removed by the shadow entry), the load of args[a],
   to its null test *)
paj_run_tok RUN HS HJ SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi3_kept_run_ro _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HFr) as KEEP2;
  specialize (KEEP2 ltac:(vm_compute; reflexivity)); clear HFr end.
psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
{ (* the abort edge 0x88170: args[a] <> 0 (acall_at) *)
  exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_eq_U in Hc; apply Z.eqb_eq in Hc;
    rewrite (U_atom _ 33 pb E33) in Hc by lia; change (U _ (SLit 0)) with 0 in Hc end.
  lia. }
(* args[a] <> 0: to the strcmp call *)
paj_run_tok RUN HS HJ SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi3_kept_run_ro _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HFr) as KEEP3;
  specialize (KEEP3 ltac:(vm_compute; reflexivity)); clear HFr end.
pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3
  ltac:(lia) ltac:(lia)) as KEEP13.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regsc [Z_to_bv 64 (cw_not (A_G_REC + 16 + 56 * c + 8)); Z_to_bv 64 pb]
    HS HAE ltac:(vm_compute; reflexivity)) as HPT;
  cbn [ms_regs restrict] in HPT;
  assert (HspT : spZ (ms_regs ms) = sp1) by (unfold spZ in Hsp |- *; rewrite Qsp, (EE 2%nat 2%bv eq_refl); exact Hsp);
  pose proof (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs ms) (ms_mem ms) mdv2 pos sp1 line c a fn args
    Hent HCOM HJ (cw_regs_kept_of_pres _ _ HPT) (cwi3_mem_kept_of _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP13)) as HCOM1;
  pose proof (cwi3_wsrc_move e lyc Sc Wc memc mdc (ms_mem ms) pos sp1 line q y EV_JOINED HJ0 Hsp1 HLINE Hsrc KEEP13) as HSRC1;
  pose proof HCOM1 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S4 & S5) & HLINE1 & _);
  destruct (cwi3_wsrc_ready e lyc Sc Wc (ms_mem ms) mdv2 pos line q y EV_JOINED Hent HJ HLINE1 S4 S5 HSRC1)
    as (Hq0 & Sy & Ry & Ty);
  pose proof (cwi3_blk_str e lyc Sc Wc (ms_mem ms) mdv2 pos EV_JOINED pb pk pb s HJ Hin0 Hin1 ltac:(lia) ltac:(lia) Hstr0)
    as Hstr1;
  destruct (cwi3_blk_ready lyc Sc Wc (ms_mem ms) mdv2 pb pk pb s (proj1 HJ) Hin1 ltac:(lia) ltac:(lia) Hstr1)
    as (Hx0 & Sx & Rx & Tx);
  pmkst HS;
  eapply SRr_bind;
  [ apply (aj_strcmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIG CS___interceptor_trampoline_strcmp) (ASTRCMP fx) Wc
      (ms_regs ms) (ms_mem ms) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc mdv2 EV_JOINED pb q s y (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + 6648)) HJ);
    [ rewrite Ra0; exact E33
    | rewrite Ra1, (EE 21%nat 21%bv eq_refl); exact H21
    | exact Hx0 | exact Hq0 | lia | exact (cwi3_al16 _ _ Hsp32 H16) | lia | rewrite WS, Hes; lia
    | rewrite Qgp, (EE 3%nat 3%bv eq_refl), H3; exact Hgp
    | rewrite Qtp, (EE 4%nat 4%bv eq_refl), H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Sx | exact Sy
    | apply Rx; rewrite HspT, Hes; lia | apply Ry; rewrite HspT, Hes; lia
    | exact Tx | exact Ty
    | exact (cwi3_rom e lyc Sc Wc (ms_mem ms) mdv2 pos EV_JOINED Hent HJ) ]
  | ] end.
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp & Hfr3).
(* back at 0x87f28: strcmp answered 0, args[a] is the item's string *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
  pose proof (cwi3_kept_call Wc (ms_mem ms) mem3 (cw_sp0 e) (sp1 - cw_sp0 e) (2 * ESTACK) sp1 ltac:(lia) Hfr3) as KEEP4 end.
pose proof (aregs_preserved_trans _ _ _ HPT HP3) as HP13.
pose proof (cw_regs_kept_of_pres _ _ HP13) as RKc.
pose proof RKc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K22 & _).
assert (H22c : getr regs3 22 = w64 CW_SB) by (rewrite K22; exact H22).
assert (H10c : getr regs3 10 = w64 0) by (apply Hcmp; exact Hsy).
clear HS SHOK HEI EE HAE E32 E33 E25.
pose proof (cwi3_seed0 Wc regs3 mem3 0x19f8 H22c) as HS.
pose proof (cwi3_sh0 (Eimg (Ereg regs3 [])) (mrestrict (w_H Wc) mem3)) as SHOK.
pose proof (Eimg_env (Ereg regs3 [])) as HEI.
pose proof (cwi3_EE regs3 []) as EE3.
assert (HAE3 : env_agree 32 (Ereg regs3 []) (Eimg (Ereg regs3 [])))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3 in *. clear HE3.
paj_run_tok RUN HS HJ3 SHOK cwi3_Bspan; [awr_ok_tac |].
set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem3) _ |- _ =>
  pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP5; clear HFr end.
psrr_branch_tok RUN BR HS SHOK cwi3_Bspan.
{ (* the abort edge 0x88170: strcmp answered 0 (words_prop_at: args[a] = y) *)
  exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_ne_U in Hc;
    rewrite (U_atom E3 10 0 ltac:(rewrite (EE3 10%nat 10%bv eq_refl); exact H10c) ltac:(lia)) in Hc;
    change (U _ (SLit 0)) with 0 in Hc; vm_compute in Hc; discriminate Hc end. }
paj_run_to_tok RUNTO HS HJ3 SHOK cwi3_Bspan 0x19fc; [awr_ok_tac |].
set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _ |- _ =>
  pose proof (cwi3_kept_run _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 eq_refl HFr) as KEEP6; clear HFr end.
pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP13 KEEP4
  ltac:(lia) ltac:(lia)) KEEP5 ltac:(lia) ltac:(lia)) KEEP6 ltac:(lia) ltac:(lia)) as KEEP.
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- _ =>
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 [] CWI3_KR HS HAE3 ltac:(vm_compute; reflexivity)) as RK3;
  cbn [ms_regs restrict] in RK3;
  pose proof (cw_regs_kept_trans _ _ _ RKc (cwi3_rk_of _ _ RK3)) as RK;
  pose proof RK as (_ & _ & _ & _ & _ & _ & _ & R20' & _ & _ & R23' & _);
  assert (INV : INV_IL B MT e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv4 pos sp1 line c a j1);
  [ exists fn, args;
    split; [exact (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs ms) (ms_mem ms) mdv4 pos sp1 line c a fn args
                     Hent HCOM HJ3 RK (cwi3_mem_kept_of _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP))|];
    split; [exact Hj1|]; split; [rewrite R23'; exact H23|]; split; [rewrite R20'; exact H20 | exact Hparse]
  | ];
  pmkst HS;
  exact (HIL e lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv4 pos sp1 line j1 Hent INV) end.
Qed.
End e.
End f.
End d.
