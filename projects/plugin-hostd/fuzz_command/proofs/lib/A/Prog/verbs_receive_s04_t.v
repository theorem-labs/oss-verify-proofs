(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S04 (TOK, 0x8d67c-0x8d6f8) of the walk of verbs_receive on the ASan build
   of plugin-hostd/fuzz_command: one call of musl's strtok_r(s, " \t", &save) from verbs_receive, through
   astrtok_r_realizes (lib/A/Rt/RtString.v) composed into the walk's journal by the kit's aj_art_own_at (PaArtOwn.v).
   The string strtok_r walks is the rest of the copy block from C (s, or the saved pointer when s is null); the call
   cuts the next word out of it in place. The word facts are the plain proof's (lib/Prog/verbs_receive_words.v,
   lib/Prog/verbs_receive_tok.v:60-102). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaArtOwn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_words strtok_r_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtAlloc04 RtAlloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s04_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Module PVW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_words.
Module PTk := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strtok_r_c.

(* ---------------------------------------------------------------------------------------------------------------
   The words of a string and the cut strtok_r makes (lib/Prog/verbs_receive_tok.v:32-102, over lists only) *)
Lemma s4_firstn_split : forall {A} (l : list A) i j, (i <= j)%nat ->
firstn j l = firstn i l ++ firstn (j - i) (skipn i l).
Proof.
intros A l. induction l as [|x l IH]; intros i j H.
- rewrite skipn_nil, !firstn_nil. reflexivity.
- destruct i as [|i]; [cbn [firstn skipn app]; rewrite Nat.sub_0_r; reflexivity|].
  destruct j as [|j]; [lia|]. cbn [firstn skipn app Nat.sub]. f_equal. apply IH. lia.
Qed.
Lemma s4_cut_len : forall r, length (PTk.tok_cut PVW.sepl r) = length r.
Proof.
intros r. pose proof (PVW.tok_j_le r). unfold PTk.tok_cut.
destruct (Nat.ltb_spec (PTk.tok_j PVW.sepl r) (length r)) as [L|L]; [|reflexivity].
rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. lia.
Qed.
Lemma s4_word_len : forall r, length (PVW.tok_word r) = (PTk.tok_j PVW.sepl r - PTk.tok_i PVW.sepl r)%nat.
Proof. intros r. pose proof (PVW.tok_j_le r). unfold PVW.tok_word. rewrite length_firstn, length_skipn. lia. Qed.
Lemma s4_cut_split : forall r, (PTk.tok_i PVW.sepl r < length r)%nat ->
PTk.tok_cut PVW.sepl r ++ [Z_to_bv 8 0] =
firstn (PTk.tok_i PVW.sepl r) r ++ (PVW.tok_word r ++ [Z_to_bv 8 0]) ++
(if Nat.ltb (PTk.tok_j PVW.sepl r) (length r) then PVW.tok_rest r ++ [Z_to_bv 8 0] else []).
Proof.
intros r H. pose proof (PVW.tok_i_le_j r) as IJ. pose proof (PVW.tok_j_le r) as JL.
unfold PTk.tok_cut, PVW.tok_word, PVW.tok_rest.
destruct (Nat.ltb_spec (PTk.tok_j PVW.sepl r) (length r)) as [L|L].
- rewrite (s4_firstn_split r (PTk.tok_i PVW.sepl r) (PTk.tok_j PVW.sepl r)) by lia. rewrite <- !app_assoc. reflexivity.
- assert (Ej : PTk.tok_j PVW.sepl r = length r) by lia. rewrite Ej.
  rewrite (firstn_all2 (n := (length r - PTk.tok_i PVW.sepl r)%nat)) by (rewrite length_skipn; lia).
  rewrite app_nil_r, app_assoc, firstn_skipn. reflexivity.
Qed.
Lemma s4_abytes_app : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) ->
abytes_atR rd a l1 /\ abytes_atR rd (a + Z.of_nat (length l1)) l2.
Proof.
intros rd a l1 l2 H. split.
- intros i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by lia. reflexivity.
- intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
  rewrite (H (length l1 + i)%nat) by (rewrite length_app; lia). rewrite app_nth2 by lia.
  replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
Qed.
Lemma s4_notin_sub : forall (l l' : list byte), (forall b, In b l' -> In b l) -> ~ In (Z_to_bv 8 0) l -> ~ In (Z_to_bv 8 0) l'.
Proof. intros l l' Hs Hn Hin. exact (Hn (Hs _ Hin)). Qed.
Lemma s4_sep_lit : RO_lit_224c0 = PVW.sepl ++ [Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma s4_sep_nz : ~ In (Z_to_bv 8 0) PVW.sepl.
Proof.
unfold PVW.sepl. cbn [map]. intros [H | [H | []]]; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.
Qed.
Lemma s4_sep_len : astr_len PVW.sepl = 2.
Proof. reflexivity. Qed.
Lemma s4_abytes_eq : forall (rd : reader) a b l, abytes_atR rd a l -> a = b -> abytes_atR rd b l.
Proof. intros rd a b l H E. subst b. exact H. Qed.

(* the rest of the copy that strtok_r will walk: none (C = 0, no word left), or the string r at C, ending at the
   copy block's end c + n, whose words are the words left *)
Definition s4_rem (rd : reader) (c n C : Z) (ws : list (list byte)) : Prop :=
(C = 0 /\ ws = []) \/
(exists r, C <> 0 /\ astr_atR rd C r /\ c <= C /\ C + Z.of_nat (length r) + 1 = c + n /\ Verbs.words r = ws).
(* what one call returns: no word (a0 = 0), or the next word w at a0, which ends at the new saved pointer sv (or at
   the block's end when none is left), and the rest from sv *)
Definition s4_tres (rd : reader) (a0 c n C sv : Z) (ws : list (list byte)) : Prop :=
match ws with
| [] => a0 = 0
| w :: ws' => a0 <> 0 /\ C <= a0 /\ astr_atR rd a0 w /\
  a0 + Z.of_nat (length w) + 1 = (if sv =? 0 then c + n else sv) /\ s4_rem rd c n sv ws'
end.

Lemma s4_tok_res : forall (rd : reader) c n C r ws, 0 < c -> ~ In (Z_to_bv 8 0) r -> C <> 0 -> c <= C ->
C + Z.of_nat (length r) + 1 = c + n -> Verbs.words r = ws ->
abytes_atR rd C (PTk.tok_cut PVW.sepl r ++ [Z_to_bv 8 0]) ->
s4_tres rd (PTk.tok_ret C PVW.sepl r) c n C (PTk.tok_save C PVW.sepl r) ws.
Proof.
intros rd c n C r ws Hc Hnz HC0 HcC HCn Hws Hb.
pose proof (PVW.tok_i_le_j r) as IJ. pose proof (PVW.tok_j_le r) as JL.
destruct (Nat.lt_ge_cases (PTk.tok_i PVW.sepl r) (length r)) as [IL | IG].
- destruct (PVW.words_step r IL) as (WS & _ & IJ'). rewrite <- Hws, WS. cbn [s4_tres].
  assert (TR : PTk.tok_ret C PVW.sepl r = C + Z.of_nat (PTk.tok_i PVW.sepl r)).
  { unfold PTk.tok_ret. rewrite (proj2 (Z.eqb_neq C 0) HC0).
    destruct (Nat.eqb_spec (PTk.tok_i PVW.sepl r) (length r)); [lia|]. reflexivity. }
  rewrite TR. rewrite (s4_cut_split r IL) in Hb.
  apply s4_abytes_app in Hb as [_ Hb]. apply s4_abytes_app in Hb as [Hw Hrest].
  rewrite length_firstn, Nat.min_l in Hw, Hrest by lia. rewrite length_app, s4_word_len in Hrest. cbn [length] in Hrest.
  assert (Hwnz : ~ In (Z_to_bv 8 0) (PVW.tok_word r)) by exact (s4_notin_sub r _ (PVW.in_tok_word r) Hnz).
  rewrite s4_word_len.
  split; [lia|]. split; [lia|]. split; [split; [exact Hw | exact Hwnz]|].
  destruct (Nat.ltb_spec (PTk.tok_j PVW.sepl r) (length r)) as [JL' | JG].
  + assert (TS : PTk.tok_save C PVW.sepl r = C + Z.of_nat (PTk.tok_j PVW.sepl r) + 1).
    { unfold PTk.tok_save. rewrite (proj2 (Z.eqb_neq C 0) HC0).
      destruct (Nat.leb_spec (length r) (PTk.tok_j PVW.sepl r)); [lia|]. reflexivity. }
    rewrite TS. replace (C + Z.of_nat (PTk.tok_j PVW.sepl r) + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota.
    split; [lia|]. right. exists (PVW.tok_rest r).
    assert (RL : length (PVW.tok_rest r) = (length r - S (PTk.tok_j PVW.sepl r))%nat)
      by (unfold PVW.tok_rest; apply length_skipn).
    split; [lia|]. split.
    * split; [|exact (s4_notin_sub r _ (PVW.in_tok_rest r) Hnz)].
      apply (s4_abytes_eq _ _ _ _ Hrest). lia.
    * split; [lia|]. split; [rewrite RL; lia | reflexivity].
  + assert (TS : PTk.tok_save C PVW.sepl r = 0).
    { unfold PTk.tok_save. rewrite (proj2 (Nat.leb_le _ _) JG). rewrite orb_true_r. reflexivity. }
    rewrite TS. cbn [Z.eqb]. split; [lia|]. left. split; [reflexivity|].
    unfold PVW.tok_rest. rewrite skipn_all2 by lia. reflexivity.
- assert (EI : PTk.tok_i PVW.sepl r = length r) by lia. rewrite <- Hws, (PVW.words_none r EI). cbn [s4_tres].
  unfold PTk.tok_ret. rewrite EI, Nat.eqb_refl, orb_true_r. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis STRTOK_R : RtString.astrtok_r_realizes SEGS B (SIGMA CS_strtok_r) 0xa7098 0x6045d8.
Hypothesis TL : PALib B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the saved-pointer word at F + 608 of the side-stack frame: its shadow byte (index 76) is 0 *)
Lemma s4_awr_save : forall stk ly S (W : world SEGS) regs mem md pos,
AR SEGS B ly S W mem md -> In (4, pos) (frames S) ->
rdW W mem (shadow_addr (frame_addr ly 4 pos) + 76) = Some 0 ->
alloc_ceiling <= spZ regs - stk -> awrite_ok SEGS B stk ly S W regs mem (frame_addr ly 4 pos + 608) 8.
Proof.
intros stk ly S W regs mem md pos HAR Hin Hsh Hs.
destruct (al_frames _ _ LAWS ly S W mem md 4 pos HAR Hin) as (_ & Happ & Hb & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md 4 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (frame_al64 SEGS B ly S W mem md 4 pos HAR Hin) as (H64 & _).
change (fs_frame_bytes 4) with 1024 in Happ, Hb, Hfc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod (frame_addr ly 4 pos) 8 ltac:(lia)) as D8.
pose proof (Z.div_mod (frame_addr ly 4 pos) 64 ltac:(lia)) as D64.
pose proof (Z.mod_pos_bound (frame_addr ly 4 pos) 8 ltac:(lia)) as M8.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. destruct (Hb a ltac:(lia)) as [Hp Ho].
  split; [exact (apresent_writable SEGS _ _ _ Hp)|]. split; [exact Ho|]. unfold ascratch_stk. lia. }
split; [exact (amem_range_sub_app (frame_addr ly 4 pos) 1024 (frame_addr ly 4 pos + 608) 8 Happ Hfc
  ltac:(lia) ltac:(lia) ltac:(lia))|]. split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (E : x / 8 = frame_addr ly 4 pos / 8 + 76) by (symmetry; apply Z.div_unique with (r := x - 8 * (frame_addr ly 4 pos / 8 + 76)); lia).
  unfold shadow_of_addr. rewrite E. unfold shadow_addr in Hsh. rewrite <- Z.add_assoc in Hsh. exact Hsh.
- intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem md 4 pos (frame_addr ly 4 pos + 608) 8 HAR Hin ltac:(lia)
    ltac:(change (fs_frame_bytes 4) with 1024; lia) ltac:(lia)).
Qed.

(* the separator literal " \t" (.str, 0x224c0): its bytes, read range and word tail *)
Lemma s4_sep_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x224c0 RO_lit_224c0.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. assumption. Qed.
Lemma s4_sep_shr : In (0x224c0, 3) vr_shr.
Proof. unfold vr_shr. apply in_or_app. left. apply in_map_iff. exists (0x224c0, RO_lit_224c0). split; [reflexivity | left; reflexivity]. Qed.
Lemma s4_rd_sep : forall stk ly S (W : world SEGS) regs mem md,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> alloc_ceiling <= spZ regs - stk ->
aread_ok SEGS stk W regs mem 0x224c0 3.
Proof.
intros stk ly S W regs mem md HAR Hro Hs.
destruct (SHOK ly S W mem md 0x224c0 3 HAR s4_sep_shr) as [HRA HHV].
pose proof (s4_sep_bytes _ Hro) as Hb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split.
  - replace a with (0x224c0 + Z.of_nat (Z.to_nat (a - 0x224c0))) by lia.
    rewrite (Hb (Z.to_nat (a - 0x224c0))); [discriminate | cbn; lia].
  - unfold ascratch_stk. lia. }
split; [left; unfold kLowMemEnd; lia|]. split; [exact HRA | intros _; exact HHV].
Qed.
Lemma s4_tail_sep : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> atail_vis SEGS W mem 0x224c2.
Proof.
intros W mem [_ HT]. intros a Ha. apply (HT 0x224c2); [|exact Ha].
apply In_of_existsb. vm_compute. reflexivity.
Qed.

(* one call of strtok_r(s, " \t", &save) at sp = s1, the saved-pointer word at F + 608 holding pv: the journal goes
   on with the same events; the call writes only below s1, the saved-pointer word, and the rest of the copy from C;
   it returns the next word, as s4_tres says *)
Lemma s4_tok_call : forall e pos F c n lyc Sc (W : world SEGS) regsT memT mdc k (s pv C : Z) ws,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W memT mdc k ->
F = frame_addr lyc 4 pos ->
In (c, n) (ablocks B lyc Sc) -> ~ In (c, n) (ablocks B (e_ly e) (e_S e)) ->
rdW W memT (shadow_addr F + 76) = Some 0 ->
spZ regsT = vr_s1 e ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regsT 1) ->
getr regsT 10 = w64 s -> getr regsT 11 = w64 0x224c0 -> getr regsT 12 = w64 (F + 608) ->
rdword (rdW W memT) (F + 608) = Some pv ->
C = (if s =? 0 then pv else s) ->
s4_rem (rdW W memT) c n C ws ->
arodata_okP SEGS RLO RHI B (rdW W memT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA CS_strtok_r)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (vr_s1 e - 4 * ESTACK <= a < vr_s1 e) -> ~ (F + 608 <= a < F + 616) ->
    ~ (C <> 0 /\ C <= a < c + n) -> rdW W mem2 a = rdW W memT a) /\
  exists a0 sv, getr regs2 10 = w64 a0 /\ rdword (rdW W mem2) (F + 608) = Some sv /\ s4_tres (rdW W mem2) a0 c n C sv ws).
Proof.
intros e pos F c n lyc Sc W regsT memT mdc k s pv C ws HJ EF Hcb Hcnew Hsh Hsp Hgp Htp Hra H10 H11 H12 Hpv EC Hrem Haro.
subst F.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HSTK : VERBS_RECEIVE_STK = 16992) by reflexivity.
destruct (s1_off e Hal16) as [Hs1o Hs1r].
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc 4 pos HAR Hfr) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
unfold MALLOC_MAX in Hcn. pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memT mdc _ _ 4 pos HAR Hcb Hfr) as Hcf.
unfold zdisjoint in Hcf. cbn [fst snd] in Hcf. change (fs_frame_bytes 4) with 1024 in Hcf.
pose proof (blk_off_imgP B lyc Sc W memT mdc _ _ HAR Hcb) as Hoff. unfold off_img in Hoff.
pose proof (ROA lyc Sc W memT mdc HAR Haro) as Hro.
(* the string strtok_r walks *)
assert (Hstr : exists str, (C <> 0 -> astr_atR (rdW W memT) C str /\ c <= C /\ C + Z.of_nat (length str) + 1 = c + n /\
  Verbs.words str = ws) /\ (C = 0 -> ws = [])).
{ destruct Hrem as [(H0 & Hw) | (r & Hr0 & Hr & Hcr & Hrn & Hwr)].
  - exists []. split; [intros Hn0; contradiction | intros _; exact Hw].
  - exists r. split; [intros _; auto | intros H0; contradiction]. }
destruct Hstr as (str & Hstr & Hstr0).
assert (Hsp1 : alloc_ceiling <= spZ regsT - 4 * ESTACK) by (rewrite Hsp; lia).
pose proof (ecall_pre_stk_at SEGS B (4 * ESTACK) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
  (e_md e) [(4, pos)] lyc Sc W memT mdc k regsT (vr_s1 e - vr_sp0 e) HJ ltac:(rewrite Hsp; lia) Hs1o ltac:(lia)
  ltac:(lia) ltac:(lia) Hra Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_art_own_at SEGS B LAWS pa_segs_low (4 * ESTACK)
    (fun a => (frame_addr lyc 4 pos + 608 <= a < frame_addr lyc 4 pos + 608 + 8) \/ (C <> 0 /\ C <= a < C + astr_len str + 1))
    (SIGMA CS_strtok_r) W regsT memT VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(4, pos)] lyc Sc mdc k (vr_s1 e - vr_sp0 e) (getr regsT 1)
    (fun regs' mem' => getr regs' 10 = w64 (PTk.tok_ret C PVW.sepl str) /\
      rdword (aview SEGS (w_H W) mem') (frame_addr lyc 4 pos + 608) = Some (PTk.tok_save C PVW.sepl str) /\
      (C <> 0 -> abytes_at SEGS W mem' C (PTk.tok_cut PVW.sepl str ++ [Z_to_bv 8 0]))) HJ).
  - rewrite Hsp. lia.
  - exact Hs1o.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - intros a [Ha | (HC0 & Ha)].
    + right; right; right; left. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 4) with 1024. lia.
    + right; right; left. exists c, n. split; [exact Hcb|]. split; [exact Hcnew|].
      destruct (Hstr HC0) as (_ & Hcr & Hrn & _). unfold astr_len in Ha. lia.
  - destruct (RECC lyc Sc W memT mdc HAR) as (_ & HAG & _).
    apply (STRTOK_R lyc Sc W regsT memT mdc s 0x224c0 (frame_addr lyc 4 pos + 608) pv PVW.sepl str C HAG HPRE H10 H11 H12).
    + lia.
    + lia.
    + exact Hpv.
    + exact EC.
    + apply astr_atR_view. split; [rewrite <- s4_sep_lit; exact (s4_sep_bytes _ Hro) | exact s4_sep_nz].
    + rewrite s4_sep_len. exact (s4_rd_sep (4 * ESTACK) lyc Sc W regsT memT mdc HAR Hro Hsp1).
    + rewrite s4_sep_len. exact (amem8_of_low 0x224c0 2 ltac:(lia) ltac:(unfold kLowMemEnd; lia)).
    + rewrite s4_sep_len. exact (s4_tail_sep W memT Hro).
    + exact (s4_awr_save (4 * ESTACK) lyc Sc W regsT memT mdc pos HAR Hfr Hsh Hsp1).
    + intros HC0. destruct (Hstr HC0) as (Hs & Hcr & Hrn & _). rewrite s4_sep_len. unfold astr_len.
      split; [lia|]. split; [apply astr_atR_view; exact Hs|]. split.
      { apply (aread_ok_of_block SEGS B LAWS (4 * ESTACK) lyc Sc W regsT memT mdc c n C _ HAR Hcb); [lia | lia | lia | exact Hsp1]. }
      split; [apply (amem8_of_blockA SEGS B LAWS lyc Sc W memT mdc C (Z.of_nat (length str)) HAR);
        [exists c, n; split; [exact Hcb | lia] | lia]|].
      split; [apply (awrite_ok_of_block SEGS B LAWS (4 * ESTACK) lyc Sc W memT mdc regsT c n C _ HAR Hcb); [lia | lia | lia | exact Hsp1]|].
      split; [apply (BLKT lyc Sc W memT mdc c n); [exact HAR | exact Hcb | lia]|].
      split; [lia|]. lia.
    + exact (vr_rtrom_ok B W memT Haro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (Q1 & Q2 & Q3) & Hfr2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split.
{ intros a Ha Hw Hsv Hcp. apply Hfr2; [exact Ha | intros Hx; apply Hw; lia |].
  intros [Hb | (HC0 & Hb)]; [apply Hsv; lia|]. apply Hcp. split; [exact HC0|].
  destruct (Hstr HC0) as (_ & Hcr & Hrn & _). unfold astr_len in Hb. lia. }
exists (PTk.tok_ret C PVW.sepl str), (PTk.tok_save C PVW.sepl str).
split; [exact Q1|]. split; [exact Q2|].
destruct (Z.eq_dec C 0) as [HC0 | HC0].
- rewrite (Hstr0 HC0). cbn [s4_tres]. unfold PTk.tok_ret. rewrite HC0. reflexivity.
- destruct (Hstr HC0) as ((Hs & Hnz) & Hcr & Hrn & Hws).
  apply (s4_tok_res (rdW W mem2) c n C str ws ltac:(lia) Hnz HC0 Hcr Hrn Hws).
  apply abytes_atR_view. exact (Q3 HC0).
Qed.

End e.
End f.
End d.
