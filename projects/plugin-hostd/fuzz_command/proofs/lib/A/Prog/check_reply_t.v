(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the facts a segment of check_reply's walk (fuzz_command.asan, 0x86d78) reads at
   a mid-walk state, carried from the entry bundle `cr_cx` and the mid-walk invariant `cr_mid` of
   lib/A/Prog/check_reply_m.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v
   (c8557374ad2e: the facts a cgif_close segment reads at a call, from the entry facts and the journal).

   The journal of cr_mid has the footprint [], so it keeps: every byte above the entry's sp (the harness's words
   w->w and w->n), every byte of a block live at the entry and now (the reply, the answer, the recorded strings and
   w's words), and every image byte that is not owned and not errno (g_rec, record.spill, the GOT words of the
   recorder and the read-only bytes; CmdRecImg's cmd_prog_unowned puts g_rec and record.spill there). The allocator
   invariant AR at the current state gives the shadow of the stack window, of g_rec and of the literals, the
   runtime's cells, and the bytes after a block's last byte up to the end of its 8-byte word (CmdRecImg's
   cmd_heap_tail_vis); the runtime's read-only view is CmdRecImg's cmd_rom_view_on. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk
  CmdRecBase CmdRecCells CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k check_reply_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* two 8-byte little-endian values with the same bytes agree mod 2^64 *)
Lemma le_byte8_inj : forall x y, (forall k, (k < 8)%nat -> le_byte x 8 k = le_byte y 8 k) -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros x y H.
assert (E : forall z k, le_byte (z mod 2 ^ 64) 8 k = le_byte z 8 k) by (intros z k; rewrite !le_byte_8, Z.mod_mod by lia; reflexivity).
rewrite <- (le_bytes8 (x mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite <- (le_bytes8 (y mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
rewrite !E. rewrite !H by lia. reflexivity.
Qed.
Lemma aval_mem_mod64 : forall (rd : reader) a x y, aval_mem rd a 8 x -> aval_mem rd a 8 y -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
intros rd a x y Hx Hy. apply le_byte8_inj. intros k Hk.
pose proof (Hx k Hk) as E1. pose proof (Hy k Hk) as E2. rewrite E1 in E2. injection E2 as E. exact E.
Qed.
(* facts over a reader carried to a reader that agrees on the bytes they name *)
Lemma aval_mem_agree : forall (rd rd' : reader) a n v,
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v K H k Hk. rewrite K by lia. exact (H k Hk). Qed.
Lemma abytes_atR_agree : forall (rd rd' : reader) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd a l -> abytes_atR rd' a l.
Proof. intros rd rd' a l K H i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma astr_atR_agree : forall (rd rd' : reader) a s,
(forall x, a <= x < a + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd a s -> astr_atR rd' a s.
Proof.
intros rd rd' a s K [H1 H2]. split; [|exact H2].
apply (abytes_atR_agree rd); [|exact H1]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply K. lia.
Qed.
Lemma in_blockA_perm : forall bl bl' a n, Permutation bl bl' -> in_blockA bl a n -> in_blockA bl' a n.
Proof. intros bl bl' a n HP (p & k & Hin & H1 & H2). exists p, k. split; [exact (Permutation_in _ HP Hin) | lia]. Qed.
(* an address range that no range of l meets, by computation *)
Lemma not_in_zr_check : forall (l : list (Z * Z)) lo n,
forallb (fun i => negb (existsb (fun r => (fst r <=? lo + Z.of_nat i) && (lo + Z.of_nat i <? fst r + snd r)) l))
(seq 0 n) = true ->
forall a, lo <= a < lo + Z.of_nat n -> ~ Exists (in_zr a) l.
Proof.
intros l lo n Hc a Ha Hex.
rewrite forallb_forall in Hc. specialize (Hc (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
apply negb_true_iff in Hc. rewrite Z2Nat.id in Hc by lia. replace (lo + (a - lo)) with a in Hc by lia.
apply Exists_exists in Hex as (r & Hr & H1 & H2).
assert (Ht : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite Ht in Hc. discriminate.
Qed.
(* the four GOT words the recorder functions load are among cmd_ro_in's read-only ranges *)
Lemma cmd_ro_in_got : forall (ro : Z -> Prop), cmd_ro_in ro -> forall a, 0xa7068 <= a < 0xa7088 -> ro a.
Proof.
intros ro H a Ha. unfold cmd_ro_in in H.
repeat lazymatch type of H with
| (forall i, 0 <= i < 8 -> ro (0xa7068 + i)) /\ _ => fail
| _ /\ _ => apply proj2 in H
end.
pose proof (proj1 H) as H1. apply proj2 in H. pose proof (proj1 H) as H2. apply proj2 in H.
pose proof (proj1 H) as H3. apply proj2 in H.
assert (H4 : forall i, 0 <= i < 8 -> ro (0xa7080 + i)) by (lazymatch type of H with _ /\ _ => exact (proj1 H) | _ => exact H end).
destruct (Z_lt_le_dec a 0xa7070); [replace a with (0xa7068 + (a - 0xa7068)) by lia; apply H1; lia|].
destruct (Z_lt_le_dec a 0xa7078); [replace a with (0xa7070 + (a - 0xa7070)) by lia; apply H2; lia|].
destruct (Z_lt_le_dec a 0xa7080); [replace a with (0xa7078 + (a - 0xa7078)) by lia; apply H3; lia|].
replace a with (0xa7080 + (a - 0xa7080)) by lia. apply H4. lia.
Qed.
Lemma mod4096_8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma z2bv_mod64 : forall e, Z_to_bv 64 (e mod 2 ^ 64) = Z_to_bv 64 e.
Proof.
intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

(* the shadow byte the allocator record (lib/A/AF0m.v) states at s: 0 inside the shadow of a zero-shadow range
   (Tfib_zero_shadow), else the value of a const one-byte shadow cell at s (Tfib_const_shadow) *)
Definition zsh_byteb (s : Z) : bool :=
existsb (fun r => (SHADOW_OFF + fst r / 8 <=? s) && (s <? SHADOW_OFF + fst r / 8 + snd r / 8)) Tfib_zero_shadow.
Fixpoint csh_val (l : list acell) (s : Z) : option Z :=
match l with
| [] => None
| ACell (ANum x) (S O) (AV (ANum w)) :: t => if x =? s then Some w else csh_val t s
| _ :: t => csh_val t s
end.
Lemma csh_val_in : forall l s w, csh_val l s = Some w -> In (ACell (ANum s) 1 (AV (ANum w))) l.
Proof.
induction l as [|c t IH]; intros s w H; [discriminate|].
assert (Hr : csh_val t s = Some w -> In (ACell (ANum s) 1 (AV (ANum w))) (c :: t)) by (intros E; right; exact (IH s w E)).
destruct c as [ca cw cv]. destruct ca; try (apply Hr; exact H).
destruct cw as [|[|cw]]; try (apply Hr; exact H).
destruct cv as [ce|m v0]; try (apply Hr; exact H).
destruct ce; try (apply Hr; exact H).
revert H. cbn [csh_val].
lazymatch goal with |- (if ?x =? s then _ else _) = _ -> _ => destruct (Z.eqb_spec x s) as [->|Hne] end;
intros H; [injection H as <-; left; reflexivity | apply Hr; exact H].
Qed.
Definition shb (s : Z) : option Z :=
if zsh_byteb s then Some 0 else option_map (fun w => le_byte w 1 0) (csh_val Tfib_const_shadow s).
(* every byte of [a, a + n) has a shadow byte that says usable (YG0v.v saddr_ok) *)
Definition lit_addr_okb (a n : Z) : bool :=
forallb (fun k => let x := a + Z.of_nat k in
  match shb (SHADOW_OFF + x / 8) with Some s => (s =? 0) || ((x mod 8 <? s) && (s <? 8)) | None => false end)
(seq 0 (Z.to_nat n)).
(* every shadow byte of the 8-byte shadow words over [a, a + n) is stated (YG0d.v shadow_hull_vis) *)
Definition lit_hull_okb (a n : Z) : bool :=
let lo := (SHADOW_OFF + a / 8) / 8 * 8 in let hi := (SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 + 8 in
forallb (fun k => match shb (lo + Z.of_nat k) with Some _ => true | None => false end) (seq 0 (Z.to_nat (hi - lo))).
(* no byte of [a, a + n) is a runtime-owned static or the errno cell *)
Definition lit_unowned_okb (a n : Z) : bool :=
forallb (fun k => negb (existsb (fun r => (fst r <=? a + Z.of_nat k) && (a + Z.of_nat k <? fst r + snd r)) Tfib_owned_static)
  && negb ((TFIB_ERRNO <=? a + Z.of_nat k) && (a + Z.of_nat k <? TFIB_ERRNO + 4))) (seq 0 (Z.to_nat n)).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma fp_spares_nil : forall a, fp_spares [] a.
Proof. intros a. apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the reader sees addresses mod 2^64 *)
Lemma aview_mod64 : forall (H : word -> bool) (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof. intros H m a. unfold aview, mbyte. rewrite z2bv_mod64. reflexivity. Qed.
Lemma atail_vis_mod : forall (W : world SEGS) mem e e', e mod 2 ^ 64 = e' mod 2 ^ 64 ->
atail_vis SEGS W mem e' -> atail_vis SEGS W mem e.
Proof.
intros W mem e e' He H a Ha.
pose proof (Z.div_mod e (2 ^ 64) ltac:(lia)) as D1. pose proof (Z.div_mod e' (2 ^ 64) ltac:(lia)) as D2.
set (q := e' / 2 ^ 64 - e / 2 ^ 64).
assert (Ee' : e' = e + q * 2 ^ 64) by (subst q; lia).
assert (M8 : e' mod 8 = e mod 8).
{ rewrite Ee'. replace (q * 2 ^ 64) with ((q * 2 ^ 61) * 8) by lia. apply Z_mod_plus_full. }
specialize (H (a + q * 2 ^ 64) ltac:(lia)).
rewrite aview_mod64 in H. rewrite Z_mod_plus_full in H. rewrite aview_mod64. exact H.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).

(* the journal with footprint [] keeps the program's statics and the blocks live at both ends *)
Lemma aj_img_PG : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
forall a, inFP cmd_PG a -> rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Ha) as (I1 & I2 & I3).
exact (Himg a I1 I2 I3 (fp_spares_nil a)).
Qed.
Lemma aj_blk : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p n i,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
rdW W' mem' (p + i) = rdW W mem (p + i).
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n i HJ H1 H2 Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _).
apply (Hblk p n i H1 H2); [unfold req_size; destruct (Z.eqb_spec n 0); lia | apply inFP_nil].
Qed.

(* 1. the image facts and the runtime's cells at the mid-walk state *)
Lemma cr_state_facts : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc) /\ cmd_got_ok (rdW Wc memc) /\
aguard_ok SEGS Wc memc 0xa7098 0x6045d8 /\ rdW Wc memc A_FLAG_REPLACE_STR = Some 1 /\
(exists ev, rd32 (rdW Wc memc) (as_errno B) ev) /\ rt_rom_view SEGS B Wc memc /\
cmd_ro_in (in_roP SEGS RLO RHI) /\ cmd_val_objs.
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
pose proof HCX as (_ & _ & HRO & HGOT & _ & HROIN & HVAL & _).
pose proof HM as (HJ & _).
pose proof HJ as (HAR & _).
assert (HROc : arodata_okP SEGS RLO RHI B (rdW Wc memc)).
{ apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [intros a _; apply inFP_nil | exact HRO]. }
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR) as (Hflag & Hguard & Hev).
split; [exact HROc|]. split; [exact (CMD_RO_AT _ _ _ _ _ HAR HROc)|].
split; [|split; [exact Hguard|]; split; [exact Hflag|]; split; [exact Hev|];
  split; [exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI Wc memc HROc)|];
  split; [exact HROIN | exact HVAL]].
assert (K : forall a, 0xa7068 <= a < 0xa7088 -> rdW Wc memc a = rdW (c_W v) (c_mem v) a).
{ intros a Ha.
  pose proof (cmd_ro_in_got _ HROIN a Ha) as Hro.
  assert (Ho : ~ Exists (in_zr a) (as_owned_static B)).
  { rewrite (ts_owned B HB). exact (not_in_zr_check Tfib_owned_static 0xa7068 32 ltac:(vm_compute; reflexivity) a ltac:(lia)). }
  assert (He : ~ (as_errno B <= a < as_errno B + 4)) by (rewrite (ts_errno B HB); unfold TFIB_ERRNO; lia).
  rewrite (HROc a Hro Ho He), (HRO a Hro Ho He). reflexivity. }
destruct HGOT as (G1 & G2 & G3 & G4).
split; [|split; [|split]].
- apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact G1]. intros x Hx. apply K. change (Z.of_nat 8) with 8 in Hx. lia.
- apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact G2]. intros x Hx. apply K. change (Z.of_nat 8) with 8 in Hx. lia.
- apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact G3]. intros x Hx. apply K. change (Z.of_nat 8) with 8 in Hx. lia.
- apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact G4]. intros x Hx. apply K. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

(* the reply's block at the entry: g_rec.reply points at its start *)
Lemma cr_reply_block : forall v,
cr_cx B RLO RHI v ->
exists m, In (c_p v, m) (ablocks B (c_ly v) (c_S v)) /\ c_nr v + 1 <= m /\
abytes_atR (rdW (c_W v) (c_mem v)) (c_p v) (c_xr v ++ [Z_to_bv 8 0]).
Proof.
intros v HCX.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & HRR & _ & HREPV & _).
destruct HREP as (Q & (_ & _ & _ & _ & _ & HRP & _) & _).
rewrite HRR in HRP. unfold areply_at in HRP. destruct (l_reply Q) as [[p m]|]; [|contradiction].
destruct HRP as (P1 & _ & _ & _ & P5 & P6 & P7 & _). cbn [fst snd] in *.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR P5) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [Hr1 _].
assert (Ep : c_p v = p).
{ unfold c_p. rewrite (aval_mem_mod64 _ _ _ _ HREPV P1). apply Z.mod_small. pose proof alloc_ceiling_lt. lia. }
exists m. rewrite Ep. rewrite length_app in P6. cbn [length] in P6. unfold c_nr.
split; [exact P5|]. split; [lia | exact P7].
Qed.

(* 2. the reply at the mid-walk state *)
Lemma cr_reply_facts : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
exists m, In (c_p v, m) (ablocks B lyc Sc) /\ c_nr v + 1 <= m /\ astr_atR (rdW Wc memc) (c_p v) (c_xr v) /\
atail_vis SEGS Wc memc (c_p v + c_nr v) /\ in_blockA (ablocks B lyc Sc) (c_p v) (c_nr v + 1) /\
(forall i, 0 <= i < c_nr v -> exists b, rdW Wc memc (c_p v + i) = Some b /\ b <> 0).
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
destruct (cr_reply_block v HCX) as (m & Hin0 & Hm & Hbytes).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNO0 & _).
pose proof HM as (HJ & HPERM & _).
pose proof HJ as (HARc & _).
assert (Hin : In (c_p v, m) (ablocks B lyc Sc)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin0).
assert (Hbc : abytes_atR (rdW Wc memc) (c_p v) (c_xr v ++ [Z_to_bv 8 0])).
{ apply (abytes_atR_agree (rdW (c_W v) (c_mem v))); [|exact Hbytes].
  intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold c_nr in Hm.
  replace x with (c_p v + (x - c_p v)) by lia.
  apply (aj_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hin0 Hin). lia. }
exists m. split; [exact Hin|]. split; [exact Hm|]. split; [split; [exact Hbc | exact HNO0]|].
split.
{ apply (cmd_heap_tail_vis SEGS B LAWS HB lyc Sc Wc memc mdc (c_p v) m); [exact HARc | exact Hin |].
  unfold req_size, c_nr in *. destruct (Z.eqb_spec m 0); lia. }
split; [exists (c_p v), m; split; [exact Hin | lia]|].
intros i Hi. unfold c_nr in Hi.
exists (bv_unsigned (nth (Z.to_nat i) (c_xr v ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
split.
- rewrite <- (Hbc (Z.to_nat i)) by (rewrite length_app; cbn [length]; lia). f_equal. lia.
- rewrite app_nth1 by lia. intros Hb0. apply HNO0.
  assert (E : nth (Z.to_nat i) (c_xr v) (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hb0; reflexivity).
  rewrite <- E. apply nth_In. lia.
Qed.

(* the recorder's state carried from one reader to another that agrees on g_rec, record.spill and every block *)
Lemma acall_at_keep : forall bl bl' (rd rd' : reader) a c P,
acall_at bl rd a c P ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn, In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hk) K KP.
unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
split; [apply (aval_mem_agree rd); [intros x Hx; apply K; unfold CALL_OFF_FN in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact Hb0]|].
split; [apply (aval_mem_agree rd); [intros x Hx; apply K; unfold CALL_OFF_NARGS in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact Hb1]|].
split; [exact Hnd|].
intros k s pn Es Ep. destruct (Hk k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
destruct (KP pn Hin) as [Hin' Kp].
split; [apply (aval_mem_agree rd); [intros x Hx; apply K; unfold CALL_OFF_ARGS in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact Hs]|].
split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (astr_atR_agree rd); [|exact Hstr]. intros x Hx. replace x with (fst pn + (x - fst pn)) by lia. apply Kp. lia.
Qed.
Lemma arep_at_keep : forall bl bl' (rd rd' : reader) gr sc R Q,
arep_at bl rd gr sc R Q ->
(forall x, gr <= x < gr + REC_SIZE \/ sc <= x < sc + SC_SIZE -> rd' x = rd x) ->
(forall pn, In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (H8 & S8 & HAp & HC & HA & HP & HX & HW) KG KP.
assert (KG1 : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply KG; left; exact Hx).
assert (KS1 : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply KG; right; exact Hx).
unfold REC_SIZE, SC_SIZE in KG1, KS1.
split; [exact H8|]. split; [exact S8|]. split; [exact HAp|].
split; [|split; [|split; [|split; [|exact HW]]]].
- destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|].
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_NCALLS in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact C3]|].
  split.
  + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (acall_at_keep bl bl' rd rd'); [exact Hc | | exact KP].
    intros x Hx. apply KG1. unfold OFF_CALLS, CALL_SIZE in Hx. lia.
  + split; [|exact C6]. apply (acall_at_keep bl bl' rd rd'); [exact C5 | | exact KP].
    intros x Hx. apply KS1. unfold CALL_SIZE in Hx. lia.
- revert HA. unfold aanswer_at. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p n]|]; intros HA; try contradiction.
  + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6). cbn [fst snd] in *.
    destruct (KP (p, n) N3) as [Kin Kp]. cbn [fst snd] in Kp.
    split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_ANSWER in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact N1]|].
    split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
    apply (astr_atR_agree rd); [|exact N5]. intros x Hx. replace x with (p + (x - p)) by lia. apply Kp. lia.
  + apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_ANSWER in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact HA].
- revert HP. unfold areply_at. destruct (r_reply R) as [y|]; destruct (l_reply Q) as [[p n]|]; intros HP; try contradiction.
  + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
    destruct (KP (p, n) P5) as [Kin Kp]. cbn [fst snd] in Kp.
    split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_REPLY in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact P1]|].
    split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_REPLY_SIZE in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact P2]|].
    split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
    apply (abytes_atR_agree rd); [|exact P7]. intros x Hx. replace x with (p + (x - p)) by lia. apply Kp. lia.
  + destruct HP as [P1 P2].
    split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_REPLY in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact P1]|].
    apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_REPLY_SIZE in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact P2].
- destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_REFUSE in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact X1]|].
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_CODE in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact X2]|].
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_NREPLIES in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact X3]|].
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_STATE in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact X4]|].
  split; [apply (aval_mem_agree rd); [intros x Hx; apply KG1; unfold OFF_HOST in Hx; change (Z.of_nat 8) with 8 in Hx; lia | exact X5]|].
  exact X6.
Qed.

(* 3. the recorder's state at the mid-walk state *)
Lemma cr_rec_facts : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos -> rec_repA B lyc Sc (rdW Wc memc) (c_R v) (c_O v).
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Q & HQ & HO) & _).
pose proof HM as (HJ & HPERM & _).
exists Q. split; [|exact HO].
apply (arep_at_keep (ablocks B (c_ly v) (c_S v)) _ (rdW (c_W v) (c_mem v))); [exact HQ | |].
- intros x Hx. apply (aj_img_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). unfold REC_SIZE, SC_SIZE in Hx.
  destruct Hx as [Hx|Hx]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)];
  (split; [unfold cmd_PG; cbn [In]; tauto | cbn [fst snd]; lia]).
- intros [p n] Hin. cbn [fst snd].
  pose proof (Permutation_in _ (Permutation_sym HPERM) Hin) as Hinc.
  split; [exact Hinc|]. intros i Hi. exact (aj_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hin Hinc Hi).
Qed.

(* 4. the harness's words at the mid-walk state *)
Lemma cr_words_facts : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
c_w v mod 8 = 0 /\ range_addressable (rdW Wc memc) SHADOW_OFF (c_w v + WORDS_W) 12 /\
aval_mem (rdW Wc memc) (c_w v + WORDS_W) 8 (c_ww v) /\ aval_mem (rdW Wc memc) (c_w v + WORDS_N) 4 (c_n v) /\
(c_n v <> 0 ->
 in_blockA (ablocks B lyc Sc) (c_ww v) 8 /\ aval_mem (rdW Wc memc) (c_ww v) 8 (c_p0 v) /\
 in_blockA (ablocks B lyc Sc) (c_p0 v) (Z.of_nat (length (c_w0 v)) + 1) /\ astr_atR (rdW Wc memc) (c_p0 v) (c_w0 v) /\
 atail_vis SEGS Wc memc (c_p0 v + Z.of_nat (length (c_w0 v)))).
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW8 & HSPW & _ & HWW & HWN & _ & HWB & _ & _ & _ & _ & _ & HWHI).
pose proof HM as (HJ & HPERM & _).
pose proof HJ as (HARc & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof Hstk as (_ & HSTK0 & _ & Hslo & _ & H47 & _).
unfold c_sp in *. unfold WORDS_W, WORDS_N.
assert (KA : forall a, spZ (c_regs v) <= a < 2 ^ 64 -> rdW Wc memc a = rdW (c_W v) (c_mem v) a).
{ intros a Ha. exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha (inFP_nil a)). }
split; [exact HW8|]. split.
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HARc))) as (_ & _ & _ & _ & PAlo & PAhi & _).
  unfold page_aligned in PAlo, PAhi.
  pose proof (al_zshadow _ _ LAWS lyc Sc Wc memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HARc (or_introl eq_refl)) as Zs.
  apply (range_addressable_sub _ _ (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc)).
  - apply zero_shadow_range; [exact (mod4096_8 _ PAlo) | | exact Zs].
    rewrite Zminus_mod, (mod4096_8 _ PAlo), (mod4096_8 _ PAhi). reflexivity.
  - lia.
  - lia. }
split; [apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact HWW]; intros x Hx; apply KA; change (Z.of_nat 8) with 8 in Hx; lia|].
split; [apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact HWN]; intros x Hx; apply KA; change (Z.of_nat 4) with 4 in Hx; lia|].
intros Hn. destruct (HWB Hn) as ((q1 & k1 & Hq1 & Hq1a & Hq1b) & HV & (q2 & k2 & Hq2 & Hq2a & Hq2b) & HS & _).
pose proof (Permutation_in _ (Permutation_sym HPERM) Hq1) as Hq1c.
pose proof (Permutation_in _ (Permutation_sym HPERM) Hq2) as Hq2c.
split; [exists q1, k1; split; [exact Hq1c | lia]|].
split.
{ apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact HV]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  replace x with (q1 + (x - q1)) by lia. apply (aj_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hq1 Hq1c). lia. }
split; [exists q2, k2; split; [exact Hq2c | lia]|].
split.
{ apply (astr_atR_agree (rdW (c_W v) (c_mem v))); [|exact HS]. intros x Hx.
  replace x with (q2 + (x - q2)) by lia. apply (aj_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hq2 Hq2c). lia. }
apply (cmd_heap_tail_vis SEGS B LAWS HB lyc Sc Wc memc mdc q2 k2); [exact HARc | exact Hq2c |].
unfold req_size. destruct (Z.eqb_spec k2 0); lia.
Qed.

(* 5. g_rec's answer and reply pointers, and the bytes after each terminator *)
Lemma cr_answer_facts : forall v lyc Sc Wc memc mdc pos,
cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
aval_mem (rdW Wc memc) (A_G_REC + OFF_ANSWER) 8 (c_ans v) /\ aval_mem (rdW Wc memc) (A_G_REC + OFF_REPLY) 8 (c_rep v) /\
atail_vis SEGS Wc memc (c_rep v + c_nr v) /\
(forall xa, r_answer (c_R v) = Some xa -> atail_vis SEGS Wc memc (c_ans v + Z.of_nat (length xa))).
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & _ & _ & HREPV & _ & HANSV & _).
pose proof HM as (HJ & HPERM & _). pose proof HJ as (HARc & _). pose proof HPRE as (HAR0 & _).
assert (KG : forall x, A_G_REC <= x < A_G_REC + 960 -> rdW Wc memc x = rdW (c_W v) (c_mem v) x).
{ intros x Hx. apply (aj_img_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia]. }
split; [apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact HANSV]; intros x Hx; apply KG; unfold OFF_ANSWER in Hx;
  change (Z.of_nat 8) with 8 in Hx; lia|].
split; [apply (aval_mem_agree (rdW (c_W v) (c_mem v))); [|exact HREPV]; intros x Hx; apply KG; unfold OFF_REPLY in Hx;
  change (Z.of_nat 8) with 8 in Hx; lia|].
split.
- destruct (cr_reply_facts v lyc Sc Wc memc mdc pos HCX HM) as (m & _ & _ & _ & Htail & _).
  apply (atail_vis_mod _ _ _ (c_p v + c_nr v)); [|exact Htail].
  unfold c_p. rewrite Zplus_mod_idemp_l. reflexivity.
- intros xa Hxa.
  destruct HREP as (Q & (_ & _ & _ & _ & HA & _) & _).
  rewrite Hxa in HA. unfold aanswer_at in HA. destruct (l_answer Q) as [[p n]|]; [|contradiction].
  destruct HA as (N1 & _ & N3 & N4 & _). cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 N3) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n (proj1 Hn)) as [_ Hreq].
  assert (Ep : c_ans v mod 2 ^ 64 = p).
  { rewrite (aval_mem_mod64 _ _ _ _ HANSV N1). apply Z.mod_small. pose proof alloc_ceiling_lt. lia. }
  pose proof (Permutation_in _ (Permutation_sym HPERM) N3) as Hinc.
  apply (atail_vis_mod _ _ _ (p + Z.of_nat (length xa))).
  + rewrite <- Ep, Zplus_mod_idemp_l. reflexivity.
  + apply (cmd_heap_tail_vis SEGS B LAWS HB lyc Sc Wc memc mdc p n); [exact HARc | exact Hinc | lia].
Qed.

(* 6. the shadow of the image's objects at every AR state, from the allocator record's zero-shadow ranges and const
   shadow cells (CmdBSyms: ts_zsh, ts_const), by computation over a concrete range *)
Lemma shb_sound : forall ly S W mem md s v, AR SEGS B ly S W mem md -> shb s = Some v -> rdW W mem s = Some v.
Proof.
intros ly S W mem md s v HAR H. unfold shb in H.
destruct (zsh_byteb s) eqn:Ez.
- injection H as <-. unfold zsh_byteb in Ez. apply existsb_exists in Ez as ([lo len] & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in H1, H2.
  pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md (lo, len) HAR Hin) as Zs.
  unfold zero_shadow, shadow_of_addr in Zs. cbn [fst snd] in Zs.
  replace s with (SHADOW_OFF + lo / 8 + (s - (SHADOW_OFF + lo / 8))) by lia. apply Zs. lia.
- destruct (csh_val Tfib_const_shadow s) as [w|] eqn:Ec; [|discriminate]. cbn [option_map] in H. injection H as <-.
  pose proof (csh_val_in _ _ _ Ec) as Hin.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as C. rewrite (ts_const B HB) in C. rewrite Forall_forall in C.
  specialize (C _ ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; right; exact Hin)).
  cbv beta zeta iota delta [cell_holds c_at c_val YG0f.c_w] in C. cbn [aeval] in C.
  specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. exact C.
Qed.
Lemma cr_lit_addressable : forall ly S W mem md a n, AR SEGS B ly S W mem md -> lit_addr_okb a n = true ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hc x Hx. unfold lit_addr_okb in Hc. rewrite forallb_forall in Hc.
specialize (Hc (Z.to_nat (x - a)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hc by lia.
replace (a + (x - a)) with x in Hc by lia.
destruct (shb (SHADOW_OFF + x / 8)) as [s|] eqn:Es; [|discriminate].
exists s. split; [unfold shadow_of_addr; exact (shb_sound ly S W mem md _ s HAR Es)|].
unfold saddr_ok. apply orb_true_iff in Hc as [H|H]; [left; apply Z.eqb_eq; exact H|].
right. apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma cr_lit_hull : forall ly S W mem md a n, AR SEGS B ly S W mem md -> lit_hull_okb a n = true ->
shadow_hull_vis (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hc s Hs. unfold lit_hull_okb in Hc. cbv zeta in Hc. unfold shadow_addr in Hs.
rewrite forallb_forall in Hc. set (lo := (SHADOW_OFF + a / 8) / 8 * 8) in *.
specialize (Hc (Z.to_nat (s - lo)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hc by lia.
replace (lo + (s - lo)) with s in Hc by lia.
destruct (shb s) as [w|] eqn:Es; [|discriminate].
rewrite (shb_sound ly S W mem md s w HAR Es). discriminate.
Qed.
Lemma cr_lit_unowned : forall a n, lit_unowned_okb a n = true -> forall i, 0 <= i < n ->
~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4).
Proof.
intros a n Hc i Hi. unfold lit_unowned_okb in Hc. rewrite forallb_forall in Hc.
specialize (Hc (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hc by lia.
apply andb_true_iff in Hc as [H1 H2]. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros Hex. apply Exists_exists in Hex as (r & Hr & R1 & R2). apply negb_true_iff in H1.
  assert (Ht : existsb (fun r => (fst r <=? a + i) && (a + i <? fst r + snd r)) Tfib_owned_static = true).
  { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in H1. discriminate.
- intros He. apply negb_true_iff in H2. apply andb_false_iff in H2 as [H2|H2]; [apply Z.leb_gt in H2 | apply Z.ltb_ge in H2]; lia.
Qed.
(* a read-only literal of the image as the string argument the recorder's callees take (CmdRep.v astr_argA's
   read-only arm: the record's shadow checkers and the literal's end among CmdRo's literal ends) *)
Lemma cr_ro_arg : forall ly S (rd : reader) (O : list (Z * Z)) a x,
a <> 0 -> astr_atR rd a x -> Z.of_nat (length x) + 1 <= LMAX + 1 ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> in_roP SEGS RLO RHI (a + i)) ->
lit_unowned_okb a (Z.of_nat (length x) + 1) = true ->
cmd_addr_b a (Z.of_nat (length x) + 1) = true -> cmd_hull_b a (Z.of_nat (length x) + 1) = true ->
In (a + Z.of_nat (length x)) cmd_ro_ends ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O a (Some x).
Proof.
intros ly S rd O a x Ha0 Hs Hl Hro Hown Hadr Hhull Hend. unfold astr_argA. cbv zeta.
split; [exact Ha0|]. split; [exact Hs|]. split; [exact Hl|]. right.
split; [|split; [exact Hadr | split; [exact Hhull | exact Hend]]].
intros i Hi. split; [exact (Hro i Hi) | exact (cr_lit_unowned _ _ Hown i Hi)].
Qed.
(* mod-host's shape "resp 0" at 0x210e0, at the mid-walk state *)
Lemma cr_lit0_arg : forall v lyc Sc Wc memc mdc pos, cr_cx B RLO RHI v -> cr_mid B v lyc Sc Wc memc mdc pos ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] 0x210e0 (Some REC_MOD_HOST_SHAPE).
Proof.
intros v lyc Sc Wc memc mdc pos HCX HM.
destruct (cr_state_facts v lyc Sc Wc memc mdc pos HCX HM) as (_ & (HRB & _) & _ & _ & _ & _ & _ & HROIN & _).
pose proof HM as ((HARc & _) & _).
unfold cmd_ro_bytes in HRB.
repeat lazymatch type of HRB with
| abytes_atR _ 0x210e0 _ /\ _ => fail
| _ /\ _ => apply proj2 in HRB
end.
apply proj1 in HRB.
unfold cmd_ro_in in HROIN.
repeat lazymatch type of HROIN with
| (forall i, 0 <= i < 7 -> in_roP _ _ _ (0x210e0 + i)) /\ _ => fail
| _ /\ _ => apply proj2 in HROIN
end.
apply proj1 in HROIN.
apply (cr_ro_arg lyc Sc (rdW Wc memc)); [discriminate | | vm_compute; congruence | | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | cbv [cmd_ro_ends]; repeat (first [left; vm_compute; reflexivity | right])].
- split; [exact HRB|]. apply no0_nz. vm_compute. reflexivity.
- exact HROIN.
Qed.
(* g_rec's shadow at every AR state *)
Lemma cr_grec_addressable : forall ly S W mem md a n, AR SEGS B ly S W mem md -> A_G_REC <= a -> a + n <= A_G_REC + 960 ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR H1 H2.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00)); [exact HAR | | reflexivity | reflexivity
  | cbn [fst]; unfold A_G_REC in H1; lia | cbn [fst snd]; unfold A_G_REC in H2; lia].
unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
Qed.

End e.
End f.
End d.
