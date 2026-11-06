(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of sup_instance_info's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan) that need no callee statement: the walk's points in B's listing, the 122 slots, the
   96-byte frame and its realignment, the entry seed, the two image literals it hands to a callee and to the
   snprintf entry, and the frame chain each callee gets for s0 (achain_push on afn_pre's chain). In the form of
   lib/B/Prog/sup_reset_aux.v (a working branch 93eeb37e147: the listing facts, the literal's shadow from
   the allocator record, the seeds) after the A walks lib/A/Prog/sup_instance_info.v (a working branch
   0de7ca03d26) and lib/A/Prog/answer_code.v (a working branch 2ba4488ce71: the side-stack frame, its header
   and shadow, the realignment arithmetic) and lib/A/Prog/arg_i_s0.v, arg_i_s1.v (a working branch
   12dc52bfe84: the "%d" text). *)

(* B's sup_instance_info (recorder.c:395-401, entry BASE + AF_sup_instance_info = 0x8bb70, 122 instructions, 488
   bytes; measured with capstone 5.0.7 on the .symtab entry of fuzz_command.asan-ubsan, sha256 658cefbe806b...):
     0x8bb70 .. 0x8bbcc  the 96-byte frame (ra, s0 .. s8 saved), s0 = entry sp, `andi sp,sp,-32`, s1 = the
                         realigned sp, the shadow-base GOT word 0xa5f50 and the use-after-return GOT word 0xa5fa8
     0x8bbd0             jal __asan_stack_malloc_0 (0x3f954, request 64)
     0x8bbd4 .. 0x8bc64  the side-stack frame: its header (0x41b58ab3, the descriptor 0x15923, this entry 0x8bb70),
                         the shadow f1 f1 f1 f1 | f8 f8 | f3 f3, b = frame + 32
     0x8bc68             jal record (0x8a728, a0 = 9)
     0x8bc6c .. 0x8bc88  b's shadow 00 00, the format "%d" (0x21f40), n = 16, a0 = b, a3 = id
     0x8bc8c             jal the snprintf wrapper (0x451d0)
     0x8bc90 .. 0x8bc94  a0 = the slot, a1 = b
     0x8bc98             jal arg_s (0x8a820)
     0x8bc9c .. 0x8bcac  b's shadow f8 f8, the verb "instance_info" (0x21de0), len = 13
     0x8bcb0             jal rec_shape_of (0x896d4)
     0x8bcb4 .. 0x8bcbc  a0 = the slot, a1 = the shape, a2 = 0
     0x8bcc0             jal answer (0x8aa10)
     0x8bcc4 .. 0x8bd54  the frame's magic 0x45e0360e, its shadow f5 x8 and the flag byte through frame + 56
                         (the release), the epilogue and `ret`
   0 inline ASan checks (no call of an __asan_report entry) and 0 UBSan trap sites (no unimp or ebreak) in
   [0x8bb70, 0x8bd58): gen/traps.B.summary `sup_instance_info 0`, gen/funcs.tsv 0 reports. The real-stack fallback
   0x8bbe8-0x8bc00 (with the only loop, a page probe) and its release arm 0x8bd04-0x8bd20 are not walked: the
   use-after-return flag cell is a constant cell of the allocator record (lib/B/YF0m.v:88, `z4 (ANum 0xb0c40) 0x1`),
   read at the AR state through AR's const-cell law, so the branches at 0x8bbc8 and 0x8bcd0 take the side-stack arm.
   A's code (0x8b5d8, 64 instructions) has no side-stack frame: it inlines record() (with two checked stores and
   their two __asan_report_store4 edges) and calls arg_i; B calls record() and arg_s() instead and inlines arg_i,
   so it owns arg_i's frame and its snprintf call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
(* the plain proof's printf facts on "%d" (lib/Prog/arg_i.v:36-54) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.

(* ---- the walk's points in the listing ---------------------------------------------------------------------- *)
Definition SII_E : Z := AF_sup_instance_info.            (* the entry (0x8bb70) *)
(* the function the call records (REC_INSTANCE_INFO, the `li a0,9` before the call of record) *)
Definition SII_FN : Z := REC_INSTANCE_INFO.
(* the verb "instance_info": the image literal at 0x21de0 (CmdRo's RO_lit_21de0), the listing's object 68 *)
Definition SII_VERB : Z := 0x21de0.
Definition SII_VOBJ : nat := A_OBJ 68.
Definition sii_verb : list byte := bstr "instance_info"%string.
(* the format "%d" of the inlined arg_i: the literal at 0x21f40, the listing's object 51 *)
Definition SII_FMT : Z := 0x21f40.
Definition SII_FOBJ : nat := A_OBJ 51.

(* ---- the listing, the call targets, the model's step --------------------------------------------------------- *)

Lemma sii_af : cmd_af CS_record = AF_record /\ cmd_af CS_arg_s = AF_arg_s /\
cmd_af CS_rec_shape_of = AF_rec_shape_of /\ cmd_af CS_answer = AF_answer.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma sii_prog_syms : In CS_record cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
In CS_rec_shape_of cmd_prog_syms /\ In CS_answer cmd_prog_syms.
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

(* the model's step: record(9) with the printed instance number, the verb's shape, answer with changes = 0 *)
Lemma sii_m : forall R id,
sup_instance_info_m R id =
rec_answer (rec_record R SII_FN [dec id]) (SII_FN, [dec id]) (shape_of sii_verb) false.
Proof. reflexivity. Qed.

Lemma sii_verb_len : Z.of_nat (length sii_verb) = 13.
Proof. reflexivity. Qed.

Lemma sii_verb_lit : RO_lit_21de0 = sii_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma sii_verb_nonul : ~ In (Z_to_bv 8 0) sii_verb.
Proof.
intros Hz. apply (in_map bv_unsigned) in Hz. vm_compute in Hz.
repeat (destruct Hz as [Hz|Hz]; [discriminate Hz|]). exact Hz.
Qed.

Lemma sii_bytes_prefix : forall (rd : reader) a l l2, abytes_atR rd a (l ++ l2) -> abytes_atR rd a l.
Proof. intros rd a l l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity. Qed.

(* the conjunct of a long conjunction that holds the literal address [a] (sup_reset_aux.v's srb_projz) *)
Local Ltac sii_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

Lemma sii_verb_at_lit : forall rd, cmd_ro_ok rd -> abytes_atR rd SII_VERB RO_lit_21de0.
Proof. intros rd [HBY _]. unfold cmd_ro_bytes in HBY. unfold SII_VERB. sii_projz HBY 0x21de0. Qed.

Lemma sii_verb_str : forall rd, cmd_ro_ok rd -> astr_atR rd SII_VERB sii_verb.
Proof.
intros rd H. pose proof (sii_verb_at_lit rd H) as HL. rewrite sii_verb_lit in HL.
split; [exact HL | exact sii_verb_nonul].
Qed.

Lemma sii_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd SII_VERB sii_verb.
Proof. intros rd H. exact (sii_bytes_prefix _ _ _ _ (proj1 (sii_verb_str rd H))). Qed.

Lemma sii_verb_ro : forall ro : Z -> Prop, cmd_ro_in ro -> forall i, 0 <= i < 14 -> ro (SII_VERB + i).
Proof. intros ro HRI. unfold cmd_ro_in in HRI. unfold SII_VERB. sii_projz HRI 0x21de0. Qed.

Lemma sii_verb_end : In (SII_VERB + Z.of_nat (length sii_verb)) cmd_ro_ends.
Proof. unfold SII_VERB. cbn [length sii_verb]. vm_compute. repeat (first [left; reflexivity | right]). Qed.

Lemma sii_verb_addr_b : cmd_addr_b SII_VERB (Z.of_nat (length sii_verb) + 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sii_verb_hull_b : cmd_hull_b SII_VERB (Z.of_nat (length sii_verb) + 1) = true.
Proof. vm_compute. reflexivity. Qed.

(* the format literal "%d" at 0x21f40 *)
Lemma sii_fmt_at_lit : forall rd, cmd_ro_ok rd -> abytes_atR rd SII_FMT RO_lit_21f40.
Proof. intros rd [HBY _]. unfold cmd_ro_bytes in HBY. unfold SII_FMT. sii_projz HBY 0x21f40. Qed.

(* a byte range none of a concrete list of ranges holds *)
Lemma sii_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* ---- the inlined arg_i's text: snprintf(b, 16, "%d", id) ---- *)

Lemma sii_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.

(* the realigned sp: 32 * ((sp - 96) / 32) is sp - 96 or sp - 112 *)
Lemma sii_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
(32 * ((x - 96) / 32) = x - 96 \/ 32 * ((x - 96) / 32) = x - 112) /\
(32 * ((x - 96) / 32)) mod 32 = 0 /\ (32 * ((x - 96) / 32) - x) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod (x - 96) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (x - 96) 32 ltac:(lia)) as M.
assert (Hm : (x - 96) mod 32 = 0 \/ (x - 96) mod 32 = 16)
  by (pose proof (Z.div_mod x 16 ltac:(lia)) as D2; rewrite H16 in D2; lia).
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
destruct Hm as [Hm|Hm]; [replace (32 * ((x - 96) / 32) - x) with (-96) by lia
                        |replace (32 * ((x - 96) / 32) - x) with (-112) by lia]; reflexivity.
Qed.

(* ---- pure list facts ---- *)

Lemma sii_nodup_disj : forall {X : Type} (l1 l2 : list X) a, List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 a H H1 H2; [destruct H1|].
cbn in H. apply List.NoDup_cons_iff in H as [Hx H].
destruct H1 as [<- | H1]; [apply Hx, in_app_iff; right; exact H2 | exact (IH l2 a H H1 H2)].
Qed.

Lemma sii_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
intros [a b] [c d]. destruct (Z.eq_dec a c) as [<-|Hn]; [|right; intros Hq; injection Hq; auto].
destruct (Z.eq_dec b d) as [<-|Hn]; [left; reflexivity | right; intros Hq; injection Hq; auto].
Qed.

(* ---- strings and the recorder's blocks over a reader ---- *)

Lemma sii_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma sii_abytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.

Lemma sii_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (sii_abytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.

Lemma sii_acall_in : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HL & _ & _ & _ & H6) pn Hpn.
destruct (In_nth_error _ _ Hpn) as (k & Hk).
assert (Hlt : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hlt; contradiction].
exact (proj1 (proj2 (proj2 (H6 k s pn Hs Hk)))).
Qed.

(* every block the representation names is a live block *)
Lemma sii_arep_in : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> forall pn, In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _ & _) pn Hpn.
unfold lay_blocks in Hpn. apply in_app_or in Hpn as [Hc | Hpn]; [|apply in_app_or in Hpn as [Hs | Hpn]; [|apply in_app_or in Hpn as [Ha | Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as (i & Hi).
  destruct HC as (_ & HlenQ & _ & Hcalls & _).
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- HlenQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc'; [|apply nth_error_Some in Hlt; contradiction].
  exact (sii_acall_in _ _ _ _ _ (proj1 (Hcalls i c P Hc' Hi)) pn Hin).
- destruct HC as (_ & _ & _ & _ & Hsp & _). exact (sii_acall_in _ _ _ _ _ Hsp pn Hs).
- unfold aanswer_at in HA. destruct (r_answer R) as [xa|], (l_answer Q) as [pa|]; cbn [oblk In] in Ha; try contradiction.
  destruct Ha as [<- | []]. exact (proj1 (proj2 (proj2 HA))).
- unfold areply_at in HR. destruct (r_reply R) as [xr|], (l_reply Q) as [pr|]; cbn [oblk In] in Hr; try contradiction.
  destruct Hr as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
Qed.

(* ---- the symbolic entry state ------------------------------------------------------------------------------ *)
(* atoms above the 32 registers: 32 = the shadow base, 33 = the use-after-return flag cell, 34 = the realigned sp *)
Definition sii_extra (uar sp1 : Z) : list word := map (Z_to_bv 64) [SB; uar; sp1].
(* the entry's regions: the word the prologue zeroes at sp - 96, the ten saved registers at sp - 80 .. sp, the
   word `sd s7,8(s1)` writes at sp1 + 8, the two GOT words and the two cells they point at *)
Definition sii_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [];
 YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [];
 YP09.mkRegion (Some 34%nat) 8 16 8 16 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sii_facts0 : facts :=
 mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition sii_ss0 : sstate := mkSS SII_E sr_atoms sii_regions0 None sii_facts0.

(* the side-stack frame's regions: its header (the magic, the descriptor and this entry), the flag word at
   frame + 56, and the frame's eight shadow bytes *)
Definition sii_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition sii_fr_flg : YP09.region :=
 YP09.mkRegion (Some 1028%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition sii_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [].
Definition sii_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the format's and the verb's shadow checks, decided by computation and turned into the semantic facts by
   a Theorem Labs lane's B CmdRecFacts (cmd_addressable_chk / cmd_hull_vis_chk / cmd_aread_ok_chk, lib/B/Prog/CmdRecBase.v) *)
Lemma sii_fmt_addr_b : cmd_addr_b SII_FMT 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sii_fmt_hull_b : cmd_hull_b SII_FMT 3 = true.
Proof. vm_compute. reflexivity. Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the two literals' object atoms hold their addresses *)
Lemma sii_vobj_verb : cmd_val_objs -> VAL SII_VOBJ = SII_VERB.
Proof. intros VOBJS. unfold SII_VOBJ. rewrite (VOBJS 68%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma sii_vobj_fmt : cmd_val_objs -> VAL SII_FOBJ = SII_FMT.
Proof. intros VOBJS. unfold SII_FOBJ. rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma sii_region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma sii_aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* --- the verb literal's premise for rec_shape_of ------------------------------------------------------------ *)
Section hb.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name (RECB-NAMED-HYPS.md) *)
Hypothesis HB : CmdBSyms B.

(* the verb's bytes, the premise rec_shape_of's statement (lib/B/Prog/rec_shape_of_c.v:91-94) asks of them *)
Lemma sii_verb_ok : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
abytes_atR (rdW W mem) SII_VERB sii_verb /\
(in_blockA (ablocks B ly S) SII_VERB (Z.of_nat (length sii_verb)) \/
 astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] SII_VERB (Some sii_verb)).
Proof.
intros ly S W mem md HAR HROK HRI.
split; [exact (sii_verb_bytes _ HROK)|]. right. cbn [astr_argA]. rewrite sii_verb_len.
split; [unfold SII_VERB; lia|]. split; [exact (sii_verb_str _ HROK)|].
split; [unfold LMAX; lia|]. right. split; [|split; [exact sii_verb_addr_b | split; [exact sii_verb_hull_b | exact sii_verb_end]]].
intros i Hi. split; [exact (sii_verb_ro _ HRI i ltac:(lia))|].
rewrite (ts_owned B HB), (ts_errno B HB). split.
- apply (sii_unowned_rng SII_VERB 14); [vm_compute; reflexivity | lia].
- unfold TFIB_ERRNO, SII_VERB. lia.
Qed.
End hb.

(* --- the call targets: record (0x8bc68), arg_s (0x8bc98), rec_shape_of (0x8bcb0), answer (0x8bcc0) ---------- *)
Section s.
(* a Theorem Labs lane states it only at PI := PB_cmd (CmdRecRest.v cmd_sig_prog_PB), so it is a Section
   hypothesis under that lemma's name *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Lemma sii_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s (proj1 (proj2 sii_prog_syms))), (proj1 (proj2 sii_af)). reflexivity. Qed.
Lemma sii_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof.
rewrite (cmd_sig_prog_PB CS_rec_shape_of (proj1 (proj2 (proj2 sii_prog_syms)))), (proj1 (proj2 (proj2 sii_af))). reflexivity.
Qed.
Lemma sii_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof.
rewrite (cmd_sig_prog_PB CS_answer (proj2 (proj2 (proj2 sii_prog_syms)))), (proj2 (proj2 (proj2 sii_af))). reflexivity.
Qed.
End s.

(* --- the recorder's blocks and the frame chain ------------------------------------------------------------- *)

Lemma sii_rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply (sii_arep_in _ rd A_G_REC A_REC_SPILL R Q HA). apply HO. exact Hpn.
Qed.

(* the statement's footprint (g_rec, record.spill and the recorder's blocks) lies below the allocator's ceiling *)
Lemma sii_FP_low : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall a, inFP ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O HAR HREP a Ha. pose proof asan_consts as (C1 & _).
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, REC_SIZE in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hbm & Hba).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (sii_rec_repA_in ly S _ R O HREP (b, m) Hbm)) as (_ & _ & Hbc & _). lia.
Qed.

(* the entry's frame chain read at a later state of the walk: the journal keeps every stack byte from the entry
   sp up (its frame clause; the footprint lies below alloc_ceiling) *)
Lemma sii_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

(* a callee's frame chain for s0 = the entry sp (the frame pointer, 0x8bba0): the prologue saved ra at sp0 - 8 and
   the caller's s0 at sp0 - 16 (0x8bb78, 0x8bb7c), so the chain is that record on top of afn_pre's chain
   (achain_push), or the empty chain when sp0 is within 16 bytes of the top *)
Lemma sii_chain_at : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k s0 ch ra sp',
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 s0 ch ->
rdword (rdW W' mem') (sp0 - 8) = Some ra -> rdword (rdW W' mem') (sp0 - 16) = Some s0 -> 4096 <= ra ->
sp' + 16 <= sp0 ->
exists ch', achain ly' (rdW W' mem') sp' sp0 ch'.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k s0 ch ra sp' HJ HF Hc H8 H16 Hra Hsp'.
pose proof (sii_achain_kept STK sp0 FP ly S W mem md own ly' S' W' mem' md' k s0 ch HJ HF Hc) as Hc'.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal in D. rewrite D.
  replace (16 * (sp0 / 16) + 0) with ((2 * (sp0 / 16)) * 8) by lia. apply Z_mod_mult. }
destruct (Z_lt_le_dec sp0 (ly_top ly' - 16)) as [Hlt | Hge].
- exists ((sp0, ra, s0) :: ch).
  apply (achain_push ly' (rdW W' mem') (rdW W' mem') sp0 s0 ra ch sp' Hc'); try assumption.
  + rewrite Etop. lia.
  + intros a _. reflexivity.
  + lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* the recorder's state survives a change of reader that keeps g_rec, record.spill and its own blocks *)
Lemma sii_rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE,
  OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
assert (Hcall : forall bl bl' a c P, acall_at bl rd a c P ->
  (forall pn, In pn P -> In pn bl') ->
  (forall i, 0 <= i < 8 + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
  (forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
  acall_at bl' rd' a c P).
{ intros bl bl' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl' Ha' Hp.
  unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (sii_aval_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha';
    pose proof (Nat2Z.is_nonneg (length (snd c))); apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; lia]|].
  split; [apply (sii_aval_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha';
    pose proof (Nat2Z.is_nonneg (length (snd c))); apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; lia]|].
  split; [exact H6|].
  intros k se pn Hse Hpn. destruct (H7 k se pn Hse Hpn) as (K1 & K2 & K3 & K4 & K5).
  pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hse; discriminate)) as Hk.
  split; [apply (sii_aval_kept rd); [exact K1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha'; lia]|].
  split; [exact K2|]. split; [apply Hbl'; exact (nth_error_In _ _ Hpn)|]. split; [exact K4|].
  apply (sii_astr_kept rd); [exact K5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]]. }
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
  split; [apply (sii_aval_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
  split.
  - intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
    pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
    pose proof HC as (_ & HL6 & _).
    apply (Hcall (ablocks B ly S) _ _ _ _ HC).
    + intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P.
      split; [exact (nth_error_In _ _ Hp) | exact Hpn].
    + intros j Hj. rewrite <- !Z.add_assoc. apply Hg. lia.
    + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P.
      split; [exact (nth_error_In _ _ Hp) | exact Hpn].
  - split; [|exact C6].
    pose proof C5 as (_ & HL6s & _).
    apply (Hcall (ablocks B ly S) _ _ _ _ C5).
    + intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
    + intros j Hj. apply Hs. lia.
    + intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
  - destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
    assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
      by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
    split; [apply (sii_aval_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
    split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
    split; [apply (sii_astr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
  - apply (sii_aval_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
  - destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
      by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
    split; [apply (sii_aval_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
    split; [apply (sii_aval_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
    split; [apply (sii_abytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
  - destruct Hr as [A1 A2]. split; apply (sii_aval_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (sii_aval_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (sii_aval_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (sii_aval_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (sii_aval_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (sii_aval_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

(* the block the recorder's answer field points at is one of the recorder's blocks O (it is the only live block
   that starts at old; old = 0 when there is no answer) *)

End e.
End f.
End d.
